/++
Structure and interpretation of Gyre nodes.

This module implements Gyre nodes (and edges).
Each structure's documentation also explains its intended semantics, albeit this may be mixed with implementation details.


Poison_values_and_UB:

In Gyre, every operation may have some conditions imposed on its inputs in order to produce correct behavior / a sane value.
When the result of a data-only operation isn't well-defined (e.g. integer division by zero), it produces a "poison".
Poison values, as in [LLVM](https://llvm.org/docs/LangRef.html#poison-values), indicate invalid program behavior;  it is as if every instance of a poison value came from the result of `0/0`.
Furthermore, these values are "poisonous" because any operation with a result which depends on a poison operand will also produce poison.
Note that in some cases a result doesn't actually depend on the value of (all of) its operands (e.g. `x * 0` is always `0`).

This is not unlike C's infamous "Undefined Behavior", because a Gyre compiler may (while respecting program semantics) assume that poison values are never used, which in turn may help with some optimizations (e.g. [loop-invariant code motion](https://en.wikipedia.org/wiki/Loop-invariant_code_motion)).
Another option is to issue warnings or errors when such erroneous behavior is detected.
In this specific implementation, we don't (by default) do aggressive optimizations based on U.B. / poison usage.


Prim_ops_rationale:

It's hard to justify our choice of primitive operations when we know binary `NAND` would have sufficed to express most of them.
We're essentially copying existing IRs (LLVM, MLIR, Thorin, SPIR-V, WASM, etc), which raise the abstraction level to two's complement integer arithmetic.
Reasoning at that level makes it easier to perform trivial transformations and optimizations (which would require deeper pattern matching if using `NAND`s only).
Then, due to C's status as a $(I de facto) $(I lingua franca) of programming languages, having our primitive operations match that lowest common denominator will probably benefit compiler performance in most cases, which wouldn't be as true if our primitives were completely different than C's.


No_overflow_operations:

Some of the last primitives to be added were the "no-overflow" variants of some operations.
They could have been expressed with [MacroNode|macro node]s, and having them as primitives means that we're introducing more situations in which the same value is being produced at different nodes.
However, the signed versions are very frequent operations in C-derived languages and we wouldn't want the compiler to lose performance whenever they're used.
And they exist for good reason, as they really do help the compiler perform more arithmetic simplifications, especiallly when combining different operations in the same expression (e.g. `(x * 30) / 15` can only be transformed into `x * 2` if overflow is not a possibility).
In short: even if the operation being performed is the same, the no-overflow versions carry more information about their operands.

To be clear: a no-overflow node performs the same operation as its wrap-on-overflow version, but there's an implicit contract put on its arguments.
This contract states that the operation could have been computed over wider integer types, but the result would still be the same.
As an example, take the expression `(x << 1) >> 1`.
If we assume that `<<` can overflow (i.e. `x` has a non-zero MSB which is being thrown away), this is equivalent to `x & 0b011...11` (i.e. set the MSB to zero); by assuming that overflow is not possible, the expression can be reduced to just `x` (because if we had used a wider integer, that would have been the result).
+/
module gyre.nodes;

import core.stdc.errno : EINVAL, ENOMEM;
import std.algorithm.mutation : moveEmplace;
import std.bitmanip : taggedPointer;
import std.traits : EnumMembers;

import eris.core : hash_t, err_t, allocate, deallocate;
import eris.hash_table;


/++
Possible edge kinds.

Please note the directionality difference between "dependency" and "flow" edges.


Each Gyre node has one or more "edge slots", which act as directed connectors.
This means that nodes don't reference each other directly.
Instead, they contain slots which connect to the slots of other nodes.
There are different kinds of edge slots, which indicate their meaning.
RULE: Every pair of connecting edge slots must have a matching kind.

See_Also: [OutEdge], [InEdge]
+/
enum EdgeKind : ubyte {
    /// A control flow edge going from node A to B indicates that, after control reaches node A, it may then proceed to B. Multiple control flow edges leaving a node indicate either concurrency or a decision point (e.g. an `if`).
    control,

    /// Data dependency edges represent use-def relations. They go from nodes using the value to the one which produced it.
    data,

    /// Memory dependencies are mostly like discriminated data dependencies. They must be treated differently because, unlike data dependencies which represent immutable values, memory is mutable and thus subject to more scheduling constraints, aliasing problems and data races.
    memory,

    /// Type dependencies represent compile-time values carrying type information.
    type,
}

private mixin template StaticEdgeFactories() {
    static foreach (kind; EnumMembers!EdgeKind) {
        mixin(
            "@nogc nothrow pure
            static typeof(this) " ~ __traits(identifier, EnumMembers!EdgeKind[kind]) ~ "(Args...)(auto ref Args args) {
                import core.lifetime : forward;
                return typeof(this)(
                    EdgeKind." ~ __traits(identifier, EnumMembers!EdgeKind[kind]) ~ ",
                    forward!args
                );
            }"
        );
    }
}

/++
An outgoing edge slot.

Connects to either zero or exactly one [InEdge].
+/
struct OutEdge {
    mixin(taggedPointer!(
        InEdge*, "target",
        EdgeKind, "_kind", 2
    ));

 pragma(inline) @nogc nothrow:
    @property EdgeKind kind() const pure {
        return this._kind;
    }

    /++
    Params:
        kind = This edge's kind, fixed on construction.
        target = Must point to a matching in-edge slot.
    +/
    this(EdgeKind kind, InEdge* target = null) pure
    in (target == null || target.kind == kind, "connecting edge slots must have matching kinds")
    {
        this._kind = kind;
        this.target = target;
    }
    @disable this();
    mixin StaticEdgeFactories;

    /++
    Semantic equality check.

    An out-edge slot is only equivalent to another if they point to equal [InEdge] slots.
    +/
    bool opEquals(const(OutEdge) other) const {
        if (this.kind != other.kind) return false;
        if (this.target == other.target) return true;
        if (this.target == null || other.target == null) return false;
        return *this.target == *other.target;
    }

    hash_t toHash() const {
        if (this.target == null) return this.kind.hashOf;
        assert(this.target.kind == this.kind);
        return this.target.toHash();
    }
}

///
@nogc nothrow unittest {
    auto def = InEdge.data;
    auto use1 = OutEdge.data;
    auto use2 = OutEdge.data;
    // data edges are directed from uses to defs
    use1.target = &def;
    use2.target = &def;
    assert(use1 == use2);
}

/// Out-edges are essentially pointers:
@nogc nothrow pure unittest {
    static assert(OutEdge.sizeof <= (InEdge*).sizeof);
}

/++
An incoming edge slot.

Can receive any number of [OutEdge]s.


When we describe our [structural sharing strategy](gyre.nodes.Node.html#details), one may be tempted to associate the notion of an SSA name to a Gyre node.
This would be perfectly valid if every node could produce at most one value, but this is not the case.
Therefore, most structural node comparisons actually translate into a series of in-edge slot semantic equality checks.
+/
struct InEdge {
    mixin(taggedPointer!(
        Node*, "owner",
        EdgeKind, "_kind", 2
    ));

    ID id;
    alias ID = ushort;

 pragma(inline) @nogc nothrow:
    @property EdgeKind kind() const pure {
        return this._kind;
    }

    /++
    Params:
        kind = This edge's kind, fixed on construction.
        owner = Must point to the node which owns this edge slot.
        id = Uniquely identifies this in-edge slot within its owner node (internal usage only).
    +/
    this(EdgeKind kind, Node* owner = null, size_t id = 0) pure
    in (id <= ID.max, "can't have an internal id greater than " ~ ID.max.stringof)
    {
        this._kind = kind;
        this.owner = owner;
        this.id = cast(ID)id;
    }
    @disable this();
    mixin StaticEdgeFactories;

    /++
    Semantic equality check.

    An in-edge slot is only equivalent to another if they represent equal values.
    We approximate this by checking that the slots' owner nodes are equal AND the slots are in a corresponding position in their respective owner (i.e. they stand for the same thing inside that node).
    +/
    bool opEquals(ref const(InEdge) other) const
    {
        if (this.kind != other.kind) return false;
        if (this.id != other.id) return false;
        if (this.owner == null && other.owner == null) return true;
        if (this.owner == null || other.owner == null) return false;
        return *this.owner == *other.owner;
    }

    hash_t toHash() const {
        hash_t hash = this.kind.hashOf ^ this.id.hashOf;
        if (this.owner != null) hash ^= this.owner.toHash();
        return hash;
    }
}

///
@nogc nothrow pure unittest {
    auto A = OutEdge.control;
    auto B = InEdge.control;
    // control is flowing out from A and into B
    A.target = &B;
    assert(A.target.owner is B.owner);
}


/++
Common prefix shared by all nodes, safely used ONLY through indirections.

References to this substructure can be used as [type-punned](https://en.wikipedia.org/wiki/Type_punning) handles to any of our nodes.


SSA form is one of Gyre's key aspects.
It can be summarized as an attempt to make program values and variable names correspond one-to-one.
In a graph, we swap 'names' for 'edges' (or pointers, in our case).
We'll try to make all uses of a specific value point to the same edge slot.

This is essentially [GVN](https://en.wikipedia.org/wiki/Value_numbering).
Doing this perfectly in all cases has a prohibitive canonicalization cost, so we approximate it on a per-node basis: whenever we're about to add a new node to the graph, we'll check if it is redundant, in which case its uses can be rewired into the existing graph.
This check requires a way to compare two nodes (and [InEdge]s) for "semantic equality", i.e., whether swapping one for the other preserves program semantics.

In data-only operations, this usually reduces to structural equality: a node produces the same value (in a corresponding [InEdge] slot) as another when they perform the same operation and their inputs are equal (notice the recursion here).
Structural comparisons are relatively expensive operations (especially since the graph could be cyclic), so we want to leverage hashing to do as few comparisons as possible.
Therefore, a node's hash value better reflect its semantic structure: having equal hashes is a necessary (but insufficient) condition for two nodes to be equal.
Now, computing a node's hash value becomes an expensive operation as well.
Fortunately, hash values can be cached once a node's structure has stabilized.

$(SMALL_TABLE
    Name        | Type              | Description
    ------------|-------------------|------------
    `hash`      | `hash_t`          | A node's cached hash value. This is what gets returned when `toHash` is called on a generic [Node], so it should be updated (see [updateHash]) whenever a node's semantic structure stabilizes.
    `asNode`    | `ref T -> Node*`  | Method which upcasts (and this always works) a concrete node `ref` to a generic `Node*`.
    `ofNode`    | `Node* -> T*`     | Static method which tries to downcast a generic `Node*` to a pointer to a concrete type, returning `null` when the cast would have resulted in an invalid reference (so this is technically type-safe).
)
+/
struct Node {
 package:
    struct VTable {
     @nogc nothrow:
        bool function(const(Node)*, const(Node)*) opEquals = null;
        hash_t function(const(Node)*) toHash = null;
    }

    struct CommonPrefix {
        immutable(VTable)* vptr;
        hash_t hash;
    }

    CommonPrefix _node;
    alias _node this;

 public pragma(inline) @nogc nothrow:
    /++
    Updates a node's cached hash value.

    Uses a type-specific `toHash` function to compute the new value.
    +/
    void updateHash() {
        this.hash = this.vptr.toHash(&this);
    }

    /++
    Compares two nodes for semantic equality.

    Since this could be an expensive operation, early exits are checked before any virtual call.
    Thus, type-specific equality functions will only be called on non-aliased same-kind nodes whose cached hash values are equal.

    Returns: True if and only if one node can be substituted by the other, while still maintaining program semantics (after an adequate rewiring of the substituted node's in-neighbors).
    +/
    bool opEquals(ref const(Node) other) const {
        const(Node)* lhs = &this;
        const(Node)* rhs = &other;
        if (lhs == rhs) return true;
        if (lhs.vptr != rhs.vptr) return false;
        if (lhs.hash != rhs.hash) return false;
        return lhs.vptr.opEquals(lhs, rhs);
    }

    /// Returns this node's (assumedly [updateHash|up to date]) cached hash value.
    hash_t toHash() const pure {
        return this.hash ^ this.vptr.hashOf;
    }
}

static assert(
    Node.sizeof == Node.CommonPrefix.sizeof && Node.alignof == Node.CommonPrefix.alignof &&
    is(typeof(Node._node) == Node.CommonPrefix) && Node._node.offsetof == 0,
    "`Node` and `Node.CommonPrefix` must be binary-interchangeable"
);

private mixin template NodeInheritance() {
    private alias This = typeof(this);

    package Node.CommonPrefix _node = { vptr: &vtbl };
    alias _node this;
    invariant (this.vptr == &vtbl);

    package static immutable(Node.VTable) vtbl = {
        opEquals: (const(Node)* lhs, const(Node)* rhs) {
            const(This)* self = This.ofNode(lhs);
            const(This)* other = This.ofNode(rhs);
            assert(self != null && other != null);
            static assert(
                __traits(hasMember, This, "opEquals"),
                "all nodes must explicitly define an `opEquals` function"
            );
            return *self == *other;
        },
        toHash: (const(Node)* node) {
            const(This)* self = This.ofNode(node);
            assert(self != null);
            static assert(
                __traits(hasMember, This, "toHash"),
                "all nodes must explicitly define a `toHash` function"
            );
            return self.toHash();
        },
    };

    public pragma(inline) @nogc nothrow {
        void updateHash() {
            this._node.hash = this.toHash();
        }

        static assert(
            This._node.offsetof == 0,
            "common node prefix must be at a zero offset for safe polymorphism"
        );

        inout(Node)* asNode() inout pure
        return /// XXX: return annotation needed in DMD 2.100.0
        {
            return cast(inout(Node)*)&this._node;
        }

        static inout(This)* ofNode(inout(Node)* node) pure {
            if (node == null || node.vptr != &vtbl) return null;
            return cast(inout(This)*)node;
        }
    }
}

version (unittest) private { // for some reason, this needs to be in global scope
    static bool usingCustomHash;
    static bool usingCustomEquals;

    struct UnittestNode {
        mixin NodeInheritance;
        int value;

     @nogc nothrow:
        this(int value) { this.value = value; }

        bool opEquals(ref const(UnittestNode) rhs) const {
            debug usingCustomEquals = true;
            return this.value == rhs.value;
        }

        hash_t toHash() const {
            debug usingCustomHash = true;
            return this.value;
        }
    }
}

@nogc nothrow unittest {
    import eris.util : HashablePointer;

    // subtype inherits Node's properties and methods
    auto test = UnittestNode(1);
    assert(is(typeof(test.hash) == typeof(Node.hash)));
    debug usingCustomHash = false;
    test.updateHash();
    debug assert(usingCustomHash);

    // subtype's opEquals works normally
    debug usingCustomEquals = false;
    auto test2 = UnittestNode(1);
    assert(test == test2);
    auto other = UnittestNode(0);
    assert(test != other);
    debug assert(usingCustomEquals);

    HashablePointer!Node node = test.asNode;
    HashablePointer!Node node2 = test2.asNode;

    // they also dispatch correctly when using a polymorphic node
    HashSet!(HashablePointer!Node) polymorphic;
    node.updateHash();
    polymorphic.add(node);
    node2.updateHash();
    polymorphic.add(node2);
    assert(polymorphic.length == 1); // since test and test2 are equal
    assert(*node != *other.asNode); // these are still different, tho
}


/++
Gyre's main mechanism for procedural abstraction, the join node.

Join nodes can be used as procedures, basic blocks or synchronization points.


Join nodes are used to define the (external) interface and (internal) contents of procedures and basic blocks.
They interact with the outside world through zero or more parameters.
As a join node begins to execute, control flows into its body, where all of its parameters are made available.
Therefore, a join node behaves like the entry block of a CFG, but with a collection of SSA phis (one for each parameter); so it can be used as an [extended basic block](https://mlir.llvm.org/docs/Rationale/Rationale/#block-arguments-vs-phi-nodes).
RULE: Gyre graphs can be cyclic, but only if every cycle goes through a join node.
This is similar to having a DFG with SSA phis, in which data-flow can still be considered causal as long as every cycle goes through phi nodes, indicating a "temporal" control-flow dependency.

Since join nodes define subprocedures, one may want to know where such a definitions begins and ends.
A join node's scope begins with all of its parameters and control flow edges.
Furthermore, whenever another node is connected to part of a join node's scope, it also becomes part of that scope.
In other words: a join node's scope is implicitly defined by the set of nodes which (a) are transitively reachable by control flow in its body or (b) have a transitive dependency on any one of its parameters.
This idea comes from [Thorin](https://compilers.cs.uni-saarland.de/papers/lkh15_cgo.pdf)'s implicit scopes.
RULE: Two scopes cannot intersect unless one is fully contained within the other.

The only way in which a Gyre subgraph may refer to a join node without becoming part of its scope is through an indirection: the join node's "definition" edge.
Through its definition, external code may [InstantiationNode|instantiate] and [JumpNode|invoke] a join node.
Since a join node's body may use any of its parameters, it can only begin executing when they were all provided by the calling code.
Furthermore, parameters are divided into (one or more) groups, called channels.
All parameters within a channel need to be provided at the same time, but each channel can receive its inputs from a different source in the calling code.
Thus, join nodes can also be used to merge concurrent control flows, which should not be surprising to those familiar with the join calculus: join nodes correspond to linear [join patterns](https://en.wikipedia.org/wiki/Join-pattern).

See_Also: [InstantiationNode], [JumpNode], [ForkNode]
+/
struct JoinNode {
    mixin NodeInheritance;

    /// This join node's definition (a `data` slot), used to instantiate and invoke it.
    InEdge definition;

    /// Control flow edge into the join node's body.
    OutEdge control;

    /// Non-empty collection of channels, each containing zero or more of this node's parameters (either data or memory edges).
    InEdge[][] channels;

 @nogc nothrow:
    /++
    Initializes a join node, must be later [dispose]d.

    Params:
        self = Address of node being initialized.
        channels = Defines this join node's interface.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid edge kinds).
    +/
    static err_t initialize(JoinNode* self, EdgeKind[][] channels)
    in (self != null && channels.length >= 1)
    {
        if (self == null) return EINVAL;
        if (channels.length == 0) return EINVAL;
        foreach (parameters; channels) {
            foreach (paramKind; parameters) {
                with (EdgeKind) final switch (paramKind) {
                    case data, memory: break;
                    case control, type: return EINVAL;
                }
            }
        }
        *self = JoinNode.init;

        self.vptr = &JoinNode.vtbl;
        self.definition = InEdge.data(self.asNode, 0);
        self.control = OutEdge.control;

        self.channels = allocate!(InEdge[])(channels.length);
        if (self.channels == null) return ENOMEM;

        InEdge.ID id = 0;
        foreach (i, parameters; channels) {
            self.channels[i] = allocate!InEdge(parameters.length);

            // on failure, undo all previous allocations
            if (parameters.length > 0 && self.channels[i] == null) {
                foreach_reverse (previous; 0 .. i) self.channels[previous].deallocate();
                self.channels.deallocate();
                return ENOMEM;
            }

            foreach (j, paramKind; parameters) {
                self.channels[i][j] = InEdge(paramKind, self.asNode, 1 + id);
                id++;
            }
        }

        return 0;
    }

    /// ditto
    static err_t initialize(JoinNode* self, EdgeKind[] parameters ...) {
        EdgeKind[][1] channels = [parameters];
        return JoinNode.initialize(self, channels);
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(JoinNode* self) {
        foreach_reverse (ref parameters; self.channels) {
            parameters.deallocate();
        }
        self.channels.deallocate();
        *self = JoinNode.init;
    }

    /++
    Semantic equality check.

    Every join node has its own identity, so no two are equal.
    NOTE: We use join nodes as cycle breakers when doing structural comparison (since that's a cheap way to avoid infinite recursion), therefore the cycle rule MUST be maintained by container graphs.
    +/
    bool opEquals(ref const(JoinNode) rhs) const {
        return this.asNode == rhs.asNode; // self-ptr
    }

    hash_t toHash() const {
        return this.asNode.hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(JoinNode) old) pure {
        this.definition.owner = this.asNode;
        foreach (parameters; this.channels) {
            foreach (ref param; parameters) {
                param.owner = this.asNode;
            }
        }
    }
}

nothrow unittest {
    // initialize one guy
    JoinNode tmp = void;
    with (EdgeKind) JoinNode.initialize(&tmp, data, memory, data, data);
    // move it
    JoinNode join = void;
    moveEmplace(tmp, join);
    // check if everything's fine
    assert(join == join);
    assert(join.definition.owner == join.asNode);
    assert(join.channels.length == 1);
    assert(join.channels[0].length == 4);
    // free it
    JoinNode.dispose(&join);
}

/++
Instantiates a [JoinNode|join node].

Join nodes correspond to static ("dead") subprograms.
In order to actually use a join node, one must first create a "live" instance of it.
The result of such an instantiation is a non-empty collection of continuations, one for each channel in the join pattern.
Then, using a continuation requires one to provide its parameters and [JumpNode|jump] into it.

See_Also: [JoinNode], [JumpNode]
+/
struct InstantiationNode {
    mixin NodeInheritance;

    /// Points to the definition of the join node being instantiated.
    OutEdge definition;

    /// Non-empty collection of live continuations, each corresponding to a channel in the join pattern.
    InEdge[] continuations;

 @nogc nothrow:
    /++
    Initializes an instantiation node.

    Params:
        self = Address of node being initialized.
        n = Number of continuations to instantiate (always statically known).

    Returns:
        Zero on success, non-zero on failure (null node, OOM or zero continuations).
    +/
    static err_t initialize(InstantiationNode* self, uint n = 1)
    in (self != null && n >= 1)
    {
        if (self == null) return EINVAL;
        if (n == 0) return EINVAL;
        *self = InstantiationNode.init;

        self.vptr = &InstantiationNode.vtbl;
        self.definition = OutEdge.data;
        self.continuations = allocate!InEdge(n);
        if (self.continuations == null) return ENOMEM;
        foreach (i, ref cont; self.continuations) {
            cont = InEdge.data(self.asNode, i);
        }

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(InstantiationNode* self) {
        self.continuations.deallocate();
        *self = InstantiationNode.init;
    }

    /++
    Semantic equality check.

    Every instantiation node has its own identity, so no two are equal.
    If this weren't the case, there would be no way to instantiate a join pattern twice and use the two instances independently.
    +/
    bool opEquals(ref const(InstantiationNode) rhs) const {
        return this.asNode == rhs.asNode; // self-ptr
    }

    hash_t toHash() const {
        return this.asNode.hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(InstantiationNode) old) pure {
        foreach (ref cont; this.continuations) cont.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    InstantiationNode tmp = void;
    InstantiationNode.initialize(&tmp);
    //
    InstantiationNode inst = void;
    moveEmplace(tmp, inst);
    //
    assert(inst == inst);
    assert(inst.continuations.length == 1);
    //
    InstantiationNode.dispose(&inst);
}

/++
Yields control flow to another part of the program through a "jump with arguments".

Jump nodes yield control to a target "place" in the program, while also carrying information.
They can be seen as a (a) `goto`, (b) function application, (c) return statement or (d) synchronous message being sent to another process.


Gyre jumps differ from classic function calls because there is no implicit expectation of a "return"; this is [CPS](https://en.wikipedia.org/wiki/Continuation-passing_style).
If a caller expects return values (or even to take control back at all), it needs to set up a "return continuation" and pass that in as an argument as well, hoping that the subprocedure it is calling will (1) eventually receive messages on all of its other channels, triggering the join pattern; (2) execute the join's body to completion; and (3) have that body jump into the provided continuation as a way to come back (perhaps with a return value) to the calling code.
This is not unlike what we (implicitly) assume of normal functions: their return depends on (1) whether it doesn't go into starvation while waiting for other threads; (2) whether it terminates; and (3) whether it actually has a `return` statement (it could call a C-like `exit` procedure instead, or use raw assembly to continue the program elsewhere, etc).

Jumps synchronize with each other when they cause a multiple-channel join pattern to trigger.
Imagine a set of concurrent processes, each carrying a continuation corresponding to a different channel of some join pattern; once they've all jumped into their respective continuations, the join triggers and its body executes.
Then, every event in those processes which happens before the jump, also happens before all events in the triggered join pattern's body.
Note that this does not apply to single-channel join patterns.

See_Also: [JoinNode]
+/
struct JumpNode {
    mixin NodeInheritance;

    /// Incoming control flow which is about to be yielded to the target continuation.
    InEdge control;

    /// A data dependency on some live continuation.
    OutEdge continuation;

    /// Arguments to be sent into the continuation and later used inside a join pattern's body.
    OutEdge[] arguments;

 @nogc nothrow:
    /++
    Initializes a jump node.

    Params:
        self = Address of node being initialized.
        args = Argument kinds.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid edge kinds).
    +/
    static err_t initialize(JumpNode* self, EdgeKind[] args ...)
    in (self != null)
    {
        if (self == null) return EINVAL;
        foreach (argKind; args) {
            with (EdgeKind) final switch (argKind) {
                case data, memory: break;
                case control, type: return EINVAL;
            }
        }
        *self = JumpNode.init;

        self.vptr = &JumpNode.vtbl;
        self.control = InEdge.control(self.asNode);
        self.continuation = OutEdge.data;
        self.arguments = allocate!OutEdge(args.length);
        if (args.length > 0 && self.arguments == null) return ENOMEM;
        foreach (i, argKind; args) {
            self.arguments[i] = OutEdge.data;
        }

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(JumpNode* self) {
        self.arguments.deallocate();
        *self = JumpNode.init;
    }

    /++
    Semantic equality check.

    Jump nodes are equal if and only if they jump into the same target continuation and they're sending the same arguments.
    Notice that, since procedure calls usually take return continuations as parameters, this does not eliminate subexpressions which are only equal in a syntactic sense.
    For instance, `printf("hi") + printf("hi")` cannot be transformed to `(t = printf("hi")), t + t`, since the continuation of each `printf` call is different.
    +/
    bool opEquals(ref const(JumpNode) rhs) const {
        if (this.continuation != rhs.continuation) return false;
        if (this.arguments != rhs.arguments) return false;
        return true;
    }

    hash_t toHash() const {
        hash_t hash = this.continuation.toHash();
        foreach (arg; this.arguments) hash ^= arg.toHash();
        return 0;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(JumpNode) old) pure {
        this.control.owner = this.asNode;
    }
}

nothrow unittest {
    JumpNode tmp = void;
    with (EdgeKind) JumpNode.initialize(&tmp, data, memory, data, data);
    //
    JumpNode jump = void;
    moveEmplace(tmp, jump);
    //
    assert(jump == jump);
    assert(jump.control.owner == jump.asNode);
    assert(jump.arguments.length == 4);
    //
    JumpNode.dispose(&jump);
}

/++
Forks a single control flow into multiple concurrent ones.

Data-only Gyre graphs are always implicitly concurrent: there is no ordering relation between data-only nodes other than the one implied by their def-use chains.
When a node also requires control flow, expressing the fact that it is concurrent with respect to another (i.e. one operation does not necessarily need to happen before the other) is impossible in a classic CFG.
Fork nodes are Gyre's way to work around this limitation by signaling explicit concurrency.


Fork nodes tell the compiler "the following subprograms have no ordering constraints between each other".
RULE: It is an error for any of the resulting control flows to make direct use of a value produced in another one of its sibling 'threads'.
Still, every event which happens before a fork also happens before the events of its resulting control flows.
Merging multiple concurrent flows back together can be done at a [JoinNode|join].

TODO: fork semantics are unclear w.r.t. progress. e.g.: when one thread blocks (and it could be waiting for a message from another sibling thread), do all other threads block as well? (in that case, we could have starvation; if other threads don't block, they need to be independently scheduled, which in turn requires help from the OS, etc)

See_Also: [JoinNode], [JumpNode]
+/
struct ForkNode {
    mixin NodeInheritance;

    /// Incoming single control flow.
    InEdge control;

    /// At least two concurrent control flows resulting from this fork.
    OutEdge[] threads;

 @nogc nothrow:
    /++
    Initializes a fork node.

    Params:
        self = Address of node being initialized.
        n = Number of forked threads.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of threads).
    +/
    static err_t initialize(ForkNode* self, uint n)
    in (self != null && n >= 2)
    {
        if (self == null) return EINVAL;
        if (n < 2) return EINVAL;
        *self = ForkNode.init;

        self.vptr = &ForkNode.vtbl;
        self.control = InEdge.control(self.asNode);
        self.threads = allocate!OutEdge(n);
        if (self.threads == null) return ENOMEM;
        foreach (ref thread; self.threads) {
            thread = OutEdge.control;
        }

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(ForkNode* self) {
        self.threads.deallocate();
        *self = ForkNode.init;
    }

    /++
    Semantic equality check.

    Fork nodes are the same if and only if all of their resulting flows behave exactly the same (in which case they are still separate logical threads, but with a shared structure in the IR).
    +/
    bool opEquals(ref const(ForkNode) rhs) const {
        if (this.threads != rhs.threads) return false;
        return true;
    }

    hash_t toHash() const {
        hash_t hash = 0;
        foreach (thread; this.threads) hash ^= thread.toHash();
        return hash;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(ForkNode) old) pure {
        this.control.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    ForkNode tmp = void;
    ForkNode.initialize(&tmp, 2);
    //
    ForkNode fork = void;
    moveEmplace(tmp, fork);
    //
    assert(fork == fork);
    assert(fork.control.owner == fork.asNode);
    //
    ForkNode.dispose(&fork);
}

/++
Directs control flow to exactly one of multiple possible edges.

The choice of which branch to take is controled by a data dependency interpreted as an unsigned integer indexing an array of options.
If the selector's value does not match the index of any option, program behavior is undefined.
A Gyre compiler may assume that this never happens and either issue warnings / errors or optimize accordingly (e.g. by assuming that the selector's value is one of the valid indexes, if control flow reaches this node).


Conditional nodes are technically redundant in the IR, since they could be emulated by a [JumpNode|jump] into the result of a [MultiplexerNode|mux node].
In the worst case, however, this would require one extra [InstantiationNode|instantiation node] for each branch, so we define this as a dedicated control branch operation.

See_Also: [MultiplexerNode]
+/
struct ConditionalNode {
    mixin NodeInheritance;

    /// Data selector used to choose the taken branch.
    OutEdge selector;

    /// Incoming control flow edge.
    InEdge control;

    /++
    At least two outgoing control flow edges, only one of which will be taken.

    Represented as a sparse mapping to avoid having an exponential number of unused options.
    +/
    UnsafeHashMap!(ulong, OutEdge) options;

 @nogc nothrow:
    /++
    Initializes a conditional node.

    Params:
        self = Address of node being initialized.
        options = Branches to pre-allocate.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of branches).
    +/
    static err_t initialize(ConditionalNode* self, ulong[] options = [0, 1] ...)
    in (self != null && options.length >= 2)
    {
        if (self == null) return EINVAL;
        if (options.length < 2) return EINVAL;
        *self = ConditionalNode.init;

        self.vptr = &ConditionalNode.vtbl;
        self.selector = OutEdge.data;
        self.control = InEdge.control(self.asNode);
        self.options = UnsafeHashMap!(ulong, OutEdge)();
        const error = self.options.rehash(options.length);
        if (error) return ENOMEM;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(ConditionalNode* self) {
        self.options.dispose();
        *self = ConditionalNode.init;
    }

    /++
    Semantic equality check.

    Conditional nodes are the same if and only if they use the same value to select the taken branch and every branch in one has a corresponding branch in the other.
    +/
    bool opEquals(ref const(ConditionalNode) rhs) const {
        if (this.selector != rhs.selector) return false;
        if (this.options != rhs.options) return false;
        return true;
    }

    hash_t toHash() const {
        return this.selector.toHash() ^ this.options.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(ConditionalNode) old) pure {
        this.control.owner = this.asNode;
    }
}

nothrow unittest {
    ConditionalNode tmp = void;
    ConditionalNode.initialize(&tmp);
    //
    ConditionalNode cond = void;
    moveEmplace(tmp, cond);
    //
    assert(cond == cond);
    assert(cond.control.owner == cond.asNode);
    //
    ConditionalNode.dispose(&cond);
}

/++
Gyre's mechanism for structural abstraction, the macro node.

One can imagine macro nodes as holes: parts of a Gyre program which will only be filled later, like `extern` definitions in a C-like language, which the linker is responsible for resolving.


Macro nodes represent Gyre subgraphs defined elsewhere (external to the graph where they're being used).
A Gyre (sub)program is said to be concrete if it contains no macro nodes, otherwise it is abstract.
This part of Gyre's design is influenced by [ANDF](https://en.wikipedia.org/wiki/Architecture_Neutral_Distribution_Format), which enabled IR "producers" (front ends) to pass along unexpanded macros to IR "installers" (back ends).

Abstract Gyre graphs can't be directly compiled to machine code, since backends wouldn't be able to lower macro nodes without their definition.
Still, having abstract Gyre graphs has its uses.
One example is when the compiler doesn't (yet) have the information it needs to concretize a graph: it may lack target-specific information which is required for code generation.
Another one is to enable more target-specific optimizations: if every "high-level" operation was lowered to a generic implementation using only primitive nodes, back ends with special support for that operation wouldn't (easily) be able to re-discover it in order to generate specialized code.
["Premature lowering is the root of all evil"](https://storage.googleapis.com/pub-tools-public-publication-data/pdf/85bf23fe88bd5c7ff60365bd0c6882928562cbeb.pdf), and macro nodes aim to avoid it.

Without any other rules, macro nodes would probably end up harming portability: abstract Gyre graphs could only be compiled by back ends providing all the right macro definitions.
RULE: Thus, a portable Gyre program must carry definitions for all of its macros (and macros cannot be recursive).
Such definitions must allow any compliant Gyre back end to correctly compile programs by concretizing them through a simple process of macro expansion (i.e. substituting macro nodes for their definition until there are no more macro nodes in the graph).
The intention is that macros must always have the same semantics, but a Gyre compiler with intimate knowledge of a specific macro can do a better job at optimizing programs using it.

Just like linker-resolved symbols, macro nodes need to be uniquely identified.
It is this identification which allows the compiler to, later in the compilation pipeline, substitute the macro node with (i.e. "link in") its definition.
+/
struct MacroNode {
    mixin NodeInheritance;

    /// Links this macro node to its external definition.
    ID id;
    alias ID = uint; /// ditto

    /// Edges (any kind) which point out from this node.
    OutEdge[] outEdges;

    /// Edges (of any kind) which point into this node.
    InEdge[] inEdges;

 @nogc nothrow:
    /++
    Initializes a macro node, must be later [dispose]d.

    Params:
        self = Address of node being initialized.
        id = Macro node identification number.
        inEdges = Defines this node's interface (in edges only).
        outEdges = Defines this node's interface (out edges only).

    Returns:
        Zero on success, non-zero on failure (null node or OOM).
    +/
    static err_t initialize(
        MacroNode* self,
        MacroNode.ID id,
        EdgeKind[] inEdges,
        EdgeKind[] outEdges
    )
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = MacroNode.init;

        self.vptr = &MacroNode.vtbl;
        self.id = id;

        self.inEdges = allocate!InEdge(inEdges.length);
        if (inEdges.length > 0 && self.inEdges == null) {
            self.outEdges.deallocate();
            return ENOMEM;
        }
        foreach (i, kind; inEdges)
            self.inEdges[i] = InEdge(kind, self.asNode, i);

        self.outEdges = allocate!OutEdge(outEdges.length);
        if (outEdges.length > 0 && self.outEdges == null) return ENOMEM;
        foreach (i, kind; outEdges)
            self.outEdges[i] = OutEdge(kind);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(MacroNode* self) {
        self.inEdges.deallocate();
        self.outEdges.deallocate();
        *self = MacroNode.init;
    }

    /++
    Semantic equality check.

    Since macro nodes can expand into arbitrary subgraphs, we treat each one individually.
    +/
    bool opEquals(ref const(MacroNode) rhs) const {
        return this.id == rhs.id && this.asNode == rhs.asNode; // self-ptr
    }

    hash_t toHash() const {
        return this.id.hashOf ^ this.asNode.hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(MacroNode) old) pure {
        foreach (ref slot; this.inEdges)
            slot.owner = this.asNode;
    }
}

nothrow unittest {
    MacroNode tmp = void;
    with (EdgeKind) MacroNode.initialize(&tmp, 42, [control, type, data], [control, control]);
    //
    MacroNode node = void;
    moveEmplace(tmp, node);
    //
    assert(node == node);
    assert(node.id == 42);
    assert(node.inEdges.length == 3);
    assert(node.outEdges.length == 2);
    //
    MacroNode.dispose(&node);
}


/++
Constructs a constant value of a certain type.

See_Also: [UndefinedNode]
+/
struct ConstantNode {
    mixin NodeInheritance;

    // FIXME: temporary assumption that all types are i64
    ulong literal;

    /// The constant's (run-time) value.
    InEdge value;

 @nogc nothrow:
    /++
    Initializes a constant node.

    Params:
        self = Address of node being initialized.
        literal = This constant's value.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(ConstantNode* self, ulong literal)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = ConstantNode.init;

        self.vptr = &ConstantNode.vtbl;
        self.literal = literal;
        self.value = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(ConstantNode* self) {
        *self = ConstantNode.init;
    }

    /++
    Semantic equality check.

    The easy case: constants are equal if and only if their values are equal.
    +/
    bool opEquals(ref const(ConstantNode) rhs) const {
        return this.literal == rhs.literal;
    }

    hash_t toHash() const {
        return this.literal.hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(ConstantNode) old) pure {
        this.value.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    ConstantNode tmp = void;
    ConstantNode.initialize(&tmp, 2);
    //
    ConstantNode lit = void;
    moveEmplace(tmp, lit);
    //
    assert(lit == lit);
    assert(lit.value.owner == lit.asNode);
    //
    ConstantNode.dispose(&lit);
}

/++
Constructs a ["don't care"](https://en.wikipedia.org/wiki/Don%27t-care_term) value of a certain type.

The compiler is free to change this node into any constant (i.e. define it), as long as it's value is consistently seen by all of its uses.
This notion of 'undefined' comes from [Click's thesis](https://scholarship.rice.edu/bitstream/handle/1911/96451/TR95-252.pdf).


Rationale: Undefined values cannot be produced by [ConstantNode]s, because the latter are always subject to structural sharing (e.g. every `1` is the same), whereas different undefined nodes can resolve to different values and therefore each needs its own identity.

See_Also: [ConstantNode]
+/
struct UndefinedNode {
    mixin NodeInheritance;

    /// The resulting value.
    InEdge value;

 @nogc nothrow:
    /++
    Initializes an undefined node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(UndefinedNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = UndefinedNode.init;

        self.vptr = &UndefinedNode.vtbl;
        self.value = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(UndefinedNode* self) {
        *self = UndefinedNode.init;
    }

    /++
    Semantic equality check.

    Since different undefined nodes can resolve to different values, each has its own identity.
    +/
    bool opEquals(ref const(UndefinedNode) rhs) const {
        return this.asNode == rhs.asNode; // self-ptr
    }

    hash_t toHash() const {
        return this.asNode.hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(UndefinedNode) old) pure {
        this.value.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    UndefinedNode tmp = void;
    UndefinedNode.initialize(&tmp);
    //
    UndefinedNode undef = void;
    moveEmplace(tmp, undef);
    //
    assert(undef == undef);
    assert(undef.value.owner == undef.asNode);
    //
    UndefinedNode.dispose(&undef);
}

/// Yields the lowermost bits of its input.
struct TruncationNode { // FIXME: doesn't make sense without type info
    mixin NodeInheritance;

    /// Bit pattern being truncated.
    OutEdge input;

    /// Lowermost input bits.
    InEdge output;

 @nogc nothrow:
    /++
    Initializes a truncation node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(TruncationNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = TruncationNode.init;

        self.vptr = &TruncationNode.vtbl;
        self.input = OutEdge.data;
        self.output = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(TruncationNode* self) {
        *self = TruncationNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(TruncationNode) rhs) const {
        return this.input == rhs.input;
    }

    hash_t toHash() const {
        return this.input.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(TruncationNode) old) pure {
        this.output.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    TruncationNode tmp = void;
    TruncationNode.initialize(&tmp);
    //
    TruncationNode trunc = void;
    moveEmplace(tmp, trunc);
    //
    assert(trunc == trunc);
    assert(trunc.output.owner == trunc.asNode);
    //
    TruncationNode.dispose(&trunc);
}

/++
Yields a wider version of its input, with added bits set to zero.

See_Also: [SignedExtensionNode]
+/
struct UnsignedExtensionNode { // FIXME: doesn't make sense without type info
    mixin NodeInheritance;

    /// Bit pattern being extended.
    OutEdge input;

    /// Resulting bit pattern.
    InEdge output;

 @nogc nothrow:
    /++
    Initializes an extension node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(UnsignedExtensionNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = UnsignedExtensionNode.init;

        self.vptr = &UnsignedExtensionNode.vtbl;
        self.input = OutEdge.data;
        self.output = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(UnsignedExtensionNode* self) {
        *self = UnsignedExtensionNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(UnsignedExtensionNode) rhs) const {
        return this.input == rhs.input;
    }

    hash_t toHash() const {
        return this.input.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(UnsignedExtensionNode) old) pure {
        this.output.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    UnsignedExtensionNode tmp = void;
    UnsignedExtensionNode.initialize(&tmp);
    //
    UnsignedExtensionNode extu = void;
    moveEmplace(tmp, extu);
    //
    assert(extu == extu);
    assert(extu.output.owner == extu.asNode);
    //
    UnsignedExtensionNode.dispose(&extu);
}

/++
Yields a wider version of its input, with added bits equal to the input's sign bit.

See_Also: [UnsignedExtensionNode]
+/
struct SignedExtensionNode { // FIXME: doesn't make sense without type info
    mixin NodeInheritance;

    /// Bit pattern being extended.
    OutEdge input;

    /// Resulting bit pattern.
    InEdge output;

 @nogc nothrow:
    /++
    Initializes a extension node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(SignedExtensionNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = SignedExtensionNode.init;

        self.vptr = &SignedExtensionNode.vtbl;
        self.input = OutEdge.data;
        self.output = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(SignedExtensionNode* self) {
        *self = SignedExtensionNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(SignedExtensionNode) rhs) const {
        return this.input == rhs.input;
    }

    hash_t toHash() const {
        return this.input.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(SignedExtensionNode) old) pure {
        this.output.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    SignedExtensionNode tmp = void;
    SignedExtensionNode.initialize(&tmp);
    //
    SignedExtensionNode exts = void;
    moveEmplace(tmp, exts);
    //
    assert(exts == exts);
    assert(exts.output.owner == exts.asNode);
    //
    SignedExtensionNode.dispose(&exts);
}

/++
An operation which chooses one of its inputs to forward as a result.

In a multiplexer node, the choice of which input to forward is controled by an unsigned integer, as if it was indexing an array of inputs.
If the selector's value does not match the index of any input, the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.


The behavior of this node could be emulated by a value-carrying [ConditionalNode|branch] into an [JoinNode|extended basic block].
However, this node does not need control flow edges at all.
Thus, its semantics are slightly different: whereas a control flow branch disallows the execution of operations in its unchosen branches (but the compiler can still move them out of the branch if that preserves program semantics), a mux node is allowed to compute all of its options before choosing which one to forward (but doesn't need to, e.g. if the selector is a constant).

See_Also: [ConditionalNode]
+/
struct MultiplexerNode {
    mixin NodeInheritance;

    /// Data dependency used to choose which of the given inputs will be returned.
    OutEdge selector;

    /// Resulting value.
    InEdge output;

    /++
    At least two inputs, one of which will be forwarded as output.

    Represented as a sparse mapping to avoid having an exponential number of unused input edges.
    +/
    UnsafeHashMap!(ulong, OutEdge) inputs;

 @nogc nothrow:
    /++
    Initializes a multiplexer node.

    Params:
        self = Address of node being initialized.
        inputs = Input slots to pre-allocate.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of inputs).
    +/
    static err_t initialize(MultiplexerNode* self, ulong[] inputs = [0, 1] ...)
    in (self != null && inputs.length >= 2)
    {
        if (self == null) return EINVAL;
        if (inputs.length < 2) return EINVAL;
        *self = MultiplexerNode.init;

        self.vptr = &MultiplexerNode.vtbl;
        self.selector = OutEdge.data;
        self.output = InEdge.data(self.asNode);
        self.inputs = UnsafeHashMap!(ulong, OutEdge)();
        const error = self.inputs.rehash(inputs.length);
        if (error) return ENOMEM;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(MultiplexerNode* self) {
        self.inputs.dispose();
        *self = MultiplexerNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(MultiplexerNode) rhs) const {
        if (this.selector != rhs.selector) return false;
        if (this.inputs != rhs.inputs) return false;
        return true;
    }

    hash_t toHash() const {
        return this.selector.toHash() ^ this.inputs.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(MultiplexerNode) old) pure {
        this.output.owner = this.asNode;
    }
}

nothrow unittest {
    MultiplexerNode tmp = void;
    MultiplexerNode.initialize(&tmp, 0, 1, 2, 3);
    //
    MultiplexerNode mux = void;
    moveEmplace(tmp, mux);
    //
    assert(mux == mux);
    assert(mux.output.owner == mux.asNode);
    //
    MultiplexerNode.dispose(&mux);
}

/// Bitwise `AND` operation.
struct AndNode {
    mixin NodeInheritance;

    /// Resulting bit pattern.
    InEdge result;

    /// Set of operands (order does not matter).
    UnsafeHashSet!OutEdge operands;

 @nogc nothrow:
    /++
    Initializes an AND node.

    Params:
        self = Address of node being initialized.
        n = Number of operands to pre-allocate.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of operands).
    +/
    static err_t initialize(AndNode* self, uint n = 2)
    in (self != null && n >= 2)
    {
        if (self == null) return EINVAL;
        if (n < 2) return EINVAL;
        *self = AndNode.init;

        self.vptr = &AndNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.operands = UnsafeHashSet!(OutEdge)();
        const error = self.operands.rehash(n);
        if (error) return ENOMEM;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(AndNode* self) {
        self.operands.dispose();
        *self = AndNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(AndNode) rhs) const {
        return this.operands == rhs.operands;
    }

    hash_t toHash() const {
        return this.operands.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(AndNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    AndNode tmp = void;
    AndNode.initialize(&tmp);
    //
    AndNode and = void;
    moveEmplace(tmp, and);
    //
    assert(and == and);
    assert(and.result.owner == and.asNode);
    //
    AndNode.dispose(&and);
}

/// Bitwise `OR` operation.
struct OrNode {
    mixin NodeInheritance;

    /// Resulting bit pattern.
    InEdge result;

    /// Set of operands (order does not matter).
    UnsafeHashSet!OutEdge operands;

 @nogc nothrow:
    /++
    Initializes an OR node.

    Params:
        self = Address of node being initialized.
        n = Number of operands to pre-allocate.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of operands).
    +/
    static err_t initialize(OrNode* self, uint n = 2)
    in (self != null && n >= 2)
    {
        if (self == null) return EINVAL;
        if (n < 2) return EINVAL;
        *self = OrNode.init;

        self.vptr = &OrNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.operands = UnsafeHashSet!(OutEdge)();
        const error = self.operands.rehash(n);
        if (error) return ENOMEM;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(OrNode* self) {
        self.operands.dispose();
        *self = OrNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(OrNode) rhs) const {
        return this.operands == rhs.operands;
    }

    hash_t toHash() const {
        return this.operands.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(OrNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    OrNode tmp = void;
    OrNode.initialize(&tmp);
    //
    OrNode or = void;
    moveEmplace(tmp, or);
    //
    assert(or == or);
    assert(or.result.owner == or.asNode);
    //
    OrNode.dispose(&or);
}

/++
Bitwise `XOR` operation.

Doubles as an unary `NOT` operation when given two operands and one is an all-ones constant.
+/
struct XorNode {
    mixin NodeInheritance;

    /// Resulting bit pattern.
    InEdge result;

    /// Set of operands (order does not matter).
    UnsafeHashSet!OutEdge operands;

 @nogc nothrow:
    /++
    Initializes a XOR node.

    Params:
        self = Address of node being initialized.
        n = Number of operands to pre-allocate.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of operands).
    +/
    static err_t initialize(XorNode* self, uint n = 2)
    in (self != null && n >= 2)
    {
        if (self == null) return EINVAL;
        if (n < 2) return EINVAL;
        *self = XorNode.init;

        self.vptr = &XorNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.operands = UnsafeHashSet!(OutEdge)();
        const error = self.operands.rehash(n);
        if (error) return ENOMEM;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(XorNode* self) {
        self.operands.dispose();
        *self = XorNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(XorNode) rhs) const {
        return this.operands == rhs.operands;
    }

    hash_t toHash() const {
        return this.operands.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(XorNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    XorNode tmp = void;
    XorNode.initialize(&tmp);
    //
    XorNode xor = void;
    moveEmplace(tmp, xor);
    //
    assert(xor == xor);
    assert(xor.result.owner == xor.asNode);
    //
    XorNode.dispose(&xor);
}

/++
Bitwise left-shift operation; shifts in zeros.

Shift amount must be no greater than the number of input bits, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).

See_Also: [LeftShiftNoOverflowNode]
+/
struct LeftShiftNode {
    mixin NodeInheritance;

    /// Initial bit pattern being shifted.
    OutEdge input;

    /// Number of times the shift is performed.
    OutEdge shift;

    /// Resulting bit pattern.
    InEdge output;

 @nogc nothrow:
    /++
    Initializes a shift node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(LeftShiftNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = LeftShiftNode.init;

        self.vptr = &LeftShiftNode.vtbl;
        self.input = OutEdge.data;
        self.shift = OutEdge.data;
        self.output = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(LeftShiftNode* self) {
        *self = LeftShiftNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(LeftShiftNode) rhs) const {
        if (this.input != rhs.input) return false;
        if (this.shift != rhs.shift) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.input.toHash() - this.shift.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(LeftShiftNode) old) pure {
        this.output.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    LeftShiftNode tmp = void;
    LeftShiftNode.initialize(&tmp);
    //
    LeftShiftNode shl = void;
    moveEmplace(tmp, shl);
    //
    assert(shl == shl);
    assert(shl.output.owner == shl.asNode);
    //
    LeftShiftNode.dispose(&shl);
}

/++
Bitwise left-shift with [no-overflow](gyre.nodes.html#no-overflow-operations) semantics; shifts in zeros.

Shift amount must be no greater than the number of input bits, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).
Furthermore, this operation guarantees that no `1` bits will be shifted off the initial word size (so the operand can never be negative).
In other words, the result is treated as multiplication by a power of two and it must fit within the given bit length, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).

See_Also: [LeftShiftNode]
+/
struct LeftShiftNoOverflowNode {
    mixin NodeInheritance;

    /// Initial bit pattern being shifted.
    OutEdge input;

    /// Number of times the shift is performed.
    OutEdge shift;

    /// Resulting bit pattern.
    InEdge output;

 @nogc nothrow:
    /++
    Initializes a shift node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(LeftShiftNoOverflowNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = LeftShiftNoOverflowNode.init;

        self.vptr = &LeftShiftNoOverflowNode.vtbl;
        self.input = OutEdge.data;
        self.shift = OutEdge.data;
        self.output = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(LeftShiftNoOverflowNode* self) {
        *self = LeftShiftNoOverflowNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(LeftShiftNoOverflowNode) rhs) const {
        if (this.input != rhs.input) return false;
        if (this.shift != rhs.shift) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.input.toHash() - this.shift.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(LeftShiftNoOverflowNode) old) pure {
        this.output.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    LeftShiftNoOverflowNode tmp = void;
    LeftShiftNoOverflowNode.initialize(&tmp);
    //
    LeftShiftNoOverflowNode shlno = void;
    moveEmplace(tmp, shlno);
    //
    assert(shlno == shlno);
    assert(shlno.output.owner == shlno.asNode);
    //
    LeftShiftNoOverflowNode.dispose(&shlno);
}

/++
Logical right-shift operation; shifts in zeros.

Shift amount must be no greater than the number of input bits, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).

See_Also: [SignedRightShiftNode]
+/
struct UnsignedRightShiftNode {
    mixin NodeInheritance;

    /// Initial bit pattern being shifted.
    OutEdge input;

    /// Number of times the shift is performed.
    OutEdge shift;

    /// Resulting bit pattern.
    InEdge output;

 @nogc nothrow:
    /++
    Initializes a shift node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(UnsignedRightShiftNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = UnsignedRightShiftNode.init;

        self.vptr = &UnsignedRightShiftNode.vtbl;
        self.input = OutEdge.data;
        self.shift = OutEdge.data;
        self.output = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(UnsignedRightShiftNode* self) {
        *self = UnsignedRightShiftNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(UnsignedRightShiftNode) rhs) const {
        if (this.input != rhs.input) return false;
        if (this.shift != rhs.shift) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.input.toHash() - this.shift.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(UnsignedRightShiftNode) old) pure {
        this.output.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    UnsignedRightShiftNode tmp = void;
    UnsignedRightShiftNode.initialize(&tmp);
    //
    UnsignedRightShiftNode shru = void;
    moveEmplace(tmp, shru);
    //
    assert(shru == shru);
    assert(shru.output.owner == shru.asNode);
    //
    UnsignedRightShiftNode.dispose(&shru);
}

/++
Arithmetic right-shift operation; bits shifted in are equal to the input's most significant bit.

Shift amount must be no greater than the number of input bits, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).

See_Also: [UnsignedRightShiftNode]
+/
struct SignedRightShiftNode {
    mixin NodeInheritance;

    /// Initial bit pattern being shifted.
    OutEdge input;

    /// Number of times the shift is performed.
    OutEdge shift;

    /// Resulting bit pattern.
    InEdge output;

 @nogc nothrow:
    /++
    Initializes a shift node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(SignedRightShiftNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = SignedRightShiftNode.init;

        self.vptr = &SignedRightShiftNode.vtbl;
        self.input = OutEdge.data;
        self.shift = OutEdge.data;
        self.output = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(SignedRightShiftNode* self) {
        *self = SignedRightShiftNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(SignedRightShiftNode) rhs) const {
        if (this.input != rhs.input) return false;
        if (this.shift != rhs.shift) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.input.toHash() - this.shift.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(SignedRightShiftNode) old) pure {
        this.output.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    SignedRightShiftNode tmp = void;
    SignedRightShiftNode.initialize(&tmp);
    //
    SignedRightShiftNode shrs = void;
    moveEmplace(tmp, shrs);
    //
    assert(shrs == shrs);
    assert(shrs.output.owner == shrs.asNode);
    //
    SignedRightShiftNode.dispose(&shrs);
}

/++
Two's complement addition operation (works for both signed and unsigned integers).

Wraps around on overflow.

See_Also: [AdditionNoOverflowSignedNode]
+/
struct AdditionNode {
    mixin NodeInheritance;

    /// Resulting sum.
    InEdge result;

    /// Set of operands (order does not matter).
    UnsafeHashSet!OutEdge operands;

 @nogc nothrow:
    /++
    Initializes an addition node.

    Params:
        self = Address of node being initialized.
        n = Number of operands to pre-allocate.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of operands).
    +/
    static err_t initialize(AdditionNode* self, uint n = 2)
    in (self != null && n >= 2)
    {
        if (self == null) return EINVAL;
        if (n < 2) return EINVAL;
        *self = AdditionNode.init;

        self.vptr = &AdditionNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.operands = UnsafeHashSet!(OutEdge)();
        const error = self.operands.rehash(n);
        if (error) return ENOMEM;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(AdditionNode* self) {
        self.operands.dispose();
        *self = AdditionNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(AdditionNode) rhs) const {
        return this.operands == rhs.operands;
    }

    hash_t toHash() const {
        return this.operands.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(AdditionNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    AdditionNode tmp = void;
    AdditionNode.initialize(&tmp);
    //
    AdditionNode add = void;
    moveEmplace(tmp, add);
    //
    assert(add == add);
    assert(add.result.owner == add.asNode);
    //
    AdditionNode.dispose(&add);
}

/++
Two's complement [no-overflow](gyre.nodes.html#no-overflow-operations) signed addition.

Produces [poison](gyre.nodes.html#poison-values-and-ub) on signed overflow.

See_Also: [AdditionNode]
+/
struct AdditionNoOverflowSignedNode {
    mixin NodeInheritance;

    /// Resulting sum.
    InEdge result;

    /// Set of operands (order does not matter).
    UnsafeHashSet!OutEdge operands;

 @nogc nothrow:
    /++
    Initializes an addition node.

    Params:
        self = Address of node being initialized.
        n = Number of operands to pre-allocate.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of operands).
    +/
    static err_t initialize(AdditionNoOverflowSignedNode* self, uint n = 2)
    in (self != null && n >= 2)
    {
        if (self == null) return EINVAL;
        if (n < 2) return EINVAL;
        *self = AdditionNoOverflowSignedNode.init;

        self.vptr = &AdditionNoOverflowSignedNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.operands = UnsafeHashSet!(OutEdge)();
        const error = self.operands.rehash(n);
        if (error) return ENOMEM;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(AdditionNoOverflowSignedNode* self) {
        self.operands.dispose();
        *self = AdditionNoOverflowSignedNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(AdditionNoOverflowSignedNode) rhs) const {
        return this.operands == rhs.operands;
    }

    hash_t toHash() const {
        return this.operands.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(AdditionNoOverflowSignedNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    AdditionNoOverflowSignedNode tmp = void;
    AdditionNoOverflowSignedNode.initialize(&tmp);
    //
    AdditionNoOverflowSignedNode addnos = void;
    moveEmplace(tmp, addnos);
    //
    assert(addnos == addnos);
    assert(addnos.result.owner == addnos.asNode);
    //
    AdditionNoOverflowSignedNode.dispose(&addnos);
}

/++
Two's complement subtraction operation (works for both signed and unsigned integers).

Wraps around on overflow.

See_Also: [SubtractionNoOverflowSignedNode]
+/
struct SubtractionNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;

    /// Right-hand-side operand.
    OutEdge rhs;

    /// Result of the subtraction.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes a subtraction node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(SubtractionNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = SubtractionNode.init;

        self.vptr = &SubtractionNode.vtbl;
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;
        self.result = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(SubtractionNode* self) {
        *self = SubtractionNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(SubtractionNode) other) const {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.lhs.toHash() - this.rhs.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(SubtractionNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    SubtractionNode tmp = void;
    SubtractionNode.initialize(&tmp);
    //
    SubtractionNode sub = void;
    moveEmplace(tmp, sub);
    //
    assert(sub == sub);
    assert(sub.result.owner == sub.asNode);
    //
    SubtractionNode.dispose(&sub);
}

/++
Two's complement [no-overflow](gyre.nodes.html#no-overflow-operations) signed subtraction.

Produces [poison](gyre.nodes.html#poison-values-and-ub) on signed overflow.

See_Also: [SubtractionNode]
+/
struct SubtractionNoOverflowSignedNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;

    /// Right-hand-side operand.
    OutEdge rhs;

    /// Result of the subtraction.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes a subtraction node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(SubtractionNoOverflowSignedNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = SubtractionNoOverflowSignedNode.init;

        self.vptr = &SubtractionNoOverflowSignedNode.vtbl;
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;
        self.result = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(SubtractionNoOverflowSignedNode* self) {
        *self = SubtractionNoOverflowSignedNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(SubtractionNoOverflowSignedNode) other) const {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.lhs.toHash() - this.rhs.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(SubtractionNoOverflowSignedNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    SubtractionNoOverflowSignedNode tmp = void;
    SubtractionNoOverflowSignedNode.initialize(&tmp);
    //
    SubtractionNoOverflowSignedNode subnos = void;
    moveEmplace(tmp, subnos);
    //
    assert(subnos == subnos);
    assert(subnos.result.owner == subnos.asNode);
    //
    SubtractionNoOverflowSignedNode.dispose(&subnos);
}

/++
Two's complement multiplication operation.

Since this only produces the lower half of a full multiplication, it is the same for both signed and unsigned integers.
Wraps around on overflow.

See_Also: [MultiplicationNoOverflowSignedNode]
+/
struct MultiplicationNode {
    mixin NodeInheritance;

    /// Resulting product.
    InEdge result;

    /// Set of operands (order does not matter).
    UnsafeHashSet!OutEdge operands;

 @nogc nothrow:
    /++
    Initializes an addition node.

    Params:
        self = Address of node being initialized.
        n = Number of operands to pre-allocate.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of operands).
    +/
    static err_t initialize(MultiplicationNode* self, uint n = 2)
    in (self != null && n >= 2)
    {
        if (self == null) return EINVAL;
        if (n < 2) return EINVAL;
        *self = MultiplicationNode.init;

        self.vptr = &MultiplicationNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.operands = UnsafeHashSet!(OutEdge)();
        const error = self.operands.rehash(n);
        if (error) return ENOMEM;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(MultiplicationNode* self) {
        self.operands.dispose();
        *self = MultiplicationNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(MultiplicationNode) rhs) const {
        return this.operands == rhs.operands;
    }

    hash_t toHash() const {
        return this.operands.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(MultiplicationNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    MultiplicationNode tmp = void;
    MultiplicationNode.initialize(&tmp);
    //
    MultiplicationNode mul = void;
    moveEmplace(tmp, mul);
    //
    assert(mul == mul);
    assert(mul.result.owner == mul.asNode);
    //
    MultiplicationNode.dispose(&mul);
}

/++
Two's complement [no-overflow](gyre.nodes.html#no-overflow-operations) signed multiplication.

Produces [poison](gyre.nodes.html#poison-values-and-ub) when the lower half of the full multiplication has signed overflow.

See_Also: [MultiplicationNode]
+/
struct MultiplicationNoOverflowSignedNode {
    mixin NodeInheritance;

    /// Resulting product.
    InEdge result;

    /// Set of operands (order does not matter).
    UnsafeHashSet!OutEdge operands;

 @nogc nothrow:
    /++
    Initializes an addition node.

    Params:
        self = Address of node being initialized.
        n = Number of operands to pre-allocate.

    Returns:
        Zero on success, non-zero on failure (null node, OOM or invalid number of operands).
    +/
    static err_t initialize(MultiplicationNoOverflowSignedNode* self, uint n = 2)
    in (self != null && n >= 2)
    {
        if (self == null) return EINVAL;
        if (n < 2) return EINVAL;
        *self = MultiplicationNoOverflowSignedNode.init;

        self.vptr = &MultiplicationNoOverflowSignedNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.operands = UnsafeHashSet!(OutEdge)();
        const error = self.operands.rehash(n);
        if (error) return ENOMEM;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(MultiplicationNoOverflowSignedNode* self) {
        self.operands.dispose();
        *self = MultiplicationNoOverflowSignedNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(MultiplicationNoOverflowSignedNode) rhs) const {
        return this.operands == rhs.operands;
    }

    hash_t toHash() const {
        return this.operands.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(MultiplicationNoOverflowSignedNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    MultiplicationNoOverflowSignedNode tmp = void;
    MultiplicationNoOverflowSignedNode.initialize(&tmp);
    //
    MultiplicationNoOverflowSignedNode mulnos = void;
    moveEmplace(tmp, mulnos);
    //
    assert(mulnos == mulnos);
    assert(mulnos.result.owner == mulnos.asNode);
    //
    MultiplicationNoOverflowSignedNode.dispose(&mulnos);
}

/++
Two's complement division operation for unsigned operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.

See_Also: [SignedDivisionNode]
+/
struct UnsignedDivisionNode {
    mixin NodeInheritance;

    /// Dividend operand.
    OutEdge dividend;

    /// Divisor operand.
    OutEdge divisor;

    /// Resulting quotient.
    InEdge quotient;

 @nogc nothrow:
    /++
    Initializes a division node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(UnsignedDivisionNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = UnsignedDivisionNode.init;

        self.vptr = &UnsignedDivisionNode.vtbl;
        self.dividend = OutEdge.data;
        self.divisor = OutEdge.data;
        self.quotient = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(UnsignedDivisionNode* self) {
        *self = UnsignedDivisionNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(UnsignedDivisionNode) other) const {
        if (this.dividend != other.dividend) return false;
        if (this.divisor != other.divisor) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.dividend.toHash() - this.divisor.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(UnsignedDivisionNode) old) pure {
        this.quotient.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    UnsignedDivisionNode tmp = void;
    UnsignedDivisionNode.initialize(&tmp);
    //
    UnsignedDivisionNode divu = void;
    moveEmplace(tmp, divu);
    //
    assert(divu == divu);
    assert(divu.quotient.owner == divu.asNode);
    //
    UnsignedDivisionNode.dispose(&divu);
}

/++
Two's complement division operation for signed operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.
Furthermore, dividing the "most negative" value representable (`-1 * 2^(N-1)` for N bits) by `-1` also results in poison.

See_Also: [UnsignedDivisionNode]
+/
struct SignedDivisionNode {
    mixin NodeInheritance;

    /// Dividend operand.
    OutEdge dividend;

    /// Divisor operand.
    OutEdge divisor;

    /// Resulting quotient.
    InEdge quotient;

 @nogc nothrow:
    /++
    Initializes a division node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(SignedDivisionNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = SignedDivisionNode.init;

        self.vptr = &SignedDivisionNode.vtbl;
        self.dividend = OutEdge.data;
        self.divisor = OutEdge.data;
        self.quotient = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(SignedDivisionNode* self) {
        *self = SignedDivisionNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(SignedDivisionNode) other) const {
        if (this.dividend != other.dividend) return false;
        if (this.divisor != other.divisor) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.dividend.toHash() - this.divisor.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(SignedDivisionNode) old) pure {
        this.quotient.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    SignedDivisionNode tmp = void;
    SignedDivisionNode.initialize(&tmp);
    //
    SignedDivisionNode divs = void;
    moveEmplace(tmp, divs);
    //
    assert(divs == divs);
    assert(divs.quotient.owner == divs.asNode);
    //
    SignedDivisionNode.dispose(&divs);
}

/++
Two's complement remainder operation for unsigned operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.

See_Also: [SignedRemainderNode]
+/
struct UnsignedRemainderNode {
    mixin NodeInheritance;

    /// Dividend operand.
    OutEdge dividend;

    /// Divisor operand.
    OutEdge divisor;

    /// Resulting remainder.
    InEdge remainder;

 @nogc nothrow:
    /++
    Initializes a remainder node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(UnsignedRemainderNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = UnsignedRemainderNode.init;

        self.vptr = &UnsignedRemainderNode.vtbl;
        self.dividend = OutEdge.data;
        self.divisor = OutEdge.data;
        self.remainder = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(UnsignedRemainderNode* self) {
        *self = UnsignedRemainderNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(UnsignedRemainderNode) other) const {
        if (this.dividend != other.dividend) return false;
        if (this.divisor != other.divisor) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.dividend.toHash() - this.divisor.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(UnsignedRemainderNode) old) pure {
        this.remainder.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    UnsignedRemainderNode tmp = void;
    UnsignedRemainderNode.initialize(&tmp);
    //
    UnsignedRemainderNode remu = void;
    moveEmplace(tmp, remu);
    //
    assert(remu == remu);
    assert(remu.remainder.owner == remu.asNode);
    //
    UnsignedRemainderNode.dispose(&remu);
}

/++
Two's complement remainder operation for signed operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.
Furthermore, dividing the "most negative" value representable (`-1 * 2^(N-1)` for N bits) by `-1` also results in poison.

See_Also: [UnsignedRemainderNode]
+/
struct SignedRemainderNode {
    mixin NodeInheritance;

    /// Dividend operand.
    OutEdge dividend;

    /// Divisor operand.
    OutEdge divisor;

    /// Resulting remainder.
    InEdge remainder;

 @nogc nothrow:
    /++
    Initializes a remainder node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(SignedRemainderNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = SignedRemainderNode.init;

        self.vptr = &SignedRemainderNode.vtbl;
        self.dividend = OutEdge.data;
        self.divisor = OutEdge.data;
        self.remainder = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(SignedRemainderNode* self) {
        *self = SignedRemainderNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(SignedRemainderNode) other) const {
        if (this.dividend != other.dividend) return false;
        if (this.divisor != other.divisor) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.dividend.toHash() - this.divisor.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(SignedRemainderNode) old) pure {
        this.remainder.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    SignedRemainderNode tmp = void;
    SignedRemainderNode.initialize(&tmp);
    //
    SignedRemainderNode rems = void;
    moveEmplace(tmp, rems);
    //
    assert(rems == rems);
    assert(rems.remainder.owner == rems.asNode);
    //
    SignedRemainderNode.dispose(&rems);
}

/// Compares two bit patterns for equality.
struct EqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;

    /// Right-hand-side operand.
    OutEdge rhs;

    /// A single resulting bit indicating whether operands are equal.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes an equal node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(EqualNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = EqualNode.init;

        self.vptr = &EqualNode.vtbl;
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;
        self.result = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(EqualNode* self) {
        *self = EqualNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(EqualNode) other) const {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    hash_t toHash() const {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(EqualNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    EqualNode tmp = void;
    EqualNode.initialize(&tmp);
    //
    EqualNode eq = void;
    moveEmplace(tmp, eq);
    //
    assert(eq == eq);
    assert(eq.result.owner == eq.asNode);
    //
    EqualNode.dispose(&eq);
}

/// Compares two bit patterns for inequality.
struct NotEqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;

    /// Right-hand-side operand.
    OutEdge rhs;

    /// A single resulting bit indicating whether operands are different.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes a not-equal node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(NotEqualNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = NotEqualNode.init;

        self.vptr = &NotEqualNode.vtbl;
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;
        self.result = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(NotEqualNode* self) {
        *self = NotEqualNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(NotEqualNode) other) const {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    hash_t toHash() const {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(NotEqualNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    NotEqualNode tmp = void;
    NotEqualNode.initialize(&tmp);
    //
    NotEqualNode ne = void;
    moveEmplace(tmp, ne);
    //
    assert(ne == ne);
    assert(ne.result.owner == ne.asNode);
    //
    NotEqualNode.dispose(&ne);
}

/++
Computes whether a (unsigned) two's complement integer is strictly less than another.

There is no equivalent for `>` because it suffices to swap this node's operands.
+/
struct UnsignedLessThanNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;

    /// Right-hand-side operand.
    OutEdge rhs;

    /// A single resulting bit indicating `lhs < rhs`.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes a unsigned-less-than node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(UnsignedLessThanNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = UnsignedLessThanNode.init;

        self.vptr = &UnsignedLessThanNode.vtbl;
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;
        self.result = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(UnsignedLessThanNode* self) {
        *self = UnsignedLessThanNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(UnsignedLessThanNode) other) const {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.lhs.toHash() - this.rhs.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(UnsignedLessThanNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    UnsignedLessThanNode tmp = void;
    UnsignedLessThanNode.initialize(&tmp);
    //
    UnsignedLessThanNode ltu = void;
    moveEmplace(tmp, ltu);
    //
    assert(ltu == ltu);
    assert(ltu.result.owner == ltu.asNode);
    //
    UnsignedLessThanNode.dispose(&ltu);
}

/++
Computes whether a (signed) two's complement integer is strictly less than another.

There is no equivalent for `>` because it suffices to swap this node's operands.
+/
struct SignedLessThanNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;

    /// Right-hand-side operand.
    OutEdge rhs;

    /// A single resulting bit indicating `lhs < rhs`.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes a signed-less-than node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(SignedLessThanNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = SignedLessThanNode.init;

        self.vptr = &SignedLessThanNode.vtbl;
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;
        self.result = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(SignedLessThanNode* self) {
        *self = SignedLessThanNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(SignedLessThanNode) other) const {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.lhs.toHash() - this.rhs.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(SignedLessThanNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    SignedLessThanNode tmp = void;
    SignedLessThanNode.initialize(&tmp);
    //
    SignedLessThanNode lts = void;
    moveEmplace(tmp, lts);
    //
    assert(lts == lts);
    assert(lts.result.owner == lts.asNode);
    //
    SignedLessThanNode.dispose(&lts);
}

/++
Computes whether a (unsigned) two's complement integer is greater than or equal to another.

There is no equivalent for `<=` because it suffices to swap this node's operands.
+/
struct UnsignedGreaterOrEqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;

    /// Right-hand-side operand.
    OutEdge rhs;

    /// A single resulting bit indicating `lhs >= rhs`.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes an unsigned-greater-than-or-equal-to node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(UnsignedGreaterOrEqualNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = UnsignedGreaterOrEqualNode.init;

        self.vptr = &UnsignedGreaterOrEqualNode.vtbl;
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;
        self.result = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(UnsignedGreaterOrEqualNode* self) {
        *self = UnsignedGreaterOrEqualNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(UnsignedGreaterOrEqualNode) other) const {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.lhs.toHash() - this.rhs.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(UnsignedGreaterOrEqualNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    UnsignedGreaterOrEqualNode tmp = void;
    UnsignedGreaterOrEqualNode.initialize(&tmp);
    //
    UnsignedGreaterOrEqualNode geu = void;
    moveEmplace(tmp, geu);
    //
    assert(geu == geu);
    assert(geu.result.owner == geu.asNode);
    //
    UnsignedGreaterOrEqualNode.dispose(&geu);
}

/++
Computes whether a (signed) two's complement integer is greater than or equal to another.

There is no equivalent for `<=` because it suffices to swap this node's operands.
+/
struct SignedGreaterOrEqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;

    /// Right-hand-side operand.
    OutEdge rhs;

    /// A single resulting bit indicating `lhs >= rhs`.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes a signed-greater-than-or-equal-to node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure (null node).
    +/
    static err_t initialize(SignedGreaterOrEqualNode* self)
    in (self != null)
    {
        if (self == null) return EINVAL;
        *self = SignedGreaterOrEqualNode.init;

        self.vptr = &SignedGreaterOrEqualNode.vtbl;
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;
        self.result = InEdge.data(self.asNode);

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(SignedGreaterOrEqualNode* self) {
        *self = SignedGreaterOrEqualNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(SignedGreaterOrEqualNode) other) const {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    hash_t toHash() const {
        return (this.lhs.toHash() - this.rhs.toHash()).hashOf;
    }

    /// Adjusts in-edge slots after a move.
    void opPostMove(ref const(SignedGreaterOrEqualNode) old) pure {
        this.result.owner = this.asNode;
    }
}

@nogc nothrow unittest {
    SignedGreaterOrEqualNode tmp = void;
    SignedGreaterOrEqualNode.initialize(&tmp);
    //
    SignedGreaterOrEqualNode ges = void;
    moveEmplace(tmp, ges);
    //
    assert(ges == ges);
    assert(ges.result.owner == ges.asNode);
    //
    SignedGreaterOrEqualNode.dispose(&ges);
}


// TODO: type ops

// TODO: mem ops
