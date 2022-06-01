/++
Structure and interpretation of Gyre nodes.

This module implements Gyre nodes (and edges).
Each structure's documentation also explains its intended semantics, albeit this may be mixed with implementation details.


Poison_values_and_UB:

In Gyre, every operation may have some conditions imposed on its inputs in order to produce correct behavior / a sane value.
When the result of a data-only operation isn't well-defined (e.g. [SignedDivisionNode|integer division] by zero), it produces a "poison".
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
import std.traits :
    EnumMembers, Parameters,
    functionAttributes, SetFunctionAttributes, functionLinkage;

import eris.core : hash_t, err_t, allocate, deallocate;
import eris.hash_table : UnsafeHashMap;


/++
Possible edge kinds.

Each Gyre node has one or more "edge slots", which act as directed connectors.
This means that nodes don't reference each other directly.
Instead, they contain slots which connect to the slots of other nodes.
There are different kinds of edge slots, which indicate their meaning.
RULE: Every pair of connecting edge slots must have a matching kind.

Please note the directionality difference between "dependency" and "flow" edges.

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
            `@nogc nothrow pure
            static typeof(this) ` ~ __traits(identifier, EnumMembers!EdgeKind[kind]) ~ `(Args...)(auto ref Args args) {
                import core.lifetime : forward;
                return typeof(this)(
                    EdgeKind.` ~ __traits(identifier, EnumMembers!EdgeKind[kind]) ~ `,
                    forward!args
                );
            }`
        );
    }
}

/++
An outgoing edge slot.

Connects to exactly one [InEdge].
+/
struct OutEdge {
    mixin(taggedPointer!(
        InEdge*, "target",
        EdgeKind, "kind", 2
    ));

 pragma(inline) @nogc nothrow pure:
    /++
    Params:
        kind = This edge's kind.
        target = Must point to a matching in-edge slot.
    +/
    this(EdgeKind kind, InEdge* target) {
        this.kind = kind;
        this.target = target;
    }
    private this(EdgeKind kind) { this(kind, null); }
    @disable this();
    mixin StaticEdgeFactories;

    /++
    Semantic equality check.

    An out-edge slot is only equivalent to another if they point to equal [InEdge] slots.
    +/
    bool opEquals(const(OutEdge) other) const
    in (this.target == null || this.target.kind == this.kind, "edge slot kind mismatch")
    {
        if (this is other) return true;
        if (this.kind != other.kind) return false;
        if (this.target == null || other.target == null) return false;
        return *this.target == *other.target;
    }

    hash_t toHash() const {
        if (this.target == null) return this.kind.hashOf;
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
        EdgeKind, "kind", 2
    ));

    ID _id;
    alias ID = ushort;

 pragma(inline) @nogc nothrow pure:
    @property ID id() const { return this._id; }
    private @property void id(ID id) { this._id = id; }

    /++
    Params:
        kind = This edge's kind.
        owner = Must point to the node which owns this slot.
        id = Uniquely identifies this in-edge slot within its owner node.
    +/
    this(EdgeKind kind, Node* owner, uint id)
    in (id <= ID.max, "in-edge slot IDs must be at most " ~ ID.max.stringof)
    {
        this.kind = kind;
        this.owner = owner;
        this.id = cast(ID)id;
    }
    private this(EdgeKind kind, Node* owner) { this(kind, owner, 0); }
    version (unittest) private this(EdgeKind kind) { this(kind, null, 0); }
    @disable this();
    mixin StaticEdgeFactories;

    /++
    Semantic equality check.

    An in-edge slot is only equivalent to another if they represent equal values.
    We approximate this by checking that the slots' owner nodes are equal AND the slots are in a corresponding position in their respective owner (i.e. they stand for the same thing inside that node).
    +/
    bool opEquals(ref const(InEdge) other) const
    in (this.owner != null && other.owner != null, "can't use an uninitialized in-edge")
    {
        if (this.kind != other.kind) return false;
        if (this.id != other.id) return false;
        return *this.owner == *other.owner;
    }

    hash_t toHash() const
    in (this.owner != null, "can't use an uninitialized in-edge")
    {
        hash_t hash = this.kind.hashOf ^ this.id.hashOf;
        hash ^= this.owner.toHash();
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
Now, computing a node's hash value becomes an expensive operation as well, but fortunately it can be cached once a node's structure has stabilized.

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
     @nogc nothrow pure:
        bool function(const(Node)*, const(Node)*) opEquals;
        hash_t function(const(Node)*) toHash;
        InEdge* function(Node*, InEdge.ID) opIndex;
    }

    struct CommonPrefix {
        immutable(VTable)* vptr;
        hash_t hash;
    }

    CommonPrefix _node;
    alias _node this;

    static assert(
        Node.sizeof == Node.CommonPrefix.sizeof && Node.alignof == Node.CommonPrefix.alignof &&
        is(typeof(Node._node) == Node.CommonPrefix) && Node._node.offsetof == 0,
        "`Node` and `Node.CommonPrefix` must be binary-interchangeable"
    );

 public pragma(inline) @nogc nothrow pure:
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
    hash_t toHash() const {
        return this.hash ^ this.vptr.hashOf;
    }

    /++
    Fetches a specific in-edge slot in this node.

    NOTE: When nodes are initialized, they must identify each of their [InEdge]s with a unique id.

    Params:
        slot = Unique identifier for the in-edge slot within this node.

    Returns:
        A pointer to the identified in-edge, or `null` if it doesn't exist.
    +/
    InEdge* opIndex(InEdge.ID slot) {
        return this.vptr.opIndex(&this, slot);
    }
}

private mixin template NodeInheritance() {
    private alias This = typeof(this);

    package Node.CommonPrefix _node = { vptr: &vtbl };
    alias _node this;

    package static immutable(Node.VTable) vtbl = {
        opEquals: (const(Node)* lhs, const(Node)* rhs) @nogc nothrow pure {
            const(This)* self = This.ofNode(lhs);
            const(This)* other = This.ofNode(rhs);
            assert(self != null && other != null);
            static assert(
                __traits(hasMember, This, "opEquals"),
                "all nodes must explicitly define an `opEquals` function"
            );
            return *self == *other;
        },
        toHash: (const(Node)* node) @nogc nothrow pure {
            const(This)* self = This.ofNode(node);
            assert(self != null);
            static assert(
                __traits(hasMember, This, "toHash"),
                "all nodes must explicitly define a `toHash` function"
            );
            return self.toHash();
        },
        opIndex: (Node* node, InEdge.ID slot) @nogc nothrow pure {
            This* self = This.ofNode(node);
            assert(self != null);
            static assert(
                __traits(hasMember, This, "opIndex"),
                "all nodes must explicitly define an `opIndex` function"
            );
            return self.opIndex(slot);
        },
    };

    public pragma(inline) @nogc nothrow pure {
        void updateHash() {
            this._node.hash = this.toHash();
        }

        static assert(
            This._node.offsetof == 0,
            "common node prefix must be at a zero offset for safe polymorphism"
        );

        inout(Node)* asNode() inout
        return // XXX: `return` annotation needed in DMD 2.100.0
        in (this.vptr == &vtbl, "can't upcast an uninitialized node")
        {
            return cast(inout(Node)*)&this._node;
        }

        static inout(This)* ofNode(inout(Node)* node) {
            if (node == null || node.vptr != &vtbl) return null;
            return cast(inout(This)*)node;
        }

        static assert(
            __traits(hasMember, This, "outEdges") && __traits(hasMember, This, "inEdges"),
            "all nodes must provide iterators for their out-edge and in-edge slots"
        );

        /// Post-move adjusts in-edge slots' self-pointer.
        void opPostMove(ref const(This) old) pure {
            foreach (ref slot; this.inEdges!(int delegate(ref InEdge) @nogc nothrow pure)) {
                slot.owner = this.asNode;
            }
        }
    }
}

version (unittest) private { // for some reason, this needs to be in global scope
    static bool usingCustomHash;
    static bool usingCustomEquals;

    struct UnittestNode {
        mixin NodeInheritance;
        int value;

     @nogc nothrow pure:
        this(int value) { this.value = value; }

        bool opEquals(ref const(UnittestNode) rhs) const {
            debug usingCustomEquals = true;
            return this.value == rhs.value;
        }

        hash_t toHash() const {
            debug usingCustomHash = true;
            return this.value;
        }

        inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
            return null;
        }

        @property OutEdgeIterator!Callable
        outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
            return OutEdgeIterator!Callable(
                this.asNode,
                (Node* self, scope Callable iter) => 0
            );
        }

        @property InEdgeIterator!Callable
        inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
            return InEdgeIterator!Callable(
                this.asNode,
                (Node* self, scope Callable iter) => 0
            );
        }
    }
}

@nogc nothrow unittest {
    import eris.hash_table : HashSet;
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


/// Iterates (with `foreach`) over a node's out-edges.
struct OutEdgeIterator(Callable) if (is(Parameters!Callable[0] : const(OutEdge))) {
    private alias Dispatch = SetFunctionAttributes!(
        int delegate(Node*, scope Callable),
        functionLinkage!Callable,
        functionAttributes!Callable
    );
    private Node* _node;
    private Dispatch _opApply;
    ///
    int opApply(scope Callable iter) {
        return this._opApply(this._node, iter);
    }
}

/// Iterates (with `foreach`) over a node's in-edges.
struct InEdgeIterator(Callable) if (is(Parameters!Callable[0] : const(InEdge))) {
    private alias Dispatch = SetFunctionAttributes!(
        int delegate(Node*, scope Callable),
        functionLinkage!Callable,
        functionAttributes!Callable
    );
    private Node* _node;
    private Dispatch _opApply;
    ///
    int opApply(scope Callable iter) {
        return this._opApply(this._node, iter);
    }
}

// common boilerplate for node unittest
private void nodeTest(NodeType)(
    Parameters!(NodeType.initialize)[1 .. $] args,
    scope void delegate(ref NodeType node) @nogc nothrow test = (ref NodeType node){}
) @nogc nothrow {
    // initialize one guy
    NodeType tmp = void;
    NodeType.initialize(&tmp, args);
    // move it
    NodeType node = void;
    moveEmplace(tmp, node);
    // check if everything is fine
    assert(node == node);
    foreach (ref inEdge; node.inEdges) {
        assert(inEdge.owner == node.asNode);
        assert(&inEdge == node[inEdge.id]);
    }
    test(node);
    // free it on scope exit (and the second free should be a no-op)
    scope(exit) {
        NodeType.dispose(&node);
        NodeType.dispose(&node);
    }
}


package struct mnemonic { string shorthand; }


/++
Gyre's main mechanism for procedural abstraction, the join node.

Join nodes can be used as procedures, basic blocks or synchronization points.


Join nodes are used to define the (external) interface and (internal) contents of procedures and basic blocks.
They interact with the outside world through zero or more parameters.
As a join node begins to execute, control flows into its body, where all of its parameters are made available.
Therefore, a join node behaves like the entry block of a CFG, but with a collection of SSA phis (one for each parameter); so it can be used as an [extended basic block](https://mlir.llvm.org/docs/Rationale/Rationale/#block-arguments-vs-phi-nodes).
RULE: Gyre graphs can be cyclic, but only if every cycle goes through a join node.
This is similar to having a DFG with SSA phis, in which data-flow can still be considered causal as long as every cycle goes through one or more phi nodes to indicate a "temporal" control-flow dependency.

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
@mnemonic("join") struct JoinNode {
    mixin NodeInheritance;

    /// This join node's definition (a `data` slot), used to instantiate and invoke it.
    InEdge definition;

    /// Control flow edge into the join node's body.
    OutEdge control;

    /// Non-empty collection of channels, each containing zero or more of this node's parameters (either data or memory edges).
    InEdge[][] channels; // SSO: InEdge[][1] most of the time

 @nogc nothrow:
    /++
    Initializes a join node, must be later [dispose]d.

    This procedure initializes the collection of channels and sets up unique indexes for each in-edge slot.
    Edge slot kinds default to `data`; this can be changed later but requires a rehash.

    Params:
        self = Address of node being initialized.
        ms = Number of parameters on each channel.

    Returns:
        Zero on success, non-zero on failure (OOM or invalid number of channels).
    +/
    static err_t initialize(JoinNode* self, uint[] ms)
    in (ms.length >= 1, "at least one channel is needed")
    {
        if (ms.length < 1) return EINVAL;
        *self = JoinNode.init;

        self.vptr = &JoinNode.vtbl;
        self.definition = InEdge.data(self.asNode, 0);
        self.control = OutEdge.control;

        self.channels = allocate!(InEdge[])(ms.length);
        if (self.channels == null) return ENOMEM;
        uint id = 1;
        foreach (i, m; ms) {
            self.channels[i] = allocate!InEdge(m);

            // on failure, undo all previous allocations
            if (m > 0 && self.channels[i] == null) {
                foreach_reverse (previous; 0 .. i) {
                    self.channels[previous].deallocate();
                }
                self.channels.deallocate();
                self.channels = null;
                return ENOMEM;
            }

            foreach (j; 0 .. m) {
                self.channels[i][j] = InEdge.data(self.asNode, id);
                id++;
            }
        }

        return 0;
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
    bool opEquals(ref const(JoinNode) rhs) const pure {
        return this.asNode == rhs.asNode; // self-ptr
    }

    ///
    hash_t toHash() const pure {
        hash_t hash = 0;
        foreach (parameters; channels) {
            foreach (param; parameters) {
                hash -= param.kind.hashOf;
            }
        }
        return hash;
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        if (slot == 0) return &this.definition;

        // fast path: single-channel join
        if (this.channels.length == 1) {
            const int i = slot - 1;
            if (i >= this.channels[0].length) return null;
            else return &this.channels[0][i];
        }

        // slow path: index a rigged array
        foreach (parameters; this.channels) {
            foreach (ref param; parameters) {
                if (param.id == slot) return &param;
            }
        }

        return null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = JoinNode.ofNode(self);
                assert(node != null);
                return iter(node.control);
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = JoinNode.ofNode(self);
                assert(node != null);
                int stop = iter(node.definition);
                if (stop) return stop;
                foreach (parameters; node.channels) {
                    foreach (ref param; parameters) {
                        stop = iter(param);
                        if (stop) return stop;
                    }
                }
                return 0;
            }
        );
    }
}

@nogc nothrow unittest {
    uint[1] channelSizes = [4u];
    nodeTest!JoinNode(channelSizes[],
        (ref JoinNode join){
            assert(join.channels.length == 1);
            assert(join.channels[0].length == 4);
        },
    );
}

/++
Instantiates a [JoinNode|join node].

Join nodes correspond to static ("dead") subprograms.
In order to actually use a join node, one must first create a "live" instance of it.
The result of such an instantiation is a non-empty collection of continuations, one for each channel in the join pattern.
Then, using a continuation requires one to provide its parameters and [JumpNode|jump] into it, which may trigger the join node's body.


TODO: continuation semantics are unclear w.r.t. multiple uses and scope. e.g.: can a continuation be used more than once (with basic blocks, we would like the answer to be a YES, with return continuations, a NO), or are they consumed when the join triggers? what happens if a continuation is instantiated and never jumped to? what if two threads race to use the same continuation? yet another case is with upwards-escaping continuations, which we want to forbid (so that a function can't return a continuation back into itself)

See_Also: [JoinNode], [JumpNode]
+/
@mnemonic("inst") struct InstantiationNode {
    mixin NodeInheritance;

    /// Points to the definition of the join node being instantiated.
    OutEdge definition;

    /// Non-empty collection of live continuations, each corresponding to a channel in the join pattern.
    InEdge[] continuations; // SSO: InEdge[1] most of the time

 @nogc nothrow:
    /++
    Initializes an instantiation node, must be later [dispose]d.

    This procedure initializes the collection of continuations and sets up unique indexes for each in-edge slot.

    Params:
        self = Address of node being initialized.
        n = Number of continuations to instantiate.

    Returns:
        Zero on success, non-zero on failure (OOM or zero continuations).
    +/
    static err_t initialize(InstantiationNode* self, uint n)
    in (n >= 1, "at least one continuation is needed")
    {
        if (n < 1) return EINVAL;
        *self = InstantiationNode.init;

        self.vptr = &InstantiationNode.vtbl;
        self.definition = OutEdge.data;
        self.continuations = allocate!InEdge(n);
        if (self.continuations == null) return ENOMEM;
        foreach (i; 0 .. n)
            self.continuations[i] = InEdge.data(self.asNode, i);

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
    bool opEquals(ref const(InstantiationNode) rhs) const pure {
        return this.asNode == rhs.asNode; // self-ptr
    }

    ///
    hash_t toHash() const pure {
        return continuations.length.hashOf;
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        if (slot >= this.continuations.length) return null;
        return &this.continuations[slot];
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = InstantiationNode.ofNode(self);
                assert(node != null);
                return iter(node.definition);
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = InstantiationNode.ofNode(self);
                assert(node != null);
                foreach (ref cont; node.continuations) {
                    int stop = iter(cont);
                    if (stop) return stop;
                }
                return 0;
            }
        );
    }
}

@nogc nothrow unittest {
    nodeTest!InstantiationNode(1,
        (ref InstantiationNode inst){
            assert(inst.continuations.length == 1);
        },
    );
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
@mnemonic("jump") struct JumpNode {
    mixin NodeInheritance;

    /// Incoming control flow which is about to be yielded to the target continuation.
    InEdge control;

    /// A data dependency on some live continuation.
    OutEdge continuation;

    /// Arguments to be sent into the continuation and later used inside a join pattern's body.
    OutEdge[] arguments;

 @nogc nothrow:
    /++
    Initializes a jump node, must be later [dispose]d.

    Argument kinds default to `data`; this can be changed later but requires a rehash.

    Params:
        self = Address of node being initialized.
        m = Number of arguments sent through this jump.

    Returns:
        Zero on success, non-zero on failure (OOM).
    +/
    static err_t initialize(JumpNode* self, uint m) {
        *self = JumpNode.init;

        self.vptr = &JumpNode.vtbl;
        self.control = InEdge.control(self.asNode);
        self.continuation = OutEdge.data;
        self.arguments = allocate!OutEdge(m);
        if (m > 0 && self.arguments == null) return ENOMEM;
        foreach (i; 0 .. m) self.arguments[i] = OutEdge.data;

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
    bool opEquals(ref const(JumpNode) rhs) const pure {
        if (this.continuation != rhs.continuation) return false;
        if (this.arguments != rhs.arguments) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        hash_t hash = this.continuation.toHash();
        foreach (arg; this.arguments) hash -= arg.toHash();
        return hash;
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.control : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = JumpNode.ofNode(self);
                assert(node != null);
                int stop = iter(node.continuation);
                if (stop) return stop;
                foreach (ref arg; node.arguments) {
                    stop = iter(arg);
                    if (stop) return stop;
                }
                return 0;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = JumpNode.ofNode(self);
                assert(node != null);
                return iter(node.control);
            }
        );
    }
}

@nogc nothrow unittest {
    nodeTest!JumpNode(4,
        (ref JumpNode jump){
            assert(jump.arguments.length == 4);
        },
    );
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
@mnemonic("fork") struct ForkNode {
    mixin NodeInheritance;

    /// Incoming single control flow.
    InEdge control;

    /// At least two concurrent control flows resulting from this fork.
    OutEdge[] threads;

 @nogc nothrow:
    /++
    Initializes a fork node, must be later [dispose]d.

    Params:
        self = Address of node being initialized.
        n = Number of forked threads.

    Returns:
        Zero on success, non-zero on failure (OOM or invalid number of threads).
    +/
    static err_t initialize(ForkNode* self, uint n)
    in (n >= 2, "fork must create at least two threads")
    {
        if (n < 2) return EINVAL;
        *self = ForkNode.init;

        self.vptr = &ForkNode.vtbl;
        self.control = InEdge.control(self.asNode);
        self.threads = allocate!OutEdge(n);
        if (self.threads == null) return ENOMEM;
        foreach (ref thread; self.threads) thread = OutEdge.control;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(ForkNode* self) {
        self.threads.deallocate();
        *self = ForkNode.init;
    }

    /++
    Semantic equality check.

    Fork nodes are the same if and only if their resulting flows behave exactly the same (in which case they are still separate logical threads, but with a shared structure in the IR).
    +/
    bool opEquals(ref const(ForkNode) rhs) const pure {
        if (this.threads != rhs.threads) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        hash_t hash = 0;
        foreach (thread; this.threads) hash -= thread.toHash();
        return hash;
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.control : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = ForkNode.ofNode(self);
                assert(node != null);
                foreach (ref thread; node.threads) {
                    int stop = iter(thread);
                    if (stop) return stop;
                }
                return 0;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = ForkNode.ofNode(self);
                assert(node != null);
                return iter(node.control);
            }
        );
    }
}

@nogc nothrow unittest {
    nodeTest!ForkNode(2,
        (ref ForkNode fork){
            assert(fork.threads.length == 2);
        },
    );
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
@mnemonic("cond") struct ConditionalNode {
    mixin NodeInheritance;

    /// Data selector used to choose the taken branch.
    OutEdge selector;

    /// Incoming control flow edge.
    InEdge control;

    // SSO: binary branches will probably be the most common
    private UnsafeHashMap!(ulong, OutEdge)* _options;

 @nogc nothrow:
    /++
    At least two outgoing control flow edges, only one of which will be taken.

    Represented as a sparse mapping to avoid having an exponential number of unused options.
    +/
    @property ref inout(UnsafeHashMap!(ulong, OutEdge)) options() inout pure {
        return *this._options;
    }

    /++
    Initializes a conditional node, must be later [dispose]d.

    Params:
        self = Address of node being initialized.
        n = Number of branches to preallocate.

    Returns:
        Zero on success, non-zero on failure (OOM or invalid number of branches).
    +/
    static err_t initialize(ConditionalNode* self, uint n)
    in (n >= 2, "conditional must have at least two branches")
    {
        if (n < 2) return EINVAL;
        *self = ConditionalNode.init;

        self.vptr = &ConditionalNode.vtbl;
        self.selector = OutEdge.data;
        self.control = InEdge.control(self.asNode);

        self._options = allocate!(UnsafeHashMap!(ulong, OutEdge));
        if (self._options == null) return ENOMEM;
        self.options = UnsafeHashMap!(ulong, OutEdge).init;
        const error = self.options.rehash(n);
        if (error) {
            deallocate(self._options);
            self._options = null;
            return ENOMEM;
        }

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(ConditionalNode* self) {
        if (self._options != null) self.options.dispose();
        deallocate(self._options);
        *self = ConditionalNode.init;
    }

    /++
    Semantic equality check.

    Conditional nodes are the same if and only if they use the same value to select the taken branch and every branch in one has a corresponding branch in the other.
    +/
    bool opEquals(ref const(ConditionalNode) rhs) const pure {
        if (this.selector != rhs.selector) return false;
        if (this.options != rhs.options) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.selector.toHash() ^ this.options.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.control : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = ConditionalNode.ofNode(self);
                assert(node != null);
                int stop = iter(node.selector);
                if (stop) return stop;
                foreach (ref option; node.options.byValue) {
                    stop = iter(option);
                    if (stop) return stop;
                }
                return 0;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = ConditionalNode.ofNode(self);
                assert(node != null);
                return iter(node.control);
            }
        );
    }
}

@nogc nothrow unittest {
    nodeTest!ConditionalNode(2,
        (ref ConditionalNode cond){
            cond.options[0] = OutEdge.control;
            cond.options[1] = OutEdge.control;
            assert(cond.options.length == 2);
        },
    );
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
@mnemonic("macro_") struct MacroNode {
    mixin NodeInheritance;

    /// Links this macro node to its external definition.
    ID id;
    alias ID = ushort; /// ditto

    /// Edges (any kind) which point out from this node.
    OutEdge[] outSlots;

    /// Edges (of any kind) which point into this node.
    InEdge[] inSlots;

 @nogc nothrow:
    /++
    Initializes a macro node, must be later [dispose]d.

    This procedure sets up unique indexes for each in-edge slot.
    All slot kinds default to `data`; this can be changed later and does not require a rehash.

    Params:
        self = Address of node being initialized.
        id = Macro node identification number.
        ins = Number of (preallocated) in-edges in this node.
        outs = Number of (preallocated) out-edges in this node.

    Returns:
        Zero on success, non-zero on failure (OOM).
    +/
    static err_t initialize(MacroNode* self, uint id, uint ins, uint outs)
    in (id <= ID.max, "macro node IDs must be at most " ~ ID.max.stringof)
    {
        *self = MacroNode.init;

        self.vptr = &MacroNode.vtbl;
        self.id = cast(ID)id;

        self.inSlots = allocate!InEdge(ins);
        if (ins > 0 && self.inSlots == null) return ENOMEM;
        foreach (i; 0 .. ins)
            self.inSlots[i] = InEdge.data(self.asNode, i);

        self.outSlots = allocate!OutEdge(outs);
        if (outs > 0 && self.outSlots == null) {
            self.inSlots.deallocate();
            self.inSlots = null;
            return ENOMEM;
        }
        foreach (i; 0 .. outs) self.outSlots[i] = OutEdge.data;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(MacroNode* self) {
        self.outSlots.deallocate();
        self.inSlots.deallocate();
        *self = MacroNode.init;
    }

    /++
    Semantic equality check.

    Since macro nodes can expand into arbitrary subgraphs, we treat each one individually.
    +/
    bool opEquals(ref const(MacroNode) rhs) const pure {
        return this.id == rhs.id && this.asNode == rhs.asNode; // self-ptr
    }

    /++
    Hash function.

    Depends only on this macro node's identifier.
    +/
    hash_t toHash() const pure {
        return this.id.hashOf;
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        if (slot >= this.inSlots.length) return null;
        return &this.inSlots[slot];
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = MacroNode.ofNode(self);
                assert(node != null);
                foreach (ref outEdge; node.outSlots) {
                    int stop = iter(outEdge);
                    if (stop) return stop;
                }
                return 0;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = MacroNode.ofNode(self);
                assert(node != null);
                foreach (ref inEdge; node.inSlots) {
                    int stop = iter(inEdge);
                    if (stop) return stop;
                }
                return 0;
            }
        );
    }
}

@nogc nothrow unittest {
    nodeTest!MacroNode(MacroNode.ID(42), 3, 2,
        (ref MacroNode node){
            assert(node.id == 42);
            assert(node.inSlots.length == 3);
            assert(node.outSlots.length == 2);
        },
    );
}


/++
Constructs a constant value of a certain type.

See_Also: [UndefinedNode]
+/
@mnemonic("const_") struct ConstantNode {
    mixin NodeInheritance;

    // TCC: temporary assumption that all types are i64
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(ConstantNode* self, ulong literal) {
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
    bool opEquals(ref const(ConstantNode) rhs) const pure {
        return this.literal == rhs.literal;
    }

    ///
    hash_t toHash() const pure {
        return this.literal.hashOf;
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.value : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter) => 0
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = ConstantNode.ofNode(self);
                assert(node != null);
                return iter(node.value);
            }
        );
    }
}

@nogc nothrow unittest {
    nodeTest!ConstantNode(1,
        (ref ConstantNode c1){
            assert(c1.literal == 1);
        },
    );
}

/++
Constructs a ["don't care"](https://en.wikipedia.org/wiki/Don%27t-care_term) value of a certain type.

The compiler is free to change this node into any constant (i.e. define it), as long as it's value is consistently seen by all of its uses.
This notion of 'undefined' comes from [Click's thesis](https://scholarship.rice.edu/bitstream/handle/1911/96451/TR95-252.pdf).


Rationale: Undefined values cannot be produced by [ConstantNode]s, because the latter are always subject to structural sharing (e.g. every `1` is the same), whereas different undefined nodes can resolve to different values and therefore each needs its own identity.

See_Also: [ConstantNode]
+/
@mnemonic("undef") struct UndefinedNode {
    mixin NodeInheritance;

    /// The resulting value.
    InEdge value;

 @nogc nothrow:
    /++
    Initializes an undefined node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(UndefinedNode* self) {
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
    bool opEquals(ref const(UndefinedNode) rhs) const pure {
        return this.asNode == rhs.asNode; // self-ptr
    }

    ///
    hash_t toHash() const pure {
        return hash_t.max;
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.value : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter) => 0
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UndefinedNode.ofNode(self);
                assert(node != null);
                return iter(node.value);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!UndefinedNode(); }

/// Yields the lowermost bits of its input.
@mnemonic("trunc") struct TruncationNode { // TCC: doesn't make sense without type info
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(TruncationNode* self) {
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
    bool opEquals(ref const(TruncationNode) rhs) const pure {
        return this.input == rhs.input;
    }

    ///
    hash_t toHash() const pure {
        return this.input.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.output : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = TruncationNode.ofNode(self);
                assert(node != null);
                return iter(node.input);
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = TruncationNode.ofNode(self);
                assert(node != null);
                return iter(node.output);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!TruncationNode(); }

/++
Yields a wider version of its input, with added bits set to zero.

See_Also: [SignedExtensionNode]
+/
@mnemonic("extu") struct UnsignedExtensionNode { // TCC: doesn't make sense without type info
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(UnsignedExtensionNode* self) {
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
    bool opEquals(ref const(UnsignedExtensionNode) rhs) const pure {
        return this.input == rhs.input;
    }

    ///
    hash_t toHash() const pure {
        return this.input.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.output : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedExtensionNode.ofNode(self);
                assert(node != null);
                return iter(node.input);
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedExtensionNode.ofNode(self);
                assert(node != null);
                return iter(node.output);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!UnsignedExtensionNode(); }

/++
Yields a wider version of its input, with added bits equal to the input's sign bit.

See_Also: [UnsignedExtensionNode]
+/
@mnemonic("exts") struct SignedExtensionNode { // TCC: doesn't make sense without type info
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(SignedExtensionNode* self) {
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
    bool opEquals(ref const(SignedExtensionNode) rhs) const pure {
        return this.input == rhs.input;
    }

    ///
    hash_t toHash() const pure {
        return this.input.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.output : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedExtensionNode.ofNode(self);
                assert(node != null);
                return iter(node.input);
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedExtensionNode.ofNode(self);
                assert(node != null);
                return iter(node.output);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!SignedExtensionNode(); }

/++
An operation which chooses one of its inputs to forward as a result.

In a multiplexer node, the choice of which input to forward is controled by an unsigned integer, as if it was indexing an array of inputs.
If the selector's value does not match the index of any input, the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.


The behavior of this node could be emulated by a value-carrying [ConditionalNode|branch] into an [JoinNode|extended basic block].
However, this node does not need control flow edges at all.
Thus, its semantics are slightly different: whereas a control flow branch disallows the execution of operations in its unchosen branches (but the compiler can still move them out of the branch if that preserves program semantics), a mux node is allowed to compute all of its options before choosing which one to forward (but doesn't need to, e.g. if the selector is a constant).

See_Also: [ConditionalNode]
+/
@mnemonic("mux") struct MultiplexerNode {
    mixin NodeInheritance;

    /// Data dependency used to choose which of the given inputs will be returned.
    OutEdge selector;

    /// Resulting value.
    InEdge output;

    // SSO: binary mux will probably be the most common
    private UnsafeHashMap!(ulong, OutEdge)* _inputs;

 @nogc nothrow:
    /++
    At least two inputs, one of which will be forwarded as output.

    Represented as a sparse mapping to avoid having an exponential number of unused input edges.
    +/
    @property ref inout(UnsafeHashMap!(ulong, OutEdge)) inputs() inout pure {
        return *this._inputs;
    }

    /++
    Initializes a multiplexer node, must be later [dispose]d.

    Params:
        self = Address of node being initialized.
        n = Number of inputs to preallocate.

    Returns:
        Zero on success, non-zero on failure (OOM or invalid number of inputs).
    +/
    static err_t initialize(MultiplexerNode* self, uint n)
    in (n >= 2, "multiplexer must have at least two inputs")
    {
        if (n < 2) return EINVAL;
        *self = MultiplexerNode.init;

        self.vptr = &MultiplexerNode.vtbl;
        self.selector = OutEdge.data;
        self.output = InEdge.data(self.asNode);

        self._inputs = allocate!(UnsafeHashMap!(ulong, OutEdge));
        if (self._inputs == null) return ENOMEM;
        self.inputs = UnsafeHashMap!(ulong, OutEdge).init;
        const error = self.inputs.rehash(n);
        if (error) {
            deallocate(self._inputs);
            self._inputs = null;
            return ENOMEM;
        }

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(MultiplexerNode* self) {
        if (self._inputs != null) self.inputs.dispose();
        deallocate(self._inputs);
        *self = MultiplexerNode.init;
    }

    /// Semantic equality <=> structural equality.
    bool opEquals(ref const(MultiplexerNode) rhs) const pure {
        if (this.selector != rhs.selector) return false;
        if (this.inputs != rhs.inputs) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.selector.toHash() ^ this.inputs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.output : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = MultiplexerNode.ofNode(self);
                assert(node != null);
                int stop = iter(node.selector);
                if (stop) return stop;
                foreach (ref input; node.inputs.byValue) {
                    stop = iter(input);
                    if (stop) return stop;
                }
                return 0;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = MultiplexerNode.ofNode(self);
                assert(node != null);
                return iter(node.output);
            }
        );
    }
}

@nogc nothrow unittest {
    nodeTest!MultiplexerNode(2,
        (ref MultiplexerNode mux){
            mux.inputs[0] = OutEdge.data;
            mux.inputs[1] = OutEdge.data;
            assert(mux.inputs.length == 2);
        }
    );
}

/// Bitwise `AND` operation.
@mnemonic("and") struct AndNode {
    mixin NodeInheritance;

    /// Resulting bit pattern.
    InEdge result;

    /// Operands.
    OutEdge lhs;
    OutEdge rhs; /// ditto

 @nogc nothrow:
    /++
    Initializes an AND node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(AndNode* self) {
        *self = AndNode.init;

        self.vptr = &AndNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(AndNode* self) {
        *self = AndNode.init;
    }

    /// Semantic equality <=> structural equality (modulo operand order).
    bool opEquals(ref const(AndNode) other) const pure {
        return (this.lhs == other.lhs && this.rhs == other.rhs)
            || (this.lhs == other.rhs && this.rhs == other.lhs);
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = AndNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = AndNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!AndNode(); }

/// Bitwise `OR` operation.
@mnemonic("or") struct OrNode {
    mixin NodeInheritance;

    /// Resulting bit pattern.
    InEdge result;

    /// Operands.
    OutEdge lhs;
    OutEdge rhs; /// ditto

 @nogc nothrow:
    /++
    Initializes an OR node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(OrNode* self) {
        *self = OrNode.init;

        self.vptr = &OrNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(OrNode* self) {
        *self = OrNode.init;
    }

    /// Semantic equality <=> structural equality (modulo operand order).
    bool opEquals(ref const(OrNode) other) const pure {
        return (this.lhs == other.lhs && this.rhs == other.rhs)
            || (this.lhs == other.rhs && this.rhs == other.lhs);
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = OrNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = OrNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!OrNode(); }

/++
Bitwise `XOR` operation.

Can be used as a unary `NOT` operation when one operand is an all-ones constant.
+/
@mnemonic("xor") struct XorNode {
    mixin NodeInheritance;

    /// Resulting bit pattern.
    InEdge result;

    /// Operands.
    OutEdge lhs;
    OutEdge rhs; /// ditto

 @nogc nothrow:
    /++
    Initializes an XOR node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(XorNode* self) {
        *self = XorNode.init;

        self.vptr = &XorNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(XorNode* self) {
        *self = XorNode.init;
    }

    /// Semantic equality <=> structural equality (modulo operand order).
    bool opEquals(ref const(XorNode) other) const pure {
        return (this.lhs == other.lhs && this.rhs == other.rhs)
            || (this.lhs == other.rhs && this.rhs == other.lhs);
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = XorNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = XorNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!XorNode(); }

/++
Bitwise left-shift operation; shifts in zeros.

Shift amount must be no greater than the number of input bits, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).

See_Also: [LeftShiftNoOverflowNode]
+/
@mnemonic("shl") struct LeftShiftNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(LeftShiftNode* self) {
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
    bool opEquals(ref const(LeftShiftNode) rhs) const pure {
        if (this.input != rhs.input) return false;
        if (this.shift != rhs.shift) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.input.toHash() - this.shift.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.output : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = LeftShiftNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.input);
                if (!stop) stop = iter(node.shift);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = LeftShiftNode.ofNode(self);
                assert(node != null);
                return iter(node.output);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!LeftShiftNode(); }

/++
Bitwise left-shift with [no-overflow](gyre.nodes.html#no-overflow-operations) semantics; shifts in zeros.

Shift amount must be no greater than the number of input bits, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).
Furthermore, this operation guarantees that no `1` bits will be shifted off the initial word size (so the operand can never be negative).
In other words, the result is treated as multiplication by a power of two and it must fit within the given bit length, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).

See_Also: [LeftShiftNode]
+/
@mnemonic("shlno") struct LeftShiftNoOverflowNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(LeftShiftNoOverflowNode* self) {
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
    bool opEquals(ref const(LeftShiftNoOverflowNode) rhs) const pure {
        if (this.input != rhs.input) return false;
        if (this.shift != rhs.shift) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.input.toHash() - this.shift.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.output : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = LeftShiftNoOverflowNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.input);
                if (!stop) stop = iter(node.shift);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = LeftShiftNoOverflowNode.ofNode(self);
                assert(node != null);
                return iter(node.output);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!LeftShiftNoOverflowNode(); }

/++
Logical right-shift operation; shifts in zeros.

Shift amount must be no greater than the number of input bits, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).

See_Also: [SignedRightShiftNode]
+/
@mnemonic("shru") struct UnsignedRightShiftNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(UnsignedRightShiftNode* self) {
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
    bool opEquals(ref const(UnsignedRightShiftNode) rhs) const pure {
        if (this.input != rhs.input) return false;
        if (this.shift != rhs.shift) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.input.toHash() - this.shift.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.output : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedRightShiftNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.input);
                if (!stop) stop = iter(node.shift);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedRightShiftNode.ofNode(self);
                assert(node != null);
                return iter(node.output);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!UnsignedRightShiftNode(); }

/++
Arithmetic right-shift operation; bits shifted in are equal to the input's most significant bit.

Shift amount must be no greater than the number of input bits, otherwise results in [poison](gyre.nodes.html#poison-values-and-ub).

See_Also: [UnsignedRightShiftNode]
+/
@mnemonic("shrs") struct SignedRightShiftNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(SignedRightShiftNode* self) {
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
    bool opEquals(ref const(SignedRightShiftNode) rhs) const pure {
        if (this.input != rhs.input) return false;
        if (this.shift != rhs.shift) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.input.toHash() - this.shift.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.output : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedRightShiftNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.input);
                if (!stop) stop = iter(node.shift);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedRightShiftNode.ofNode(self);
                assert(node != null);
                return iter(node.output);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!SignedRightShiftNode(); }

/++
Two's complement addition operation (works for both signed and unsigned integers).

Wraps around on overflow.

See_Also: [AdditionNoOverflowSignedNode]
+/
@mnemonic("add") struct AdditionNode {
    mixin NodeInheritance;

    /// Resulting sum.
    InEdge result;

    /// Operands.
    OutEdge lhs;
    OutEdge rhs; /// ditto

 @nogc nothrow:
    /++
    Initializes an addition node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(AdditionNode* self) {
        *self = AdditionNode.init;

        self.vptr = &AdditionNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(AdditionNode* self) {
        *self = AdditionNode.init;
    }

    /// Semantic equality <=> structural equality (modulo operand order).
    bool opEquals(ref const(AdditionNode) other) const pure {
        return (this.lhs == other.lhs && this.rhs == other.rhs)
            || (this.lhs == other.rhs && this.rhs == other.lhs);
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = AdditionNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = AdditionNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!AdditionNode(); }

/++
Two's complement [no-overflow](gyre.nodes.html#no-overflow-operations) signed addition.

Produces [poison](gyre.nodes.html#poison-values-and-ub) on signed overflow.

See_Also: [AdditionNode]
+/
@mnemonic("addnos") struct AdditionNoOverflowSignedNode {
    mixin NodeInheritance;

    /// Resulting sum.
    InEdge result;

    /// Operands.
    OutEdge lhs;
    OutEdge rhs; /// ditto

 @nogc nothrow:
    /++
    Initializes an addition node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(AdditionNoOverflowSignedNode* self) {
        *self = AdditionNoOverflowSignedNode.init;

        self.vptr = &AdditionNoOverflowSignedNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(AdditionNoOverflowSignedNode* self) {
        *self = AdditionNoOverflowSignedNode.init;
    }

    /// Semantic equality <=> structural equality (modulo operand order).
    bool opEquals(ref const(AdditionNoOverflowSignedNode) other) const pure {
        return (this.lhs == other.lhs && this.rhs == other.rhs)
            || (this.lhs == other.rhs && this.rhs == other.lhs);
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = AdditionNoOverflowSignedNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = AdditionNoOverflowSignedNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!AdditionNoOverflowSignedNode(); }

/++
Two's complement subtraction operation (works for both signed and unsigned integers).

Wraps around on overflow.

See_Also: [SubtractionNoOverflowSignedNode]
+/
@mnemonic("sub") struct SubtractionNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(SubtractionNode* self) {
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
    bool opEquals(ref const(SubtractionNode) other) const pure {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() - this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SubtractionNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SubtractionNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!SubtractionNode(); }

/++
Two's complement [no-overflow](gyre.nodes.html#no-overflow-operations) signed subtraction.

Produces [poison](gyre.nodes.html#poison-values-and-ub) on signed overflow.

See_Also: [SubtractionNode]
+/
@mnemonic("subnos") struct SubtractionNoOverflowSignedNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(SubtractionNoOverflowSignedNode* self) {
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
    bool opEquals(ref const(SubtractionNoOverflowSignedNode) other) const pure {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() - this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SubtractionNoOverflowSignedNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SubtractionNoOverflowSignedNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!SubtractionNoOverflowSignedNode(); }

/++
Two's complement multiplication operation.

Since this only produces the lower half of a full multiplication, it is the same for both signed and unsigned integers.
Wraps around on overflow.

See_Also: [MultiplicationNoOverflowSignedNode]
+/
@mnemonic("mul") struct MultiplicationNode {
    mixin NodeInheritance;

    /// Resulting product.
    InEdge result;

    /// Operands.
    OutEdge lhs;
    OutEdge rhs; /// ditto

 @nogc nothrow:
    /++
    Initializes a multiplication node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(MultiplicationNode* self) {
        *self = MultiplicationNode.init;

        self.vptr = &MultiplicationNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(MultiplicationNode* self) {
        *self = MultiplicationNode.init;
    }

    /// Semantic equality <=> structural equality (modulo operand order).
    bool opEquals(ref const(MultiplicationNode) other) const pure {
        return (this.lhs == other.lhs && this.rhs == other.rhs)
            || (this.lhs == other.rhs && this.rhs == other.lhs);
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = MultiplicationNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = MultiplicationNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!MultiplicationNode(); }

/++
Two's complement [no-overflow](gyre.nodes.html#no-overflow-operations) signed multiplication.

Produces [poison](gyre.nodes.html#poison-values-and-ub) when the lower half of the full multiplication has signed overflow.

See_Also: [MultiplicationNode]
+/
@mnemonic("mulnos") struct MultiplicationNoOverflowSignedNode {
    mixin NodeInheritance;

    /// Resulting product.
    InEdge result;

    /// Operands.
    OutEdge lhs;
    OutEdge rhs; /// ditto

 @nogc nothrow:
    /++
    Initializes a multiplication node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(MultiplicationNoOverflowSignedNode* self) {
        *self = MultiplicationNoOverflowSignedNode.init;

        self.vptr = &MultiplicationNoOverflowSignedNode.vtbl;
        self.result = InEdge.data(self.asNode);
        self.lhs = OutEdge.data;
        self.rhs = OutEdge.data;

        return 0;
    }

    /// Frees all resources allocated by this node and sets it to an uninitialized state.
    static void dispose(MultiplicationNoOverflowSignedNode* self) {
        *self = MultiplicationNoOverflowSignedNode.init;
    }

    /// Semantic equality <=> structural equality (modulo operand order).
    bool opEquals(ref const(MultiplicationNoOverflowSignedNode) other) const pure {
        return (this.lhs == other.lhs && this.rhs == other.rhs)
            || (this.lhs == other.rhs && this.rhs == other.lhs);
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = MultiplicationNoOverflowSignedNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = MultiplicationNoOverflowSignedNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!MultiplicationNoOverflowSignedNode(); }

/++
Two's complement division operation for unsigned operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.

See_Also: [SignedDivisionNode]
+/
@mnemonic("divu") struct UnsignedDivisionNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(UnsignedDivisionNode* self) {
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
    bool opEquals(ref const(UnsignedDivisionNode) other) const pure {
        if (this.dividend != other.dividend) return false;
        if (this.divisor != other.divisor) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.dividend.toHash() - this.divisor.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.quotient : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedDivisionNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.dividend);
                if (!stop) stop = iter(node.divisor);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedDivisionNode.ofNode(self);
                assert(node != null);
                return iter(node.quotient);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!UnsignedDivisionNode(); }

/++
Two's complement division operation for signed operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.
Furthermore, dividing the "most negative" value representable (in N bits, $(MATH -1 \times 2^{N-1})) by `-1` also results in poison.

See_Also: [UnsignedDivisionNode]
+/
@mnemonic("divs") struct SignedDivisionNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(SignedDivisionNode* self) {
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
    bool opEquals(ref const(SignedDivisionNode) other) const pure {
        if (this.dividend != other.dividend) return false;
        if (this.divisor != other.divisor) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.dividend.toHash() - this.divisor.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.quotient : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedDivisionNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.dividend);
                if (!stop) stop = iter(node.divisor);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedDivisionNode.ofNode(self);
                assert(node != null);
                return iter(node.quotient);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!SignedDivisionNode(); }

/++
Two's complement remainder operation for unsigned operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.

See_Also: [SignedRemainderNode]
+/
@mnemonic("remu") struct UnsignedRemainderNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(UnsignedRemainderNode* self) {
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
    bool opEquals(ref const(UnsignedRemainderNode) other) const pure {
        if (this.dividend != other.dividend) return false;
        if (this.divisor != other.divisor) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.dividend.toHash() - this.divisor.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.remainder : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedRemainderNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.dividend);
                if (!stop) stop = iter(node.divisor);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedRemainderNode.ofNode(self);
                assert(node != null);
                return iter(node.remainder);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!UnsignedRemainderNode(); }

/++
Two's complement remainder operation for signed operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](gyre.nodes.html#poison-values-and-ub) value.
Furthermore, dividing the "most negative" value representable (in N bits, $(MATH -1 \times 2^{N-1})) by `-1` also results in poison.

See_Also: [UnsignedRemainderNode]
+/
@mnemonic("rems") struct SignedRemainderNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(SignedRemainderNode* self) {
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
    bool opEquals(ref const(SignedRemainderNode) other) const pure {
        if (this.dividend != other.dividend) return false;
        if (this.divisor != other.divisor) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.dividend.toHash() - this.divisor.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.remainder : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedRemainderNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.dividend);
                if (!stop) stop = iter(node.divisor);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedRemainderNode.ofNode(self);
                assert(node != null);
                return iter(node.remainder);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!SignedRemainderNode(); }

/// Compares two bit patterns for equality.
@mnemonic("eq") struct EqualNode {
    mixin NodeInheritance;

    /// Operands (order doesn't matter).
    OutEdge lhs;
    OutEdge rhs; /// ditto

    /// A single resulting bit indicating whether operands are equal.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes an equal node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(EqualNode* self) {
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
    bool opEquals(ref const(EqualNode) other) const pure {
        return (this.lhs == other.lhs && this.rhs == other.rhs)
            || (this.lhs == other.rhs && this.rhs == other.lhs);
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = EqualNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = EqualNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!EqualNode(); }

/// Compares two bit patterns for inequality.
@mnemonic("ne") struct NotEqualNode {
    mixin NodeInheritance;

    /// Operands (order doesn't matter).
    OutEdge lhs;
    OutEdge rhs; /// ditto

    /// A single resulting bit indicating whether operands are different.
    InEdge result;

 @nogc nothrow:
    /++
    Initializes a not-equal node.

    Params:
        self = Address of node being initialized.

    Returns:
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(NotEqualNode* self) {
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
    bool opEquals(ref const(NotEqualNode) other) const pure {
        return (this.lhs == other.lhs && this.rhs == other.rhs)
            || (this.lhs == other.rhs && this.rhs == other.lhs);
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() ^ this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = NotEqualNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = NotEqualNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!NotEqualNode(); }

/++
Computes whether a (unsigned) two's complement integer is strictly less than another.

There is no equivalent for `>` because it suffices to swap this node's operands.
+/
@mnemonic("ltu") struct UnsignedLessThanNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(UnsignedLessThanNode* self) {
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
    bool opEquals(ref const(UnsignedLessThanNode) other) const pure {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() - this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedLessThanNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedLessThanNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!UnsignedLessThanNode(); }

/++
Computes whether a (signed) two's complement integer is strictly less than another.

There is no equivalent for `>` because it suffices to swap this node's operands.
+/
@mnemonic("lts") struct SignedLessThanNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(SignedLessThanNode* self) {
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
    bool opEquals(ref const(SignedLessThanNode) other) const pure {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() - this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedLessThanNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedLessThanNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!SignedLessThanNode(); }

/++
Computes whether a (unsigned) two's complement integer is greater than or equal to another.

There is no equivalent for `<=` because it suffices to swap this node's operands.
+/
@mnemonic("geu") struct UnsignedGreaterOrEqualNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(UnsignedGreaterOrEqualNode* self) {
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
    bool opEquals(ref const(UnsignedGreaterOrEqualNode) other) const pure {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() - this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedGreaterOrEqualNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = UnsignedGreaterOrEqualNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!UnsignedGreaterOrEqualNode(); }

/++
Computes whether a (signed) two's complement integer is greater than or equal to another.

There is no equivalent for `<=` because it suffices to swap this node's operands.
+/
@mnemonic("ges") struct SignedGreaterOrEqualNode {
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
        Zero on success, non-zero on failure.
    +/
    static err_t initialize(SignedGreaterOrEqualNode* self) {
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
    bool opEquals(ref const(SignedGreaterOrEqualNode) other) const pure {
        if (this.lhs != other.lhs) return false;
        if (this.rhs != other.rhs) return false;
        return true;
    }

    ///
    hash_t toHash() const pure {
        return this.lhs.toHash() - this.rhs.toHash();
    }

    ///
    inout(InEdge)* opIndex(InEdge.ID slot) inout pure {
        return slot == 0 ? &this.result : null;
    }

    /// Provides an iterator over this node's out-edges.
    @property OutEdgeIterator!Callable
    outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
        return OutEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedGreaterOrEqualNode.ofNode(self);
                assert(node != null);
                int stop = 0;
                if (!stop) stop = iter(node.lhs);
                if (!stop) stop = iter(node.rhs);
                return stop;
            }
        );
    }

    /// Provides an iterator over this node's in-edges.
    @property InEdgeIterator!Callable
    inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
        return InEdgeIterator!Callable(
            this.asNode,
            (Node* self, scope Callable iter){
                auto node = SignedGreaterOrEqualNode.ofNode(self);
                assert(node != null);
                return iter(node.result);
            }
        );
    }
}

@nogc nothrow unittest { nodeTest!SignedGreaterOrEqualNode(); }


// TCC: type ops

// TCC: mem ops
