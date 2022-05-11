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

import std.bitmanip : taggedPointer;
import std.traits : EnumMembers;

import eris.core : hash_t;
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
            "static typeof(this) " ~ __traits(identifier, EnumMembers!EdgeKind[kind]) ~ "() @nogc nothrow pure {
                return typeof(this)(EdgeKind." ~ __traits(identifier, EnumMembers!EdgeKind[kind]) ~ ");
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

 @nogc nothrow pure:
    @property EdgeKind kind() const {
        return this._kind;
    }

    @disable this();

    /++
    Params:
        kind = This edge's kind, fixed on construction.
        target = Either points to another edge slot, or is `null`.
    +/
    this(EdgeKind kind, InEdge* target = null) {
        this._kind = kind;
        this.target = target;
        assert(
            target == null || target.kind == this.kind,
            "connecting edge slots must have matching kinds"
        );
    }

    mixin StaticEdgeFactories;
}

/// Example usage:
@nogc nothrow pure unittest {
    auto def = InEdge.data;
    auto use1 = OutEdge.data;
    auto use2 = OutEdge.data;
    // data edges are directed from uses to defs
    use1.target = &def;
    use2.target = &def;
    assert(use1 == use2);
}

/// Edge slots better be no bigger than a raw pointer:
@nogc nothrow pure unittest {
    static assert(OutEdge.sizeof <= (InEdge*).sizeof);
}

/++
An incoming edge slot.

Can receive any number of [OutEdge]s.
+/
struct InEdge {
    mixin(taggedPointer!(
        Node*, "owner",
        EdgeKind, "_kind", 2
    ));

 @nogc nothrow pure:
    @property EdgeKind kind() const {
        return this._kind;
    }

    @disable this();

    /++
    Params:
        kind = This edge's kind, fixed on construction.
        owner = Points back to the node which owns this edge.
    +/
    this(EdgeKind kind, Node* owner = null) {
        this._kind = kind;
        this.owner = owner;
    }

    mixin StaticEdgeFactories;
}

/// Example usage:
@nogc nothrow pure unittest {
    auto A = OutEdge.control;
    auto B = InEdge.control;
    // in this example, control flows out from A and into B
    A.target = &B;
    assert(A.target.owner is B.owner);
}

/// Edge slots better be no bigger than a raw pointer:
@nogc nothrow pure unittest {
    static assert(InEdge.sizeof <= (Node*).sizeof);
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
This check requires a way to compare two nodes for "semantic equality", i.e., whether swapping one node for the other preserves program semantics.

In data-only operations, this reduces to structural equality: a node produces the same value as another when they perform the same operation and their inputs are equal (notice the recursion here).
Structural comparisons are relatively expensive operations (especially since the graph could be cyclic), so we want to leverage hashing to do as few comparisons as possible.
Therefore, a node's hash value better reflect its semantic structure: having equal hashes is a necessary (but insufficient) condition for two nodes to be equal.
Now, computing a node's hash value becomes an expensive operation.
Fortunately, hash values can be cached once a node's structure has stabilized.
This leads us to a common interface for node [hash consing](https://en.wikipedia.org/wiki/Hash_consing):

$(SMALL_TABLE
    Name        | Type              | Description
    ------------|-------------------|------------
    `hash`      | `hash_t`          | A node's cached hash value. This is what gets returned when `toHash` is called on a generic [Node], so it should be updated (see [updateHash]) whenever a node's semantic structure stabilizes.
    `observers` | `HashSet!(Node*)` | Set of in-neighbors. Through its [OutEdge]s, we can easily find a node's out-neighbors. However, in case a node is substituted (e.g. transformed by a [peephole optimization](https://en.wikipedia.org/wiki/Peephole_optimization)), we need to rewire all of its in-edges. In order to make this fast, each node needs to keep track of its in-neighbor set (this is an optimization, so this member should not influence a node's semantic structure).
    `asNode`    | `ref T -> Node*`  | Method which upcasts (and this always works) a concrete node `ref` to a generic `Node*`.
    `ofNode`    | `Node* -> T*`     | Static method which tries to downcast a generic `Node*` to a pointer to a concrete type, returning `null` when the cast would have resulted in an invalid reference (so this is technically type-safe).
)
+/
package struct Node {
    struct VTable {
     @nogc nothrow:
        bool function(const(Node)*, const(Node)*) opEquals = null;
        hash_t function(const(Node)*) toHash = null;
    }

    struct CommonPrefix {
        immutable(VTable)* vptr;
        HashSet!(Node*) observers;
        hash_t hash;
    }

    CommonPrefix _node;
    alias _node this;

 pragma(inline) @nogc nothrow:
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

    Returns: True if and only if one node can be entirely substituted by the other in a Gyre program.
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
        return this.hash;
    }
}

static assert(
    Node.sizeof == Node.CommonPrefix.sizeof && Node.alignof == Node.CommonPrefix.alignof &&
    is(typeof(Node._node) == Node.CommonPrefix) && Node._node.offsetof == 0,
    "`Node` and `Node.CommonPrefix` need to be binary-interchangeable"
);

private mixin template NodeInheritance() {
    private alias This = typeof(this);

    package Node.CommonPrefix _node = { vptr: &vtbl };
    alias _node this;

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
            return (*self).toHash();
        },
    };

 pragma(inline) @nogc nothrow:
    void updateHash() {
        this._node.hash = this.toHash();
    }

    static assert(
        This._node.offsetof == 0,
        "common node prefix must be at a zero offset for safe polymorphism"
    );

    inout(Node)* asNode() inout pure {
        return cast(inout(Node)*) &this._node;
    }

    static inout(This)* ofNode(inout(Node)* node) pure {
        if (node == null || node.vptr != &vtbl) return null;
        return cast(inout(This)*) node;
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

        bool opEquals(ref const(typeof(this)) rhs) const {
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

    // subtype inherits Node's attributes
    auto test = UnittestNode(1);
    assert(is(typeof(test.observers) == typeof(Node.observers)));

    // it also inheris its methods (e.g. updateHash)
    debug usingCustomHash = false;
    test.updateHash();
    debug assert(usingCustomHash);

    // subtype's opEquals works normally
    debug usingCustomEquals = false;
    auto test2 = UnittestNode(1);
    assert(test == test2);
    auto other = UnittestNode(-1);
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

    // storing a generic node in a subtyped variable does not work
    static assert(!__traits(compiles, other = *node));
}


/++
Gyre's main mechanism for procedural abstraction, the join node.

Join nodes can be used as procedures, basic blocks or synchronization points.


Join nodes are used to define the (external) interface and (internal) contents of procedures and basic blocks.
They interact with the outside world through zero or more parameters.
As a join node begins to execute, control flows into its body, where all of its parameters are made available.
Therefore, a join node behaves like the entry block of a CFG, but with a collection of SSA phis (one for each parameter); so it can be used as an [extended basic block](https://mlir.llvm.org/docs/Rationale/Rationale/#block-arguments-vs-phi-nodes).

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
    invariant (definition.kind == EdgeKind.data);

    /// Control flow edge into the join node's body.
    OutEdge control;
    invariant (control.kind == EdgeKind.control);

    /// Non-empty collection of channels, each containing zero or more of this node's parameters.
    Parameters[] channels;
    alias Parameters = InEdge[]; /// ditto
    invariant {
        assert(channels.length > 0);
        foreach (parameters; channels) {
            foreach (param; parameters) {
                with (EdgeKind) final switch (param.kind) {
                    case data, memory: break;
                    case control, type: assert(false);
                }
            }
        }
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (definition.kind == EdgeKind.data);

    /// Non-empty collection of live continuations, each corresponding to a channel in the join pattern.
    InEdge[] continuations;
    invariant {
        assert(continuations.length > 0);
        foreach (cont; continuations)
            assert(cont.kind == EdgeKind.data);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (control.kind == EdgeKind.control);

    /// A data dependency on some live continuation.
    OutEdge continuation;
    invariant (control.kind == EdgeKind.data);

    /// Arguments to be sent into the continuation and later be used inside a join pattern's body.
    OutEdge[] arguments;
    invariant {
        foreach (arg; arguments) {
            with (EdgeKind) final switch (arg.kind) {
                case data, memory: break;
                case control, type: assert(false);
            }
        }
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (control.kind == EdgeKind.control);

    /// At least two concurrent control flows resulting from this fork.
    OutEdge[] threads;
    invariant {
        assert(threads.length >= 2);
        foreach (thread; threads)
            assert(thread.kind == EdgeKind.control);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (selector.kind == EdgeKind.data);

    /// Incoming control flow edge.
    InEdge control;
    invariant (control.kind == EdgeKind.control);

    /++
    At least two outgoing control flow edges, only one of which will be taken.

    Represented as a sparse mapping to avoid having an exponential number of unused options.
    +/
    HashMap!(size_t, OutEdge) options;
    invariant {
        assert(options.length >= 2);
        foreach (branch; options.byValue)
            assert(branch.kind == EdgeKind.control);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    uint id;

    /// Edges (any kind) which point out from this node.
    OutEdge[] outEdges;

    /// Edges (of any kind) which point into this node.
    InEdge[] inEdges;

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}


/++
Constructs a constant value of a certain type.

See_Also: [UndefinedNode]
+/
struct ConstantNode {
    mixin NodeInheritance;

    // FIXME: temporary assumption that all types are i64
    size_t literal;

    /// The constant's (run-time) value.
    InEdge value;
    invariant (value.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (value.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/// Yields the lowermost bits of its input.
struct TruncationNode {
    mixin NodeInheritance;

    /// Bit pattern being truncated.
    OutEdge input;
    invariant (input.kind == EdgeKind.data);

    /// Lowermost input bits.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/// Yields a wider version of its input, with added bits set to zero.
struct UnsignedExtensionNode {
    mixin NodeInheritance;

    /// Bit pattern being extended.
    OutEdge input;
    invariant (input.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/// Yields a wider version of its input, with added bits equal to the input's sign bit.
struct SignedExtensionNode {
    mixin NodeInheritance;

    /// Bit pattern being extended.
    OutEdge input;
    invariant (input.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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

    /// Resulting value.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

    /// Data dependency used to choose which of the given inputs will be returned.
    OutEdge selector;
    invariant (selector.kind == EdgeKind.data);

    /++
    At least two inputs, one of which will be forwarded as output.

    Represented as a sparse mapping to avoid having an exponential number of unused input edges.
    +/
    HashMap!(size_t, OutEdge) inputs;
    invariant {
        assert(inputs.length >= 2);
        foreach (option; inputs.byValue)
            assert(option.kind == EdgeKind.data);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/// Bitwise `AND` operation.
struct AndNode {
    mixin NodeInheritance;

    /// Resulting bit pattern.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

    /// Set of operands (unordered due to commutativity).
    HashSet!OutEdge operands;
    invariant {
        assert(operands.length >= 2);
        foreach (operand; operands.byKey)
            assert(operand.kind == EdgeKind.data);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/// Bitwise `OR` operation.
struct OrNode {
    mixin NodeInheritance;

    /// Resulting bit pattern.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

    /// Set of operands (unordered due to commutativity).
    HashSet!OutEdge operands;
    invariant {
        assert(operands.length >= 2);
        foreach (operand; operands.byKey)
            assert(operand.kind == EdgeKind.data);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/++
Bitwise `XOR` operation.

Doubles as an unary `NOT` operation when given two operands and one is an all-ones constant.
+/
struct XorNode {
    mixin NodeInheritance;

    /// Resulting bit pattern.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

    /// Set of operands (unordered due to commutativity).
    HashSet!OutEdge operands;
    invariant {
        assert(operands.length >= 2);
        foreach (operand; operands.byKey)
            assert(operand.kind == EdgeKind.data);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (input.kind == EdgeKind.data);

    /// Number of times the shift is performed.
    OutEdge shift;
    invariant (shift.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (input.kind == EdgeKind.data);

    /// Number of times the shift is performed.
    OutEdge shift;
    invariant (shift.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (input.kind == EdgeKind.data);

    /// Number of times the shift is performed.
    OutEdge shift;
    invariant (shift.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (input.kind == EdgeKind.data);

    /// Number of times the shift is performed.
    OutEdge shift;
    invariant (shift.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (result.kind == EdgeKind.data);

    /// Set of operands (unordered due to commutativity).
    HashSet!OutEdge operands;
    invariant {
        assert(operands.length >= 2);
        foreach (operand; operands.byKey)
            assert(operand.kind == EdgeKind.data);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (result.kind == EdgeKind.data);

    /// Set of operands (unordered due to commutativity).
    HashSet!OutEdge operands;
    invariant {
        assert(operands.length >= 2);
        foreach (operand; operands.byKey)
            assert(operand.kind == EdgeKind.data);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// Result of the subtraction.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// Result of the subtraction.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (result.kind == EdgeKind.data);

    /// Set of operands (unordered due to commutativity).
    HashSet!OutEdge operands;
    invariant {
        assert(operands.length >= 2);
        foreach (operand; operands.byKey)
            assert(operand.kind == EdgeKind.data);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (result.kind == EdgeKind.data);

    /// Set of operands (unordered due to commutativity).
    HashSet!OutEdge operands;
    invariant {
        assert(operands.length >= 2);
        foreach (operand; operands.byKey)
            assert(operand.kind == EdgeKind.data);
    }

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (dividend.kind == EdgeKind.data);

    /// Divisor operand.
    OutEdge divisor;
    invariant (divisor.kind == EdgeKind.data);

    /// Resulting quotient.
    InEdge quotient;
    invariant (quotient.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (dividend.kind == EdgeKind.data);

    /// Divisor operand.
    OutEdge divisor;
    invariant (divisor.kind == EdgeKind.data);

    /// Resulting quotient.
    InEdge quotient;
    invariant (quotient.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (dividend.kind == EdgeKind.data);

    /// Divisor operand.
    OutEdge divisor;
    invariant (divisor.kind == EdgeKind.data);

    /// Resulting remainder.
    InEdge remainder;
    invariant (remainder.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
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
    invariant (dividend.kind == EdgeKind.data);

    /// Divisor operand.
    OutEdge divisor;
    invariant (divisor.kind == EdgeKind.data);

    /// Resulting remainder.
    InEdge remainder;
    invariant (remainder.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/// Compares two bit patterns for equality.
struct EqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating whether operands are equal.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/// Compares two bit patterns for inequality.
struct NotEqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating whether operands are different.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/++
Computes whether a (unsigned) two's complement integer is strictly less than another.

There is no equivalent for `>` because it suffices to swap this node's operands.
+/
struct UnsignedLessThanNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating `lhs < rhs`.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/++
Computes whether a (signed) two's complement integer is strictly less than another.

There is no equivalent for `>` because it suffices to swap this node's operands.
+/
struct SignedLessThanNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating `lhs < rhs`.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/++
Computes whether a (unsigned) two's complement integer is greater than or equal to another.

There is no equivalent for `<=` because it suffices to swap this node's operands.
+/
struct UnsignedGreaterOrEqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating `lhs >= rhs`.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}

/++
Computes whether a (signed) two's complement integer is greater than or equal to another.

There is no equivalent for `<=` because it suffices to swap this node's operands.
+/
struct SignedGreaterOrEqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating `lhs >= rhs`.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow: // TODO
    bool opEquals(ref const(typeof(this)) rhs) const {
        return this is rhs;
    }

    hash_t toHash() const {
        return 0;
    }
}


// TODO: type ops

// TODO: mem ops
