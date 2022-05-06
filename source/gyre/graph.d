/++
"Low-level" program construction and transformation procedures.

When expressed in Gyre, programs become sets of nodes and edges: a directed graph.
It is very important that these graphs have a low memory footprint and enable the efficient implementation of program transformations.
Following the design of Click's "sea of nodes", our graphs are represented as mutable objects with (possibly cyclic) references to each other.
In order to understand the benefits of such an IR, refer to [libFIRM (sec. 2.3)](http://beza1e1.tuxen.de/pdfs/braun11wir.pdf).

See_Also: [Graph](#Graph)
+/
module gyre.graph;

import std.bitmanip : taggedPointer;

import eris.core : hash_t;
import eris.hash_table;
import eris.util : HashablePointer;


/++
Possible edge kinds.

Each Gyre node has one or more "edge slots", which act as directed connectors.
This means that nodes don't reference each other directly.
Instead, they contain slots which connect to the slots of other nodes.
There are different kinds of edge slots, which indicate their meaning.
Every pair of connecting edge slots must have a matching kind.
Slot types provide factory members named after each EdgeKind (see examples below).

Enum_Members:
Name | Description
---- | -----------
`control` | A control flow edge going from node A to B indicates that, after control reaches node A, it may then proceed to B. Multiple control flow edges leaving a node indicate either concurrency or a decision point (e.g. an `if`).
`data`    | Data dependency edges represent use-def relations. They go from nodes using the value to the one which produced it.
`memory`  | Memory dependencies are mostly like discriminated data dependencies. They must be treated differently because, unlike data dependencies which represent immutable values, memory is mutable and thus subject to problems such as scheduling constraints, aliasing and races.

Please note the directionality difference between "dependency" and "flow" edges.

See_Also: [OutEdge](#OutEdge), [InEdge](#InEdge)
+/
enum EdgeKind : ubyte { control, data, memory, }

// this enum is better kept with at most 2 bits of information for pointer tagging
static assert(EdgeKind.min >= 0 && EdgeKind.max < 4, "EdgeKind should have at most 2 useful bits");

private mixin template StaticEdgeFactories() {
    private import std.traits : EnumMembers;
    static foreach (kind; EnumMembers!EdgeKind) {
        mixin(
            "static typeof(this) " ~ __traits(identifier, EnumMembers!EdgeKind[kind]) ~ "() @nogc nothrow pure @safe {
                return typeof(this)(EdgeKind." ~ __traits(identifier, EnumMembers!EdgeKind[kind]) ~ ");
            }"
        );
    }
}

/++
An outgoing edge slot.

Connects to either zero or exactly one [InEdge](#InEdge).
+/
struct OutEdge {
    // XXX: taggedPointer's generated accessors are not scope, so we need to make
    // @trusted custom accessors, see https://issues.dlang.org/show_bug.cgi?id=23095
    mixin(taggedPointer!(
        InEdge*, "_target",
        EdgeKind, "_kind", 2
    ));

 @nogc nothrow pure @safe:
    /// Either points to another edge slot, or is null.
    @property inout(InEdge)* target() inout return scope @trusted {
        return this._target;
    }

    /// ditto
    @property void target(return scope InEdge* target) scope @trusted {
        this._target = target;
    }

    /// This edge's kind, fixed on construction.
    @property EdgeKind kind() const scope @trusted {
        return this._kind;
    }

    /// ditto
    @property void kind(EdgeKind kind) scope @trusted {
        this._kind = kind;
    }

    @disable this();

    ///
    this(EdgeKind kind, return scope InEdge* target = null) {
        this.kind = kind;
        this.target = target;
        assert(
            target == null || target.kind == this.kind,
            "connecting edge slots must have matching kinds."
        );
    }

    mixin StaticEdgeFactories;
}

///
@nogc nothrow pure unittest {
    auto def = InEdge.data;
    auto use1 = OutEdge.data;
    auto use2 = OutEdge.data;
    // data edges are directed from uses to defs
    use1.target = &def;
    use2.target = &def;
    assert(use1 == use2);
}

/++
An incoming edge slot.

Can receive any number of [OutEdge](#OutEdge)s.

See_Also: [INode](#INode)
+/
struct InEdge {
    // XXX: taggedPointer's generated accessors are not scope, so we need to make
    // @trusted custom accessors, see https://issues.dlang.org/show_bug.cgi?id=23095
    mixin(taggedPointer!(
        INode*, "_owner",
        EdgeKind, "_kind", 2
    ));

 @nogc nothrow pure @safe:
    /// Points back to the node which owns this edge.
    @property inout(INode)* owner() inout return scope @trusted {
        return this._owner;
    }

    /// ditto
    @property void owner(return scope INode* owner) scope @trusted {
        this._owner = owner;
    }

    /// This edge's kind, fixed on construction.
    @property EdgeKind kind() const scope @trusted {
        return this._kind;
    }

    /// ditto
    @property void kind(EdgeKind kind) scope @trusted {
        this._kind = kind;
    }

    @disable this();

    ///
    this(EdgeKind kind, return scope INode* owner = null) {
        this.kind = kind;
        this.owner = owner;
    }

    mixin StaticEdgeFactories;
}

///
@nogc nothrow pure unittest {
    auto A = OutEdge.control;
    auto B = InEdge.control;
    // in this example, control flows out from A and into B
    A.target = &B;
    assert(A.target.owner is B.owner);
}


/++
Common interface shared by all Gyre nodes; safely used only as a referece type.

Other things all nodes have in common:
Name | Description
---- | -----------
`asNode` | Method which upcasts (and this always works) a concrete node `ref` to a generic `INode*`.
`ofNode` | Static method which tries to downcast a generic `INode*` to a pointer of a concrete type, returning `null` when the cast would not be valid.
+/
struct INode {
 pragma(inline) @nogc nothrow @safe:
    private immutable(VTable)* vptr = &vtbl;

    /++
    This node's cached structural hash; to be updated whenever this node's structure stabilizes.

    NOTE: This is the value which gets returned when `toHash` is called on a node (e.g. by hash tables).
        It is cached for performance reasons, as computing the structural hash of a node within an arbitrary graph can be costly.

    See_Also: [updateHash](#INode.updateHash)
    +/
    @property hash_t hash() const scope pure { return this._hash; }
    private hash_t _hash;

    /++
    Set of in-neighbors which have edges pointing to this node; to be updated along with graph structure.

    Through its [OutEdge](#OutEdge) slots, one can easily reach a node's out-neighbors.
    In order to achieve efficient graph traversals and program transformations, every node must also keep track of its in-neighbors set (i.e. those which have [OutEdge](#OutEdge)s to one of its [InEdge](#InEdge) slots).
    Does not change this specific node's structure.

    See_Also: [Hash sets](./eris.hash_table.html#UnsafeHashSet)
    +/
    HashSet!(INode*) observers;

    private static immutable(VTable) vtbl = VTable.init;
    private immutable struct VTable {
     @nogc nothrow @safe:
        hash_t function(scope const(INode)*) computeHash = null;
        bool function(scope const(INode)*, scope const(INode)*) opEquals = null;
    }

    size_t toHash() const scope pure {
        return this.hash;
    }

    /++
    Recomputes this node's structural hash and stores it in its `hash` field.

    The new hash is obtained as the return value of the `computeHash` virtual method.
    +/
    void updateHash() scope
    @trusted // because we're taking the address of a scope input
    {
        this._hash = this.vptr.computeHash(&this);
    }

    /++
    Compares two nodes for equality. Must be consistent with hash computation.

    NOTE: In an arbitrary graph, this can be a costly operation, so early exits are checked before any virtual call.
        Thus, custom overrides will only be called on non-aliased same-type nodes with matching hashes.

    Returns: True if and only if one node can be entirely substituted by the other in a Gyre program.
    +/
    bool opEquals(scope ref const(INode) other) const scope
    @trusted // because we're taking the address of scope inputs
    {
        const(INode)* lhs = &this, rhs = &other;
        if (lhs == rhs) return true;
        if (lhs.vptr != rhs.vptr) return false;
        if (lhs.hash != rhs.hash) return false;
        return lhs.vptr.opEquals(lhs, rhs);
    }
}

// hand-made struct inheritance
private mixin template NodeInheritance() {
    private alias This = typeof(this);

    INode _node = { vptr: &vtbl };
    alias _node this;
    static assert(
        This._node.offsetof == 0,
        "common INode prefix must be at a zero offset for safe struct inheritance"
    );

    public pragma(inline) @nogc nothrow pure @safe {
        inout(INode)* asNode() inout return {
            return &this._node;
        }

        static inout(This)* ofNode(return scope inout(INode)* node)
        @trusted // cast is safe because of vptr check + common prefix
        {
            if (node == null || node.vptr != &vtbl) return null;
            return cast(inout(This)*)(node);
        }

        size_t toHash() const scope {
            return this.hash;
        }
    }

    private static immutable(INode.VTable) vtbl = {
        computeHash: (scope const(INode)* node) @nogc nothrow @safe {
            auto self = This.ofNode(node);
            assert(self != null);
            return (*self).computeHash();
        },
        opEquals: (scope const(INode)* lhs, scope const(INode)* rhs) @nogc nothrow @safe {
            auto self = This.ofNode(lhs), other = This.ofNode(rhs);
            assert(self != null && other != null);
            return *self == *other;
        },
    };
}

version (unittest) private {
    static bool usingCustomHash;
    static bool usingCustomEquals;

    struct UnittestNode {
        mixin NodeInheritance;
        int value;

     @nogc nothrow @safe:
        this(int value) scope { this.value = value; }

        hash_t computeHash() const scope {
            debug usingCustomHash = true;
            return this.value;
        }

        bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
            debug usingCustomEquals = true;
            return this.value == rhs.value;
        }
    }
}

@nogc nothrow @safe unittest {
    // subtype inherits INode's attributes
    auto test = UnittestNode(1);
    assert(is(typeof(test.observers) == typeof(INode.observers)));

    // it also inheris its methods (e.g. updateHash)
    debug usingCustomHash = false;
    test.updateHash();
    debug assert(usingCustomHash);

    // subtype's opEquals works normally
    debug usingCustomEquals = false;
    auto test2 = test; // hash is up to date
    assert(test == test2);
    auto other = UnittestNode(-1);
    other.updateHash();
    assert(test != other);
    debug assert(usingCustomEquals);

    HashablePointer!INode node = test.asNode;
    HashablePointer!INode node2 = test2.asNode;

    // they also dispatch correctly when using a polymorphic node
    HashSet!(HashablePointer!INode) polymorphic;
    polymorphic.add(node); polymorphic.add(node2);
    assert(polymorphic.length == 1); // but node and node2 are equal
    assert(*node != *other.asNode); // these are still different, tho

    // storing a generic node in a subtyped variable does not work
    static assert(!__traits(compiles, other = *node));
}

/++
Gyre's main mechanism for procedural abstraction, the join node.

Join nodes are used to define the (external) interface and (internal) contents of procedures and basic blocks.
They interact with the outside world through zero or more parameters.
As a join node begins to execute, control flows into its body, where all of its parameters are made available.
Therefore, a join node behaves like the entry block of a [CFG](https://en.wikipedia.org/wiki/Control-flow_graph) (i.e. a function header), but combined with a set of [SSA](https://en.wikipedia.org/wiki/Static_single_assignment_form) phi instructions (one for each parameter).

Since join nodes define subprocedures, one may want to know where such a definitions begins and ends.
A join node's scope begins with all of its parameters and control flow edges.
Furthermore, whenever another node is connected to part of a join node's scope, it also becomes part of that scope.
In other words: a join node's scope is implicitly defined by the set of nodes (a) which are transitively reachable by control flow in its body or (b) which have a transitive dependency on any one of its parameters.
This idea originates from [Thorin](https://compilers.cs.uni-saarland.de/papers/lkh15_cgo.pdf)'s implicit scopes.
Two scopes cannot intersect unless one is entirely contained within the other (i.e. they are "well-structured").

The only way in which a Gyre subgraph may refer to a join node without becoming part of its scope is through an indirection: the join node's "definition" edge.
Through its definition, external code may instantiate and invoke a join node.
Since a join node's body may use any of its parameters, it can only begin executing when they were all provided by the calling code.
Furthermore, parameters are divided into (one or more) groups, called channels.
All parameters within a channel need to be provided at the same time, but each channel can receive its inputs from a different source in the calling code.
Thus, join nodes can also be used to merge concurrent control flows, which should not be surprising to those familiar with the join calculus: join nodes correspond to linear [join patterns](https://en.wikipedia.org/wiki/Join-pattern).

See_Also: [InstantiationNode](#InstantiationNode)
+/
struct JoinNode {
    mixin NodeInheritance;

    /// This join node's definition (a `data` slot), used to instantiate and invoke it.
    InEdge definition;
    invariant (definition.kind == EdgeKind.data);

    /// Control flow edge into the join node's body.
    OutEdge body;
    invariant (body.kind == EdgeKind.control);

    /// Non-empty collection of channels, each containing zero or more of this node's parameters.
    Parameters[] channels;
    alias Parameters = InEdge[]; /// ditto
    invariant {
        assert(channels.length > 0);
        foreach (ref parameters; channels) {
            foreach (ref param; parameters)
                assert(param.kind != EdgeKind.control);
        }
    }

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Instantiates a join node.

Join nodes correspond to static ("dead") subprograms.
In order to actually use a join node, one must first create a "live" instance of it.
The result of such an instantiation is a non-empty collection of continuations, one for each channel in the join pattern.
Using a continuation requires one to provide its parameters and jump into it.

See_Also: [JumpNode](#JumpNode)
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
        foreach (ref cont; continuations)
            assert(cont.kind == EdgeKind.data);
    }

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Yields control flow to another part of the program through a "jump with arguments".

Jump nodes yield control to a target "place" in the program, while also carrying information.
They can be seen as a (a) `goto`, (b) function application, (c) return statement or (d) synchronous message being sent to another process.

Gyre jumps differ from classic function calls because there is no implicit expectation of a "return"; this is [CPS](https://en.wikipedia.org/wiki/Continuation-passing_style).
If a caller expects return values (or even to take control back at all), it needs to set up a "return continuation" and pass that in as an argument as well, hoping that the subprocedure it is calling will (1) eventually receive messages on all of its other channels, triggering the join pattern; (2) execute the join's body to completion; and (3) have that body jump into the provided continuation as a way to come back (perhaps with a return value) to the calling code.

Jumps synchronize with each other when a join pattern triggers.
Imagine a set of concurrent processes, each carrying a continuation corresponding to a different channel of some join pattern; once they've all jumped into their respective continuations, the join pattern triggers and its body executes.
Then, every event in those processes which happens before the jump, also happens before all events in the triggered join pattern body.

See_Also: [JoinNode](#JoinNode)
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
        foreach (ref arg; arguments)
            assert(arg.kind != EdgeKind.control);
    }

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}


/++
Directs control flow to exactly one of multiple possible edges.

The choice of which branch to take is controled by a data dependency interpreted as an unsigned integer indexing an array of options.
If the selector's value does not match the index of any option, program behavior is undefined.
A Gyre compiler may assume that this never happens and either issue warnings / errors or optimize accordingly (e.g. by assuming that the selector's value is one of the valid indexes, if control flow reaches this branch node).

See_Also: [MuxNode](#MuxNode)
+/
struct BranchNode {
    mixin NodeInheritance;

    /// Incoming control flow edge.
    InEdge control;
    invariant (control.kind == EdgeKind.control);

    /// Data dependency used to choose the taken branch.
    OutEdge selector;
    invariant (selector.kind == EdgeKind.data);

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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Forks a single control flow into multiple concurrent ones.

Data-only Gyre graphs are always implicitly concurrent: there is no ordering relation between data-only nodes other than the one implied by their def-use chains.
When a node also requires control flow, expressing the fact that it is concurrent with respect to another (i.e. one is not necessarily ordered before the other) would be impossible in a classic CFG.
Fork nodes work around this by signaling explicit concurrency in a Gyre graph.

Fork nodes tell the compiler "the following subprograms have no ordering constraints between each other".
Therefore, it is an error for any of the resulting control flows to make direct use of a value produced in another one of its sibling 'threads'.
Still, every event which happens before a fork also happens before the events of its resulting control flows.
Merging concurrent flows back into one can be done at a [join node](#JoinNode).

See_Also: [JoinNode](#JoinNode), [JumpNode](#JumpNode)
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
        foreach (ref thread; threads)
            assert(thread.kind == EdgeKind.control);
    }

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
An operation which chooses one of its inputs to forward as a result.

In a mux node, the choice of which input to forward is controled by an unsigned integer, as if it was indexing an array of inputs.
If the selector's value does not match the index of any input, the result is a poison value.

Meta:
Starting at this one, most (but not all) other primitives are data-only, representing purely combinatorial operations.

Poison:
Each data-only operation has fixed-type inputs and outputs, but may have some conditions imposed on its inputs in order to produce a sane value.
When the result of an operation isn't well-defined (e.g. integer division by zero), it produces a "poison".
Poison values originate from [LLVM](https://llvm.org/docs/LangRef.html#poison-values) and indicate invalid program behavior.
Furthermore, these values are poisonous because any operation with poison operands also produces poison (mux nodes are the exception, since poisoned inputs may not be chosen depending on the selector's value).

This is not unlike C's infamous "Undefined Behavior", because a Gyre compiler may (while respecting program semantics) assume that poison values are never used, which in turn may help with some optimizations (e.g. [loop-invariant code motion](https://en.wikipedia.org/wiki/Loop-invariant_code_motion)).
Another option is to issue warnings or errors when such erroneous behavior is detected.
Therefore, this library's default is to ignore any detected undefined behavior / poison value usage.

See_Also: [BranchNode](#BranchNode)
+/
struct MuxNode {
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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Constructs a constant / literal value of a certain type.

See_Also: [UndefinedNode](#UndefinedNode)
+/
struct ConstantNode {
    mixin NodeInheritance;

    /// The constant's value.
    InEdge value;
    invariant (value.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Constructs a ["don't care"](https://en.wikipedia.org/wiki/Don%27t-care_term) value of a certain type.

The compiler is free to make this node produce any value, as long as it is consistently seen by all of its uses.
This notion of an "undefined value" originates from [Click's](https://scholarship.rice.edu/bitstream/handle/1911/96451/TR95-252.pdf) formalization of monotone analyses.

Rationale:
Undefined values cannot be produced by constant nodes, because the latter are subject to structural sharing, whereas different undefined nodes can resolve to different values and therefore have their own "identity".
+/
struct UndefinedNode {
    mixin NodeInheritance;

    /// The resulting value.
    InEdge value;
    invariant (value.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Bitwise NOT operation.
struct NotNode {
    mixin NodeInheritance;

    /// Bit pattern being negated.
    OutEdge input;
    invariant (input.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Bitwise AND operation.
struct AndNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Bitwise OR operation.
struct OrNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Bitwise XOR operation.
struct XorNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Bitwise left-shift operation; bits shifted in are all zero.

The shift amount must be no greater than the number of input bits, otherwise the result is a [poison](#MuxNode) value.
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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Logical right-shift operation; bits shifted in are all zero.

The shift amount must be no greater than the number of input bits, otherwise the result is a [poison](#MuxNode) value.

See_Also: [SignedRightShiftNode](#SignedRightShiftNode)
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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Arithmetic right-shift operation; bits shifted in are equal to the input's most significant bit.

The shift amount must be no greater than the number of input bits, otherwise the result is a [poison](#MuxNode) value.

See_Also: [UnsignedRightShiftNode](#UnsignedRightShiftNode)
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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Two's complement addition operation (works for both signed and unsigned integers).
struct AdditionNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// Result of the addition.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Two's complement subtraction operation (works for both signed and unsigned integers).
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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Two's complement multiplication operation.

Since this only produces the lower half of a full multiplication, it is the same for both signed and unsigned integers.
+/
struct MultiplicationNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// Result of the multiplication.
    InEdge result;
    invariant (result.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Two's complement division operation for unsigned operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](#MuxNode) value.

See_Also: [SignedDivisionNode](#SignedDivisionNode)
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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Two's complement division operation for signed operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](#MuxNode) value.
Furthermore, dividing the "most negative" value representable (i.e. `-1 * 2^(N-1)` for N-bit integers) by `-1` also results in poison.

See_Also: [UnsignedDivisionNode](#UnsignedDivisionNode)
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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Two's complement remainder operation for unsigned operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](#MuxNode) value.

See_Also: [SignedRemainderNode](#SignedRemainderNode)
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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/++
Two's complement remainder operation for signed operands, rounds towards zero.

The divisor must not be zero, otherwise the result is a [poison](#MuxNode) value.
Furthermore, dividing the "most negative" value representable (i.e. `-1 * 2^(N-1)` for N-bit integers) by `-1` also results in poison.

See_Also: [UnsignedRemainderNode](#UnsignedRemainderNode)
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

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
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

    /// A single resulting bit indicating whether the operands are equal.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Computes whether a two's complement integer is strictly less than another (both unsigned).
struct UnsignedLessThanNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating whether `lhs < rhs`.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Computes whether a two's complement integer is strictly less than another (both signed).
struct SignedLessThanNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating whether `lhs < rhs`.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Computes whether a two's complement integer is greater or equal than another (both unsigned).
struct UnsignedGreaterOrEqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating whether `lhs >= rhs`.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Computes whether a two's complement integer is greater or equal than another (both signed).
struct SignedGreaterOrEqualNode {
    mixin NodeInheritance;

    /// Left-hand-side operand.
    OutEdge lhs;
    invariant (lhs.kind == EdgeKind.data);

    /// Right-hand-side operand.
    OutEdge rhs;
    invariant (rhs.kind == EdgeKind.data);

    /// A single resulting bit indicating whether `lhs >= rhs`.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Truncation operation: given a bit pattern, yields only the lower bits.
struct TruncationNode {
    mixin NodeInheritance;

    /// Bit pattern being truncated.
    OutEdge input;
    invariant (input.kind == EdgeKind.data);

    /// Lowermost input bits.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Extension operation: returns a wider version of its input, with added bits set to zero.
struct UnsignedExtensionNode {
    mixin NodeInheritance;

    /// Bit pattern being extended.
    OutEdge input;
    invariant (input.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

/// Extension operation: returns a wider version of its input, with added bits equal to the input's sign bit.
struct SignedExtensionNode {
    mixin NodeInheritance;

    /// Bit pattern being extended.
    OutEdge input;
    invariant (input.kind == EdgeKind.data);

    /// Resulting bit pattern.
    InEdge output;
    invariant (output.kind == EdgeKind.data);

 @nogc nothrow @safe: // TODO:
    hash_t computeHash() const scope {
        return 0;
    }

    bool opEquals()(scope auto ref const(typeof(this)) rhs) const scope {
        return this is rhs;
    }
}

// TODO: mem ops, macro nodes and type ops

/++
Graph structure storing a Gyre (sub)program.

Every Graph independently operates under the assumption that it fully owns the entire (sub)program, so node and edge objects cannot be shared between different graphs.
When multiple Gyre graphs are being used to represent a program (e.g. if each one was independently generated from a separate procedure / module / compilation unit), it is often a good idea to unite them in a single Graph.
This may enable subgraph deduplication and yield more opportunities to perform certain optimizations (e.g. [CSE](https://en.wikipedia.org/wiki/Common_subexpression_elimination)).

See_Also: [EdgeKind](#EdgeKind), [INode](#INode)
+/
struct Graph { // TODO
    HashSet!(HashablePointer!INode) nodes;
}
