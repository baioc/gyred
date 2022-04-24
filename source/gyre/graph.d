/++
Program construction and transformation procedures.

When expressed in Gyre, programs become sets of nodes and edges: a directed graph.
It is very important that these graphs have a low memory footprint and enable the efficient implementation of program transformations.
Following the design of Click's "sea of nodes", our graphs are represented as mutable objects with (possibly cyclic) references to each other.
In order to understand the benefits of such an IR, refer to [libFIRM (sec. 2.3)](http://beza1e1.tuxen.de/pdfs/braun11wir.pdf).

See_Also: [Graph](#Graph)
+/
module gyre.graph;

import std.bitmanip : taggedPointer;

import eris.hash_table;


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
    mixin(taggedPointer!(
        InEdge*, "target", /// Either points to another edge slot, or is null.
        EdgeKind, "kind", 2 /// This edge's kind, fixed on construction.
    ));

 @nogc nothrow pure @safe:
    @disable this();

    ///
    this(EdgeKind kind, InEdge* target = null) {
        this.kind = kind;
        this.target = target;
        assert(
            target is null || target.kind == this.kind,
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
    assert(use1.target == use2.target);
    assert(use1 == use2);
}

/++
An incoming edge slot.

Can receive any number of [OutEdge](#OutEdge)s.

See_Also: [Node](#Node)
+/
struct InEdge {
    mixin(taggedPointer!(
        Node*, "owner", /// Points back to the node which owns this edge.
        EdgeKind, "kind", 2 /// This edge's kind, fixed on construction.
    ));

 @nogc nothrow pure @safe:
    @disable this();

    ///
    this(EdgeKind kind, Node* owner = null) {
        this.kind = kind;
        this.owner = owner;
    }

    mixin StaticEdgeFactories;
}

///
@nogc nothrow pure unittest {
    Node node;
    auto A = OutEdge.control;
    auto B = InEdge.control;
    // in this example, control flows out from A and into B
    A.target = &B;
    B.owner = &node;
    assert(A.target.owner == &node);
}


/++
Common interface shared by all Gyre nodes.

Through its [OutEdge](#OutEdge) slots, one can easily reach a node's out-neighbors.
In order to achieve efficient def-use traversal and peephole transformations, every Node must also keep track of its in-neighbors set (i.e. those which have [OutEdge](#OutEdge)s to one of its [InEdge](#InEdge) slots).

See_Also: [Hash sets](./eris.hash_table.html#HashSet)
+/
struct Node {
    private immutable(VTable)* vptr = &vtbl;

    HashSet!(Node*) observers; /// Set of in-neighbors which have edges pointing to this node.

    private static immutable(VTable) vtbl = VTable.init;
    immutable struct VTable {
     nothrow:
        size_t function(ref const(Node)) toHash = (ref self) => 0;
        bool function(ref const(Node), ref const(Node)) opEquals = (ref lhs, ref rhs) => lhs is rhs;
    }

 pragma(inline) nothrow:
    size_t toHash() const {
        return this.vptr.toHash(this);
    }

    bool opEquals()(auto ref const(Node) rhs) const {
        return this.vptr.opEquals(this, rhs);
    }
}

// hand-made struct inheritance
private mixin template NodeInheritance(Node.VTable vtable = Node.VTable.init) {
    private static immutable(Node.VTable) vtbl = vtable;

    public Node _node = { vptr: &vtbl };
    public alias _node this;

    public pragma(inline) nothrow {
        @property ref inout(Node) asNode() inout @trusted {
            static assert(
                typeof(this)._node.offsetof == 0,
                "common Node prefix must be at a zero offset for safe struct inheritance"
            );
            return cast(inout(Node))(this);
        }

        size_t toHash() const {
            return this.vptr.toHash(this.asNode);
        }

        bool opEquals()(auto ref const(typeof(this)) rhs) const {
            return this.vptr.opEquals(this.asNode, rhs.asNode);
        }
    }
}

///
nothrow unittest {
    static bool usingCustomHash;
    static bool usingCustomEquals;
    struct TestNode {
        mixin NodeInheritance!(vtable);
        enum Node.VTable vtable = {
            toHash: (ref self) {
                debug usingCustomHash = true;
                return 0;
            },
            opEquals: (ref self, ref rhs) {
                debug usingCustomEquals = true;
                return self is rhs;
            },
        };
    }

    // subtype inherits Node's members
    TestNode test;
    assert(is(typeof(test.observers) == typeof(Node.observers)));

    // subtype's toHash and opEquals work normally
    debug usingCustomHash = usingCustomEquals = false;
    bool[TestNode] monomorphic;
    monomorphic[test] = true;
    assert(test == test);
    debug assert(usingCustomHash && usingCustomEquals);

    // they also dispatch correctly when using a polymorphic Node
    debug usingCustomHash = usingCustomEquals = false;
    auto node = test.asNode;
    assert(node == node);
    debug assert(usingCustomEquals);
    bool[Node] polymorphic;
    polymorphic[node] = true;
    debug assert(usingCustomHash);
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
This idea originates from [Thorin](https://compilers.cs.uni-saarland.de/papers/lkh15_cgo.pdf).

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
}

/++
Instantiates a join node.

Join nodes correspond to static ("dead") program code.
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
}

/++
Yields control flow to another part of the program through a "jump with arguments".

Jump nodes yield control to a target "place" in the program, while also carrying information.
They can be seen as a (a) `goto`, (b) function application, (c) return statement or (d) synchronous message being sent to another process.

Gyre jumps differ from classic function calls because there is no implicit expectation of a "return"; this is [CPS](https://en.wikipedia.org/wiki/Continuation-passing_style).
If a caller expects return values (or even to take control back at all), it needs to set up a "return continuation" and pass that in as an argument as well, hoping that the subprocedure it is calling will (1) eventually receive messages on all of its other channels, triggering the join pattern; (2) execute the join's body to completion; and (3) have that body jump into the provided continuation as a way to come back (perhaps with a return value) to the calling code.

Jumps synchronize with each other when a join pattern triggers.
Imagine a set of concurrent processes, each carrying a continuation corresponding to a different channel of some join pattern; once they've all jumped into their respective continuations, the join pattern triggers and its body executes.
Therefore, every event in those processes which is ordered before the jump, also happens before all events in the triggered join pattern body.

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
}

struct BranchNode {
    mixin NodeInheritance;

    InEdge control;
    OutEdge selector;
    OutEdge[] options;

    invariant {
        with (EdgeKind) {
            assert(this.control.kind == control);
            assert(selector.kind == data);
            foreach (ref branch; options)
                assert(branch.kind == control);
        }
    }
}

struct ForkNode {
    mixin NodeInheritance;

    OutEdge minParallelism;
    OutEdge maxParallelism;
    InEdge control;
    OutEdge[] threads;

    invariant {
        with (EdgeKind) {
            assert(minParallelism.kind == data);
            assert(maxParallelism.kind == data);
            assert(this.control.kind == control);
            foreach (ref thread; threads)
                assert(thread.kind == control);
        }
    }
}

// TODO: other prim ops { literals, arithmetic, mem ops }

struct MacroNode {
    mixin NodeInheritance;

    OutEdge[] dataUses;
    InEdge[] dataDefs;
    InEdge[] controlIncoming;
    OutEdge[] controlOutgoing;
    OutEdge minThreads;
    OutEdge maxThreads;
}


/++
Graph structure storing a Gyre (sub)program.

Every Graph independently operates under the assumption that it fully owns the entire (sub)program, so node and edge objects cannot be shared between different graphs.
When multiple Gyre graphs are being used to represent a program (e.g. if each one was independently generated from a separate procedure / module / compilation unit), it is often a good idea to unite them in a single Graph.
This may enable subgraph deduplication and yield more opportunities to perform certain optimizations (e.g. [CSE](https://en.wikipedia.org/wiki/Common_subexpression_elimination)).

See_Also: [EdgeKind](#EdgeKind), [Node](#Node)
+/
struct Graph { // TODO
    /// Storage space for all (including unused) nodes within this graph.
    Node[] arena;
}
