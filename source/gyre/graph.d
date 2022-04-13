/++
Graph construction and manipulation procedures.

When expressed in Gyre, programs become sets of nodes and (directed) edges.
It is very important that these graphs have a low memory footprint and enable the efficient implementation of program transformations.
Following the design of [Click's sea of nodes](https://www.oracle.com/technetwork/java/javase/tech/c2-ir95-150110.pdf), our graphs are represented as mutable objects with (possibly cyclic) references to each other.
The current implementation relies on D's automatic memory management, mainly because managed references (i.e. any variable of a class type) are kept stable by the runtime.
The alternative would be to use pointers to struct types, which would basically require us to implement a special-purpose moving GC with either double indirections or updates *everywhere* whenever a node is moved (e.g. when growing a dynamic array, when an AA is rehashed, etc).

Gyre follows SSA form (but not necessarily minimal SSA).
This implies that values must be produced before they are used (def-before-use property) and that values and "variable names" have a one-to-one correspondence (single-assignment property).
In graph-based SSA, every name becomes a reference to the value produced in its defining node; equal references imply equal values and *vice versa*.
Furthermore, the sea of nodes is characterized by a lack of "places": nodes are "floating around" and edges are the only mechanism to define partial orders.
Due to this sea-of-nodes SSA-form, the mere act of expressing a program in the IR yields some optimizations.
These include: Global Value Numbering (GVN) - which combines copy propagation and Common Subexpression Elimination (CSE) - and simple Dead Code Elimination (DCE).
Other optimizations also become straightforward to implement, namely constant folding.
In order to understand why these optimizations become implicit/inherent in the IR, refer to [FIRM (sec. 2.3)](http://beza1e1.tuxen.de/pdfs/braun11wir.pdf).

See_Also:
[Graph]
+/
module gyre.graph;

import gyre.set : Set;


/++
Graph structure representing a Gyre (sub)program.

In this implementation, Gyre nodes are contained within Graph objects, which coordinate the construction and manipulation of their subgraphs.
Every Graph independently operates under the (closed-world) assumption that it owns the entire (sub)program, so **node and edge objects cannot be shared between different Graphs**.

When multiple Graphs are being used to represent a program (e.g. if they were independently generated from separate procedures / modules / compilation units), it is often a good idea to unite them in a single Graph.
This will enable subgraph deduplication and may yield more opportunities to perform certain optimizations.

See_Also:
[Node], [EdgeKind]
+/
struct Graph {
    // TODO
}


/++
Possible edge kinds.

Each Gyre [Node] has one or more "edge slots", which act as directed connectors.
This means that nodes don't reference each other directly.
Instead, they contain slots which connect to the slots of other nodes.
There are different kinds of Edge slots.
These indicate the meaning of each Edge.
Every pair of connecting edge slots must have a matching EdgeKind.
In order to make construction easier, slot types provide static factory members named after the constructed kind (see the examples below).

### Enum members

Name | Description
---- | -----------
`control` | A *control flow* edge going from node A to B indicates that, when control reaches node A and its operation terminates, it may proceed to B. Multiple control flow edges leaving a node indicate either concurrency or a decision point (e.g. an `if`).
`data`    | *Data dependency* edges represent use-def relations. They go from nodes using the value to the one which produced it.
`memory`  | *Memory dependencies* are mostly like discriminated data dependencies. They must be treated differently because, unlike data dependencies which represent immutable values, memory is mutable and thus subject to problems such as scheduling constraints, aliasing and races.

**Please notice the directionality difference between *dependency* and *flow* edges.**

See_Also:
[OutEdge], [InEdge]
+/
enum EdgeKind : ubyte { control, data, memory }

// XXX: this enum is better kept with at most 2 bits of information: we could
// pack it inside edge slots through a taggedPointer, but we're currently not
// doing this because those are incompatible with CTFE (due to pointer casts)
static assert(EdgeKind.min >= 0 && EdgeKind.max < 4, "EdgeKind should have at most 2 useful bits");

private mixin template StaticEdgeFactories(alias SlotType) {
    private import std.conv : to;
    private import std.format : format;
    private import std.traits : EnumMembers;
    static foreach (kind; EnumMembers!EdgeKind) {
        mixin(q{
            static %1$s %2$s() nothrow pure @safe {
                auto e = new %1$s(EdgeKind.%2$s);
                return e;
            }
        }.format(SlotType.stringof, to!string(kind)));
    }
}

/++
An outgoing edge slot.

An OutEdge connects to zero or one [InEdge].

See_Also:
[InEdge]
+/
final class OutEdge {
    InEdge target; /// Either points to another edge slot, or is null.
    const EdgeKind kind; /// This edge's kind, fixed on construction.

    this(EdgeKind kind, InEdge target = null) nothrow pure @safe {
        this.kind = kind;
        this.target = target;
    }

    mixin StaticEdgeFactories!(typeof(this));

    invariant {
        assert(target is null || target.kind == this.kind);
    }
}

///
nothrow pure @safe unittest {
    // data edges are directed from uses to defs
    auto def = InEdge.data;
    auto use1 = OutEdge.data;
    auto use2 = OutEdge.data;
    use1.target = def;
    use2.target = def;
    assert(use1.target is def);
    assert(use2.target is def);
}

/++
An incoming edge slot.

InEdge slots can receive zero or more [OutEdge]s.

See_Also:
[Node]
+/
final class InEdge {
    Node owner; /// Points back to the [Node] which owns this edge.
    const EdgeKind kind; /// This edge's kind, fixed on construction.

    this(EdgeKind kind, Node owner = null) nothrow pure @safe {
        this.kind = kind;
        this.owner = owner;
    }

    mixin StaticEdgeFactories!(typeof(this));
}

///
nothrow pure @safe unittest {
    // in this example, control flows out from A and into B
    auto node = new Node();
    auto A = OutEdge.control;
    auto B = InEdge.control;
    A.target = B;
    B.owner = node;
    assert(A.target.owner is node);
}


/++
Represents a Gyre node.

In order to achieve efficient def-use traversal and peephole transformations, every Node must keep track of its set of in-neighbors (i.e. those which have [OutEdge]s to one of its [InEdge] slots).
Meanwhile, the set of out-neighbors is implicitly defined by a Node's [OutEdge] slots.

See_Also:
[Hash sets](./set.html)
+/
final class Node {
    Set!(Node) observers;
    // TODO
    // override bool opEquals(Object rhs) const;
    // override size_t toHash() const nothrow @trusted;
}

struct JoinNode {
    auto definition = InEdge.data;
    auto control = OutEdge.control;
    private alias Parameters = InEdge[];
    Parameters[] pattern;
}

struct InstantiateNode {
    auto definition = OutEdge.data;
    InEdge[] continuations;
}

struct ContinueNode {
    auto control = InEdge.control;
    auto continuation = OutEdge.data;
    OutEdge[] values;
}

struct IfNode {
    auto control = InEdge.control;
    auto selector = OutEdge.data;
    auto thenBranch = OutEdge.control;
    auto elseBranch = OutEdge.control;
}

struct ConcurrentNode {
    auto control = InEdge.control;
    bool explicit = false;
    auto leftFork = OutEdge.control;
    auto rightFork = OutEdge.control;
}

struct MacroNode {
    OutEdge[] dataUses;
    InEdge[]  dataDefs;
    InEdge[]  controlIncoming;
    OutEdge[] controlOutgoing;
    auto minThreads = OutEdge.data;
    auto maxThreads = OutEdge.data;
}

// TODO: prim ops { literals, arithmetic, mem ops }
