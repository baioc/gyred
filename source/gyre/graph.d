/++
Graph construction and manipulation procedures.

When expressed in Gyre, programs become sets of nodes and (directed) edges.
It is very important that these graphs have a low memory footprint and enable the efficient implementation of program transformations.
Following the design of [Click's sea of nodes](https://www.oracle.com/technetwork/java/javase/tech/c2-ir95-150110.pdf), our graphs are represented as mutable objects with (possibly cyclic) references to each other.

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

import std.bitmanip : taggedPointer;
import std.conv : to;
import std.format : format;
import std.traits : EnumMembers;

import set;


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

private mixin template StaticEdgeBuilders(string slotType) {
    static foreach (kind; EnumMembers!EdgeKind) {
        mixin(q{
            static %1$s %2$s() @nogc nothrow pure @safe {
                %1$s e;
                e.kind = EdgeKind.%2$s;
                return e;
            }
        }.format(slotType, to!string(kind)));
    }
}

/++
An outgoing edge slot.

An OutEdge connects to zero or one [InEdge].
It can be used as a pointer to its target edge slot.

See_Also:
[InEdge]
+/
struct OutEdge {
    mixin(taggedPointer!(
        InEdge*, "target", /// Either points to another edge slot, or is null.
        EdgeKind, "kind", 2 /// This edge's kind, usually fixed on construction.
    ));

    mixin StaticEdgeBuilders!(this.stringof);

    ref inout(InEdge) opUnary(string op)() inout @nogc nothrow pure if (op == "*")
    in {
        assert(this.target != null);
    } do {
        return *this.target;
    }

    void opAssign(return InEdge* rhs) @nogc nothrow pure @safe
    out {
        assert(rhs == null || rhs.kind == this.kind);
    } do {
        this.target = rhs;
    }
}

///
@nogc nothrow pure unittest {
    // data edges are directed from uses to defs
    auto use = OutEdge.data;
    auto def = InEdge.data;
    assert(use.target == null); // initially, target is null

    // assigning a target adress will set the target field
    use = &def;
    assert(use.target == &def);

    // dereferencing an OutEdge will yield a ref to its target
    assert(*use == def);
}

/++
An incoming edge slot.

InEdge slots can receive zero or more [OutEdge]s.
May be used as a pointer to its owner [Node].

See_Also:
[Node]
+/
struct InEdge {
    mixin(taggedPointer!(
        Node*, "owner", /// Points back to the [Node] which owns this edge.
        EdgeKind, "kind", 2 /// This edge's kind, usually fixed on construction.
    ));

    mixin StaticEdgeBuilders!(this.stringof);

    ref inout(Node) opUnary(string op)() inout @nogc nothrow pure if (op == "*")
    in {
        assert(this.owner != null);
    } do {
        return *this.owner;
    }

    void opAssign(return Node* rhs) @nogc nothrow pure @safe {
        this.owner = rhs;
    }
}

///
@nogc nothrow pure unittest {
    // in this example, control flows out from A and into B
    auto A = OutEdge.control;
    auto B = InEdge.control;
    A.target = &B;
    assert(B.owner == null); // initially, node is null

    // dereferencing an OutEdge will yield a ref to its owner
    Node node;
    B = &node;
    assert(B.owner == &node);
    assert(*B == node);
    assert(**A == node); // A (out) -> B (in) -> node (contains B)
}

// edge slots are no heavier than pointers
static assert(OutEdge.sizeof == (Node*).sizeof && InEdge.sizeof <= OutEdge.sizeof);


/++
Represents a Gyre node.

In order to achieve efficient def-use traversal and peephole transformations, every Node must keep track of its set of in-neighbors (i.e. those which have [OutEdge]s to one of its [InEdge] slots).
Meanwhile, the set of out-neighbors is implicitly defined by a Node's [OutEdge] slots.

See_Also:
[Hash sets](./set.html)
+/
struct Node {
    // TODO
    Set!(Node*) observers;
}
