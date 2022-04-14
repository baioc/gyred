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

The current implementation relies on D's automatic memory management, mainly because managed references (i.e. any variable of a class type) are kept stable by the runtime.
The alternative would be to use pointers to struct types, which would basically require us to implement a special-purpose moving GC with either double indirections or updates *everywhere* whenever a node is moved (e.g. when growing a dynamic array, when an AA is rehashed, etc).

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

private mixin template StaticEdgeFactories() {
    private import std.traits : EnumMembers;
    private import std.conv : to;
    private import std.format : format;
    static foreach (kind; EnumMembers!EdgeKind) {
        mixin(q{
            static typeof(this) %1$s() nothrow pure @safe {
                auto e = new typeof(this)(EdgeKind.%1$s);
                return e;
            }
        }.format(to!string(kind)));
    }
}

// eponymous template type, for documentation purposes only
private template Ref(T) {
    static if (is(T == class)) alias Ref = T;
    else                       alias Ref = T*;
}

/++
An outgoing edge slot.

An OutEdge connects to zero or one [InEdge].

See_Also:
[InEdge]
+/
final class OutEdge {
    Ref!InEdge target; /// Either points to another edge slot, or is null.
    const EdgeKind kind; /// This edge's kind, fixed on construction.

    ///
    this(EdgeKind kind, Ref!InEdge target = null) nothrow pure @safe {
        this.kind = kind;
        this.target = target;
    }

    mixin StaticEdgeFactories;

 @nogc nothrow pure @safe:
    override bool opEquals(Object rhs) const {
        if (auto other = cast(OutEdge)(rhs))
            return this.kind == other.kind && this.target is other.target;
        else
            return false;
    }

    override size_t toHash() const {
        return this.target.hashOf;
    }

    invariant {
        assert(target is null || target.kind == this.kind);
    }
}

///
unittest {
    auto def = InEdge.data;
    auto use1 = OutEdge.data;
    auto use2 = OutEdge.data;
    // data edges are directed from uses to defs
    use1.target = def;
    use2.target = def;
    assert(use1.target is use2.target);
    assert(use1 == use2);
    assert(use1 !is use2);
}

/++
An incoming edge slot.

InEdge slots can receive zero or more [OutEdge]s.

See_Also:
[Node]
+/
final class InEdge {
    Ref!Node owner; /// Points back to the [Node] which owns this edge.
    const EdgeKind kind; /// This edge's kind, fixed on construction.

    ///
    this(EdgeKind kind, Ref!Node owner = null) nothrow pure @safe {
        this.kind = kind;
        this.owner = owner;
    }

    mixin StaticEdgeFactories;

 @nogc nothrow pure @safe:
    override bool opEquals(Object rhs) const {
        if (auto other = cast(InEdge)(rhs))
            return this.kind == other.kind && this.owner is other.owner;
        else
            return false;
    }

    override size_t toHash() const {
        return this.owner.hashOf;
    }
}

///
nothrow pure @safe unittest {
    auto node = new Node();
    auto A = OutEdge.control;
    auto B = InEdge.control;
    // in this example, control flows out from A and into B
    A.target = B;
    B.owner = node;
    assert(A.target.owner is node);
}


/++
Represents any Gyre node.

In order to achieve efficient def-use traversal and peephole transformations, every Node must keep track of its set of in-neighbors (i.e. those which have [OutEdge]s to one of its [InEdge] slots).
Meanwhile, the set of out-neighbors is implicitly defined by a Node's [OutEdge] slots.

See_Also:
[Hash sets](./set.html)
+/
struct Node { // TODO
    private const(VTable*) vptr = &vtbl;

    Set!(Ref!Node) observers;

 private:
    static immutable VTable vtbl = VTable.init;
    immutable struct VTable {
     nothrow pure @safe:
        size_t function(Ref!(const Node)) toHash = (self) => self.hashOf;
        bool function(Ref!(const Node), Ref!(const Node)) opEquals = (lhs, rhs) => lhs is rhs;
    }

 public nothrow pure @safe:
    size_t toHash() const {
        return this.vptr.toHash(&this);
    }

    bool opEquals(ref const Node rhs) const @trusted {
        return this.vptr.opEquals(&this, &rhs);
    }
}

///
nothrow unittest {
    static bool usingCustomHash;
    static bool usingCustomEquals;

    struct TestNode {
        mixin NodeInheritance!(vtable);
        enum Node.VTable vtable = {
            toHash: (self) {
                debug usingCustomHash = true;
                return 0;
            },
            opEquals: (self, rhs) {
                debug usingCustomEquals = true;
                return self is rhs;
            },
        };
    }

    // subtype inherits Node's members
    TestNode test;
    assert(is(typeof(test.observers) == typeof(Node.observers)));

    // subtype's toHash and opEquals work normally
    usingCustomHash = usingCustomEquals = false; {
        bool[TestNode] map = [ test: true ];
        assert(test == test);
    } assert(usingCustomHash && usingCustomEquals);

    // they also dispatch correctly when using a polymorphic Node
    usingCustomHash = usingCustomEquals = false; {
        auto nodep = cast(Node*)(&test);
        Set!(Node*) set;
        set.add(nodep); set.add(nodep);
        assert(*nodep == *nodep);
        assert(set.length == 1);
    } assert(usingCustomHash && usingCustomEquals);
}

// hand-made struct inheritance
private mixin template NodeInheritance(Node.VTable vtable = Node.VTable.init) {
    private static immutable(Node.VTable) vtbl = vtable;

    private Node _node = { vptr: &vtbl };
    alias _node this;

    // this static assertion justifies the casts below being @trusted
    static assert(
        typeof(this)._node.offsetof == 0u,
        "common Node prefix must be at a zero offset for safe struct inheritance"
    );

    public size_t toHash() const nothrow pure @trusted {
        return this.vptr.toHash(cast(Node*)(&this));
    }

    public bool opEquals(ref const typeof(this) rhs) const nothrow pure @trusted {
        return this.vptr.opEquals(cast(Node*)(&this), cast(Node*)(&rhs));
    }
}

struct JoinNode {
    mixin NodeInheritance;

    auto definition = InEdge.data;
    auto body = OutEdge.control;
    private alias Parameters = InEdge[];
    Parameters[] channels;
}

struct InstantiationNode {
    mixin NodeInheritance;

    auto definition = OutEdge.data;
    InEdge[] continuations;
}

struct JumpNode {
    mixin NodeInheritance;

    auto control = InEdge.control;
    auto continuation = OutEdge.data;
    OutEdge[] arguments;
}

struct BranchNode {
    mixin NodeInheritance;

    auto control = InEdge.control;
    auto selector = OutEdge.data;
    OutEdge[] options;
}

struct ForkNode {
    mixin NodeInheritance;

    auto minParallelism = OutEdge.data;
    auto maxParallelism = OutEdge.data;
    auto control = InEdge.control;
    OutEdge[] threads;
}

struct MacroNode {
    mixin NodeInheritance;

    OutEdge[] dataUses;
    InEdge[]  dataDefs;
    InEdge[]  controlIncoming;
    OutEdge[] controlOutgoing;
    auto minThreads = OutEdge.data;
    auto maxThreads = OutEdge.data;
}

// TODO: prim ops { literals, arithmetic, mem ops }
