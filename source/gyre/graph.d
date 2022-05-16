/++
Program construction and manipulation API.

Recommended Reading Order:
$(NUMBERED_LIST
    * [EdgeKind|Edge slots]
    * [Node|Node handles] and [intrinsic optimizations](gyre.nodes.Node.html#details)
    * Primitive control operations: [JoinNode|join], [InstantiationNode|inst.], [JumpNode|jump], [ForkNode|fork] and [ConditionalNode|cond.]
    * [Poison values and undefined behavior](gyre.nodes.html#poison-values-and-ub)
    * Other [primitive](gyre.nodes.html#prim-ops-rationale) and [MacroNode|non-primitive] nodes
)


The ADT which most closely resembles Gyre's structure is the directed multigraph: a set of nodes and directed edges, where different edges can have the same nodes at their endpoints.
Although theoretically quadratic in the worst case, we expect the number of edges to be rougly proportional to the number of nodes in the graph; and we estimate that the number of nodes will grow as a polynomial function of source program size (varying by language being compiled, of course).
Therefore, we want to keep [Node|node]s as slim as possible (and [EdgeKind|edge]s even more so), while still being able to transform subgraphs in an efficient manner.

As seen in [libFIRM](http://beza1e1.tuxen.de/pdfs/braun11wir.pdf), some optimizations can become inherent to the IR if we're able to identify common substructures in the graph.
In order to make this as efficient as possible, we'll use hash tables and specially crafted hash functions for each node, leveraging [SSA form](https://en.wikipedia.org/wiki/Static_single_assignment_form) to approximate semantic equality from structural equality.
This means that hashing a node or comparing two nodes won't be trivial operations, so we better (a) cache hash values; and (b) be careful during structural comparisons, since Gyre graphs can be cyclic.
More details [here](gyre.nodes.Node.html#details).

[Click's sea of nodes](https://www.oracle.com/technetwork/java/javase/tech/c2-ir95-150110.pdf) uses objects and pointers to represent a graph; lets copy that.
In order to maintain referential integrity (i.e. keeping our pointers valid), we can either (a) allocate all nodes on the global heap and keep that memory pinned for as long as there are references to it (easily done with D's GC), or (b) allocate in bulk and manually manage our memory, fixing references whenever objects are moved (more performant but harder to get right).
Since we'll want to call this library from other languages, we better err on the side of the `betterC`-compatible option, so (b) it is.
We'll always manage memory like this in the context of a [Graph].
+/
module gyre.graph;

import core.stdc.errno : ENOMEM;
import std.meta : AliasSeq, Filter;
import std.sumtype;

import eris.core : err_t, allocate, deallocate;
import eris.hash_table;
import eris.util : HashablePointer, empty;

import gyre.nodes;


// XXX: I wanted to do this metaprogramming in the nodes module, but using
// `__traits(allMembers, ...)` there while defining new symbols is hard, so...

private { // step 1: implement conversions AliasSeq of symbols <-> AliasSeq of types
    template JoinArgs(Args...) {
        static if (Args.length == 0)
            enum JoinArgs = "";
        else static if (Args.length == 1)
            enum JoinArgs = Args[0];
        else
            enum JoinArgs = Args[0] ~ ", " ~ JoinArgs!(Args[1 .. $]);
    }

    template Unquote(Symbols...) {
        alias Unquote = mixin("AliasSeq!(" ~ JoinArgs!Symbols ~ ")");
    }

    template Quote(Types...) {
        static if (Types.length == 0)
            alias Quote = AliasSeq!();
        else static if (Types.length == 1)
            alias Quote = AliasSeq!(Types[0].stringof);
        else
            alias Quote = AliasSeq!(Types[0].stringof, Quote!(Types[1 .. $]));
    }

    @nogc nothrow pure @safe unittest {
        alias types = AliasSeq!(int, bool, string);
        enum typenames = AliasSeq!("int", "bool", "string");

        // AliasSeq of symbols <-> AliasSeq of types
        static assert(is(Unquote!typenames == types));
        static assert(typenames == Quote!types);

        // Quote and Unquote are inverses of each other
        static assert(is(Unquote!(Quote!types) == types));
        static assert(Quote!(Unquote!typenames) == typenames);
    }
}

private { // step 2: collect all symbols/types corresponding to concrete nodes
    template isGyreNode(Type) {
        enum isGyreNode =
            is(Type == struct)
            && __traits(hasMember, Type, "_node") && is(typeof(Type._node) == Node.CommonPrefix)
            && !is(Type == Node);
    }

    template isGyreNode(string symbol) {
        enum isGyreNode = is(mixin(symbol)) && isGyreNode!(mixin(symbol));
    }

    enum nodeNames = Filter!(isGyreNode, __traits(allMembers, gyre.nodes)); // symbols
    alias AllNodes = Unquote!nodeNames; // types
}


/++
Graph structure storing a Gyre (sub)program.

Any such graph could also be used as the definition of an associated [MacroNode|macro node].


NOTE: Every graph manages memory for its own nodes and edges, which in turn cannot be safely shared with the outside world.
Due to our representation, internal graph storage will probably resemble a spaghetti of pointers, and if a node (or edge slot!) ever moves in memory, we'll need to fix every pointer which referenced it.
As a result, relocations are expensive, and in the worst case we could be moving the entire graph (e.g. if we need to expand our backing memory arena).
Since references may need to be adjusted anyway, we might as well keep related nodes close to each other, improving locality while we're at it.
In the end, we'll implement something similar to a moving mark-and-sweep GC over a private memory pool.
+/
struct Graph { // TODO
 private:
    // map of generic nodes (used for structural sharing) => in-neighbor sets,
    // where any reference held here must point into this graph's arena
    UnsafeHashMap!(NodeHandle, InNeighbors) nodes;
    alias NodeHandle = HashablePointer!Node;
    alias InNeighbors = UnsafeHashSet!(Node*);

    // corresponds to the notion of a "top-level". also used as a GC root:
    // any subgraph not reachable from this node's inteface is considered dead
    MacroNode topLevel;

    // backing memory pool for this graph's nodes (all except the topLevel)
    NodeStorage[] nodePool;
    alias NodeStorage = SumType!AllNodes;
    version (unittest) pragma(msg, "Bytes per node: " ~ Graph.NodeStorage.sizeof.stringof);

    // bump allocator index, either at the first free slot or `>= nodePool.length`
    size_t cursor;

 public @nogc nothrow:
    /++
    Initializes an empty Gyre graph.

    Params:
        self = Graph being initialized.
        id = This graph's unique identifier.
        capacity = Initial number of nodes to preallocate.
        inEdges = Kinds of [InEdges] in this subgraph's top-level.
        outEdges = Kinds of [OutEdges] in this subgraph's top-level.

    Returns:
        Zero on success, non-zero on failure (e.g. OOM).
    +/
    err_t initialize(
        MacroNode.ID id,
        size_t capacity = 256,
        EdgeKind[] inEdges = [],
        EdgeKind[] outEdges = []
    )
    in (this is Graph.init, "detected memory leak caused by Graph re-initialization")
    out (error; !error || this is Graph.init)
    {
        err_t error = 0;
        scope(exit) if (error) this = Graph.init;

        // allocate backing memory pool and set up free index
        this.nodePool = allocate!(Graph.NodeStorage)(capacity);
        scope(exit) if (error) this.nodePool.deallocate();
        if (capacity > 0 && this.nodePool == null) return (error = ENOMEM);
        this.cursor = 0;

        // reserve space for node handles
        error = this.nodes.rehash(capacity);
        scope(exit) if (error) this.nodes.dispose();
        if (error) return error;

        // initialize top-level
        error = MacroNode.initialize(&this.topLevel, id, inEdges, outEdges);
        scope(exit) if (error) MacroNode.dispose(&this.topLevel);
        if (error) return error;
        this.topLevel.updateHash();

        assert(error == 0);
        return error;
    }

    /// Frees all resources allocated by this graph and sets it to an uninitialized state.
    void dispose() {
        MacroNode.dispose(&this.topLevel);
        this.nodes.dispose();
        this.nodePool.deallocate();
        this = Graph.init;
    }
}

nothrow unittest {
    Graph graph;
    graph.initialize(42);
    scope(exit) graph.dispose();
    assert(graph.topLevel.id == 42);
}
