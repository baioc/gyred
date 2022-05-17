/++
Program construction and manipulation API.

Recommended Reading Order:
$(NUMBERED_LIST
    * [EdgeKind|Edge slots] and their different kinds
    * [Node|Node handles] and [structural sharing optimizations](gyre.nodes.Node.html#details)
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
import std.traits : EnumMembers, Fields, Parameters;

import eris.core : err_t, allocate, deallocate;
import eris.util : HashablePointer;
import eris.hash_table : UnsafeHashMap, UnsafeHashSet;

import gyre.nodes;


// XXX: I wanted to do some of this metaprogramming in the nodes module, but using
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

private { // step 3: profit
    mixin("enum NodeKind : ubyte { " ~ JoinArgs!nodeNames ~ " }"); // enum (type tag)
    // NOTE: these tags are technically redundant: we could derive them from vptrs

    union AnyNode { // big union type
        static foreach (NodeType; AllNodes) {
            mixin(NodeType.stringof ~ " as" ~ NodeType.stringof ~ ";");
        }
    }
    ref AllNodes[kind] as(NodeKind kind)(ref AnyNode node) {
        mixin("return node.as" ~ AllNodes[kind].stringof ~ ";");
    }

    // sanity check: tags must correspond to the right types and union members
    static foreach (tag; EnumMembers!NodeKind) {
        static assert(__traits(identifier, EnumMembers!NodeKind[tag]) == AllNodes[tag].stringof);
        static assert(is(AllNodes[tag] == Fields!AnyNode[tag]));
    }

    // XXX: needs to be declared outside Graph because "delegate cannot be struct members"
    alias DefaultSetUp(NodeType) = delegate(NodeType* node){};
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
struct Graph {
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
    struct NodeStorage { AnyNode node; NodeKind tag; }
    static if (Graph.NodeStorage.sizeof > 64) pragma(msg, __FILE__ ~ "(" ~ __LINE__.stringof ~ ",0)"
        ~ ": Warning: Fat nodes: each one is taking up " ~ Graph.NodeStorage.sizeof.stringof ~ " bytes"
    );

    // bump allocator index, either at the first free slot or `>= nodePool.length`
    size_t cursor;

 public @nogc nothrow:
    /++
    Initializes an empty Gyre graph, must be later [dispose]d to avoid leaking memory.

    Our graphs eliminate dead code automatically.
    Therefore, every top-level function (represented by a [JoinNode|join node]) must be "anchored" to the graph by having their `definition` slot linked to one of the graph's in-edge slots.
    Conceptually, this is as if these functions were being "exported" to code outside of this graph.
    Nodes which are not directly exported and aren't reachable by an exported node may be marked as dead code and silently eliminated.
    Similarly, a graph may also depend on external information (`type` parameters, for instance), in which case it needs to point to these "imported" definitions with its out-edge slots.

    Params:
        self = Graph being initialized.
        id = This graph's unique identifier.
        exports = Preallocated number of "exported" symbols (or [InEdge|in-edge]s for macro node definitions).
        imports = Preallocated number of "imported" symbols (or [OutEdge|out-edge]s for macro node definitions).
        capacity = Number of nodes to preallocate.

    Returns:
        Zero on success, non-zero on failure (OOM).
    +/
    err_t initialize(MacroNode.ID id, uint exports = 1, uint imports = 0, size_t capacity = 256)
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

        // reserve some space for node handles
        error = this.nodes.rehash(1 + capacity/2);
        scope(exit) if (error) this.nodes.dispose();
        if (error) return error;

        // initialize top-level, but with swapped "ins" and "outs" due to how
        // our edges are directed. we'll essentially have our top-level work
        // as a pointer forwarding mechanism. eg: (def A) <-- [Graph(def B)] <-- (use B)
        // internally is ... [InEdge(import A) <- B <- OutEdge(export B)] ...
        const outs = exports;
        const ins = imports;
        error = MacroNode.initialize(&this.topLevel, id, ins, outs);
        scope(exit) if (error) MacroNode.dispose(&this.topLevel);
        if (error) return error;
        this.topLevel.updateHash();

        assert(!error);
        return error;
    }

    /// Frees all resources allocated by this graph and sets it to an uninitialized state.
    void dispose() {
        MacroNode.dispose(&this.topLevel);
        this.nodes.dispose();
        this.nodePool.deallocate(); // TODO: dispose each in-use node slot
        this = Graph.init;
    }

    private alias InitParams(NodeType) = Parameters!(NodeType.initialize)[1 .. $];
    private alias SetUp(NodeType) = void delegate(NodeType*) @nogc nothrow;

    /++
    Allocates and adds a single node to the graph.

    NOTE: Adding a node with this method only works if its dependencies have already been added, so a topological order is required.
    NOTE: Operations which use the added node's address (such as adding it to another's in-neighbors) can only be done with the return value.

    Params:
        args = Arguments used to in-place initialize the node.
        setUp = Callback used to set up the new node once it's been allocated.
            When this callable returns, the node's structure is assumed stable; notably, `toHash` must yield a valid hash.

    Returns:
        Either a pointer to the node in the graph, or `null` in case of failure.
        Even on success, the returned pointer might not be the same one which was passed to `setUp`, since our structural sharing scheme may have chosen to return some equivalent pre-existing node.
    +/
    AllNodes[kind]* add(NodeKind kind)(
        auto ref InitParams!(AllNodes[kind]) args,
        scope SetUp!(AllNodes[kind]) setUp = DefaultSetUp!(AllNodes[kind])
    ) {
        import core.lifetime : forward;
        err_t error = 0;

        assert(
            this.cursor < this.nodePool.length,
            "TODO: implement garbage collection"
        );

        // coerce the first available slot from the memory pool into the requested node
        alias NodeType = AllNodes[kind];
        NodeStorage* storage = &this.nodePool[this.cursor];
        NodeType* newNode = &storage.node.as!kind;

        // in-place initialize that slot
        error = NodeType.initialize(newNode, forward!args);
        if (error) return null;
        setUp(newNode);
        // TODO: enforce IR rules

        // this node's structure should now be stable, so we can store its hash
        newNode.updateHash();

        // abort the node in case an equivalent one already exists in the graph
        auto handle = NodeHandle(newNode.asNode);
        NodeHandle* existing;
        InNeighbors* neighbors;
        const found = this.nodes.get(handle, existing, neighbors);
        if (found) {
            newNode = NodeType.ofNode(existing.ptr);
            assert(newNode != null);
            return newNode;
        }

        // add the new node to the graph, with an empty set of in-neighbors
        error = (this.nodes[handle] = InNeighbors.init);
        if (error) return null;
        cursor++; // and bump our allocator forward

        return newNode;
    }

    ///
    unittest {
        Graph graph;
        graph.initialize(MacroNode.ID(42));
        scope(exit) graph.dispose();
        assert(graph.topLevel.id == 42);

        /*
            join (x, y):
                a = x + 1
                b = 1 + x
        */
        with (NodeKind) {
            auto join = graph.add!JoinNode([2], (join){
                assert(join.channels.length == 1);
                assert(join.channels[0].length == 2);
            });

            auto c1 = graph.add!ConstantNode(1);

            auto a = graph.add!AdditionNode((a){
                a.lhs.target = &join.channels[0][0];
                a.rhs.target = &c1.value;
            });

            auto b = graph.add!AdditionNode((b){
                b.lhs.target = &c1.value;
                b.rhs.target = &join.channels[0][0];
            });

            // but b computes the same value as a, so it gets optimized away!
            assert(b is a);
            assert(graph.nodes.length == 3);
        }
    }
}
