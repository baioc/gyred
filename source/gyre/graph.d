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

import core.stdc.errno : ENOMEM, EINVAL;
import core.lifetime : forward, move, moveEmplace;
import std.bitmanip : taggedPointer;
import std.meta : AliasSeq, Filter;
import std.traits : EnumMembers, Fields, Parameters;

import betterclist : List;
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
    package alias AllNodes = Unquote!nodeNames; // types
}

private { // step 3: profit
    version (D_Ddoc) {
        /++
        Indicates node types in this module's API.

        See_Also: [gyre.mnemonics]
        +/
        public enum NodeKind : ubyte {
            JoinNode, /// Corresponds to the eponymous [gyre.nodes.JoinNode|type].
            etc /// Other members follow the same naming pattern.
        }
    } else {
        mixin("public enum NodeKind : ubyte { " ~ JoinArgs!nodeNames ~ " }"); // enum (type tag)
    }

    union AnyNode { // big union type
        static foreach (NodeType; AllNodes) {
            mixin(NodeType.stringof ~ " as" ~ NodeType.stringof ~ ";");
        }
    }
    ref AllNodes[kind] as(NodeKind kind)(ref AnyNode node) {
        mixin("return node.as" ~ AllNodes[kind].stringof ~ ";");
    }

    // sanity check: tags must index the right types and union members
    static foreach (tag; EnumMembers!NodeKind) {
        static assert(__traits(identifier, EnumMembers!NodeKind[tag]) == AllNodes[tag].stringof);
        static assert(is(AllNodes[tag] == Fields!AnyNode[tag]));
    }

    // NOTE: type tags are technically redundant since they could be derived from vptrs
    struct NodeStorage {
        AnyNode node;
        NodeKind tag;

        static if (NodeStorage.sizeof > 64) pragma(msg, __FILE__ ~ "(" ~ __LINE__.stringof ~ ",0)"
            ~ ": Warning: Fat nodes: each one is taking up " ~ NodeStorage.sizeof.stringof ~ " bytes"
        );

     @nogc nothrow:
        void dispose() {
            final switch (this.tag) {
                static foreach (kind; EnumMembers!NodeKind) {
                    case kind: {
                        alias NodeType = AllNodes[kind];
                        NodeType.dispose(&this.node.as!kind);
                        return;
                    }
                }
            }
        }

        void opPostMove(ref NodeStorage old) pure {
            final switch (this.tag) {
                static foreach (kind; EnumMembers!NodeKind) {
                    case kind: {
                        move(old.node.as!kind, this.node.as!kind);
                        return;
                    }
                }
            }
        }
    }
}

/++
Represents frequent [NodeKind] use patterns.

These symbols are also re-exported in [gyre.mnemonics].
+/
enum NodeSugar {
    @mnemonic("func") SingleChannelJoinNode, /// A single-channel [JoinNode].
}


/++
Graph structure storing a Gyre (sub)program.

Any such graph could also be used as the definition of an associated [MacroNode|macro node].


NOTE: Every graph manages memory for its own nodes and edges, which in turn cannot be safely shared with the outside world.
Due to our representation, internal graph storage will probably resemble a spaghetti of pointers, and if a node (or edge slot!) ever moves in memory, we'll need to fix every pointer which referenced it.
As a result, relocations are expensive, and in the worst case we could be moving the entire graph (e.g. if we need to expand our backing memory arena).
Since references may need to be adjusted anyway, we might as well keep related nodes close to each other, improving locality while we're at it.
In the end, we'll implement something similar to a moving mark-and-sweep GC over a private memory pool.

See_Also: [Transaction]
+/
struct Graph {
 private:
    // map of generic nodes (used for structural sharing) => in-neighbor sets,
    // where any reference held here must point into this graph's arena
    UnsafeHashMap!(HashableNode, InNeighbors) nodes;
    alias HashableNode = HashablePointer!Node;
    alias InNeighbors = UnsafeHashSet!(Node*);

    // corresponds to the notion of a "top-level". also used as a GC root:
    // any subgraph not reachable from this node's inteface is considered dead
    MacroNode topLevel;

    // backing memory pool for this graph's nodes (all except the topLevel)
    List!NodeStorage nodePool;

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
        exports = Preallocated number of "exported" defs (or [InEdge|in-edge]s for [MacroNode|macro node] definitions).
        imports = Preallocated number of "imported" defs (or [OutEdge|out-edge]s for [MacroNode|macro node] definitions).
        capacity = Number of nodes to preallocate.

    Returns:
        Zero on success, non-zero on failure (OOM).
    +/
    err_t initialize(MacroNode.ID id, uint exports = 1, uint imports = 0, size_t capacity = 256)
    in (this is Graph.init, "detected memory leak caused by Graph re-initialization")
    {
        err_t error = 0;
        scope(exit) if (error) this = Graph.init;

        // allocate backing memory pool and set up free index
        this.nodePool = List!NodeStorage(allocate!NodeStorage(capacity));
        scope(exit) if (error) this.nodePool.array.deallocate();
        if (capacity > 0 && this.nodePool.capacity == 0) return (error = ENOMEM);

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

        foreach (ref inNeighbors; this.nodes.byValue) {
            inNeighbors.dispose();
        }
        this.nodes.dispose();

        foreach_reverse (ref node; this.nodePool) {
            node.dispose();
        }
        this.nodePool.array.deallocate();

        this = Graph.init;
    }

 private:
    // moves a single node into the graph in case there's enough space for it
    // NOTE: assumes node structure is stable and its hash is already cached
    Node* add(NodeStorage* temp)
    in (temp != null && !this.nodePool.full)
    {
        if (temp == null) return null;
        if (this.nodePool.full) return null;

        // abort the node in case an equivalent one already exists in the graph
        auto oldNode = cast(Node*)&temp.node;
        HashableNode* existing;
        InNeighbors* neighbors;
        const found = this.nodes.get(HashableNode(oldNode), existing, neighbors);
        if (found) {
            assert(existing != null);
            return *existing;
        }

        // add the new node to the graph, with an empty set of in-neighbors
        this.nodePool ~= NodeStorage.init;
        NodeStorage* storage = &this.nodePool[$ - 1];
        moveEmplace(*temp , *storage);
        auto newNode = cast(Node*)&storage.node;
        const error = (this.nodes[HashableNode(newNode)] = InNeighbors.init);
        if (error) {
            moveEmplace(*storage, *temp); // undo the move
            this.nodePool.pop();
            return null;
        }

        // TODO: register imports/exports

        return newNode;
    }
}


/++
First-class representation of a graph operation.

Transactions are used to update a Gyre [Graph] in an "all-or-nothing" fashion while verifying IR rules, expanding graph memory as needed and wiring up in-neighbors correctly.
Last but not least: whenever a transaction commits, simple peephole optimizations (e.g. arithmetic simplification, constant folding and strength reduction) are performed automatically.

NOTE: Despite the name, transactions cannot be concurrently applied to the same [Graph].
+/
struct Transaction {
 private:
    mixin(taggedPointer!(
        Graph*, "graph",
        bool, "began", 1
    ));

    List!NodeStorage nursery;

 public @nogc nothrow:
    /// Creates a new transaction.
    this(ref Graph graph) pure {
        this.graph = &graph;
        this.began = false;
    }
    @disable this();

    /**
    Begins the transaction.

    All transactions which have begun must explicitly finish (successfully or otherwise).

    Params:
        newNodes = Maximum number of added nodes (does not dynamically expand).

    Returns:
        Zero on success, non-zero otherwise (in which case the transaction fails to begin).

    See_Also: [commit], [abort]
    **/
    err_t begin(size_t newNodes)
    in (!this.began)
    out (error; error || this.began)
    {
        if (this.began) return EINVAL;
        this.nursery = List!NodeStorage(allocate!NodeStorage(newNodes));
        if (newNodes > 0 && this.nursery.capacity == 0) return ENOMEM;
        this.began = true;
        return 0;
    }

    /// Finishes the transaction by cancelling it.
    void abort()
    in (this.began)
    out (; !this.began)
    {
        if (!this.began) return;
        foreach_reverse (ref node; this.nursery) {
            node.dispose();
        }
        this.nursery.array.deallocate();
        this = Transaction(*this.graph);
    }

    /**
    Finishes this transaction by applying its changes.

    Returns:
        Zero on success, non-zero otherwise (in which case the transaction must be [abort]ed).
    */
    err_t commit()
    in (this.began)
    out (error; error || !this.began)
    {
        if (!this.began) return EINVAL;

        // compute how much space we need and how much we have available
        const neededSpace = this.nursery.availableCapacity;
        const freeSpace = this.graph.nodePool.availableCapacity;

        assert(
            freeSpace >= neededSpace,
            "TODO: implement garbage collection"
        );

        // TODO: check IR rules

        // TODO: add nodes in topological order
        foreach (ref slot; this.nursery) {
            NodeStorage* storage = &slot;
            auto node = cast(Node*)&storage.node;
            node.updateHash();
            this.graph.add(storage);
        }

        // TODO: rewire in-neighbors
        // TODO: peephole optimizations

        this.nursery.array.deallocate();
        this = Transaction(*this.graph);
        return 0;
    }

    private alias InitParams(NodeType) = Parameters!(NodeType.initialize)[1 .. $];

    /**
    Inserts a node during an ongoing transaction.

    Returns:
        A pointer to the inserted node, or `null` in case something went wrong (OOM).
    */
    AllNodes[kind]* insert(NodeKind kind)(auto ref InitParams!(AllNodes[kind]) args)
    in (this.began)
    {
        if (!this.began) return null;
        alias NodeType = AllNodes[kind];

        // the nursery doesn't expand, so we give up if it would overflow
        if (this.nursery.full) return null;

        // grab the first available slot and in-place initialize the node there
        this.nursery ~= NodeStorage.init;
        NodeStorage* storage = &this.nursery[$ - 1];
        storage.tag = kind;
        NodeType* newNode = &storage.node.as!kind;
        const error = NodeType.initialize(newNode, forward!args);
        if (error) {
            this.nursery.pop();
            return null;
        }

        return newNode;
    }

    /// ditto
    JoinNode* insert(NodeSugar sugar : NodeSugar.SingleChannelJoinNode)(uint argc) {
        uint[1] ms = [argc];
        return this.insert!(NodeKind.JoinNode)(cast(uint[])ms);
    }
}


///
@nogc nothrow unittest {
    import gyre.mnemonics;

    Graph graph;
    graph.initialize(MacroNode.ID(42));
    scope(exit) graph.dispose();
    assert(graph.topLevel.id == 42);

    /*
        foo(x, y):
            a = x + 1
            b = 1 + x
    */
    with (Transaction(graph)) {
        begin(1);
        {
            auto oops = insert!mul;
        }
        abort();

        begin(4);
        {
            auto func = insert!func(2);
            auto x = &func.channels[0][0];

            auto c1 = insert!const_(1);

            auto a = insert!add;
            a.lhs.target = x;
            a.rhs.target = &c1.value;

            auto b = insert!add;
            b.lhs.target = &c1.value;
            b.rhs.target = x;
        }
        const error = commit();
        assert(!error);
    }
    // but b computes the same value as a, so it gets optimized away!
    assert(graph.nodes.length == 3);
}
