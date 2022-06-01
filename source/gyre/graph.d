/++
Program construction and manipulation API.

Recommended Reading Order:
$(NUMBERED_LIST
    * [EdgeKind|Edge slots] and their different kinds
    * [Node|Generic nodes] and [structural sharing optimizations](gyre.nodes.Node.html#details)
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

import core.stdc.errno : ENOMEM, EINVAL, EACCES, EOVERFLOW;
import core.lifetime : forward;
import std.meta : AliasSeq, Filter;
import std.traits : EnumMembers, Fields, Parameters;

import eris.core : err_t, allocate, deallocate;
import eris.util : HashablePointer;
import eris.hash_table : UnsafeHashMap, UnsafeHashSet;

public import gyre.nodes;


// XXX: I wanted to do some of this metaprogramming in the nodes module, but using
// `__traits(allMembers, ...)` there while defining new symbols is hard, so...

private { // step 1: implement conversions AliasSeq of symbols <-> AliasSeq of types
    template JoinArgs(Args...) {
        static if (Args.length == 0)
            enum JoinArgs = ``;
        else static if (Args.length == 1)
            enum JoinArgs = Args[0];
        else
            enum JoinArgs = Args[0] ~ `, ` ~ JoinArgs!(Args[1 .. $]);
    }

    template Unquote(Symbols...) {
        alias Unquote = mixin(`AliasSeq!(` ~ JoinArgs!Symbols ~ `)`);
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
        mixin(`public enum NodeKind : ubyte { ` ~ JoinArgs!nodeNames ~ ` }`); // enum (type tag)
    }

    union NodeUnion {
        static foreach (NodeType; AllNodes) {
            mixin(NodeType.stringof ~ ` as` ~ NodeType.stringof ~ `;`);
        }
    }
    pragma(inline) ref as(NodeKind kind)(ref inout(NodeUnion) node) {
        mixin(`return node.as` ~ AllNodes[kind].stringof ~ `;`);
    }

    // sanity check: tags must index the right types and union members
    static foreach (tag; EnumMembers!NodeKind) {
        static assert(__traits(identifier, EnumMembers!NodeKind[tag]) == AllNodes[tag].stringof);
        static assert(is(AllNodes[tag] == Fields!NodeUnion[tag]));
    }

    struct NodeStorage { // a big tagged union
        NodeUnion node;
        static if (NodeStorage.sizeof > 64) pragma(msg, __FILE__ ~ "(" ~ __LINE__.stringof ~ ",0)"
            ~ ": Warning: Fat nodes: each one is taking up " ~ NodeStorage.sizeof.stringof ~ " bytes"
        );

     @nogc nothrow:
        // OPT: we actually derive type tags from vptrs, but it still remains
        // to be seen whether this is better for performance than a cached tag
        pragma(inline) @property NodeKind tag() const pure {
            static foreach (kind; EnumMembers!NodeKind) {
                if (this.asNode.vptr == &AllNodes[kind].vtbl) return kind;
            }
            assert(false, "unreachable");
        }

        pragma(inline) inout(Node)* asNode() inout pure
        return // XXX: `return` annotation needed in DMD 2.100.0
        {
            return cast(inout(Node)*)&this.node;
        }

        pragma(inline) static inout(NodeStorage)* ofNode(inout(Node)* node) pure {
            static assert(
                NodeStorage.node.offsetof == 0 && NodeStorage.sizeof == NodeUnion.sizeof,
                "NodeStorage layout must allow casting from Node*"
            );
            return cast(inout(NodeStorage)*)node;
        }

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

        void opPostMove(ref const(NodeStorage) old) pure {
            final switch (this.tag) {
                static foreach (kind; EnumMembers!NodeKind) {
                    case kind: {
                        this.node.as!kind.opPostMove(old.node.as!kind);
                        return;
                    }
                }
            }
        }

        @property OutEdgeIterator!Callable
        outEdges(Callable = int delegate(ref OutEdge) @nogc nothrow)() {
            final switch (this.tag) {
                static foreach (kind; EnumMembers!NodeKind) {
                    case kind: {
                        auto node = &this.node.as!kind;
                        return node.outEdges!Callable;
                    }
                }
            }
        }

        @property InEdgeIterator!Callable
        inEdges(Callable = int delegate(ref InEdge) @nogc nothrow)() {
            final switch (this.tag) {
                static foreach (kind; EnumMembers!NodeKind) {
                    case kind: {
                        auto node = &this.node.as!kind;
                        return node.inEdges!Callable;
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
    @mnemonic("func") JoinNodeSingleChannel, /// A single-channel [JoinNode].
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
    UnsafeHashMap!(HashableNode, InNeighbors) adjacencies;
    alias HashableNode = HashablePointer!Node;
    alias InNeighbors = UnsafeHashSet!(Node*);

    // corresponds to the notion of a "top-level". also used as a GC root:
    // any subgraph not reachable from this node's inteface is considered dead
    MacroNode topLevel;
    uint _exported; // number of actually exported definitions

    // backing memory pool for this graph's nodes (all except the topLevel)
    NodeStorage[] arena;
    size_t cursor; // bump allocator index for the arena

 public @nogc nothrow:
    /// This subgraph's unique identifier.
    @property MacroNode.ID id() const pure {
        return this.topLevel.id;
    }

    /// Number of definitions exported by this graph.
    @property uint exported() const pure {
        return this._exported;
    }

    /// Number of definitions imported by this graph.
    @property uint imported() const pure {
        return cast(uint)this.topLevel.inSlots.length;
    }

    /// Number of unique nodes in the graph.
    @property size_t length() const pure {
        return this.adjacencies.length;
    }

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
        imports = Maximum number of "imported" defs (or [OutEdge|out-edge]s for [MacroNode|macro node] definitions).
        capacity = Number of nodes to preallocate.

    Returns:
        Zero on success, non-zero on failure (OOM).
    +/
    err_t initialize(MacroNode.ID id, uint exports = 1, uint imports = 0, size_t capacity = 256) {
        err_t error = 0;
        scope(exit) if (error) this = Graph.init;

        // allocate backing memory pool and set up free index
        this.arena = allocate!NodeStorage(capacity);
        scope(exit) if (error) this.arena.deallocate();
        if (capacity > 0 && this.arena == null) return (error = ENOMEM);
        this.cursor = 0;

        // reserve some space for node handles
        error = this.adjacencies.rehash(1 + capacity/2);
        scope(exit) if (error) this.adjacencies.dispose();
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
        this._exported = 0;

        assert(!error);
        return error;
    }

    /// Frees all resources allocated by this graph and sets it to an uninitialized state.
    void dispose() {
        MacroNode.dispose(&this.topLevel);

        foreach (ref inNeighbors; this.adjacencies.byValue) {
            inNeighbors.dispose();
        }
        this.adjacencies.dispose();

        assert(this.cursor <= this.arena.length);
        foreach_reverse (i; 0 .. this.cursor) {
            this.arena[i].dispose();
        }
        this.arena.deallocate();

        this = Graph.init;
    }

 private:
    // shallow copy a node into the graph in case there's space for it,
    // returning the resulting internal pointer (stable until the next rehash)
    // NOTE: node structure must be stable and its hash already cached, which
    // implies its dependencies were already added (requires a topological sort)
    NodeStorage* add(NodeStorage* temp) {
        if (this.cursor >= this.arena.length) return null;

        // abort the node in case an equivalent one already exists in the graph
        {
            auto handle = const(HashableNode)(temp.asNode);
            HashableNode* existing;
            InNeighbors* neighbors;
            const found = this.adjacencies.get(handle, existing, neighbors);
            if (found) {
                assert(existing != null);
                return NodeStorage.ofNode(existing.ptr);
            }
        }

        // add the new node to the graph, with an empty set of in-neighbors
        NodeStorage* newStorage = &this.arena[this.cursor];
        *newStorage = *temp;
        newStorage.opPostMove(*temp);
        auto handle = HashableNode(newStorage.asNode);
        const error = (this.adjacencies[handle] = InNeighbors.init);
        if (error) return null;
        this.cursor++;

        return newStorage;
    }

    err_t export_(InEdge* definition) {
        // expand the export array if needed. this does not cause rehashes and,
        // since it's a dynamic array, pointers to the topLevel are kept stable
        if (this.exported >= this.topLevel.outSlots.length) {
            assert(this.exported == this.topLevel.outSlots.length);
            // allocate a new array
            uint n = this.exported * 2;
            if (n == 0) n = 1;
            else if (n <= this.exported) return EOVERFLOW;
            auto newSlots = allocate!OutEdge(n);
            if (newSlots == null) return ENOMEM;
            // copy the old exports into it, then swap the old array out
            foreach (i, outEdge; this.topLevel.outSlots) newSlots[i] = outEdge;
            this.topLevel.outSlots.deallocate();
            this.topLevel.outSlots = newSlots;
        }

        // wire up a free out-edge to the exported definition
        this.topLevel.outSlots[this.exported] = OutEdge(definition.kind, definition);
        this._exported++;
        return 0;
    }

    @property ref inout(InEdge[]) imports() inout pure {
        return this.topLevel.inSlots;
    }
}

// TODO: expose a pass API over Graphs (check LLVM for inspiration)


/++
First-class representation of a graph operation.

Transactions are used to update a Gyre [Graph] in an "all-or-nothing" fashion while verifying IR rules, expanding graph memory as needed and wiring up in-neighbors correctly.
Last but not least: whenever a transaction commits, simple peephole optimizations (e.g. arithmetic simplification, constant folding and strength reduction) are performed automatically.

See_Also: [NodeHandle]
+/
struct Transaction {
 private:
    Graph* graph;

    // temporary buffer for new nodes. maps pointers to their ownership status
    // (such that true indicates that they were allocated by this transaction)
    UnsafeHashMap!(NodeStorage*, bool) nursery;

 public @nogc nothrow:
    /// Creates a new transaction.
    this(ref Graph graph) pure { this.graph = &graph; }
    @disable this();

    /++
    Begins the transaction.

    All transactions which have begun must explicitly finish (successfully or otherwise).

    Params:
        n = Expected number of inserted nodes.

    Returns:
        Zero on success, non-zero otherwise (in which case the transaction fails to begin).

    See_Also: [commit], [abort]
    +/
    err_t begin(size_t n = 0)
    in (this.nursery.capacity == 0, "can't begin a transaction twice")
    {
        if (this.nursery.capacity > 0) return EINVAL;
        else return this.nursery.rehash(n);
    }

    /// Finishes the transaction by cancelling it.
    void abort() {
        foreach (entry; this.nursery.byKeyValue) {
            if (entry.value) deallocate(entry.key);
        }
        this.nursery.dispose();
    }

    private alias InitParams(NodeType) = Parameters!(NodeType.initialize)[1 .. $];

    /++
    Creates a node during an ongoing transaction.

    The created node has a stable address as long as this transaction is ongoing.

    Returns:
        A pointer to the new node, which is `null` in case something went wrong (OOM or the provided arguments were rejected by the node's initializer).
    +/
    AllNodes[kind]* insert(NodeKind kind)(auto ref InitParams!(AllNodes[kind]) args) {
        alias NodeType = AllNodes[kind];
        err_t error = 0;

        // allocate a node in the global heap
        auto storage = allocate!NodeStorage;
        if (storage == null) return null;
        scope(exit) if (error) deallocate(storage);
        auto newNode = &storage.node.as!kind;

        // initialize and register the newly inserted node
        error = NodeType.initialize(newNode, forward!args);
        if (error) return null;
        scope(exit) if (error) NodeType.dispose(newNode);
        error = (this.nursery[storage] = true);
        if (error) return null;

        return newNode;
    }

    /// ditto
    pragma(inline) JoinNode* insert(NodeSugar sugar : NodeSugar.JoinNodeSingleChannel)(
        uint argc
    ) {
        uint[1] ms = [argc];
        return this.insert!(NodeKind.JoinNode)(ms[]);
    }

    /++
    Inserts a user-initialized node in the transaction.

    The unsafe prefix signals that correct usage of this method depends on how the node's memory is managed.
    In particular, every unsafely-inserted node must still be alive by the time the transaction commits, and its contents must not be mutated after that happens.
    Freeing memory that's backing the node itself (not its contents!) is still the user's responsibility.

    Returns:
        Zero on success, non-zero on failure (OOM).
    +/
    pragma(inline) err_t unsafeInsert(Node* node) in (node != null) {
        return (this.nursery[NodeStorage.ofNode(node)] = false);
    }

    /++
    Links two edge slots during a transaction.

    Nodes which existed prior to this transaction can ONLY be updated through this method.
    NOTE: The updated out-edge's slot kind will be automatically set to match `to`'s'.

    Params:
        node = Node being updated.
        index = Required when the field is only accessible through an indirection.
        to = Target in-edge slot.

    Returns:
        Non-zero in case of failure (e.g. OOM or detected U.B. such as updating nodes from another transaction).
    +/
    err_t update(string member, NodeType)(NodeType* node, InEdge* to)
    if (is(typeof(mixin(`node.` ~ member)) == OutEdge))
    {
        // safety check: a transaction can only update its own nodes
        if (NodeStorage.ofNode(node.asNode) !in this.nursery
         || NodeStorage.ofNode(to.owner) !in this.nursery
        ) {
            version (assert) assert(false, "tried to update a node from another transaction");
            else return EACCES;
        }
        // TCC: how do we update edges linking to/from outside the nursery?

        auto link = OutEdge(to.kind, to);
        mixin(`node.` ~ member ~ ` = link;`);
        return 0;
    }

    /// ditto
    pragma(inline) err_t update(string member, NodeType)(NodeType* node, ref InEdge to) {
        return update!member(node, &to);
    }

    /// ditto
    err_t update(string member, NodeType)(NodeType* node, size_t index, InEdge* to)
    if (__traits(compiles, mixin(`node.` ~ member ~ `[index] = OutEdge.init`)))
    {
        if (NodeStorage.ofNode(node.asNode) !in this.nursery
         || NodeStorage.ofNode(to.owner) !in this.nursery
        ) {
            version (assert) assert(false, "tried to update a node from another transaction");
            else return EACCES;
        }

        auto link = OutEdge(to.kind, to);
        alias FieldType = typeof(mixin(`node.` ~ member));
        static if (is(FieldType == UnsafeHashMap!(ulong, OutEdge))) {
            return mixin(`node.` ~ member ~ `[index] = link`);
        } else {
            static assert(is(FieldType == OutEdge[]));
            mixin(`node.` ~ member ~ `[index] = link;`);
            return 0;
        }
    }

    /// ditto
    pragma(inline) err_t update(string member, NodeType)(NodeType* node, size_t index, ref InEdge to) {
        return update!member(node, index, &to);
    }

    /++
    Finishes the transaction by applying its changes.

    Returns:
        Zero on success, non-zero otherwise (in which case the transaction must be [abort]ed).

    Version:
        NOTE: Technically speaking, this operation is not transactional; on OOM conditions the graph may be left in an incomplete/invalid state. This is OK under a ["worse is better"](https://www.dreamsongs.com/RiseOfWorseIsBetter.html) philosophy.
    +/
    err_t commit() {
        // TCC: validate nodes and check IR rules BEFORE mutating anything

        // compute how much space we need and how much we have available
        const neededSpace = this.nursery.length;
        assert(this.graph.cursor <= this.graph.arena.length);
        const freeSpace = this.graph.arena.length - this.graph.cursor;
        if (freeSpace < neededSpace) {
            version (assert) assert(false, "TCC: implement garbage collection");
            else return ENOMEM;
        }

        // rewires an out-edge to the right slot of another stored node
        void rewire(ref OutEdge outEdge, NodeStorage* storage)
        out (; outEdge.target != null)
        {
            outEdge.target = storage.asNode.opIndex(outEdge.target.id);
        }

        // registers the second node as an in-neighbor of the first
        err_t registerInNeighbor(Node* node, Node* inNeighbor) {
            auto outNeighbor = Graph.HashableNode(node);
            Graph.HashableNode* found;
            Graph.InNeighbors* inNeighbors;
            this.graph.adjacencies.get(outNeighbor, found, inNeighbors);
            assert(found);
            return inNeighbors.add(inNeighbor);
        }

        // mapping of transaction-owned addresses to graph-owned addresses
        alias TLB = UnsafeHashMap!(NodeStorage*, NodeStorage*);

        // recursively adds nodes to the graph, assuming IR rules are respected
        NodeStorage* depthFirstAdd(ref TLB transfers, NodeStorage* original) @nogc nothrow {
            // first, let's make sure we never process the same node twice
            auto mapping = transfers[original];
            if (mapping != null) return mapping;
            const bool isJoinNode = JoinNode.ofNode(original.asNode) != null;

            // try to go deeper by visiting this node's out-neighbors
            // (except on join nodes, since they are allowed to induce cycles)
            if (!isJoinNode) {
                foreach (ref outEdge; original.outEdges) {
                    auto outNeighbor = NodeStorage.ofNode(outEdge.target.owner);
                    // we'll only recurse if the out-neighbor's also in the nursery
                    if (outNeighbor !in this.nursery) continue;
                    auto newNeighbor = depthFirstAdd(transfers, outNeighbor);
                    if (newNeighbor == null) return null;
                    // then, rewire this node's out-edge to its updated neighbor
                    rewire(outEdge, newNeighbor);
                }
            }

            // this node is now stable, so we can hash it and add it to the graph
            original.asNode.updateHash();
            auto transferred = this.graph.add(original);
            if (transferred == null) return null;
            transfers[original] = transferred;

            // since we now know this node's stable address in the graph, we can
            // add it to the in-neighbor set of each of its out-neighbors
            if (!isJoinNode) {
                foreach (ref outEdge; transferred.outEdges) {
                    auto outNeighbor = outEdge.target.owner;
                    const error = registerInNeighbor(outNeighbor, transferred.asNode);
                    if (error) return null;
                }
            }

            return transferred;
        }

        // set up DFS bookkeeping data structures
        TLB transfers;
        auto error = transfers.rehash(this.nursery.length);
        scope(exit) transfers.dispose();
        if (error) return ENOMEM;
        // then trigger the recursions
        foreach (storage; this.nursery.byKey) {
            auto added = depthFirstAdd(transfers, storage);
            if (!added) {
                // I don't really know how to handle a mid-commit error in such
                // a way as to make it an all-or-nothing operation. Thus, if this
                // ever happens, the commited subgraph may be left in an incomplete
                // state. This is probably not as bad as it sounds; because we
                // check IR rules before starting this loop, mid-commit errors mean
                // an OOM condition, where there's not much that can be done anyway
                version (assert) assert(false, "mid-commit error (out of memory)");
                else return ENOMEM;
            }
        }

        // since we treat join nodes differently in the DFS, we now have to ensure that
        // their edges were rewired and that they have been registered as in-neighbors
        foreach (NodeStorage* storage; transfers.byValue) {
            JoinNode* join = JoinNode.ofNode(storage.asNode);
            if (join == null) continue;
            foreach (ref outEdge; join.outEdges) {
                Node* outNeighbor = outEdge.target.owner;
                // pointers into the nursery need to be rewired
                if (auto key = NodeStorage.ofNode(outNeighbor) in this.nursery) {
                    rewire(outEdge, transfers[*key]);
                    outNeighbor = outEdge.target.owner;
                }
                // now we make sure the join is registered as an in-neighbor
                error = registerInNeighbor(outNeighbor, join.asNode);
                if (error) {
                    version (assert) assert(false, "mid-commit error (out of memory)");
                    else return error;
                }
            }
        }

        // TCC: peephole optimizations

        // after this transaction's contents have been copied, we can finish it
        this.abort();
        return 0;
    }
}

///
@nogc nothrow unittest {
    import gyre.mnemonics;

    Graph graph;
    graph.initialize(MacroNode.ID(42));
    scope(exit) graph.dispose();

    assert(graph.id == 42);
    assert(graph.length == 0);
    assert(graph.exported == 0);
    assert(graph.imported == 0);

    // manual memory management is still possible
    auto a = allocate!AdditionNode;
    scope(exit) deallocate(a);

    // while compiling something like
    //    foo(return, x) {
    //        a = x + 1
    //        b = 1 + x
    //        y = a / b
    //        return(y)
    //    }
    with (Transaction(graph))
    {
        begin;

        auto foo = insert!func(2);
        auto jump = insert!jump(1);
        auto y = insert!divu;
        AdditionNode.initialize(a);
        unsafeInsert(a.asNode);
        auto b = insert!add;
        auto c1 = insert!const_(1);

        auto params = foo.channels[0];
        auto ret = &params[0];
        auto x = &params[1];

        // export_(foo.definition);
        update!"control"(foo, jump.control);

        update!"continuation"(jump, ret);
        update!"arguments"(jump, 0, y.quotient);

        update!"dividend"(y, a.result);
        update!"divisor"(y, b.result);

        update!"lhs"(a, x);
        update!"rhs"(a, c1.value);

        update!"lhs"(b, c1.value);
        update!"rhs"(b, x);

        commit;
    }

    // one of the additions was optimized away
    assert(graph.length == 5);
    // assert(graph.exported == 1);
}
