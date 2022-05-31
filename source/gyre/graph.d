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

import core.stdc.errno : ENOMEM, EINVAL, EACCES;
import core.lifetime : forward;
import std.meta : AliasSeq, Filter;
import std.traits : EnumMembers, Fields, Parameters, isArray, Unconst, isPointer;

import eris.core : err_t, allocate, deallocate;
import eris.util : HashablePointer;
import eris.hash_table : UnsafeHashMap, UnsafeHashSet;

import gyre.nodes;


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
                NodeStorage.node.offsetof == 0,
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

    // backing memory pool for this graph's nodes (all except the topLevel)
    NodeStorage[] arena;

    // bump allocator index, either at the first free slot or `== arena.length`
    // such that all in-use storage slots are to the left of the cursor
    size_t cursor;

 public @nogc nothrow:
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
    // copies a node into the graph in case there's space for it, returning the internal pointer
    // NOTE: node structure must be stable and its hash already cached (and it must not depend on the node's address)
    Node* add(NodeStorage* temp)
    in (temp != null && this.cursor < this.arena.length)
    {
        if (temp == null) return null;
        if (this.cursor >= this.arena.length) return null;

        // abort the node in case an equivalent one already exists in the graph
        {
            auto handle = const(HashableNode)(temp.asNode);
            HashableNode* existing;
            InNeighbors* neighbors;
            const found = this.adjacencies.get(handle, existing, neighbors);
            if (found) {
                assert(existing != null);
                return *existing;
            }
        }

        // add the new node to the graph, with an empty set of in-neighbors
        NodeStorage* newStorage = &this.arena[this.cursor];
        *newStorage = *temp;
        newStorage.opPostMove(*temp);
        Node* newNode = newStorage.asNode;
        const error = (this.adjacencies[HashableNode(newNode)] = InNeighbors.init);
        if (error) return null;
        this.cursor++;

        // TODO: register imports/exports

        return newNode;
    }
}

// TODO: add (and test) more public functionality to Graphs


/++
First-class representation of a graph operation.

Transactions are used to update a Gyre [Graph] in an "all-or-nothing" fashion while verifying IR rules, expanding graph memory as needed and wiring up in-neighbors correctly.
Last but not least: whenever a transaction commits, simple peephole optimizations (e.g. arithmetic simplification, constant folding and strength reduction) are performed automatically.

See_Also: [NodeHandle]
+/
struct Transaction {
 private:
    import std.bitmanip : taggedPointer;
    mixin(taggedPointer!(
        Graph*, "graph",
        bool, "began", 1
    ));

    // temporary buffer for new nodes
    NodeStorage[] nursery;
    size_t cursor;

 public @nogc nothrow:
    /// Creates a new transaction.
    this(ref Graph graph) pure {
        this.graph = &graph;
        this.began = false;
    }
    @disable this();

    /++
    Begins the transaction.

    All transactions which have begun must explicitly finish (successfully or otherwise).

    Params:
        n = Maximum number of added nodes (does not dynamically expand).

    Returns:
        Zero on success, non-zero otherwise (in which case the transaction fails to begin).

    See_Also: [commit], [abort]
    +/
    err_t begin(size_t n)
    in (!this.began, "tried to start a transaction which was already ongoing")
    out (error; error || this.began)
    {
        if (this.began) return EINVAL;

        this.nursery = allocate!NodeStorage(n);
        if (n > 0 && this.nursery == null) return ENOMEM;
        this.cursor = 0;

        this.began = true;
        return 0;
    }

    /// Finishes the transaction by cancelling it.
    void abort()
    in (this.began, "can't operate on an unstarted transaction")
    out (; !this.began)
    {
        if (!this.began) return;

        foreach_reverse (i; 0 .. this.cursor) {
            this.nursery[i].dispose();
        }
        this.nursery.deallocate();

        this = Transaction(*this.graph);
    }

    private alias InitParams(NodeType) = Parameters!(NodeType.initialize)[1 .. $];

    /++
    Inserts a node during an ongoing transaction.

    Returns:
        A [NodeHandle|handle] to the inserted node, which `isNull` in case something went wrong (OOM).
    +/
    NodeHandle!kind insert(NodeKind kind)(auto ref InitParams!(AllNodes[kind]) args)
    in (this.began, "can't operate on an unstarted transaction")
    {
        alias NodeType = AllNodes[kind];
        enum nil = NodeHandle!kind(null, -1);
        static assert(nil.isNull);

        if (!this.began) return nil;

        // the nursery doesn't expand, so we give up if it would overflow
        // TODO: actually, we could make it grow by packing node+slot indexes into pointers
        if (this.cursor >= this.nursery.length) return nil;

        // grab the first available slot and in-place initialize the node there
        NodeStorage* storage = &this.nursery[this.cursor];
        auto error = NodeType.initialize(&storage.node.as!kind, forward!args);
        if (error) return nil;

        auto newNode = NodeHandle!kind(&this, this.cursor);
        this.cursor++;
        return newNode;
    }

    /// ditto
    NodeHandle!(NodeKind.JoinNode) insert(NodeSugar sugar : NodeSugar.JoinNodeSingleChannel)(
        uint argc
    ) {
        uint[1] ms = [argc];
        return this.insert!(NodeKind.JoinNode)(ms[]);
    }

    /++
    Links two edge slots during a transaction.

    Pointers in our safe [NodeHandle|handles] can only be updated through this method.
    NOTE: `from`'s edge kind will be automatically set to match `to`'s', so slot kind mismatches are not cheked here.

    Params:
        from = Out-edge slot being updated.
        to = Target in-edge slot.

    Returns:
        Zero on success, non-zero on failure (e.g. invalid parent transaction).
    +/
    err_t update(A, B)(A from, B to)
    if (is(A.FieldType == OutEdge) && is(B.FieldType == InEdge))
    in (this.began, "can't operate on an unstarted transaction")
    {
        if (!this.began) return EINVAL;

        // yet another wrapper type, this time to provide a unified field interface
        struct UnifiedField(T) {
            enum kind = T.HandleType.kind;
            enum string name = T.field;

            T wrapper;

            static if (is(T == NodeHandle!kind.DirectField!name)) {
                @property auto handle() inout { return wrapper.handle; }
                template get(string self) {
                    enum get =
                        self ~ ".node." ~ name;
                }
            } else static if (is(T == NodeHandle!kind.SingleIndexedField!name)) {
                @property auto handle() inout { return wrapper.base.handle; }
                template get(string self) {
                    enum get =
                        self ~ ".node." ~ name
                        ~ "[" ~ self ~ ".wrapper.index]";
                }
            } else {
                static assert(is(T == NodeHandle!kind.DoubleIndexedField!name));
                @property auto handle() inout { return wrapper.base.base.handle; }
                template get(string self) {
                    enum get =
                        self ~ ".node." ~ name
                        ~ "[" ~ self ~ ".wrapper.base.index]"
                        ~ "[" ~ self ~ ".wrapper.index]";
                }
            }

            @property auto ref node() {
                return this.handle.owner.nursery[this.handle.index].node.as!kind;
            }
        }

        auto fromField = UnifiedField!A(from);
        enum outSlot = UnifiedField!A.get!q{fromField};
        auto toField = UnifiedField!B(to);
        enum inSlot = UnifiedField!B.get!q{toField};

        // safety check: a transaction can only update its own nodes
        if (fromField.handle.owner != &this || toField.handle.owner != &this) {
            version (assert) assert(false, "tried to update a node from another transaction");
            else return EACCES;
        }
        // TODO: how do we update edges linking to/from outside the nursery?

        // do the actual edge slot linking (which may fail in case of a hashmap insert)
        auto link = OutEdge(to.kind, &mixin(inSlot));
        static if (is(A.HandleType == UnsafeHashMap!(ulong, OutEdge))) {
            err_t error = (mixin(outSlot ~ `= link`));
        } else {
            mixin(outSlot ~ `= link;`);
            err_t error = 0;
        }
        if (error) return error;

        return error;
    }

    /++
    Finishes the transaction by applying its changes.

    Returns:
        Zero on success, non-zero otherwise (in which case the transaction must be [abort]ed).

    Version:
        NOTE: Technically speaking, this operation is not transactional; on OOM conditions the graph may be left in an incomplete/invalid state. This is OK under a ["worse is better"](https://www.dreamsongs.com/RiseOfWorseIsBetter.html) philosophy.
    +/
    err_t commit()
    in (this.began, "can't operate on an unstarted transaction")
    out (error; error || !this.began)
    {
        if (!this.began) return EINVAL;
        // TODO: validate nodes and check IR rules BEFORE mutating anything

        // compute how much space we need and how much we have available
        assert(this.cursor <= this.nursery.length);
        const neededSpace = this.cursor;
        assert(this.graph.cursor <= this.graph.arena.length);
        const freeSpace = this.graph.arena.length - this.graph.cursor;
        if (freeSpace < neededSpace) {
            version (assert) assert(false, "TODO: implement garbage collection");
            else return ENOMEM;
        }

        // finds out whether a reference points into the nursery
        NodeStorage* inNursery(Node* node) {
            auto ptr = NodeStorage.ofNode(node);
            const min = &this.nursery[0];
            const max = &this.nursery[this.cursor - 1];
            return min <= ptr && ptr <= max ? ptr : null;
        }

        // rewires an out-edge to the right slot of a stored node
        void rewire(ref OutEdge outEdge, NodeStorage* storage)
        in (outEdge.target != null && storage != null)
        out (; outEdge.target != null)
        {
            outEdge.target = storage.asNode.opIndex(outEdge.target.id);
        }

        // registers the second node as an in-neighbor of the first
        err_t registerInNeighbor(Node* node, Node* inNeighbor)
        in (Graph.HashableNode(node) in this.graph.adjacencies)
        {
            auto outNeighbor = Graph.HashableNode(node);
            Graph.HashableNode* found;
            Graph.InNeighbors* inNeighbors;
            this.graph.adjacencies.get(outNeighbor, found, inNeighbors);
            assert(found);
            const error = inNeighbors.add(inNeighbor);
            return error;
        }

        // recursively adds nodes to the graph, assuming IR rules are respected
        NodeStorage* depthFirstAdd(NodeStorage*[] transfers, size_t index) @nogc nothrow {
            // first, let's make sure we never process the same node twice
            if (transfers[index] != null) return transfers[index];
            NodeStorage* original = &this.nursery[index];
            const bool isJoinNode = JoinNode.ofNode(original.asNode) != null;

            // try to go deeper by visiting this node's out-neighbors
            // (except on join nodes, since they are allowed to induce cycles)
            if (!isJoinNode) {
                foreach (ref outEdge; original.outEdges) {
                    Node* outNeighbor = outEdge.target.owner;
                    auto nextStorage = inNursery(outNeighbor);
                    // we'll only recurse if the out-neighbor's also in the nursery
                    if (nextStorage == null) continue;
                    const size_t nextIndex = nextStorage - &this.nursery[0];
                    NodeStorage* newNeighbor = depthFirstAdd(transfers, nextIndex);
                    if (newNeighbor == null) return null;
                    // then, rewire this node's out-edge to its updated neighbor
                    rewire(outEdge, newNeighbor);
                }
            }

            // this node is now stable, so we can hash it and add it to the graph
            original.asNode.updateHash();
            Node* added = this.graph.add(original);
            if (added == null) return null;
            transfers[index] = NodeStorage.ofNode(added);

            // since we now know this node's stable address in the graph, we can
            // add it to the in-neighbor set of each of its out-neighbors
            if (!isJoinNode) {
                foreach (ref outEdge; transfers[index].outEdges) {
                    auto outNeighbor = outEdge.target.owner;
                    const error = registerInNeighbor(outNeighbor, added);
                    if (error) return null;
                }
            }

            return transfers[index];
        }

        // set up DFS bookkeeping data structures
        NodeStorage*[] transfers = allocate!(NodeStorage*)(this.cursor);
        scope(exit) transfers.deallocate();
        if (this.cursor > 0 && transfers == null) return ENOMEM;
        foreach (ref forwardingPointer; transfers) forwardingPointer = null;
        // then trigger the recursions
        foreach (i; 0 .. this.cursor) {
            auto added = depthFirstAdd(transfers, i);
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
        foreach (NodeStorage* storage; transfers) {
            JoinNode* join = JoinNode.ofNode(storage.asNode);
            if (join == null) continue;
            foreach (ref outEdge; join.outEdges) {
                Node* outNeighbor = outEdge.target.owner;
                // pointers into the nursery need to be rewired
                if (auto neighborInNusery = inNursery(outNeighbor)) {
                    const size_t neighborIndex = neighborInNusery - &this.nursery[0];
                    rewire(outEdge, transfers[neighborIndex]);
                    outNeighbor = outEdge.target.owner;
                }
                // now we make sure the join is registered as an in-neighbor
                const error = registerInNeighbor(outNeighbor, join.asNode);
                if (error) {
                    version (assert) assert(false, "mid-commit error (out of memory)");
                    else return error;
                }
            }
        }

        // TODO: peephole optimizations

        // after this transaction's contents have been copied, we can finish it
        this.cursor = 0;
        this.abort();
        return 0;
    }
}

///
@nogc nothrow unittest {
    import gyre.mnemonics;

    Graph graph;
    graph.initialize(42);
    scope(exit) graph.dispose();

    assert(graph.length == 0);

    // while compiling something like
    //    foo(return, x) {
    //        a = x + 1
    //        b = 1 + x
    //        y = a / b
    //        return(y)
    //    }
    with (Transaction(graph)) {
        begin(6);
        {
            // insertion order does not matter ...
            auto a = insert!add;
            auto b = insert!add;
            auto foo = insert!func(2);
            auto c1 = insert!const_(1);
            auto y = insert!divu;
            auto jump = insert!jump(1);

            // ... as long as the graph is set up correctly
            auto params = foo.channels[0];
            auto ret = params[0];
            auto x = params[1];

            update(a.lhs, x);
            update(a.rhs, c1.value);

            update(b.lhs, c1.value);
            update(b.rhs, x);

            update(foo.control, jump.control);

            update(y.dividend, a.result);
            update(y.divisor, b.result);

            update(jump.continuation, ret);
            update(jump.arguments[0], y.quotient);
        }
        commit;
    }

    // b computes the same value as a, so it gets optimized away!
    assert(graph.length == 5);
}

@nogc nothrow unittest {
    import gyre.mnemonics;
    import gyre.nodes : Node, EdgeKind;

    Graph graph;
    graph.initialize(42);
    scope(exit) graph.dispose();

    NodeHandle!(NodeKind.MultiplicationNode).DirectField!"lhs" laterInvalid;
    with (Transaction(graph)) {
        begin(10);
        {
            auto mul = insert!mul;
            auto operand = mul.lhs;
            laterInvalid = operand;
            static assert(!__traits(compiles, {
                auto ptr = operand.target; // exposes inner ptr
            }));
            static assert(!__traits(compiles, {
                mul.updateHash(); // mutating methods can't be called
            }));
            auto mulp = mul.asNode(); // method on node
            auto h = operand.toHash(); // method on field

            auto mux = insert!mux(2);
            auto ins = mux.inputs; // single indexed access (hashtable)
            static assert(!__traits(compiles, {
                ins[0].kind = EdgeKind.control; // can't modify fixed kind
            }));

            auto foo = insert!func(2);
            auto params = foo.channels[0];
            auto x = params[0]; // double indexed access
            static assert(!__traits(compiles, {
                const cx = x;
                cx.kind = EdgeKind.data; // just because of the `const`
            }));

            auto jump = insert!jump(2);
            auto args = jump.arguments; // single indexed access (array)
            assert(args[0].kind == EdgeKind.data);
            args[0].kind = EdgeKind.memory; // jumps have mutable kind slots
            assert(args[0].kind == EdgeKind.memory);

            auto inst = insert!inst(1);
            update(inst.definition, foo.definition); // direct x direct
            update(jump.continuation, inst.continuations[0]); // direct x single
            update(mul.lhs, x); // direct x doubly-indexed

            update(args[1], mul.result); // single x direct
            update(ins[0], inst.continuations[0]); // single x single
            update(args[0], x); // single x double

            // this should have worked even if the outedge sits in a hashmap
            assert(ins._field[0].target == &inst.continuations._field[0]);
        }
        abort();
    }

    with (Transaction(graph)) {
        begin(1);
        {
            auto div = insert!divu;
            // update(laterInvalid, div.quotient); // runtime error

            auto oom = insert!divs;
            assert(oom.isNull);
        }
        abort();
    }
}


// our transactions need to track modification to any nodes they control (new or otherwise),
// in particular for the purpose of in-neighbor bookkeeping. in order to expose a safe API
// that's also fast & nice (it's an EDSL, really), we'll make heavy (ab)use of metaprogramming

private { // helper templates used below
    // whether we want to expose a member of a certain type
    // XXX: for some reason, `package` members (e.g. vptr) also pass this check
    template canAccess(Type, string member) {
        enum canAccess =
            __traits(hasMember, Type, member)
            && __traits(getVisibility, __traits(getMember, Type, member)) == "public"
            && !isPointer!(typeof(__traits(getMember, Type, member)));
    }

    // whether we want to wrap a given type for the purposes of our EDSL
    // NOTE: template must be kept in sync with fields exposed in gyre.nodes
    template needsWrapper(Type) {
        enum needsWrapper =
            is(Type : const(OutEdge))
            || is(Type : const(OutEdge[]))
            || is(Type : const(UnsafeHashMap!(ulong, OutEdge)))
            || is(Type : const(InEdge))
            || is(Type : const(InEdge[]))
            || is(Type : const(InEdge[][]));
    }

    // whether user code can mutate the kind of a certain edge slot field
    template canMutateSlotKind(NodeType, SlotType) {
        enum canMutateSlotKind =
            (is(NodeType == JoinNode) && is(SlotType == InEdge))
            || (is(NodeType == JumpNode) && is(SlotType == OutEdge))
            || is(NodeType == MacroNode);
    }
}

/++
Ephemeral node handle.

Instead of giving out pointers to nodes they manage, [Transaction]s use safer handles.
These allow users to address node fields in a type-safe manner, while prohibiting direct mutation.
Like pointers, handles are nullable to indicate the possibility of a missing value or failure case.
+/
struct NodeHandle(NodeKind _kind) {
 private:
    Transaction* owner;
    size_t index;

 @nogc nothrow:
    @property ref inout(NodeType) _node() inout pure {
        return this.owner.nursery[index].node.as!kind;
    }

 public:
    /// This handle's underlying node type.
    alias NodeType = AllNodes[kind];
    private enum kind = _kind;

    /// Indicates whether this is a valid node handle.
    bool isNull() const pure { return this.owner == null; }

    auto ref opDispatch(string member)() inout
    if (canAccess!(NodeType, member))
    in (!this.isNull, "can't use a null handle")
    {
        // certain field/property members need an extra wrapper
        alias T = typeof(mixin(`this._node.` ~ member));
        static if (needsWrapper!T)
            return inout(DirectField!member)(this);
        else
            return mixin(`this._node.` ~ member);
    }

 private:
    // first-class field handles help transactions when mutating actual fields
    struct DirectField(string name) {
     private:
        // every field wrapper needs these
        alias HandleType = NodeHandle;
        enum field = name;
        alias FieldType = Unconst!(typeof(this._field));

        NodeHandle handle;

     @nogc nothrow:
        @property auto ref _field() inout pure {
            return mixin(`this.handle._node.` ~ name);
        }

     public:
        // most, but not all, const member accesses work normally for field handles
        auto ref opDispatch(string member, Args...)(auto ref Args args) const
        if (canAccess!(FieldType, member) && member != "opIndex")
        {
            return mixin(`this._field.` ~ member)(forward!args);
        }

        // but indexing (if present on this field) may require extra work
        static if (isArray!FieldType || canAccess!(FieldType, "opIndex")) {
            auto ref opIndex(size_t index) inout pure {
                alias T = typeof(this._field[index]);
                static if (needsWrapper!T)
                    return inout(SingleIndexedField!name)(this, index);
                else
                    return this._field[index];
            }
        }
    }

    // indexed fields behave very much like direct fields, but with an extra indirection
    struct SingleIndexedField(string name) {
        mixin IndexedFieldBoilerplate!(DirectField!name);
        static if (isArray!FieldType || canAccess!(FieldType, "opIndex")) {
            auto ref opIndex(size_t index) inout pure {
                alias T = typeof(this._field[index]);
                static if (needsWrapper!T)
                    return inout(DoubleIndexedField!name)(this, index);
                else
                    return this._field[index];
            }
        }
    }

    // we only (need to) go two levels deep, so this is the last one, I promise
    struct DoubleIndexedField(string name) {
        mixin IndexedFieldBoilerplate!(SingleIndexedField!name);
    }

    // boilerplate for the comptime interface and dispatching of indexed fields
    mixin template IndexedFieldBoilerplate(BaseWrapper) {
     private:
        alias HandleType = NodeHandle;
        enum field = name;
        alias FieldType = Unconst!(typeof(this._field));

        BaseWrapper base;
        size_t index;

     @nogc nothrow:
        @property auto ref _field() inout pure {
            return mixin(`this.base._field`)[this.index];
        }

     public:
        // we *mostly* only allow const acces ...
        auto ref opDispatch(string member, Args...)(auto ref Args args) const
        if (canAccess!(FieldType, member) && member != "opIndex")
        {
            return mixin(`this._field.` ~ member)(forward!args);
        }

        // .. except for kind assignment on some edge slots
        auto ref opDispatch(string member)(EdgeKind kind)
        if (canAccess!(FieldType, member) && canMutateSlotKind!(HandleType.NodeType, FieldType))
        {
            return mixin(`this._field.` ~ member)(kind);
        }
    }
}
