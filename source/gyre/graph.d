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

import core.stdc.errno : ENOMEM, EOVERFLOW;
import core.lifetime : forward, copyEmplace, move;
import std.meta : AliasSeq, Filter;
import std.traits : EnumMembers, Fields, Parameters;

import eris.core : err_t, allocate, deallocate;
import eris.util : HashablePointer;
import eris.hash_table : UnsafeHashMap, UnsafeHashSet;

import betterclist : List;

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
            assert(false, "unreachable (probably tried to use a node with a broken heart)");
        }

        pragma(inline) inout(Node)* asNode() inout pure
        return // XXX: fuck v2.100.0
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
            if (this.asNode.isForwarding) return;
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

// rewires an out-edge to the right slot of another stored node
private @nogc nothrow pure
void rewire(ref OutEdge outEdge, NodeStorage* storage)
out (; outEdge.target != null)
{
    outEdge.target = storage.asNode.opIndex(outEdge.target.id);
}


/++
Graph structure storing a Gyre (sub)program.

Any such graph could also be used as the definition of an associated [MacroNode|macro node].


Version:
    NOTE: Every graph manages memory for its own nodes and edges, which in turn cannot be safely shared with the outside world.
    Due to our representation, internal graph storage will probably resemble a spaghetti of pointers, and if a node (or edge slot!) ever moves in memory, we'll need to fix every pointer which referenced it.
    As a result, relocations are expensive, and in the worst case we could be moving the entire graph (e.g. if we need to expand our backing memory arena).
    Since references may need to be adjusted anyway, we might as well keep related nodes close to each other, improving locality while we're at it.
    In the end, we'll implement something similar to a moving mark-and-sweep GC over a private memory pool.

See_Also: [Subgraph]
+/
struct Graph {
 private:
    // map of generic nodes (used for structural sharing) => in-neighbor sets,
    // where any reference held here must point into this graph's arena
    UnsafeHashMap!(HashConsedNode, InNeighbors) adjacencies;
    alias HashConsedNode = HashablePointer!Node;
    alias InNeighbors = UnsafeHashSet!(Node*);

    // corresponds to the notion of a "top-level". also used as a GC root:
    // any subgraph not reachable from this node's inteface is considered dead
    MacroNode topLevel;
    uint _exported; // number of actually exported definitions

    // backing memory pool for this graph's nodes (all except the topLevel)
    NodeStorage[] arena;
    size_t cursor; // bump allocator index for the arena

 public @nogc nothrow:
    /// This graph's unique identifier.
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
    @property size_t length() const pure
    out (used; used <= this.arena.length)
    {
        return this.adjacencies.length;
    }

    // TCC: register imports and exports

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

    /++
    Destructively merges another graph into this one.

    Returns: Zero on success, non-zero on failure.
    +/
    err_t merge(ref Graph consumed) {
        // this total is actually a conservative estimate due to hash consing
        const total = this.cursor + consumed.cursor;
        if (total < this.cursor) return EOVERFLOW;

        // unhappy case: the arena can NOT fit both graphs, which we handle by
        // creating a bigger third graph and merging the other two into it
        if (this.arena.length < total) {
            // the new graph has the sum of the previous' capacities, and then some
            size_t capacity = this.arena.length + consumed.arena.length;
            capacity = cast(size_t)(capacity * 1.618);
            if (capacity < total) return EOVERFLOW;
            Graph newGraph;
            auto error = Graph.initialize(
                this.id,
                this.exported + consumed.exported,
                this.imported + consumed.imported,
                capacity
            );
            if (error) return error;

            // we must also substitute this graph for the bigger one
            error = newGraph.merge(this);
            if (error) {
                newGraph.dispose();
                return error;
            }
            this.dispose();
            move(newGraph, this);
            return this.merge(consumed);
        }

        // since node hashes don't depend on their physical addresses, we "only"
        // need to deal with the moving GC, and not hash cache invalidation issues.
        //
        // the GC itself does precise mark & sweep, where we use the forwading bit
        // on every node to signal whether its been visited already or not.
        // after visiting a node, we'll set that bit and leave the node with a
        // "broken heart", a forwarding pointer which leads us to its new place.
        //
        // also, since we're moving nodes, we might as well improve locality of
        // future traversals, so we do them in "root-first-depth-second" order

        // since we're going depth-first, we'll use a stack to hold grey objects
        // also, we assert that OOM doesn't happen because we can't deal with it
        alias Stack = List!(NodeStorage*);
        void grow(ref Stack stack) {
            size_t newCapacity = stack.capacity == 0 ? 8 : stack.capacity * 2;
            assert(newCapacity > stack.capacity);
            auto memory = allocate!(NodeStorage*)(newCapacity);
            assert(memory != null);
            auto newStack = Stack(memory);
            foreach (x; stack) {
                const failed = newStack.push(x);
                assert(!failed);
            }
            stack.array.deallocate();
            move(newStack, stack);
        }
        void forcePush(ref Stack stack, NodeStorage* node) { // no midi-chlorians required
            if (stack.full) grow(stack);
            const failed = stack.push(node);
            assert(!failed);
        }
        NodeStorage* pop(ref Stack stack) {
            auto popped = stack[$ - 1];
            stack.pop();
            return popped;
        }

        // step 0: when we begin, all objects are white
        auto stack = Stack(allocate!(NodeStorage*)(consumed.exported));
        if (consumed.exported > 0 && stack.array == null) return ENOMEM;
        scope(exit) stack.array.deallocate();

        // step 1: color all roots grey
        foreach (outEdge; consumed.topLevel.outSlots[0 .. consumed.exported]) {
            auto root = outEdge.target.owner;
            assert(!root.wasVisited && !root.isForwarding);
            root.wasVisited = true;
            forcePush(stack, NodeStorage.ofNode(root));
        }

        // step 2: mark phase darkens all grey objects and what they can reach
        auto addedBegin = this.cursor;
        while (!stack.empty) {
            // we always pop a grey object from the stack
            auto oldStorage = pop(stack);
            auto oldNode = oldStorage.asNode;
            assert(oldNode.wasVisited && !oldNode.isForwarding);

            // darkening it means it goes black, which translates to
            // moving it into the graph and setting up its forwading pointer
            bool wasRedundant = false;
            auto newStorage = this.add(oldStorage, wasRedundant);
            assert(newStorage != null);
            // avoid leaking dynamic node payloads when hash consing kicks in.
            // this does not lead to double frees because of the GC move mark
            if (wasRedundant) {
                oldStorage.dispose();
                copyEmplace(*newStorage, *oldStorage);
            }
            oldNode.isForwarding = true;
            oldNode.forwardingPointer = newStorage.asNode;

            // now, we only mark *white* neighbors as grey, so as to avoid loops
            foreach (outEdge; newStorage.outEdges) {
                auto neighbor = outEdge.target.owner;
                if (neighbor.wasVisited) continue;
                neighbor.wasVisited = true;
                forcePush(stack, NodeStorage.ofNode(neighbor));
            }
        }
        auto addedEnd = this.cursor;

        // step 3: extra pass through transferred nodes to adjust pointers
        foreach (i; addedBegin .. addedEnd) {
            auto storage = &this.arena[i];

            // when we add nodes to the graph, their grey bit is copied.
            // we know it must be set, and we use this moment to unset it
            auto node = storage.asNode;
            assert(node.wasVisited && !node.isForwarding);
            node.wasVisited = false;

            // all of its out-neighbors were transfered as well, so we chase
            // outgoing pointers in order to adjust edges and in-neighbor sets
            foreach (ref outEdge; storage.outEdges) {
                auto outNeighbor = outEdge.target.owner;
                if (outNeighbor.isForwarding) {
                    outNeighbor = outNeighbor.forwardingPointer;
                    rewire(outEdge, NodeStorage.ofNode(outNeighbor));
                }
                const error = this.registerInNeighbor(outNeighbor, node);
                assert(!error);
            }
        }

        // TCC: before sweeping, we need to adjust imports and exports...

        // step 4: the "sweep" phase happens when we free the consumed graph
        // (notice that NodeStorage.dispose() takes moved nodes into account)
        consumed.dispose();
        return 0;
    }

 private:
    // shallow copy a node into the graph in case there's space for it,
    // returning the resulting internal pointer (stable until the next GC)
    // NOTE: node structure must be stable and its hash already cached, which
    // implies its dependencies were already added (requires a topological sort)
    NodeStorage* add(NodeStorage* temp, out bool redundant)
    in (!temp.asNode.isForwarding, "nodes added to the graph must be valid")
    {
        if (this.cursor >= this.arena.length) return null;

        // abort the node in case an equivalent one already exists in the graph
        {
            auto handle = const(HashConsedNode)(temp.asNode);
            HashConsedNode* existing;
            InNeighbors* neighbors;
            const found = this.adjacencies.get(handle, existing, neighbors);
            if (found) {
                assert(existing != null);
                redundant = true;
                return NodeStorage.ofNode(existing.ptr);
            }
        }

        // add the new node to the graph, with an empty set of in-neighbors
        NodeStorage* newStorage = &this.arena[this.cursor];
        copyEmplace(*temp, *newStorage);
        newStorage.opPostMove(*temp);
        auto handle = HashConsedNode(newStorage.asNode);
        const error = (this.adjacencies[handle] = InNeighbors.init);
        if (error) return null;
        this.cursor++;

        return newStorage;
    }

    // registers the second node as an in-neighbor of the first
    err_t registerInNeighbor(Node* node, Node* inNeighbor)
    in (Graph.HashConsedNode(node) in this.adjacencies)
    {
        auto outNeighbor = Graph.HashConsedNode(node);
        Graph.HashConsedNode* found;
        Graph.InNeighbors* inNeighbors;
        this.adjacencies.get(outNeighbor, found, inNeighbors);
        return inNeighbors.add(inNeighbor);
    }
}

// TODO: expose a pass API over Graphs (check LLVM for inspiration)


/++
Temporary buffer used to add nodes to a [Graph].

Most operations on a graph involve adding multiple nodes at once.
This type does precisely that, while verifying IR rules, expanding graph memory as needed and wiring up in-neighbors correctly.
Last but not least: it will also perform "bread-and-butter" peephole optimizations (e.g. arithmetic simplification, constant folding and strength reduction) automatically.
+/
struct Subgraph {
 private:
    // temporary buffer for new nodes
    UnsafeHashSet!(NodeStorage*) nursery;

 public @nogc nothrow:
    /// Initializes a new subgraph with a certain number of preallocated nodes.
    this(size_t n) {
        this.reserve(n);
    }

    /// Ensures a certain number of preallocated nodes.
    err_t reserve(size_t n) {
        return this.nursery.rehash(n);
    }

    /// This type's resources get automatically deallocated on scope exit (and it's not copyable).
    ~this() {
        this.clearNursery!true;
        this.nursery.dispose();
    }
    @disable this(this);

    private void clearNursery(bool deep)() {
        foreach (storage; this.nursery.byKey) {
            static if (deep) storage.dispose();
            deallocate(storage);
        }
    }

    private alias InitParams(NodeType) = Parameters!(NodeType.initialize)[1 .. $];

    /++
    Allocates and initializes a new node.

    The new node's address is stable as long as this subgraph isn't merged.

    Returns: A pointer to the new node, which is `null` in case something went wrong (OOM or the provided arguments were rejected by the node's initializer).
    +/
    AllNodes[kind]* insert(NodeKind kind)(auto ref InitParams!(AllNodes[kind]) args) {
        alias NodeType = AllNodes[kind];
        err_t error = 0;

        // allocate a node in the global heap. its address is stable
        // OPT: performance-wise, we could do better with a pool chain; right now
        // we're hoping that malloc's implementation allocates small objects fast
        auto storage = allocate!NodeStorage;
        if (storage == null) return null;
        scope(exit) if (error) deallocate(storage);
        auto newNode = &storage.node.as!kind;

        // initialize and register the newly inserted node
        error = NodeType.initialize(newNode, forward!args);
        if (error) return null;
        scope(exit) if (error) NodeType.dispose(newNode);
        error = this.nursery.add(storage);
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
    Commits this subgraph into a parent graph.

    This is a destructive copy which empties the subgraph being commited.

    Returns: Zero on success, non-zero otherwise.
    +/
    err_t commit(ref Graph graph) {
        // TCC: validate nodes and check IR rules BEFORE mutating anything

        // compute how much space we need and how much we have available
        const neededSpace = this.nursery.length;
        const freeSpace = graph.arena.length - graph.cursor;

        // if the graph's private memory pool needs to grow, we'll do a GC cycle
        if (freeSpace < neededSpace) {
            auto capacity = cast(size_t)((graph.cursor + neededSpace) * 1.618);
            if (capacity < graph.cursor + neededSpace) return EOVERFLOW;
            Graph newGraph;
            auto error = newGraph.initialize(graph.id, graph.exported, graph.imported, capacity);
            if (error) return error;
            error = newGraph.merge(graph);
            if (error) {
                newGraph.dispose();
                return error;
            }
            move(newGraph, graph);
        }

        // set of nodes which still need fixing after the depth-first traversal
        UnsafeHashSet!(JoinNode*) joinNodes;
        scope(exit) joinNodes.dispose();

        // recursively adds nodes to the graph, assuming IR rules are respected
        NodeStorage* depthFirstAdd(NodeStorage* original) @nogc nothrow {
            // first, let's make sure we never process the same node twice
            Node* oldNode = original.asNode;
            if (oldNode.isForwarding) return NodeStorage.ofNode(oldNode.forwardingPointer);
            const bool isJoinNode = JoinNode.ofNode(oldNode) != null;

            // try to go deeper by visiting this node's out-neighbors
            // (except on join nodes, since they are allowed to induce cycles)
            if (!isJoinNode) {
                foreach (ref outEdge; original.outEdges) {
                    auto outNeighbor = NodeStorage.ofNode(outEdge.target.owner);
                    // we'll only recurse if the out-neighbor's also in the nursery
                    if (outNeighbor !in this.nursery) continue;
                    auto newNeighbor = depthFirstAdd(outNeighbor);
                    assert(newNeighbor != null);
                    // then, rewire this node's out-edge to its updated neighbor
                    rewire(outEdge, newNeighbor);
                }
            }

            // this node is now stable, so we can hash it and add it to the graph
            original.asNode.updateHash();
            bool wasRedundant = false;
            auto transferred = graph.add(original, wasRedundant);
            assert(transferred != null);
            Node* newNode = transferred.asNode;
            // small detail: if hash consing reveals that this node is redundant,
            // we have to deallocate its payload here to avoid leaks and then
            // shallow-copy the existing node into it. this does NOT lead to payload
            // double frees, but only because we're marking the node as moved
            if (wasRedundant) {
                original.dispose();
                copyEmplace(*transferred, *original);
            }
            oldNode.isForwarding = true;
            oldNode.forwardingPointer = newNode;
            // sanity check: the old node has a broken heart, not the new one
            assert(newNode.isForwarding == false);

            // since we now know this node's stable address in the graph, we can
            // add it to the in-neighbor set of each of its out-neighbors
            if (!isJoinNode) {
                foreach (ref outEdge; transferred.outEdges) {
                    auto outNeighbor = outEdge.target.owner;
                    const error = graph.registerInNeighbor(outNeighbor, newNode);
                    assert(!error);
                }
            } else {
                JoinNode* join = JoinNode.ofNode(newNode);
                assert(join != null);
                const error = joinNodes.add(join);
                assert(!error);
            }

            return transferred;
        }

        // this loops triggers the recursions
        foreach (storage; this.nursery.byKey) {
            auto added = depthFirstAdd(storage);
            // I don't really know how to handle a mid-commit error in such
            // a way as to make it an all-or-nothing operation. Thus, if this
            // ever happens, the commited subgraph may be left in an incomplete
            // state. This is probably not as bad as it sounds; because we
            // check IR rules before starting this loop, mid-commit errors mean
            // an OOM condition, where there's not much that can be done anyway
            assert(added != null);
        }

        // since we treated join nodes differently before, we now have to ensure that
        // their edges were rewired and that they have been registered as in-neighbors
        foreach (join; joinNodes.byKey) {
            foreach (ref outEdge; join.outEdges) {
                Node* outNeighbor = outEdge.target.owner;
                // some pointers may still need to be rewired
                if (outNeighbor.isForwarding) {
                    outNeighbor = outNeighbor.forwardingPointer;
                    rewire(outEdge, NodeStorage.ofNode(outNeighbor));
                }
                // and we must ensure the join is registered as an in-neighbor
                const error = graph.registerInNeighbor(outNeighbor, join.asNode);
                assert(!error);
            }
        }

        // if nodes were transferred successfully, we can free the nursery. but we
        // only free node storage, not payloads (which are being reused by the graph)
        this.clearNursery!false;
        this.nursery.clear();

        // TCC: peephole optimizations

        return 0;
    }
}

///
@nogc nothrow unittest {
    import gyre.mnemonics;

    Graph graph;
    graph.initialize(MacroNode.ID(42), 1, 1);
    scope(exit) graph.dispose();

    assert(graph.id == 42);
    assert(graph.exported == 0);
    assert(graph.imported == 1);
    assert(graph.length == 0);

    // while compiling something like
    //    foo(return, x) {
    //        a = x + 1
    //        b = 1 + x
    //        y = a / b
    //        return(y)
    //    }
    with (Subgraph(8)) {
        auto foo = insert!func(2);
        auto jmp = insert!jump(1);
        auto y = insert!divu;
        auto a = insert!add;
        auto b = insert!add;
        auto c1 = insert!const_(1);

        auto params = foo.channels[0];
        auto ret = &params[0];
        auto x = &params[1];

        // export_(foo.definition);
        foo.control.target = &jmp.control;

        jmp.continuation.target = ret;
        jmp.arguments[0].target = &y.quotient;

        y.dividend.target = &a.result;
        y.divisor.target = &b.result;

        a.lhs.target = x;
        a.rhs.target = &c1.value;

        b.lhs.target = &c1.value;
        b.rhs.target = x;

        // these have a dynamic payload, but are subject to hash consing, so ...
        // do both payloads get deallocated correctly after structural sharing?
        auto deadCode1 = insert!mux(2);
        deadCode1.selector.target = &c1.value;
        deadCode1.inputs[0] = OutEdge.data(x);
        deadCode1.inputs[1] = OutEdge.data(&c1.value);
        auto deadCode2 = insert!mux(2);
        deadCode2.selector.target = &c1.value;
        deadCode2.inputs[0] = OutEdge.data(x);
        deadCode2.inputs[1] = OutEdge.data(&c1.value);

        commit(graph);
    }

    // one of the additions was optimized away
    assert(graph.length == 6);

    // assert(graph.exported == 1);
}
