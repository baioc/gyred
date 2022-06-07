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

import core.stdc.errno : ENOMEM, EOVERFLOW, EACCES;
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

    alias Unquote(Symbols...) = mixin(`AliasSeq!(` ~ JoinArgs!Symbols ~ `)`);

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
    enum isGyreNode(Type) =
        is(Type == struct)
        && __traits(hasMember, Type, "_node") && is(typeof(Type._node) == Node.CommonPrefix)
        && !is(Type == Node);

    enum isGyreNode(string symbol) = is(mixin(symbol)) && isGyreNode!(mixin(symbol));

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
    @mnemonic("call") InstantiationNodeSingleChannel, /// A single-channel [InstantiationNode].
    @mnemonic("if_") ConditionalNodeBinary, /// A binary [ConditionalNode|cond] (but remember that inputs are ordered, unlike LLVM's `br` instruction).
    @mnemonic("sel") MultiplexerNodeBinary, /// A binary [MultiplexerNode|mux] (but remember that inputs are ordered, unlike LLVM's `select` instruction).
}

// rewires an out-edge to a specific in-slot of a given stored node
// NOTE: the current pointed-to node must still be valid (not-freed) memory
private void rewire(ref OutEdge outEdge, NodeStorage* storage, InEdge.ID id) @nogc nothrow pure
out (; outEdge.target != null)
{
    outEdge.target = storage.asNode.opIndex(id);
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
    NodeStorage* _topLevel;
    List!OutEdge _exported; // actually exported definitions

    // backing memory pool for this graph's nodes (including the top-level)
    NodeStorage[] arena;
    size_t cursor; // bump allocator index for the arena

 @nogc nothrow:
    bool assertInitialized() const pure {
        assert(this._topLevel != null, "can't use an uninitialized graph");
        return true;
    }

    @property inout(MacroNode)* topLevel() inout pure
    return // XXX: fuck v2.100.0
    in (this.assertInitialized)
    {
        return &this._topLevel.node.asMacroNode;
    }

 public:
    @disable this(this);

    /// This graph's unique identifier.
    @property MacroNode.ID id() const pure in (this.assertInitialized) {
        return this.topLevel.id;
    }

    /// Number of definitions exported by this graph.
    @property uint exported() const pure in (this.assertInitialized) {
        return cast(uint)this.topLevel.outSlots.length;
    }

    /// Number of definitions imported by this graph.
    @property uint imported() const pure in (this.assertInitialized) {
        return cast(uint)this.topLevel.inSlots.length;
    }

    /// Number of unique nodes in the graph.
    @property size_t length() const pure
    out (used; used <= this.arena.length)
    {
        if (this.adjacencies.length == 0) return 0;
        return this.adjacencies.length - 1; // minus the toplevel
    }

    /++
    Initializes an empty Gyre graph, must be later [dispose]d to avoid leaking memory.

    Our graphs eliminate dead code automatically.
    Therefore, every top-level function (represented by a [JoinNode|join node]) must be "anchored" to the graph by having their `definition` slot linked to one of the graph's in-edge slots.
    Conceptually, this is as if these functions were being "exported" to code outside of this graph.
    Nodes which are not directly exported and aren't reachable by an exported node may be marked as dead code and silently eliminated.
    Similarly, a graph may also depend on external information (`type` parameters, for instance), in which case it needs to point to these "imported" definitions with its out-edge slots.

    Params:
        id = This graph's unique identifier.
        exports = Preallocated number of "exported" defs (or [InEdge|in-edge]s for [MacroNode|macro node] definitions).
        imports = Maximum number of "imported" defs (or [OutEdge|out-edge]s for [MacroNode|macro node] definitions).
        capacity = Number of nodes to preallocate.

    Returns:
        Zero on success, non-zero on failure (in which case the graph can't be safely used).
    +/
    err_t initialize(MacroNode.ID id, uint exports = 1, uint imports = 0, size_t capacity = 256) {
        err_t error = 0;
        scope(exit) if (error) this = Graph.init;

        // we need 1 extra slot in the arena for the top-level
        if (capacity == capacity.max) return EOVERFLOW;
        capacity += 1;

        // allocate backing memory pool and set up free index
        this.arena = allocate!NodeStorage(capacity);
        scope(exit) if (error) this.arena.deallocate();
        if (this.arena == null) return (error = ENOMEM);
        this.cursor = 0;

        // reserve some space for node handles
        error = this.adjacencies.rehash(1 + capacity/2);
        scope(exit) if (error) this.adjacencies.dispose();
        if (error) return error;

        // initialize top-level, but with swapped "ins" and "outs" due to how
        // our edges are directed. we'll essentially have our top-level work
        // as a pointer forwarding mechanism. eg: (def A) <-- [Graph(def B)] <-- (use B)
        // internally is ... [InEdge(import A) <- B <- OutEdge(export B)] ...
        this._topLevel = &this.arena[0];
        this.cursor = 1;
        error = MacroNode.initialize(this.topLevel, id, imports, 0);
        scope(exit) if (error) MacroNode.dispose(this.topLevel);
        if (error) return error;
        // exports are actually handled outside the node
        this._exported = List!OutEdge(allocate!OutEdge(exports));
        scope(exit) if (error) this._exported.array.deallocate();
        if (exports > 0 && this._exported.capacity == 0) return (error = ENOMEM);
        this.topLevel.outSlots = this._exported.usedSlice;

        // register the top-level as the first node in the graph
        this.topLevel.updateHash();
        auto topLevelHandle = HashConsedNode(this.topLevel.asNode);
        error = (this.adjacencies[topLevelHandle] = InNeighbors.init);
        if (error) return error;

        assert(!error);
        return error;
    }

    /// Frees all resources allocated by this graph and sets it to an uninitialized state.
    void dispose() {
        this._exported.array.deallocate();
        if (this._topLevel != null) this.topLevel.outSlots = null;

        foreach (ref inNeighbors; this.adjacencies.byValue) {
            inNeighbors.dispose();
        }
        this.adjacencies.dispose();

        assert(this.cursor <= this.arena.length);
        foreach (i; 0 .. this.cursor) {
            this.arena[i].dispose();
        }
        this.arena.deallocate();

        this = Graph.init;
    }

    /++
    Registers a new exported definition.

    One can only export definitions already within the graph.

    Returns: An index which identifies this export, or a negative error code.
    +/
    int export_(ref const(InEdge) definition)
    in (this.assertInitialized)
    out (index; index < 0 || this.topLevel.outSlots[index].target == &definition)
    {
        // safety check before getting a mutable alias
        auto node = definition.owner;
        auto storage = this.inArena(node);
        if (storage == null) {
            version (assert) assert(false, "can't export definition from outside the graph");
            else return -EACCES;
        }
        InEdge* def = storage.asNode.opIndex(definition.id);

        // grow the export array if needed (does not cause any rehashing)
        if (this._exported.full) {
            uint n = this.exported == 0 ? 1 : this.exported * 2;
            if (n <= this.exported) return -EOVERFLOW;
            auto newExports = allocate!OutEdge(n);
            if (newExports == null) return -ENOMEM;
            // copy, then replace old exports array
            foreach (i, outEdge; this._exported) newExports[i] = outEdge;
            this._exported.array.deallocate();
            this._exported.array = newExports;
        }

        // push the new export and only then update the "public" view
        const failed = this._exported.push(OutEdge(def.kind, def));
        assert(!failed);
        this.topLevel.outSlots = this._exported.usedSlice;

        // remember to register the top-level as an in-neighbor before returning
        this.getInNeighbors(node).add(this.topLevel.asNode);
        int index = this.exported - 1;
        return index;
    }

    /++
    Destructively merges another graph into this one.

    The resulting graph's exports and imports will be the concatenation of this one's and the consumed's.
    Therefore, graph merging is not a commutative operation with respect to import/export interfaces, even if it is when considering only their internals.

    Returns: Zero on success, non-zero on failure.

    Version:
        TODO: Add a "merge spec" parameter which controls how imports/exports are merged.
    +/
    err_t merge(ref Graph consumed)
    in (this.assertInitialized && consumed.assertInitialized)
    {
        if (consumed is this) return 0; // #noAlias

        // TCC: what if one graph is a macro node in the other?
        // TCC: implement macro expansion

        // in case the arena can't fit both graphs, we'll create a bigger third
        // graph and merge the other two into it (in the right order)
        if (this.arena.length - this.cursor < consumed.length) {
            // the new graph has the sum of the previous' capacities, and then some
            size_t newCapacity = this.arena.length + consumed.arena.length;
            newCapacity = cast(size_t)(newCapacity * 1.618);
            if (newCapacity < this.cursor + consumed.length) return EOVERFLOW;
            Graph newGraph;
            auto error = newGraph.initialize(this.id, 0, 0, newCapacity);
            if (error) return error;
            // merge this graph into the new one, then tail-merge the other
            error = newGraph.merge(this);
            if (error) {
                newGraph.dispose();
                return error;
            }
            move(newGraph, this); // `this` was destroyed in the previous merge
            return this.merge(consumed);
        }

        // we begin by reallocating this graph's import and export arrays
        const ins = this.imported + consumed.imported;
        const outs = this.exported + consumed.exported;
        auto newImports = allocate!InEdge(ins);
        auto newExports = allocate!OutEdge(outs);
        if ((ins > 0 && newImports == null) || (outs > 0 && newExports == null)) {
            newImports.deallocate();
            newExports.deallocate();
            return ENOMEM;
        }
        foreach (i, inEdge; this.topLevel.inSlots) newImports[i] = inEdge;
        foreach (i, outEdge; this.topLevel.outSlots) newExports[i] = outEdge;

        // we still need to rewire in-neighbors of this graph's top-level, so
        // we do that before deallocating its current import array. since a macro
        // node's hash depends only on its ID, we don't need to invalidate caches
        auto oldImports = this.topLevel.inSlots;
        const oldImportCount = oldImports.length;
        this.topLevel.inSlots = newImports;
        foreach (inNeighbor; this.getInNeighbors(this.topLevel.asNode).byKey) {
            foreach (ref edge; NodeStorage.ofNode(inNeighbor).outEdges) {
                if (edge.target.owner == this.topLevel.asNode) {
                    edge.rewire(this._topLevel, edge.target.id);
                }
            }
        }
        oldImports.deallocate(); // ok to free now that there are no refs to it
        this._exported.array.deallocate();
        this._exported.array = newExports;
        this.topLevel.outSlots = this._exported.usedSlice;

        // changing import slots will trigger cache invalidations in the CONSUMED
        // graph, so before mutating anything we'll save its in-neighbor set
        UnsafeHashSet!(Node*) invalidationFrontier;
        scope(exit) invalidationFrontier.dispose();
        err_t error = 0;
        invalidationFrontier = consumed.getInNeighbors(consumed.topLevel.asNode).dup(error);
        assert(!error);

        // now we do the actual merge of imports & exports. once this happens,
        // our two graphs are interwined: this graph's top-level has edges into
        // the consumed graph, which in turn has edges into this graph's top-level
        const beginGcRoots = this.exported;
        foreach (ref outEdge; consumed.topLevel.outSlots) {
            const failed = this._exported.push(outEdge);
            assert(!failed);
        }
        this.topLevel.outSlots = this._exported.usedSlice;
        const endGcRoots = this.exported;
        foreach (offset, inEdge; consumed.topLevel.inSlots) {
            assert(inEdge.id == offset);
            const newIndex = oldImportCount + offset;
            assert(newIndex >= oldImportCount);
            this.topLevel.inSlots[newIndex] = InEdge(
                inEdge.kind, // same kind
                this.topLevel.asNode, // different owner
                cast(uint)newIndex // ID with offset
            );
        }
        // after this next loop, the consumed graph's top-level is no longer
        // reachable, which means the GC will never move it into this graph
        foreach (inNeighbor; invalidationFrontier.byKey) {
            foreach (ref edge; NodeStorage.ofNode(inNeighbor).outEdges) {
                if (edge.target.owner == consumed.topLevel.asNode) {
                    const offset = edge.target.id;
                    assert(edge.target == &consumed.topLevel.inSlots[offset]);
                    const newIndex = oldImportCount + offset;
                    assert(newIndex <= InEdge.ID.max);
                    edge.rewire(this._topLevel, cast(InEdge.ID)newIndex);
                }
            }
        }

        // before the GC moves the consumed graph, we'll refresh its cached hashes
        consumed.refreshHashes(invalidationFrontier);

        // the GC itself does precise mark & sweep, where we use the forwading bit
        // on every node to signal whether its been visited already or not.
        // after visiting a node, we'll set that bit and leave the node with a
        // "broken heart", a forwarding pointer which leads us to its new place.
        // also, since we're moving nodes, we might as well improve locality of
        // future traversals, so we do them in "root-first-depth-second" order

        // since we're going depth-first, we'll use a stack to hold grey objects
        alias Stack = List!(NodeStorage*);
        void grow(T)(ref List!T list) {
            size_t newCapacity = list.capacity == 0 ? 8 : list.capacity * 2;
            assert(newCapacity > list.capacity);
            auto memory = allocate!T(newCapacity);
            assert(memory != null);
            auto newList = List!T(memory);
            foreach (x; list) {
                const failed = newList.push(x);
                assert(!failed);
            }
            list.array.deallocate();
            move(newList, list);
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

        // step 0: at first, all objects are white
        Stack stack;
        scope(exit) stack.array.deallocate();

        // step 1: we begin by greying out roots, i.e. the merged exports
        foreach (edge; this._exported[beginGcRoots .. endGcRoots]) {
            auto root = edge.target.owner;
            assert(!root.wasVisited && !root.isForwarding);
            root.wasVisited = true;
            forcePush(stack, NodeStorage.ofNode(root));
        }

        // step 2: mark phase darkens all grey objects and what they can reach
        auto addedBegin = this.cursor;
        UnsafeHashSet!(Node*) hitList;
        scope(exit) hitList.dispose();
        while (!stack.empty) {
            // we always pop a grey object which is in the CONSUMED graph
            auto oldStorage = pop(stack);
            auto oldNode = oldStorage.asNode;
            assert(oldNode.wasVisited && !oldNode.isForwarding);
            assert(consumed.inArena(oldNode));

            // darkening it means it goes black, which translates to moving it
            // into the new graph and setting up its forwading pointer
            bool wasRedundant = false;
            auto newStorage = this.add(oldStorage, wasRedundant);
            assert(newStorage != null);
            // in order to avoid leaking memory when hash consing kicks in, we need
            // to remember this node and free it later (when it is safe to do so)
            if (wasRedundant) {
                error = hitList.add(oldNode);
                assert(!error);
            }
            oldNode.forwardingPointer = newStorage.asNode;

            // now, we darken this node's neighbors, but only if they're white
            // (ensures no grey nodes are repeated) and they're in the CONSUMED
            // graph (so that we never stack nodes from THIS graph, which would
            // have been possible in the case of a hash consed node)
            foreach (outEdge; newStorage.outEdges) {
                auto neighbor = outEdge.target.owner;
                if (neighbor.wasVisited) continue;
                if (!consumed.inArena(neighbor)) continue;
                neighbor.wasVisited = true;
                forcePush(stack, NodeStorage.ofNode(neighbor));
            }
        }
        auto addedEnd = this.cursor;

        // step 3: extra pass through just-transferred nodes to fix pointers
        void fixPointers(NodeStorage* storage) {
            // added nodes had their grey bit copied, so let's unset it
            auto node = storage.asNode;
            assert(node.wasVisited || storage == this._topLevel);
            node.wasVisited = false;

            // all of its out-neighbors were transfered as well, so we chase
            // outgoing pointers in order to adjust edges and in-neighbor sets
            foreach (ref outEdge; storage.outEdges) {
                auto outNeighbor = outEdge.target.owner;
                if (outNeighbor.isForwarding) {
                    outNeighbor = outNeighbor.forwardingPointer;
                    outEdge.rewire(NodeStorage.ofNode(outNeighbor), outEdge.target.id);
                }
                error = this.getInNeighbors(outNeighbor).add(node);
                assert(!error);
            }

        }
        foreach (i; addedBegin .. addedEnd) fixPointers(&this.arena[i]);
        fixPointers(this._topLevel); // <- has edges into the old graph as well

        // step 4: the "sweep" phase happens when we free the consumed graph
        // (notice that NodeStorage.dispose() takes moved nodes into account)
        // but before that we need to restore type info for hash consed nodes
        foreach (ref redundantNode; hitList.byKey) {
            assert(consumed.inArena(redundantNode));
            assert(redundantNode.isForwarding);
            auto vptr = redundantNode.forwardingPointer.vptr;
            redundantNode.vptr = vptr;
            assert(!redundantNode.isForwarding);
        }
        consumed.dispose();
        return 0;
    }

 private:
    inout(InNeighbors)* getInNeighbors(const(Node)* node) inout pure {
        auto key = const(HashConsedNode)(node);
        inout(HashConsedNode)* found;
        inout(InNeighbors)* inNeighbors;
        this.adjacencies.get(key, found, inNeighbors);
        return found ? inNeighbors : null;
    }

    inout(NodeStorage)* inArena(inout(Node)* node) inout pure
    out (result; result == null || result.asNode == node)
    {
        auto ptr = NodeStorage.ofNode(node);
        const min = &this.arena[0];
        const max = &this.arena[$ - 1];
        if (min <= ptr && ptr <= max) {
            const size_t index = ptr - min;
            return &this.arena[index];
        } else {
            return null;
        }
    }

    // shallow copy a node into the graph assuming there's space for it,
    // returning the resulting internal pointer (stable until the next GC)
    // NOTE: node structure must be stable and its hash already cached, which
    // implies its dependencies were also hashed (may need a topological sort)
    NodeStorage* add(NodeStorage* temp, out bool redundant)
    in (this.cursor < this.arena.length, "no space in the graph")
    in (!temp.asNode.isForwarding, "nodes added to the graph must be valid")
    in (!inArena(temp.asNode), "can't add a node to the arena twice")
    {
        // abort the node in case an equivalent one already exists in the graph
        auto found = const(HashConsedNode)(temp.asNode) in this.adjacencies;
        if (found) {
            redundant = true;
            return NodeStorage.ofNode(found.ptr);
        }

        // add the new node to the graph, with an empty set of in-neighbors
        NodeStorage* newStorage = &this.arena[this.cursor];
        copyEmplace(*temp, *newStorage);
        newStorage.opPostMove(*temp);
        auto handle = HashConsedNode(newStorage.asNode);
        const error = (this.adjacencies[handle] = InNeighbors.init);
        assert(!error);
        this.cursor++;

        return newStorage;
    }

    // updates invalidated hashes in this graph, starting from the given set
    void refreshHashes(ref UnsafeHashSet!(Node*) workSet) {
        Node* popAny(ref UnsafeHashSet!(Node*) set) {
            auto popped = set.byKey.front;
            assert(popped != null);
            set.remove(popped);
            return popped;
        }

        // we refresh invalidated hashes in breadth-first fashion, traversing
        // edges backwards through in-neighbor sets. we do this "until it runs out"
        // and without worrying about cycles, which is ok because IR rules imply
        // the absence of cyclic hash dependencies (e.g. see how a join hashes)
        while (workSet.length > 0) {
            // before refreshing a node, we remove it from the hash table
            // (notice that its backing memory in the arena isn't moved)
            auto node = popAny(workSet);
            auto inNeighbors = this.adjacencies[HashConsedNode(node)];
            this.adjacencies.remove(HashConsedNode(node));

            // check whether its cached hash was actually invalidated
            const oldHash = node.toHash();
            node.updateHash();
            const newHash = node.toHash();

            // if it did change, its in-neighbors need to be refreshed as well
            if (newHash != oldHash) {
                foreach (inNeighbor; inNeighbors.byKey) {
                    const error = workSet.add(inNeighbor);
                    assert(!error);
                }
            }

            // now that this node's up to date, we put it back in the table
            this.adjacencies[HashConsedNode(node)] = inNeighbors;
        }
    }
}

// TODO: expose a query/pass/transformation API over Graphs (check other libs for inspiration)


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

    /// This type's resources get automatically deallocated on scope exit (also, it is not copyable).
    ~this() {
        foreach (storage; this.nursery.byKey) {
            storage.dispose();
            deallocate(storage);
        }
        this.nursery.dispose();
    }
    @disable this(this);

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
        // OPT: performance-wise, we could do better with a chain of pools
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

    pragma(inline) {
        /// ditto
        JoinNode* insert(NodeSugar sugar : NodeSugar.JoinNodeSingleChannel)(uint argc) {
            uint[1] ms = [argc];
            return this.insert!(NodeKind.JoinNode)(ms[]);
        }

        /// ditto
        InstantiationNode* insert(NodeSugar sugar : NodeSugar.InstantiationNodeSingleChannel)() {
            return this.insert!(NodeKind.InstantiationNode)(1);
        }

        /// ditto
        ConditionalNode* insert(NodeSugar sugar : NodeSugar.ConditionalNodeBinary)() {
            return this.insert!(NodeKind.ConditionalNode)(2);
        }

        /// ditto
        MultiplexerNode* insert(NodeSugar sugar : NodeSugar.MultiplexerNodeBinary)() {
            return this.insert!(NodeKind.MultiplexerNode)(2);
        }
    }

    /++
    Links two edge slots within this subgraph.

    The updated out-edge's slot kind will be automatically set to match `to`'s'.

    Params:
        node = Node being updated.
        index = Required when the field is only accessible through an indirection.
        to = Target in-edge slot.
    +/
    err_t link(string member, NodeType)(NodeType* node, InEdge* to)
    if (is(typeof(mixin(`node.` ~ member)) == OutEdge))
    in (
        NodeStorage.ofNode(node.asNode) in this.nursery && NodeStorage.ofNode(to.owner) in this.nursery,
        "tried to update a node from another subgraph"
    ) do {
        auto link = OutEdge(to.kind, to);
        mixin(`node.` ~ member ~ ` = link;`);
        return 0;
    }

    /// ditto
    pragma(inline) err_t link(string member, NodeType)(NodeType* node, ref InEdge to) {
        return link!member(node, &to);
    }

    /// ditto
    err_t link(string member, NodeType)(NodeType* node, size_t index, InEdge* to)
    if (__traits(compiles, mixin(`node.` ~ member ~ `[index] = OutEdge.init`)))
    in (
        NodeStorage.ofNode(node.asNode) in this.nursery && NodeStorage.ofNode(to.owner) in this.nursery,
        "tried to update a node from another subgraph"
    ) do {
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
    pragma(inline) err_t link(string member, NodeType)(NodeType* node, size_t index, ref InEdge to) {
        return link!member(node, index, &to);
    }

    /++
    Post-hook callback delegate.

    This callback is invoked on every successfully [commit]ed node.
    Its first argument is a pointer matching one of the nodes [insert]ed in this subgraph.
    However, that node's contents have since been moved into the graph, so it can no longer be safely used as a concrete node type.
    The second argument is a pointer to the corresponding in-graph node.

    Holding onto these pointers is not safe, much less mutating them.
    In fact, the only thing users can do in the post-hook is to use the first argument to choose whether or not to call [Graph] methods on the second argument.
    +/
    alias PostHook = void delegate(const(Node)*, const(Node)*) @nogc nothrow;

    /++
    Commits this subgraph into a parent graph.

    This is a destructive copy which empties the subgraph being commited.
    After all nodes have been moved, user code can use a [PostHook] to export new definitions.

    Returns: Zero on success, non-zero otherwise.
    +/
    err_t commit(ref Graph graph, scope PostHook postHook) {
        // TCC: validate nodes and check IR rules BEFORE mutating anything

        // compute how much space we need and how much we have available
        const neededSpace = this.nursery.length;
        const freeSpace = graph.arena.length - graph.cursor;

        // if the graph's private memory pool needs to grow, trigger the GC
        if (freeSpace < neededSpace) {
            auto newCapacity = cast(size_t)((graph.cursor + neededSpace) * 1.618);
            if (newCapacity < graph.cursor + neededSpace) return EOVERFLOW;
            Graph newGraph;
            auto error = newGraph.initialize(graph.id, 0, 0, newCapacity);
            if (error) return error;
            error = newGraph.merge(graph);
            if (error) {
                newGraph.dispose();
                return error;
            }
            move(newGraph, graph);
        }

        // set of nodes which were hash-consed and therefore need to be deallocated
        UnsafeHashSet!(Node*) hitList;
        scope(exit) hitList.dispose();

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
                    outEdge.rewire(newNeighbor, outEdge.target.id);
                }
            }

            // this node is now stable, so we can hash it and add it to the graph
            oldNode.updateHash();
            bool wasRedundant = false;
            auto transferred = graph.add(original, wasRedundant);
            assert(transferred != null);
            Node* newNode = transferred.asNode;
            // small detail: if hash consing reveals that this node is redundant,
            // we need to deallocate its payload (if any) to avoid leaks. however,
            // since there may still be pointers into it, we need to defer this
            // until after edges are adjusted to avoid use-after free bugs
            if (wasRedundant) {
                const error = hitList.add(oldNode);
                assert(!error);
            }
            // sanity check: the old node has a broken heart, not the new one
            oldNode.forwardingPointer = newNode;
            assert(oldNode.isForwarding && !newNode.isForwarding);

            // since we now know this node's stable address in the graph, we can
            // add it to the in-neighbor set of each of its out-neighbors
            if (!isJoinNode) {
                foreach (ref outEdge; transferred.outEdges) {
                    auto outNeighbor = outEdge.target.owner;
                    assert(!outNeighbor.isForwarding);
                    const error = graph.getInNeighbors(outNeighbor).add(newNode);
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

        // this loops starts the recursion(s)
        foreach (storage; this.nursery.byKey) depthFirstAdd(storage);

        // since we treated join nodes differently before, we now have to ensure that
        // their edges were rewired and that they have been registered as in-neighbors
        foreach (join; joinNodes.byKey) {
            foreach (ref outEdge; join.outEdges) {
                Node* outNeighbor = outEdge.target.owner;
                // some of their pointers may still need to be rewired
                if (outNeighbor.isForwarding) {
                    outNeighbor = outNeighbor.forwardingPointer;
                    outEdge.rewire(NodeStorage.ofNode(outNeighbor), outEdge.target.id);
                }
                // and we must ensure the join is registered as an in-neighbor
                const error = graph.getInNeighbors(outNeighbor).add(join.asNode);
                assert(!error);
            }
        }

        // run post-commit hooks
        foreach (storage; this.nursery.byKey) {
            auto oldNode = storage.asNode;
            assert(oldNode.isForwarding);
            auto newNode = oldNode.forwardingPointer;
            postHook(oldNode, newNode);
        }

        // no one should still have pointers to hash-consed nodes, so we can
        // restore their type info to let the destructor free their payloads
        foreach (ref redundantNode; hitList.byKey) {
            assert(redundantNode.isForwarding);
            auto vptr = redundantNode.forwardingPointer.vptr;
            redundantNode.vptr = vptr;
            assert(!redundantNode.isForwarding);
        }

        // TCC: pre-hook to connect TO external nodes (e.g. imports)
        // TCC: peephole optimizations

        destroy(this);
        return 0;
    }
}

///
@nogc nothrow unittest {
    import gyre.mnemonics;

    Graph graph;
    graph.initialize(MacroNode.ID(42));
    scope(exit) graph.dispose();

    assert(graph.exported == 0);
    assert(graph.length == 0);

    // imagine we're compiling something like
    //    foo(ret, x) {
    //        a = x + 1
    //        b = 1 + x
    //        y = a / b
    //        ret(y)
    //    }
    with (Subgraph.init) {
        reserve(6);

        auto foo = insert!func(2);
        auto jmp = insert!jump(1);
        auto y = insert!divu;
        auto a = insert!addnos;
        auto b = insert!addnos;
        auto c1 = insert!const_(1);

        auto params = foo.channels[0];
        auto ret = &params[0];
        auto x = &params[1];

        link!"control"(foo, jmp.control);

        link!"continuation"(jmp, ret);
        link!"arguments"(jmp, 0, y.quotient);

        link!"dividend"(y, a.result);
        link!"divisor"(y, b.result);

        link!"lhs"(a, x);
        link!"rhs"(a, c1.value);

        link!"lhs"(b, c1.value);
        link!"rhs"(b, x);

        commit(graph, (node, inGraph){
            if (node is foo.asNode) {
                auto fooInGraph = JoinNode.ofNode(inGraph);
                graph.export_(fooInGraph.definition);
            }
        });
    }

    // since `a` and `b` compute the same value, one was CSE'd away
    assert(graph.length == 5);
    assert(graph.exported == 1);
}

@nogc nothrow unittest {
    import gyre.mnemonics;

    Graph g1;
    g1.initialize(MacroNode.ID(1), 1, 1, 0);
    scope(exit) g1.dispose();
    with (Subgraph.init) {
        reserve(4);

        auto c1 = insert!const_(1);
        auto y = insert!add;

        link!"lhs"(y, c1.value);
        link!"rhs"(y, c1.value);

        // these have a dynamic payload, but are subject to hash consing, so
        // this helps us test that both payloads get deallocated correctly
        auto deadCode2 = insert!sel;
        link!"selector"(deadCode2, c1.value);
        link!"inputs"(deadCode2, 0, y.result);
        link!"inputs"(deadCode2, 1, c1.value);
        auto deadCode1 = insert!sel;
        link!"selector"(deadCode1, c1.value);
        link!"inputs"(deadCode1, 0, y.result);
        link!"inputs"(deadCode1, 1, c1.value);

        commit(g1, (node, inGraph){
            if (node is y.asNode) {
                auto yInGraph = AdditionNode.ofNode(inGraph);
                assert(yInGraph);
                g1.export_(yInGraph.result);
            }
        });
    }
    assert(g1.length == 3);
    assert(g1.exported == 1);
    assert(g1.imported == 1);


    Graph g2;
    g2.initialize(MacroNode.ID(2), 1, 1, 2);
    scope(exit) g2.dispose();
    with (Subgraph.init) {
        reserve(2);

        auto c1 = insert!const_(1);
        auto y = insert!add;

        link!"lhs"(y, c1.value);
        link!"rhs"(y, c1.value);

        commit(g2, (node, inGraph){
            if (node is y.asNode) {
                auto incInGraph = AdditionNode.ofNode(inGraph);
                assert(incInGraph);
                g2.export_(incInGraph.result);
            }
        });
    }
    assert(g2.length == 2);
    assert(g2.exported == 1);
    assert(g2.imported == 1);


    g2.merge(g1);
    assert(g2.length == 2); // mux DCE'd, g1 CSE'd
    assert(g2.exported == 2);
    assert(g2.imported == 2);
}
