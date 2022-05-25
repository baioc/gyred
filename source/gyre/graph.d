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
import std.traits : EnumMembers, Fields, Parameters, isFunction, isArray, Unconst, isPointer;

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

        inout(Node)* asNode() inout pure
        return // XXX: `return` annotation needed in DMD 2.100.0
        {
            return cast(inout(Node)*)&this.node;
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
    UnsafeHashMap!(HashableNode, InNeighbors) nodes;
    alias HashableNode = HashablePointer!Node;
    alias InNeighbors = UnsafeHashSet!(Node*);

    // corresponds to the notion of a "top-level". also used as a GC root:
    // any subgraph not reachable from this node's inteface is considered dead
    MacroNode topLevel;

    // backing memory pool for this graph's nodes (all except the topLevel)
    NodeStorage[] nodePool;

    // bump allocator index, either at the first free slot or `== nodePool.length`
    // such that all in-use storage slots are to the left of the cursor
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
        this.nodePool = allocate!NodeStorage(capacity);
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

        foreach (ref inNeighbors; this.nodes.byValue) {
            inNeighbors.dispose();
        }
        this.nodes.dispose();

        assert(this.cursor <= this.nodePool.length);
        foreach_reverse (i; 0 .. this.cursor) {
            this.nodePool[i].dispose();
        }
        this.nodePool.deallocate();

        this = Graph.init;
    }

 private:
    // copies a node into the graph in case there's space for it, returning the internal pointer
    // NOTE: node structure must be stable and its hash already cached (and it must not depend on the node's address)
    Node* add(NodeStorage* temp)
    in (temp != null && this.cursor < this.nodePool.length)
    {
        if (temp == null) return null;
        if (this.cursor >= this.nodePool.length) return null;

        // abort the node in case an equivalent one already exists in the graph
        {
            auto handle = const(HashableNode)(temp.asNode);
            HashableNode* existing;
            InNeighbors* neighbors;
            const found = this.nodes.get(handle, existing, neighbors);
            if (found) {
                assert(existing != null);
                return *existing;
            }
        }

        // add the new node to the graph, with an empty set of in-neighbors
        NodeStorage* newStorage = &this.nodePool[this.cursor];
        *newStorage = *temp;
        newStorage.opPostMove(*temp);
        Node* newNode = newStorage.asNode;
        const error = (this.nodes[HashableNode(newNode)] = InNeighbors.init);
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
struct Transaction { // FIXME: this is actually a bad name, as it gives the wrong idea
 private:
    import std.bitmanip : taggedPointer;
    mixin(taggedPointer!(
        Graph*, "graph",
        bool, "began", 1
    ));

    // temporary buffer for new nodes and their in-neighbors
    NodeStorage[] nursery;
    InNeighbors[] inNeighbors;
    size_t cursor;
    alias InNeighbors = UnsafeHashSet!size_t;

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
        this.inNeighbors = allocate!InNeighbors(n);
        if (n > 0 && this.inNeighbors == null) {
            this.nursery.deallocate();
            this.nursery = null;
            return ENOMEM;
        }
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
            this.inNeighbors[i].dispose();
            this.nursery[i].dispose();
        }
        this.inNeighbors.deallocate();
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
        // TODO: we could actually make this work by packing node+slot indexes into pointers
        if (this.cursor >= this.nursery.length) return nil;

        // grab the first available slot and in-place initialize the node there
        NodeStorage* storage = &this.nursery[this.cursor];
        auto error = NodeType.initialize(&storage.node.as!kind, forward!args);
        if (error) return nil;
        this.inNeighbors[this.cursor] = InNeighbors.init;

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
    Updates an edge during an ongoing transaction.

    Pointers in our safe [NodeHandle|handles] can only be updated through this method.

    Params:
        from = Out-edge slot being updated.
        to = Target in-edge slot.

    Returns:
        Zero on success, non-zero on failure (e.g. invalid parent transaction).
    +/
    pragma(inline) err_t update(A, B)(A from, const B to)
    if (is(Unconst!(A.FieldType) == OutEdge) && is(Unconst!(B.FieldType) == InEdge))
    in (this.began, "can't operate on an unstarted transaction")
    {
        if (!this.began) return EINVAL;

        // in order to only compile the right overloads, we'll use a custom mangling scheme
        template mangleOf(T, NodeKind kind, string field) {
            static if (is(Unconst!T == NodeHandle!kind.DirectField!field)) {
                enum mangleOf = "f";
            } else static if (is(Unconst!T == NodeHandle!kind.SingleIndexedField!field)) {
                enum mangleOf = "s";
            } else {
                static assert(is(Unconst!T == NodeHandle!kind.DoubleIndexedField!field));
                enum mangleOf = "d";
            }
        }

        // we also need to make sure handles are actually owned by this transaction
        template getOwner(string local, string mangle) {
            static if (mangle == "f") {
                enum getOwner = local ~ `.handle.owner`;
            } else static if (mangle == "s") {
                enum getOwner = local ~ `.base.handle.owner`;
            } else {
                static assert(mangle == "d");
                enum getOwner = local ~ `.base.base.handle.owner`;
            }
        }

        enum kindA = A.HandleType.kind;
        enum kindB = B.HandleType.kind;
        enum string fieldA = A.field;
        enum string fieldB = B.field;
        enum a = mangleOf!(A, kindA, fieldA);
        enum b = mangleOf!(B, kindB, fieldB);

        auto ownerA = mixin(getOwner!("from", a));
        auto ownerB = mixin(getOwner!("to", b));
        if (ownerA != &this || ownerB != &this) {
            version (assert) assert(false, "transactions can only manage their own nodes");
            else return EACCES;
        }
        // TODO: how do we update edges linking to outside the nursery?

        // calls the right "overload" (implementations below) w/ template params + args
        enum overload = `_update_` ~ a ~ `_` ~ b;
        return mixin(overload ~ q{!(kindA, fieldA, kindB, fieldB)(from, to)});
    }

    /++
    Finishes this transaction by applying its changes.

    Returns:
        Zero on success, non-zero otherwise (in which case the transaction must be [abort]ed).
    +/
    err_t commit()
    in (this.began, "can't operate on an unstarted transaction")
    out (error; error || !this.began)
    {
        if (!this.began) return EINVAL;

        // compute how much space we need and how much we have available
        assert(this.cursor <= this.nursery.length);
        const neededSpace = this.nursery.length - this.cursor;
        assert(this.graph.cursor <= this.graph.nodePool.length);
        const freeSpace = this.graph.nodePool.length - this.graph.cursor;
        if (freeSpace < neededSpace) {
            version (assert) assert(false, "TODO: implement garbage collection");
            else return ENOMEM;
        }

        // TODO: validate nodes and check IR rules, especially the cycle restrictions

        // TODO: add nodes in topological order
        foreach (i; 0 .. this.cursor) {
            NodeStorage* storage = &this.nursery[i];
            storage.asNode.updateHash();
            Node* node = this.graph.add(storage);
            assert(node != null);
        }

        // TODO: rewire in-neighbors
        // TODO: peephole optimizations

        this.inNeighbors.deallocate();
        this.nursery.deallocate();
        this = Transaction(*this.graph);
        return 0;
    }

 private:
    err_t _update_f_f(NodeKind kindA, string fieldA, NodeKind kindB, string fieldB)(
        NodeHandle!kindA.DirectField!fieldA from,
        const(NodeHandle!kindB.DirectField!fieldB) to
    ) {
        const a = from.handle.index;
        const b = to.handle.index;
        auto nodeA = &this.nursery[a].node.as!kindA;
        auto nodeB = &this.nursery[b].node.as!kindB;

        auto link = OutEdge(from.kind, mixin(`&nodeB.` ~ fieldB));
        mixin(`nodeA.` ~ fieldA ~ ` = link;`);

        return 0;
    }

    err_t _update_f_s(NodeKind kindA, string fieldA, NodeKind kindB, string fieldB)(
        NodeHandle!kindA.DirectField!fieldA from,
        const(NodeHandle!kindB.SingleIndexedField!fieldB) to
    ) {
        const a = from.handle.index;
        const b = to.base.handle.index;
        auto nodeA = &this.nursery[a].node.as!kindA;
        auto nodeB = &this.nursery[b].node.as!kindB;

        auto link = OutEdge(from.kind, mixin(`&nodeB.` ~ fieldB ~ `[to.index]`));
        mixin(`nodeA.` ~ fieldA ~ ` = link;`);

        return 0;
    }

    err_t _update_f_d(NodeKind kindA, string fieldA, NodeKind kindB, string fieldB)(
        NodeHandle!kindA.DirectField!fieldA from,
        const(NodeHandle!kindB.DoubleIndexedField!fieldB) to
    ) {
        const a = from.handle.index;
        const b = to.base.base.handle.index;
        auto nodeA = &this.nursery[a].node.as!kindA;
        auto nodeB = &this.nursery[b].node.as!kindB;

        auto link = OutEdge(from.kind, mixin(`&nodeB.` ~ fieldB ~ `[to.base.index][to.index]`));
        mixin(`nodeA.` ~ fieldA ~ ` = link;`);

        return 0;
    }

    err_t _update_s_f(NodeKind kindA, string fieldA, NodeKind kindB, string fieldB)(
        NodeHandle!kindA.SingleIndexedField!fieldA from,
        const(NodeHandle!kindB.DirectField!fieldB) to
    ) {
        const a = from.base.handle.index;
        const b = to.handle.index;
        auto nodeA = &this.nursery[a].node.as!kindA;
        auto nodeB = &this.nursery[b].node.as!kindB;

        auto link = OutEdge(from.kind, mixin(`&nodeB.` ~ fieldB));
        mixin(`nodeA.` ~ fieldA ~ `[from.index] = link;`);

        return 0;
    }

    err_t _update_s_s(NodeKind kindA, string fieldA, NodeKind kindB, string fieldB)(
        NodeHandle!kindA.SingleIndexedField!fieldA from,
        const(NodeHandle!kindB.SingleIndexedField!fieldB) to
    ) {
        const a = from.base.handle.index;
        const b = to.base.handle.index;
        auto nodeA = &this.nursery[a].node.as!kindA;
        auto nodeB = &this.nursery[b].node.as!kindB;

        auto link = OutEdge(from.kind, mixin(`&nodeB.` ~ fieldB ~ `[to.index]`));
        mixin(`nodeA.` ~ fieldA ~ `[from.index] = link;`);

        return 0;
    }

    err_t _update_s_d(NodeKind kindA, string fieldA, NodeKind kindB, string fieldB)(
        NodeHandle!kindA.SingleIndexedField!fieldA from,
        const(NodeHandle!kindB.DoubleIndexedField!fieldB) to
    ) {
        const a = from.base.handle.index;
        const b = to.base.base.handle.index;
        auto nodeA = &this.nursery[a].node.as!kindA;
        auto nodeB = &this.nursery[b].node.as!kindB;

        auto link = OutEdge(from.kind, mixin(`&nodeB.` ~ fieldB ~ `[to.base.index][to.index]`));
        mixin(`nodeA.` ~ fieldA ~ `[from.index] = link;`);

        return 0;
    }
}

///
@nogc nothrow unittest {
    import gyre.graph;
    import gyre.nodes : Node, EdgeKind;
    import gyre.mnemonics;

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
                operand.kind = EdgeKind.control; // can't modify fixed kind
            }));
            auto mulp = mul.asNode(); // method on node
            auto h = operand.toHash(); // method on field

            auto mux = insert!mux(2);
            auto ins = mux.inputs; // single indexed access (hashtable)
            static assert(!__traits(compiles, {
                ins[0].kind = EdgeKind.control; // also can't modify kind
            }));

            const foo = insert!func(2);
            auto params = foo.channels[0];
            auto x = params[0]; // double indexed access
            static assert(!__traits(compiles, {
                x.kind = EdgeKind.memory; // just because foo is const
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

    assert(graph.nodes.length == 0);

    // ... while compiling something like
    //         foo(x, y):
    //             a = x + 1
    //             b = 1 + x
    with (Transaction(graph)) {
        begin(4);
        {
            auto foo = insert!func(2);
            auto params = foo.channels[0];
            auto x = params[0];

            auto c1 = insert!const_(1);
            // update(laterInvalid, c1.value); // runtime error

            auto a = insert!add;
            update(a.lhs, x);
            update(a.rhs, c1.value);

            auto b = insert!add;
            update(b.lhs, c1.value);
            update(b.rhs, x);

            const oops = insert!divu;
            assert(oops.isNull);
        }
        const error = commit();
        assert(!error);
    }

    // but b computes the same value as a, so it gets optimized away!
    assert(graph.nodes.length == 3);
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
    template canMutateSlotKind(Node, Slot) {
        alias NodeType = Unconst!Node;
        alias SlotType = Unconst!Slot;
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

    auto ref opDispatch(string member, Args...)(auto ref Args args) inout
    if (canAccess!(NodeType, member))
    in (!this.isNull, "can't use a null handle")
    {
        static if (isFunction!(__traits(getMember, NodeType, member)) && Args.length > 0) {
            // method calls work normally as long as they can operate with a const node
            const constThis = &this;
            return mixin(`(*constThis)._node.` ~ member)(forward!args);
        } else {
            // certain field/property members will need an extra wrapper
            alias T = typeof(mixin(`this._node.` ~ member));
            static if (needsWrapper!T)
                return inout(DirectField!member)(this);
            else
                return mixin(`this._node.` ~ member);
        }
    }

 private:
    // first-class field handles help transactions when mutating actual fields
    struct DirectField(string name) {
     private:
        // every field wrapper needs these
        alias HandleType = NodeHandle;
        enum field = name;
        alias FieldType = typeof(this._field);

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
        alias FieldType = typeof(this._field);

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
