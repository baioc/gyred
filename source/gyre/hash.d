/// Efficient betterC-compatible hash tables.
module gyre.hash;

import core.stdc.errno : ENOMEM, EINVAL;
import core.stdc.string : memcpy;
import std.math.traits : isPowerOf2;
import std.math.algebraic : nextPow2;
import std.typecons : Tuple, tuple;

import gyre.core : err_t, allocate, free, Unit;


private {
    alias hash_t = size_t; /// D uses `size_t` for hash values.

    /// Hash table bucket.
    struct Bucket(Key) {
        Key key;

     private:
        static if (Key.sizeof >= 2) {
            bool isOccupied = false; /// Whether this bucket is filled.
            bool wasDeleted = false; /// Marks this (filled) bucket for deletion.
        } else {
            private import std.bitmanip : bitfields;
            mixin(bitfields!(
                // lower bits
                bool, "isOccupied", 1,
                bool, "wasDeleted", 1,
                // upper bits (padding)
                ubyte, "", 6
            ));
        }
        static assert(!Bucket.init.isOccupied && !Bucket.init.wasDeleted);
    }

    enum float maxLoadFactor = 0.75;
    static assert(
        maxLoadFactor > 0.0 && maxLoadFactor < 1.0,
        "max load factor should be greater than zero and less than one"
    );

    enum size_t minAllocatedSize = 8;
    static assert(
        cast(size_t)(minAllocatedSize * maxLoadFactor) > 0,
        "min allocation size and max load factor are incompatible"
    );

    /// Returns the index where the given key is or would be placed.
    size_t probeFor(K)(
        scope const(Bucket!K)[] buckets,
        scope ref const(K) key
    ) @nogc nothrow pure @safe
    in (buckets.length > 0, "can't probe an empty table")
    in (buckets.length.isPowerOf2, "table size is not a power of two")
    {
        // number of buckets must be a power of 2 so that we may swap modulos for bitmasks
        const n = buckets.length;
        const size_t mask = n - 1U;

        // step 1: start at index hash(key) % n, check for a hit or free slot
        static if (__traits(compiles, key.toHash)) {
            const hash_t hash = key.toHash;
        } else {
            const hash_t hash = key.hashOf;
        }
        size_t index = hash & mask;
        auto bucket = &buckets[index];
        if (!bucket.isOccupied || (!bucket.wasDeleted && bucket.key == key))
            return index;

        // step 2: collision detected, use the upper hash bits to jump elsewhere
        index = (index + (hash >> (hash_t.sizeof * 8U / 2U))) & mask;

        // step 3: sequentially probe buckets, looking for deleted ones along the way
        // this procedure is correct as long as probing is deterministic (i.e.
        // insert(k) ... other key operations .. lookup(k) find the same bucket),
        // and it terminates because we look at all buckets and at least one is free
        // termination criteria are trivially met because we're doing a linear probe
        static assert(maxLoadFactor < 1.0); // ensures free buckets
        enum notFound = size_t.max; // impossible index because it's always > n
        assert(notFound > n);
        size_t recycled = notFound;
        while (true) {
            bucket = &buckets[index];
            if (!bucket.isOccupied) {
                // if we had previously found a deleted bucket, reuse it
                return recycled == notFound ? index : recycled;
            } else if (bucket.wasDeleted && recycled == notFound) {
                // save first bucket marked for deletion, but keep going
                // in case we're supposed to find the key later on
                recycled = index;
            } else if (!bucket.wasDeleted && bucket.key == key) {
                // key was already present, return its index
                return index;
            }
            index = (index + 1U) & mask;
        }
    }
}

/++
BetterC-compatible hash map; should be treated like a reference type.

Manages memory with [gyre.core.allocate](./core.html#allocate) and [gyre.core.free](./core.html#free), which can also be used with a GC.
The mechanism used to override hashing and comparison functions is [the same as for standard AAs](https://dlang.org/spec/hash-map.html#using_struct_as_key).
Unlike AA's, however, this hash table does NOT guarantee that references to its internal storage will be kept stable between rehashes.
What it does guarantee is that only insertions may cause a rehash (and explicit calls to [rehash](#rehash), of course).
+/
struct HashMap(Key, Value) {
 private:
    alias Bucket = gyre.hash.Bucket!Key;

    Bucket[] buckets = null;
    size_t occupied = 0;
    size_t used = 0;

    // we only need to allocate a value array if its size is non-zero
    static if (Value.sizeof > 0) Value* values = null;

    // since we're doing closed hashing, for every set of slots we have:
    // used <= occupied <= allocate (where allocations are performed in bulk)
    invariant {
        assert(used <= occupied);
        assert(occupied <= allocated);
        static if (Value.sizeof > 0) {
            assert((buckets  is null && values == null)
                || (buckets !is null && values != null));
        }
    }

    version (D_BetterC) {} else {
        public string toString() const scope pure
        @trusted // XXX: for some reason, using byKeyValue on `scope this` does not work here
        {
            import std.array : appender;
            import std.conv : to;
            import std.string : format;

            auto result = appender!string;
            const n = this.length;
            result.reserve(2U + n*8U + n*(Key.sizeof + Value.sizeof));
            result ~= "{";

            bool first = true;
            foreach (key, value; this.byKeyValue) {
                if (!first) {
                    result ~= ", ";
                } else {
                    first = false;
                }
                static if (Value.sizeof > 0)
                    result ~= "(%s => %s)".format(key.to!string, value.to!string);
                else
                    result ~= key.to!string;
            }

            result ~= "}";
            return result[];
        }
    }

 @nogc nothrow:
    pragma(inline, true) {
        @property size_t allocated() const scope pure @safe {
            return this.buckets.length;
        }

        inout(Value)* valueAt(size_t index) inout return scope pure
        @trusted // indexes raw pointer `values`
        in (index < this.allocated)
        {
            static if (Value.sizeof > 0) {
                assert(this.values != null);
                return &this.values[index];
            } else {
                return null;
            }
        }
    }

 public:
    size_t toHash() const scope
    @trusted // XXX: for some reason, using byKeyValue on `scope this` does not work here
    {
        hash_t tableHash = 0;
        foreach (key, value; this.byKeyValue) {
            // hash the key
            static if (__traits(compiles, key.toHash)) {
                hash_t entryHash = key.toHash;
            } else {
                hash_t entryHash = key.hashOf;
            }
            // hash the value
            static if (__traits(compiles, value.toHash)) {
                entryHash ^= value.toHash;
            } else {
                entryHash ^= value.hashOf;
            }
            // accumulate
            tableHash ^= entryHash;
        }
        return tableHash;
    }

    bool opEquals()(scope auto ref const(typeof(this)) other) const scope
    @trusted // XXX: for some reason, using byKeyValue on `scope this` does not work here
    {
        if (other.length != this.length) return false;
        foreach (key, value; this.byKeyValue) {
            if (key !in other || value != other[key]) return false;
        }
        return true;
    }

    /// Returns the number of entries currently being used in the hash table.
    @property size_t length() const scope pure @safe {
        return this.used;
    }

    /++
    Returns a pointer to a matching KEY in the table, or `null` if there isn't one.

    See_Also: [get](#get)
    +/
    inout(Key)* opBinaryRight(string op : "in")(
        scope auto ref const(Key) key
    ) inout return scope pure @safe {
        if (this.allocated == 0) return null;
        const k = this.buckets.probeFor(key);
        auto bucket = &this.buckets[k];
        return bucket.isOccupied && !bucket.wasDeleted ? &bucket.key : null;
    }

    /++
    Returns the value associated with a given key, or its `.init` if there isn't one.

    See_Also: [require](#require), [get](#get)
    +/
    inout(Value) opIndex()(scope auto ref const(Key) key) inout scope pure @safe
    out (value; key in this || value == Value.init)
    {
        inout(Key)* keyp;
        inout(Value)* valp;
        const found = this.get(key, keyp, valp);
        static if (Value.sizeof > 0)
            return found ? *valp : Value.init;
        else
            return Value.init;
    }

    /++
    Upserts a `<key,value>` entry in the hash table. May cause a [rehash](#rehash).

    Returns: Zero on success, non-zero on failure (e.g. OOM or overflow).

    See_Also: [update](#update)
    +/
    err_t opIndexAssign(Value value, Key key) scope @safe
    out (error; error || this[key] == value)
    {
        err_t error;
        this.update(key, () => value, (ref Value old) => value, error);
        return error;
    }
}

@nogc nothrow {
    @nogc nothrow pure @safe unittest {
        alias NonZero = long;
        alias Zero = void[0];
        static assert(HashMap!(char, Zero).sizeof < HashMap!(char, NonZero).sizeof);
    }

    /// Frees any resources allocated by the hash table.
    void destroy(K, V)(scope ref HashMap!(K,V) self)
    @trusted // due to `free`
    out (; self.length == 0)
    out (; self.buckets is null)
    {
        assert(self.allocated == self.buckets.length);
        static if (V.sizeof > 0) self.values.free(self.allocated);
        self.buckets.ptr.free(self.allocated);
        self = HashMap!(K,V).init;
    }

    /// Consider using `scope(exit)` to always ensure [HashMap](#HashMap) deallocation.
    @nogc nothrow @safe unittest {
        HashMap!(char, long) table;
        scope(exit) table.destroy();
    }

    /// Initializes a hash table.
    private err_t initialize(K, V)(scope out HashMap!(K,V) self, size_t capacity)
    @trusted // due to `free` and turning pointer into range
    in (self == HashMap!(K,V).init)
    out (; self.length == 0)
    {
        if (capacity == 0) return 0;

        // adjust allocation size based on max load factor and round to power of two
        capacity = cast(size_t)(capacity / maxLoadFactor);
        if (capacity < minAllocatedSize) {
            capacity = minAllocatedSize;
            static assert(minAllocatedSize.isPowerOf2, "min allocated size must be a power of 2");
        } else if (!capacity.isPowerOf2) {
            capacity = nextPow2(capacity);
            if (capacity == 0) return ENOMEM;
        }
        assert(capacity >= minAllocatedSize && capacity.isPowerOf2);

        // allocate bucket (and value) array
        auto buffer = allocate!(Bucket!K)(capacity);
        if (buffer == null) return ENOMEM;
        self.buckets = buffer[0 .. capacity];
        static if (V.sizeof > 0) {
            self.values = allocate!V(capacity);
            if (self.values == null) {
                self.buckets = null;
                buffer.free(capacity);
                return ENOMEM;
            }
        }

        // initialize buckets and other table attributes
        foreach (ref bucket; self.buckets) {
            bucket.isOccupied = false;
            bucket.wasDeleted = false;
        }
        self.occupied = 0;
        self.used = 0;

        return 0;
    }

    /++
    Rehashes the table (possibly making future lookups more efficient).

    This is the only way to reduce a hash table's memory footprint.
    Nothing happens in case of failure.

    Params:
        self = Hash table.
        newCapacity = Min pre-allocated entries. Must be enough to fit current entries.

    Returns:
        Zero on success, non-zero on failure.
        Reasons for failure include OOM, overflow or an invalid capacity.
    +/
    err_t rehash(K, V)(scope ref HashMap!(K,V) self, size_t newCapacity) @safe
    in (newCapacity >= self.length, "table capacity must be enough to fit its current entries")
    {
        if (newCapacity < self.length) return EINVAL;

        // edge case: rehash empty table to zero capacity
        if (newCapacity == 0 && self.length == 0) {
            self.destroy();
            const error = self.initialize(0);
            assert(!error, "zero capacity doesn't allocate and thus can't fail");
            return 0;
        }

        // otherwise, pretend that we're initializing a new table
        HashMap!(K,V) newTable;
        const error = newTable.initialize(newCapacity);
        if (error) return error;

        // relocate every in-use entry to a newly-computed bucket
        assert(newTable.allocated >= self.used);
        size_t filled = 0;
        foreach (size_t i, ref oldBucket; self.buckets) {
            if (!oldBucket.isOccupied || oldBucket.wasDeleted) continue;
            const k = newTable.buckets.probeFor(oldBucket.key);
            auto newBucket = &newTable.buckets[k];
            newBucket.key = oldBucket.key;
            newBucket.isOccupied = true;
            newBucket.wasDeleted = false;
            static if (V.sizeof > 0) *newTable.valueAt(k) = *self.valueAt(i);
            filled++;
        }
        assert(filled == self.used);
        newTable.occupied = filled;
        newTable.used = filled;

        // finally, free the old table and replace it with the new one
        self.destroy();
        self = newTable;
        return 0;
    }

    /// ditto
    err_t rehash(K, V)(scope ref HashMap!(K,V) self) @safe {
        return self.rehash(self.length);
    }

    /++
    Looks up an entry in the table's internal storage.

    Params:
        self = Backing hash table.
        find = Key which designates the entry being looked up.
        keyp = Set to entry key's address (or `null` when not found).
        valp = Set to entry value's address.

    Returns: Whether or not the entry was found in the table.
    +/
    pragma(inline) bool get(K, V)(
        return scope ref inout(HashMap!(K,V)) self,
        scope auto ref const(K) find,
        scope out inout(K)* keyp,
        scope out inout(V)* valp
    ) pure
    @trusted // due to cast from Bucket* to Key*
    out (found; (found && *keyp in self) || (!found && keyp == null))
    {
        auto key = find in self;
        if (key == null) return false;
        static assert(Bucket!K.key.offsetof == 0, "bucket layout must ensure safe cast to key");
        const size_t k = cast(inout(Bucket!K)*)(key) - self.buckets.ptr;
        keyp = key;
        valp = self.valueAt(k);
        return true;
    }

    /// ditto
    bool get(K, V)(
        return scope ref inout(HashMap!(K,V)) self,
        scope auto ref const(K) find,
        scope out inout(K)* keyp,
    ) pure @safe {
        inout(V)* valp;
        return self.get(find, keyp, valp);
    }

    /++
    Removes a key's entry from the table.

    Returns: Whether or not the key had an entry to begin with.
    +/
    bool remove(K, V)(scope ref HashMap!(K, V) self, scope auto ref const(K) key) pure @safe
    out (; key !in self)
    {
        if (self.length == 0) return false;
        const k = self.buckets.probeFor(key);
        auto bucket = &self.buckets[k];
        if (!bucket.isOccupied || bucket.wasDeleted) return false;
        // on deletion, we simply mark the bucket and decrease entry count
        bucket.wasDeleted = true;
        self.used--;
        return true;
    }

    ///
    @nogc nothrow @safe unittest {
        HashMap!(char, long) table;
        scope(exit) table.destroy();
        assert(table.length == 0);

        assert('a' !in table);
        table['a'] = 0; // inserts
        assert('a' in table);
        table['a'] = 1; // updates
        assert(table.length == 1);

        assert(table.remove('a') == true);
        assert('a' !in table);
        assert(table.remove('a') == false);
        assert(table.length == 0);

        static immutable reverse = ['a', 'b', 'c', 'd', 'e'];
        foreach (i, c; reverse) table[c] = i + 1;
        table.rehash(); // must preserve elements
        assert(table.length == reverse.length);
        foreach (key; table.byKey) assert(key == reverse[table[key] - 1]);
        foreach (val; table.byValue) assert(val == table[reverse[val - 1]]);
    }

    /++
    Looks up a key's entry in the table, then either updates it or creates a new one.

    If a new entry needs to be created, a [rehash](#rehash) may happen.

    Params:
        self = Hash table.
        key = Key being looked up (only stored when a new entry is created).
        create = Called to construct a new value if the key isn't in the table.
        update = Called to update the value if an entry was found.
        error = Set to zero on success, non-zero otherwise.

    Returns: The entry's final value (or its `.init` in case of failure).
    +/
    pragma(inline) V update(K, V)(
        return scope ref HashMap!(K,V) self,
        K key,
        scope V delegate() @nogc nothrow create,
        scope V delegate(ref V) @nogc nothrow update,
        scope out err_t error
    )
    @trusted // only as @safe as the passed in delegates
    in (create != null, "can't create an entry with a null delegate")
    in (update != null, "can't update an entry with a null delegate")
    out (value; (error && value == V.init) || (!error && self[key] == value))
    {
        if (create == null) {
            error = EINVAL;
            return V.init;
        }
        update = update != null ? update : (ref old) => old;

        // check whether a load factor increase needs to trigger a rehash
        if (self.occupied + 1 > cast(size_t)(self.allocated * maxLoadFactor)) {
            // let's make sure rehash growth consistenly reduces load factor
            static assert(minAllocatedSize * 2 > minAllocatedSize);
            size_t newCapacity = self.allocated >= minAllocatedSize
                                 ? self.allocated * 2
                                 : minAllocatedSize;
            error = self.rehash(newCapacity);
            if (error) return V.init;
        }

        // find the key's designated bucket (after rehash)
        const k = self.buckets.probeFor(key);
        auto bucket = &self.buckets[k];
        const hadEntry = bucket.isOccupied && !bucket.wasDeleted;

        // increase load factor only if we're not reusing some freed bucket
        if (!bucket.isOccupied) self.occupied++;
        bucket.isOccupied = true;
        bucket.wasDeleted = false;

        // check whether we need to create a value or update the old one
        V newValue;
        if (!hadEntry) {
            self.used++;
            bucket.key = key;
            newValue = create();
        } else /* hadEntry */ {
            static if (V.sizeof > 0) {
                newValue = update(*self.valueAt(k));
            } else {
                V oldValue = V.init;
                newValue = update(oldValue);
            }
        }
        static if (V.sizeof > 0) *self.valueAt(k) = newValue;
        error = 0;
        return newValue;
    }

    /// ditto
    V update(K, V)(
        return scope ref HashMap!(K,V) self,
        K key,
        scope V delegate() @nogc nothrow create,
        scope V delegate(ref V) @nogc nothrow update
    ) @safe {
        err_t ignored;
        return self.update(key, create, update, ignored);
    }

    /++
    Looks up a key, inserting an entry if there isn't any (may [rehash](#rehash)).

    Params:
        self = Hash table.
        key = Key being looked up (only stored when a new entry is created).
        create = Called to construct a new value if the key isn't in the table.
        error = Set to zero on success, non-zero otherwise.

    Returns: The entry's final value (or its `.init` in case of failure).
    +/
    V require(K, V)(
        return scope ref HashMap!(K,V) self,
        K key,
        scope V delegate() @nogc nothrow create,
        scope out err_t error
    ) @safe {
        return self.update(key, create, (ref V x) => x, error);
    }

    /// ditto
    V require(K, V)(
        return scope ref HashMap!(K,V) self,
        K key,
        scope V delegate() @nogc nothrow create
    ) @safe {
        err_t ignored;
        return self.require(key, create, ignored);
    }

    ///
    @nogc nothrow @safe unittest {
        import core.stdc.ctype : isalnum;

        bool isAnagram(string a, string b) @nogc nothrow @safe {
            // count letter frequencies in A
            HashMap!(char, long) letters;
            scope(exit) letters.destroy();
            foreach (char c; a) {
                if (!c.isalnum) continue;
                const freq = letters.require(c, () => 0L);
                letters[c] = freq + 1;
            }

            // check if they match B's
            foreach (char c; b) {
                if (!c.isalnum) continue;
                const freq = letters.update(c, () => -1L, (ref long f) => f - 1);
                if (freq < 0) return false;
                else if (freq == 0) letters.remove(c);
            }
            return letters.length == 0;
        }

        assert(  isAnagram("eleven plus two", "twelve plus one") );
        assert( !isAnagram("aabaa", "bbabb")                     );
        assert(  isAnagram("123", "3 2 1")                       );
    }

    private mixin template RangeBoilerplate(HashTable) {
        private const(HashTable)* table;
        private size_t index;

        private this(return scope const(HashTable)* t, size_t i = 0) scope @nogc nothrow pure {
            table = t;
            for (index = i; index < table.buckets.length; ++index) {
                const bucket = &table.buckets[index];
                if (bucket.isOccupied && !bucket.wasDeleted) break;
            }
        }

        public bool empty() const scope @nogc nothrow pure {
            return index >= table.buckets.length;
        }

        public void popFront() scope @nogc nothrow pure {
            this = typeof(this)(table, index + 1);
        }
    }

    /++
    Can be used to iterate over this table's entries (in an unspecified order).

    NOTE: These must NEVER outlive their backing hash table.
        Furthermore, mutating a table invalidates any ranges over it.
    +/
    auto byKey(K, V)(return ref const(HashMap!(K,V)) self) pure @safe {
        struct ByKey {
            mixin RangeBoilerplate!(HashMap!(K,V));
            public const(K) front() const scope @nogc nothrow pure in (!this.empty) {
                auto bucket = &table.buckets[index];
                assert(bucket.isOccupied && !bucket.wasDeleted);
                return bucket.key;
            }
        }
        return ByKey(&self);
    }

    /// ditto
    auto byValue(K, V)(return ref const(HashMap!(K,V)) self) pure @safe {
        struct ByValue {
            mixin RangeBoilerplate!(HashMap!(K,V));
            public const(V) front() const scope @nogc nothrow pure in (!this.empty) {
                auto bucket = &table.buckets[index];
                assert(bucket.isOccupied && !bucket.wasDeleted);
                static if (V.sizeof > 0)
                    return *table.valueAt(index);
                else
                    return V.init;
            }
        }
        return ByValue(&self);
    }

    /// ditto
    auto byKeyValue(K, V)(return ref const(HashMap!(K,V)) self) pure @safe {
        alias ConstKeyValue = Tuple!(const(K), "key", const(V), "value");
        struct ByKeyValue {
            mixin RangeBoilerplate!(HashMap!(K,V));
            public const(ConstKeyValue) front() const scope @nogc nothrow pure in (!this.empty) {
                auto bucket = &table.buckets[index];
                assert(bucket.isOccupied && !bucket.wasDeleted);
                static if (V.sizeof > 0)
                    return ConstKeyValue(bucket.key, *table.valueAt(index));
                else
                    return ConstKeyValue(bucket.key, V.init);
            }
        }
        return ByKeyValue(&self);
    }

    ///
    @nogc nothrow @safe unittest {
        static assert(
            !__traits(compiles, // ... assuming -dip1000
                () @safe {
                    HashMap!(char, long) table; // local variable
                    return table.byKeyValue;    // Error: range outlives table
                }
            ),
            "must not allow a range to outlive its backing hash table"
        );
    }

    /++
    Creates an independent copy of a given hash table.

    Params:
        self = Hash table to be copied.
        error = Set to zero on success, non-zero otherwise.

    Returns: A copy of the given hash table, or an empty table in case of failure (OOM).
    +/
    HashMap!(K,V) dup(K, V)(scope ref const(HashMap!(K,V)) self, scope out err_t error)
    @trusted // XXX: for some reason, using byKeyValue on `scope self` does not work here
    out (copy) {
        if (!error) {
            assert(copy.length == self.length);
            foreach (key, value; self.byKeyValue)
                assert(key in copy && copy[key] == value);
        } else {
            assert(copy.length == 0);
        }
    } do {
        HashMap!(K,V) copy;
        error = copy.initialize(self.length);
        if (error) return copy;
        foreach (key, value; self.byKeyValue) {
            error = (copy[key] = value);
            assert(!error, "memory already reserved, so insertion won't fail");
        }
        return copy;
    }

    /// ditto
    HashMap!(K,V) dup(K, V)(scope ref const(HashMap!(K,V)) self) @safe {
        err_t ignored;
        return self.dup(ignored);
    }
}


/++
BetterC-compatible hash set; essentially a wrapper around a `HashMap!(T, Unit)`.

See_Also: [gyre.core.Unit](./core.html#Unit)
+/
struct HashSet(T) {
    private HashMap!(T, Unit) table;
    alias table this;

    version (D_BetterC) {} else {
        string toString() const pure {
            return this.table.toString();
        }
    }
}

/++
Adds an element to the set, possibly causing a [rehash](#rehash).

Returns: Zero on success, non-zero on failure (e.g. OOM or overflow).
+/
pragma(inline) err_t add(T)(scope ref HashMap!(T, Unit) self, T key) @nogc nothrow @safe
out (error; error || key in self)
{
    return (self[key] = Unit.init);
}

///
nothrow @safe unittest {
    import std.algorithm : each;

    HashSet!long a, b;
    scope(exit) {
        a.destroy();
        b.destroy();
    }

    static immutable long[6] list = [0, 1, 42, 32_767, -32_768, 0];
    enum N = list.length;
    a.rehash(N);
    list.each!(n => a.add(n));
    assert(a.length == N - 1); // one less because of the duplicate 0

    assert(a != b);
    b = a.dup;
    assert(a == b); // structural equality works

    HashMap!(HashSet!long, string) stringified;
    scope(exit) stringified.destroy();
    stringified[a] = a.toString();
    assert(b in stringified); // structural hashing as well

    b.remove(0);
    b.add(-1);
    assert(a != b);
    assert(b !in stringified); // but be careful with mutability
}
