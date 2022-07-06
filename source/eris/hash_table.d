/++
This module provides hash tables with deterministic memory usage (not reliant on the GC), as a betterC alternative to the built-in AAs.

Includes both unsafe (explicitly managed) and safe (refcounted) hash-based data types.


Performance is roughly equivalent to AAs, but can be made a bit better with preallocation.
![upserts](https://user-images.githubusercontent.com/27034173/169673970-43d98400-8be2-48e1-b70d-6b13217d830c.png)
+/
module eris.hash_table;

import core.stdc.errno : ENOMEM, EINVAL, EOVERFLOW;
import std.algorithm.mutation : moveEmplace, swap;
import std.math.traits : isPowerOf2;
import std.traits : Parameters, ReturnType, hasElaborateDestructor;

import eris.core : allocate, deallocate, err_t, hash_t, Unit;
import eris.rational : Rational;
import eris.util : RefCountedTrusted;


private {
    // Hash table bucket.
    struct Bucket(Key) {
        Key key;

        static if (Key.sizeof >= 2) {
            bool isOccupied = false; // Whether this bucket is filled.
            bool wasDeleted = false; // Marks this (filled) bucket for deletion.
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
    }

    // static settings
    enum maxLoadFactor = Rational!size_t(3, 4);
    enum size_t minAllocatedSize = 4;

    // Returns the index where the given key is or would be placed.
    size_t probeFor(Key)(const(Bucket!(Key)[]) buckets, ref const(Key) key)
    in (buckets.length > 0, "can't probe an empty table")
    in (buckets.length.isPowerOf2, "table size is not a power of two")
    {
        // number of buckets must be a power of 2 so that we may swap modulos for bitmasks
        const size_t n = buckets.length;
        const size_t mask = n - 1;

        // step 1: start at index hash(key) % n, check for a hit or free slot
        const hash_t hash = key.hashOf;
        size_t index = hash & mask;
        auto bucket = &buckets[index];
        if (!bucket.isOccupied || (!bucket.wasDeleted && bucket.key == key))
            return index;

        // step 2: collision detected, use the upper hash bits to jump elsewhere
        enum shift = hash_t.sizeof * 8 / 2;
        index = (index + (hash >> shift)) & mask;

        // step 3: sequentially probe buckets, looking for deleted ones along the way.
        // this procedure is correct as long as probing is deterministic (i.e.
        // insert(k) -> ... -> lookup(k) find the same bucket), and it terminates
        // because at least one bucket must be free and we eventually try them all.

        // a valid max load factor ensures that at least one bucket is free
        static assert(
            maxLoadFactor > 0.0 && maxLoadFactor < 1.0,
            "invalid max load factor " ~ maxLoadFactor.stringof ~
            ": must be greater than zero and less than one"
        );

        enum notFound = size_t.max; // impossible index because it's always > n
        assert(notFound > n);
        size_t recycled = notFound;

        // we increment by j, where j grows by 1 every iteration, to implement a
        // quadratic probe sequence over the triangular numbers; since we modulo by
        // a power of two, we'll take n steps to probe all n buckets. for a proof of this,
        // see http://www.chilton-computing.org.uk/acl/literature/reports/p012.htm
        for (size_t j = 1; true; ++j) {
            assert(j <= n, "we're looping more than we should be");
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
            index = (index + j) & mask;
        }
    }
}

/++
Dense hash map acting as a mostly-compatible (even if unsafe) AA replacement.

The mechanism used to override hashing and comparison functions is [the same as for standard AAs](https://dlang.org/spec/hash-map.html#using_struct_as_key).
Unlike AA's, however, this hash table does NOT guarantee that references to its internal storage will be kept stable between [rehash]es, which may also be caused by insertion operations.

See_Also: The safer [HashMap]
+/
struct UnsafeHashMap(Key, Value) {
 private:
    alias Bucket = .Bucket!Key;

    Bucket[] buckets;
    size_t occupied;
    size_t used;

    // we only need to allocate a value array if its size is non-zero
    static if (Value.sizeof > 0) Value* values;

    pragma(inline) {
        @property size_t allocated() const {
            return this.buckets.length;
        }

        inout(Value)* valueAt(size_t index) inout
        @trusted // indexes raw pointer
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
    /// Initializes a new table with a certain preallocated capacity.
    this(size_t capacity) { this.initialize(capacity); }

    version (D_BetterC) {} else {
        string toString() const {
            import std.array : appender;
            import std.conv : to;
            import std.string : format;

            auto result = appender!string;
            const size_t n = this.length;
            result.reserve(3 + n*8 + n*(Key.sizeof + Value.sizeof)); // ok even if overflows
            result ~= "#{";

            bool first = true;
            foreach (entry; this.byKeyValue) {
                if (!first) {
                    result ~= ", ";
                } else {
                    first = false;
                }
                static if (Value.sizeof > 0)
                    result ~= "(%s => %s)".format(entry.key.to!string, entry.value.to!string);
                else
                    result ~= entry.key.to!string;
            }

            result ~= "}";
            return result[];
        }
    }

    /// Structural hash of this table.
    size_t toHash() const {
        // entry order does not matter in a hash table, so we accumulate with XOR
        hash_t tableHash = 0;
        foreach (entry; this.byKeyValue) {
            // for each entry, we use a noncommutative operation
            static if (Value.sizeof > 0 && __traits(compiles, () @safe => entry.value.hashOf)) {
                enum size_t scale = 2654435771LU; // approx. 2^32 / phi
                tableHash ^= (entry.key.hashOf - entry.value.hashOf) * scale; // ok if overflows
            }
            // if hashing values is unsafe, we want to depend only on the key's hash
            else {
                tableHash ^= entry.key.hashOf;
            }
        }
        return tableHash;
    }

    /// Structural equality comparison.
    bool opEquals()(auto ref const(UnsafeHashMap) other) const {
        if (this is other) return true;
        if (other.length != this.length) return false;
        foreach (entry; this.byKeyValue) {
            const(Key)* keyp;
            const(Value)* valp;
            const found = other.get(entry.key, keyp, valp);
            if (!found) return false;
            static if (Value.sizeof > 0) if (entry.value != *valp) return false;
        }
        return true;
    }

    /++
    Number of entries currently being used in the hash table.

    See_Also: [capacity]
    +/
    @property size_t length() const {
        return this.used;
    }

    /++
    Entries the table can hold without being rehashed.

    See_Also: [length]
    +/
    @property size_t capacity() const {
        assert(this.allocated * maxLoadFactor.numerator >= this.allocated); // overflow check
        return this.allocated * maxLoadFactor.numerator / maxLoadFactor.denominator;
    }

    /++
    Returns a pointer to a matching KEY in the table, or `null`

    See_Also: [get]
    +/
    inout(Key)* opBinaryRight(string op : "in")(auto ref const(Key) key) inout {
        if (this.length == 0) return null;
        const k = this.buckets.probeFor!Key(key);
        auto bucket = &this.buckets[k];
        return bucket.isOccupied && !bucket.wasDeleted ? &bucket.key : null;
    }

    /++
    Returns (a ref to) the value associated with a given key.

    If there is no entry associated with the given key, dereferencing this function's return value leads to undefined behavior.

    See_Also: [require], [get]
    +/
    static if (Value.sizeof > 0) ref inout(Value) opIndex()(auto ref const(Key) key) inout
    in (key in this, "tried to index a key which was not in the hash table")
    {
        inout(Key)* keyp;
        inout(Value)* valp;
        this.get(key, keyp, valp);
        return *valp;
    }

    /++
    Upserts an entry in the hash table. May cause a [rehash].

    Returns: Zero on success, non-zero on failure (e.g. OOM or overflow).

    See_Also: [update]
    +/
    pragma(inline) err_t opIndexAssign(Value value, Key key) {
        err_t error;
        this.update(key, () => value, (ref Value old) => value, error);
        return error;
    }

    private err_t initialize(size_t capacity) nothrow
    in (this.buckets == null)
    out (; this.length == 0)
    {
        if (capacity == 0) return 0;

        // adjust allocation size based on max load factor and round to power of two
        if (capacity * maxLoadFactor.denominator <= capacity) return EOVERFLOW;
        capacity = capacity * maxLoadFactor.denominator / maxLoadFactor.numerator;
        if (capacity < minAllocatedSize) {
            capacity = minAllocatedSize;
            static assert(
                minAllocatedSize.isPowerOf2,
                "min allocated size must be a power of 2"
            );
        } else if (!capacity.isPowerOf2) {
            import std.math.algebraic : nextPow2;
            capacity = nextPow2(capacity);
            if (capacity * maxLoadFactor.numerator <= capacity) return EOVERFLOW;
        }
        assert(capacity >= minAllocatedSize && capacity.isPowerOf2);

        // allocate bucket (and value) array
        this.buckets = allocate!Bucket(capacity);
        if (this.buckets == null) return ENOMEM;
        static if (Value.sizeof > 0) {
            this.values = () @trusted { return allocate!Value(capacity).ptr; }();
            if (this.values == null) {
                () @trusted { this.buckets.deallocate(); }();
                this.buckets = null;
                return ENOMEM;
            }
        }

        // initialize bookkeeping state
        foreach (ref bucket; this.buckets) {
            bucket.isOccupied = false;
            bucket.wasDeleted = false;
        }
        this.occupied = 0;
        this.used = 0;

        return 0;
    }

    /// [clear|Clear]s and frees the table's internal storage.
    void dispose() nothrow @system
    out (; this.capacity == 0)
    {
        static if (hasElaborateDestructor!Key || hasElaborateDestructor!Value) this.clear();
        static if (Value.sizeof > 0) deallocate(this.values[0 .. this.allocated]);
        this.buckets.deallocate();
        this = UnsafeHashMap.init;
    }

    /++
    Rehashes the table.

    Manual rehashes may make future lookups more efficient.
    This is also the only way to reduce a hash table's memory footprint.
    Nothing happens to the table in case of failure.

    Params:
        newCapacity = Min number of preallocated entries, must be enough to fit current entries.

    Returns:
        Zero on success, non-zero on failure (on OOM, overflow or an invalid capacity).
    +/
    err_t rehash(size_t newCapacity) nothrow @system
    in (newCapacity >= this.length, "table capacity must be enough to fit its current entries")
    out (error; error || this.capacity >= newCapacity)
    {
        if (newCapacity < this.length) return EINVAL;

        // edge case: rehash empty table to zero capacity
        if (newCapacity == 0 && this.length == 0) {
            this.dispose();
            const error = this.initialize(0);
            assert(!error, "zero capacity doesn't allocate and thus can't fail");
            return 0;
        }

        // otherwise, pretend that we're initializing a new table
        UnsafeHashMap newTable;
        const error = newTable.initialize(newCapacity);
        if (error) return error;

        // relocate every in-use entry to a newly-computed bucket
        assert(newTable.allocated >= this.used);
        size_t filled = 0;
        foreach (size_t i, ref oldBucket; this.buckets) {
            if (!oldBucket.isOccupied || oldBucket.wasDeleted) continue;
            const k = newTable.buckets.probeFor(oldBucket.key);
            auto newBucket = &newTable.buckets[k];
            newBucket.isOccupied = true;
            newBucket.wasDeleted = false;
            moveEmplace(oldBucket.key, newBucket.key);
            static if (Value.sizeof > 0) moveEmplace(*this.valueAt(i), *newTable.valueAt(k));
            filled++;
        }
        assert(filled == this.used);
        newTable.occupied = filled;
        newTable.used = filled;

        // finally, free the old table and replace it with the new one
        this.dispose();
        this = newTable;
        return 0;
    }

    /// ditto
    err_t rehash() {
        return this.rehash(this.length);
    }

    private pragma(inline) bool getEntry(
        ref const(Key) needle,
        out inout(Bucket)* bucket,
        out inout(Value)* value
    ) inout
    @trusted // due to cast from Key* to Bucket*
    {
        auto key = needle in this;
        if (key == null) return false;
        static assert(
            Bucket.key.offsetof == 0,
            "bucket layout must ensure safe cast to key"
        );
        bucket = cast(inout(Bucket)*)key;
        const size_t k = bucket - this.buckets.ptr;
        value = this.valueAt(k);
        return true;
    }

    /++
    Looks up an entry in the table's internal storage.

    Yields pointers to the hash table's internal storage, which may be invalidated by any [rehash]es.

    Params:
        needle = Key which designates the entry being looked up.
        keyp = Set to entry key's address (or `null` when not found).
        valp = Set to entry value's address (or `null` when it is a zero-sized type).

    Returns: Whether or not the entry was found in the table.
    +/
    bool get()(
        auto ref const(Key) needle,
        out inout(Key)* keyp,
        out inout(Value)* valp
    ) inout {
        inout(Bucket)* bucket;
        const found = this.getEntry(needle, bucket, valp);
        if (!found) return false;
        keyp = &bucket.key;
        return true;
    }

    /++
    Removes a key's entry from the table.

    This procedure will also call `destroy` on both key and value.

    Returns: Whether or not the key had an entry to begin with.
    +/
    bool remove()(auto ref const(Key) key) nothrow {
        Bucket* bucket;
        Value* valp;
        const found = this.getEntry(key, bucket, valp);
        if (!found) return false;
        // on deletion, we simply mark the bucket and decrease entry count
        destroy!false(bucket.key);
        static if (Value.sizeof > 0) destroy!false(*valp);
        bucket.wasDeleted = true;
        this.used--;
        return true;
    }

    /// [remove|Remove]s all elements from the hash table, without changing its capacity.
    void clear() nothrow
    out (; this.length == 0)
    {
        size_t toBeCleared = this.length;
        for (size_t k = 0; toBeCleared > 0 && k < this.buckets.length; ++k) {
            auto bucket = &this.buckets[k];
            if (!bucket.isOccupied || bucket.wasDeleted) continue;
            destroy!false(bucket.key);
            static if (Value.sizeof > 0) destroy!false(*this.valueAt(k));
            bucket.isOccupied = false;
            bucket.wasDeleted = false;
            --toBeCleared;
        }
        this.occupied = 0;
        this.used = 0;
    }

    /++
    Looks up a key's entry in the table, then either updates it or creates a new one (may [rehash]).

    Params:
        key = Key being looked up and stored in the table.
        create = Called to construct a new value if the key isn't in the table.
        update = Called to update the value of an entry, if it was found.
        error = Set to zero on success, non-zero otherwise.

    Returns: The entry's final value (or its `.init` in case of failure).
    +/
    Value update(Create, Update)(
        Key key,
        scope auto ref const(Create) create,
        scope auto ref const(Update) update,
        out err_t error
    ) nothrow
    if (is(ReturnType!Create == Value)
        && Parameters!Create.length == 0
        && is(ReturnType!Update == Value)
        && Parameters!Update.length == 1
        && is(Parameters!Update[0] == Value))
    out (; this.used <= this.occupied && this.occupied <= this.allocated)
    {
        // check whether a load factor increase needs to trigger a rehash
        if (this.occupied + 1 > this.capacity) {
            size_t newCapacity = this.capacity * 2;
            if (newCapacity == 0) {
                newCapacity = cast(size_t)(minAllocatedSize * maxLoadFactor);
                static assert(
                    minAllocatedSize * maxLoadFactor > 0,
                    "min allocation size " ~ minAllocatedSize.stringof ~
                    " and max load factor " ~ maxLoadFactor.stringof ~
                    " are incompatible: their product must be greater than zero"
                );
            } else if (newCapacity <= this.capacity) {
                error = EOVERFLOW;
                return Value.init;
            }
            assert(newCapacity > this.capacity);
            error = this.rehash(newCapacity);
            if (error) return Value.init;
        }

        // find the key's designated bucket
        const k = this.buckets.probeFor(key);
        auto bucket = &this.buckets[k];
        const hadEntry = bucket.isOccupied && !bucket.wasDeleted;

        // increase load factor only if we're not reusing some freed bucket
        if (!bucket.isOccupied) this.occupied++;
        bucket.isOccupied = true;
        bucket.wasDeleted = false;

        // check whether we need to create a value or update the old one
        if (!hadEntry) {
            this.used++;
            moveEmplace(key, bucket.key);
            Value newValue = create();
            static if (Value.sizeof > 0) {
                moveEmplace(newValue, *this.valueAt(k));
                return *this.valueAt(k);
            } else {
                return newValue;
            }
        } else /* hadEntry */ {
            swap(key, bucket.key);
            static if (Value.sizeof > 0) {
                Value newValue = update(*this.valueAt(k));
                swap(newValue, *this.valueAt(k));
                return *this.valueAt(k);
            } else {
                Value oldValue = Value.init;
                return update(oldValue);
            }
        }
    }

    /// ditto
    Value update(Create, Update)(
        Key key,
        scope auto ref const(Create) create,
        scope auto ref const(Update) update
    ) {
        err_t ignored;
        return this.update(key, create, update, ignored);
    }

    /++
    Looks up a key's entry, inserting one if not found (may [rehash]).

    Params:
        key = Key being looked up and stored in the table.
        create = Called to construct a new value if the key isn't in the table.
        error = Set to zero on success, non-zero otherwise.

    Returns: The entry's final value (or its `.init` in case of failure).
    +/
    pragma(inline) Value require(Create)(
        Key key,
        scope auto ref const(Create) create,
        out err_t error
    ) {
        return this.update(key, create, (ref Value x) => x, error);
    }

    /// ditto
    Value require(Create)(Key key, auto ref const(Create) create) {
        err_t ignored;
        return this.require(key, create, ignored);
    }

    /++
    Creates an independent copy of a hash table.

    Elements are copied by simple assignment, which may translate into a shallow copy.

    Params:
        error = Set to zero on success, non-zero otherwise.

    Returns: A shallow copy of the given hash table, or an empty table in case of failure (OOM).
    +/
    UnsafeHashMap dup(out err_t error) const nothrow
    out (copy; (!error && copy.length == this.length) || (error && copy.capacity == 0))
    {
        UnsafeHashMap copy;
        error = copy.initialize(this.length);
        if (error) return copy;
        foreach (entry; this.byKeyValue) {
            error = (copy[cast(Key)entry.key] = cast(Value)entry.value);
            assert(!error, "memory already reserved, so insertion can't fail");
        }
        return copy;
    }

    /// ditto
    UnsafeHashMap dup() const {
        err_t ignored;
        return this.dup(ignored);
    }

    /++
    Adds an element to the hash set; may [rehash].

    Returns: Zero on success, non-zero on failure (e.g. OOM or overflow).
    +/
    static if (Value.sizeof == 0) pragma(inline) err_t add(Key element) {
        return (this[element] = Value.init);
    }

    private {
        mixin template UnsafeRangeBoilerplate(bool isConst) {
            static if (isConst) private const(UnsafeHashMap)* table;
            else                private UnsafeHashMap* table;
            private size_t index;

            private this(typeof(this.table) t) {
                this.table = t;
                this.updateIndexFrom(0);
                // OPT: what if we already knew a good starting index
            }

            private void updateIndexFrom(size_t i) {
                for (; i < this.table.buckets.length; ++i) {
                    const bucket = &this.table.buckets[i];
                    if (bucket.isOccupied && !bucket.wasDeleted) break;
                }
                this.index = i;
            }

            public bool empty() const {
                return this.index >= this.table.buckets.length;
            }

            public void popFront() in (!this.empty) {
                this.updateIndexFrom(this.index + 1);
            }
        }

        struct ByKey(bool isConst) {
            mixin UnsafeRangeBoilerplate!isConst;
            public ref front() in (!this.empty) {
                return this.table.buckets[this.index].key;
            }
        }

        struct ByValue(bool isConst) if (Value.sizeof > 0) {
            mixin UnsafeRangeBoilerplate!isConst;
            public ref front() in (!this.empty) {
                return *this.table.valueAt(this.index);
            }
        }

        struct ByKeyValue(bool isConst) {
            mixin UnsafeRangeBoilerplate!isConst;
            private struct Pair(K, V) if (V.sizeof > 0) { K key; V value; }
            private struct Pair(K, V) if (V.sizeof == 0) { K key; enum value = Value.init; }
            static if (isConst) alias KeyValue = Pair!(const(Key), const(Value));
            else                alias KeyValue = Pair!(Key, Value);
            public KeyValue front() in (!this.empty) {
                auto bucket = &this.table.buckets[this.index];
                static if (Value.sizeof > 0)
                    return KeyValue(bucket.key, *this.table.valueAt(this.index));
                else
                    return KeyValue(bucket.key);
            }
        }
    }

    /++
    Can be used to iterate over this table's entries (but iteration order is unspecified).

    NOTE: Mutating a table (silently) invalidates any ranges over it.
        Also, ranges must NEVER outlive their backing tables (this is only OK for the refcounted versions).
    +/
    auto byKey() const { return ByKey!true(&this); }

    /// ditto
    auto byKey() { return ByKey!false(&this); }

    /// ditto
    static if (Value.sizeof > 0) {
        auto byValue() const { return ByValue!true(&this); }
        auto byValue() { return ByValue!false(&this); }
    }

    /// ditto
    auto byKeyValue() const { return ByKeyValue!true(&this); }

    /// ditto
    auto byKeyValue() { return ByKeyValue!false(&this); }
}

/// This type optimizes storage when value types are zero-sized (e.g. for [UnsafeHashSet]):
@nogc nothrow pure @safe unittest {
    alias NonZero = long;
    alias Zero = void[0];
    static assert(UnsafeHashMap!(char, Zero).sizeof < UnsafeHashMap!(char, NonZero).sizeof);
}

/// Consider using `scope(exit)` to ensure hash table memory doesn't leak.
@nogc nothrow unittest {
    UnsafeHashMap!(char, long) outer;
    {
        auto inner = UnsafeHashMap!(char, long)(42);
        scope(exit) inner.dispose();
        outer = inner; // but be careful with shallow copies
    }
    // outer.dispose(); // would have caused a double free: `dispose` is unsafe!
}

/// Basic usage:
@nogc nothrow @safe unittest {
    HashMap!(char, long) table;
    assert(table.length == 0);

    assert('a' !in table);
    table['a'] = 0; // inserts
    assert('a' in table);
    table['a'] = 1; // updates
    assert(table.length == 1);

    assert('a' in table);
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

    const cap = table.capacity;
    table.clear(); // preserves capacity
    assert(table.length == 0);
    assert(table.capacity == cap);
}

/// Sligthly more advanced example:
@nogc nothrow @safe unittest {
    import core.stdc.ctype : isalnum;
    import eris.util : empty;

    bool isAnagram(const(string) a, const(string) b) {
        // count letter frequencies in A
        HashMap!(char, long) letters;
        foreach (c; a) {
            if (!c.isalnum) continue;
            const freq = letters.get(c, () => 0L);
            letters[c] = freq + 1;
        }
        // check if they match B's
        foreach (c; b) {
            if (!c.isalnum) continue;
            const freq = letters.update(c, () => -1L, (long f) => f - 1);
            if (freq < 0) return false;
            else if (freq == 0) letters.remove(c);
        }
        return letters.empty;
    }

    assert(  isAnagram("tom marvolo riddle", "i am lord voldemort") );
    assert( !isAnagram("aabaa", "bbabb")                            );
}

@nogc nothrow @safe unittest {
    HashMap!(int, int) a, b;
    a[0] = 1;
    b[1] = 0;
    assert(a.toHash() != b.toHash());
}


/++
Unordered hash set.

See_Also: The safer [HashSet]
+/
alias UnsafeHashSet(T) = UnsafeHashMap!(T, Unit);

///
@nogc nothrow @safe unittest {
    static immutable long[6] list = [0, 1, 42, 32_767, -32_768, 0];
    enum N = list.length;

    auto a = HashSet!long(N);
    auto b = HashSet!long();
    a.rehash(N);
    assert(a.capacity == N);
    foreach (n; list) a.add(n);
    assert(a.length == N - 1); // one less because of the duplicate 0

    assert(a != b);
    b = a.dup;
    assert(a !is b && a == b); // structural equality works
}

nothrow @safe unittest {
    HashSet!long a, b;
    a.add(0);
    b = a.dup;

    HashMap!(HashSet!long, string) stringified;
    stringified[a] = a.toString();
    assert(stringified[a] == "#{0}");
    assert(b in stringified); // structural hashing as well

    b.remove(0);
    b.add(-1);
    assert(a != b);
    assert(b !in stringified); // but be careful with mutability
}


/++
Safe version of [UnsafeHashMap].

Uses reference counting to avoid manual deallocation problems (i.e. double free) and never exposes references to its internal storage (so the API is similar but not the same).
Again, this type uses reference counting, so cycles must be avoided to ensure memory doesn't leak.
+/
struct HashMap(Key, Value) {
 private:
    import core.lifetime : forward;
    import std.typecons : RefCountedAutoInitialize;

    // a safe version of our hash table needs to ensure two things:
    // 1) `dispose` is never called twice on a hash table + its copies (i.e. double frees don't happen)
    // 2) internal storage is never referenced from the outside (i.e. rehashes don't invalidate pointers)

    // we begin by making it impossible for user code to call `dispose` on the safe version
    static assert(!__traits(compiles, {
        HashMap table;
        table.dispose();
    }));

    // the above would solve (1), but always leak memory, so we make an RAII version
    // of the hash table which is non-copyable and ALWAYS calls dispose on scope exit
    struct RAIIUnsafeHashMap {
        UnsafeHashMap!(Key, Value) table;
        @disable this(this);
        ~this() @trusted { this.table.dispose(); }
    }

    // since non-copyable types are a pain in the ass, we make the RAII table refcounted,
    // which ensures the destructor is only called once (so we mark it as @trusted)
    RefCountedTrusted!(RAIIUnsafeHashMap, RefCountedAutoInitialize.no) rc;

    // as for (2), we manually review the hash table API to only ever expose functionality
    // which does not leak references to the hash table's internal storage
    // and then mark as @trusted any operation which could rehash (because that's safe now)
    pragma(inline) @safe {
        @property bool isInitialized() const {
            return this.rc.refCountedStore.isInitialized;
        }

        void ensureInitialized() {
            this.rc.refCountedStore.ensureInitialized();
        }

        @property ref inout(UnsafeHashMap!(Key, Value)) impl() inout @trusted
        in (this.isInitialized)
        {
            return this.rc.refCountedPayload.table;
        }
    }

 public:
    this(size_t capacity) {
        this.ensureInitialized();
        this.impl.initialize(capacity);
    }

    void opAssign(HashMap other) {
        this.rc = other.rc;
    }

    version (D_BetterC) {} else {
        auto toString() const {
            if (!this.isInitialized) return "#{}";
            return this.impl.toString();
        }
    }

    auto toHash() const {
        if (!this.isInitialized) return 0;
        return this.impl.toHash();
    }

    auto opEquals()(auto ref const(HashMap) other) const {
        if (!this.isInitialized && !other.isInitialized) return true; // both null
        if (!this.isInitialized || !other.isInitialized) return false; // one null
        return this.impl == other.impl; // both non-null
    }

    @property auto length() const {
        if (!this.isInitialized) return 0;
        return this.impl.length;
    }

    @property auto capacity() const {
        if (!this.isInitialized) return 0;
        return this.impl.capacity;
    }

    /// Changed to safely return a `bool` instead of an internal pointer.
    bool opBinaryRight(string op : "in")(auto ref const(Key) key) const {
        if (!this.isInitialized) return false;
        return (key in this.impl) != null;
    }

    static if (Value.sizeof > 0) auto opIndex()(auto ref const(Key) key) const {
        return this.get(key, () => Value.init);
    }

    auto opIndexAssign(Value value, Key key) @trusted {
        this.ensureInitialized();
        return (this.impl[key] = value);
    }

    // removed: dispose

    auto rehash(size_t newCapacity) @trusted {
        this.ensureInitialized();
        return this.impl.rehash(newCapacity);
    }

    auto rehash() @trusted {
        this.ensureInitialized();
        return this.impl.rehash();
    }

    /// The safe version matches AA's [get](https://dlang.org/spec/hash-map.html#properties).
    inout(Value) get(Default)(auto ref const(Key) key, scope auto ref const(Default) defaultValue) inout
    if (is(ReturnType!Default == Value) && Parameters!Default.length == 0)
    {
        if (!this.isInitialized) return defaultValue();
        inout(Key)* keyp;
        inout(Value)* valp;
        const found = this.impl.get(key, keyp, valp);
        return found ? *valp : defaultValue();
    }

    auto remove()(auto ref const(Key) key) {
        this.ensureInitialized();
        return this.impl.remove(key);
    }

    auto clear() {
        this.ensureInitialized();
        return this.impl.clear();
    }

    auto update(Args...)(Key needle, auto ref Args args) @trusted {
        this.ensureInitialized();
        return this.impl.update(needle, forward!args);
    }

    auto require(Args...)(Key needle, auto ref Args args) @trusted {
        this.ensureInitialized();
        return this.impl.require(needle, forward!args);
    }

    HashMap dup(out err_t error) const @trusted {
        if (!this.isInitialized) return HashMap.init;
        HashMap copy;
        copy.ensureInitialized();
        copy.impl = this.impl.dup(error);
        return copy;
    }

    HashMap dup() const {
        err_t ignored;
        return this.dup(ignored);
    }

    static if (Value.sizeof == 0) auto add(Key element) @trusted  {
        return (this[element] = Value.init);
    }

    private {
        mixin template RangeBoilerplate(bool isConst = true) {
            static if (isConst) private const(HashMap) table;
            else                private HashMap table;
            private size_t index;

            private this(typeof(this.table) t) {
                this.table = t;
                this.updateIndexFrom(0);
            }

            private void updateIndexFrom(size_t i) {
                if (!this.table.isInitialized) return;
                for (; i < this.table.impl.buckets.length; ++i) {
                    const bucket = &this.table.impl.buckets[i];
                    if (bucket.isOccupied && !bucket.wasDeleted) break;
                }
                this.index = i;
            }

            public bool empty() const {
                return !this.table.isInitialized || this.index >= this.table.impl.buckets.length;
            }

            public void popFront() in (!this.empty) {
                this.updateIndexFrom(this.index + 1);
            }
        }

        struct ByKey(bool isConst) {
            mixin RangeBoilerplate!isConst;
            public auto front() in (!this.empty) {
                return this.table.impl.buckets[this.index].key;
            }
        }

        struct ByValue(bool isConst) if (Value.sizeof > 0) {
            mixin RangeBoilerplate!isConst;
            public auto front() in (!this.empty) {
                return *this.table.impl.valueAt(this.index);
            }
        }

        struct ByKeyValue(bool isConst) {
            mixin RangeBoilerplate!isConst;
            private struct Pair(K, V) if (V.sizeof > 0) { K key; V value; }
            private struct Pair(K, V) if (V.sizeof == 0) { K key; enum value = Value.init; }
            static if (isConst) alias KeyValue = Pair!(const(Key), const(Value));
            else                alias KeyValue = Pair!(Key, Value);
            public KeyValue front() in (!this.empty) {
                auto bucket = &this.table.impl.buckets[this.index];
                static if (Value.sizeof > 0)
                    return KeyValue(bucket.key, *this.table.impl.valueAt(this.index));
                else
                    return KeyValue(bucket.key);
            }
        }
    }

    auto byKey() const { return ByKey!true(this); }
    auto byKey() { return ByKey!false(this); }

    static if (Value.sizeof > 0) {
        auto byValue() const { return ByValue!true(this); }
        auto byValue() { return ByValue!false(this); }
    }

    auto byKeyValue() const { return ByKeyValue!true(this); }
    auto byKeyValue() { return ByKeyValue!false(this); }
}

///
@nogc nothrow @safe unittest {
    HashMap!(char, long) outer;
    outer['o'] = 0; // outer -> { 'o': 0 }

    {
        HashMap!(char, long) inner;
        inner['i'] = 1; // inner -> { 'i': 1 }
        outer = inner;
        // with the previous assignment, { 'o': 0 } was deallocated
    }

    // as inner goes out of scope, it decreases the ref count of { 'i': 1 }
    // but since outer still holds a reference to it, it wasn't deallocated
    assert(outer['i'] == 1); // outer -> { 'i': 1 }
    assert('o' !in outer);
}

/// Safe version of [UnsafeHashSet].
alias HashSet(T) = HashMap!(T, Unit);
