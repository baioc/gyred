/++
This module provides hash tables with deterministic memory usage (not reliant on the GC), as a betterC alternative to the built-in AAs.

Includes both unsafe (explicitly managed) and safe (refcounted) hash-based data types.
+/
module eris.hash_table;

import core.stdc.errno : ENOMEM, EINVAL;
import std.algorithm.mutation : moveEmplace, swap;
import std.math.traits : isPowerOf2;
import std.meta : ApplyRight;
import std.traits : Parameters, ReturnType;

import eris.core : allocate, deallocate, err_t, Unit, hash_t;
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
    enum size_t minAllocatedSize = 8;

    // Returns the index where the given key is or would be placed.
    size_t probeFor(K)(const(Bucket!(K)[]) buckets, ref const(K) key)
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

    Bucket[] buckets = null;
    size_t occupied = 0;
    size_t used = 0;

    // we only need to allocate a value array if its size is non-zero
    static if (Value.sizeof > 0) Value* values = null;

    pragma(inline) {
        @property size_t allocated() const {
            return this.buckets.length;
        }

        inout(Value)* valueAt(size_t index) inout
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

    // since we're doing closed hashing, for every set of slots we have:
    // used <= occupied <= allocate (where allocations are performed in bulk)
    invariant {
        assert(used <= occupied);
        assert(occupied <= allocated);
        assert((buckets.ptr == null && allocated == 0)
            || (buckets.ptr != null && allocated != 0));
        static if (Value.sizeof > 0) {
            assert((buckets.ptr == null && values == null)
                || (buckets.ptr != null && values != null));
        }
    }

 public:
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
            // for each entry, we use a noncommutative operation, scaled by a Fibonacci number
            static if (__traits(compiles, () @safe => entry.value.hashOf)) {
                enum size_t scale = 2654435771UL; // approx. 2^32 / phi
                tableHash ^= (entry.key.hashOf - entry.value.hashOf) * scale;
            }
            // if hashing values is unsafe, we want to depend only on the key's hash
            else {
                tableHash ^= entry.key.hashOf;
            }
        }
        return tableHash;
    }

    /// Structural equality comparison.
    bool opEquals(ref const(UnsafeHashMap) other) const {
        if (this is other) return true;
        if (other.length != this.length) return false;
        foreach (entry; this.byKeyValue) {
            if (entry.key !in other || entry.value != other[entry.key]) return false;
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
        return cast(size_t)(this.allocated * maxLoadFactor);
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
    Returns the value associated with a given key, or its `.init`

    See_Also: [require], [get]
    +/
    inout(Value) opIndex()(auto ref const(Key) key) inout
    out (value; key in this || value is Value.init)
    {
        inout(Key)* keyp;
        inout(Value)* valp;
        const found = this.get!(Key, Value)(key, keyp, valp);
        static if (Value.sizeof > 0)
            return found ? *valp : Value.init;
        else
            return Value.init;
    }

    /++
    Upserts an entry in the hash table. May cause a [rehash].

    Returns: Zero on success, non-zero on failure (e.g. OOM or overflow).

    See_Also: [update]
    +/
    err_t opIndexAssign(Value value, Key key) {
        err_t error;
        this.update(key, () => value, (ref Value old) => value, error);
        return error;
    }
}

/// This type optimizes storage when value types are zero-sized (e.g. for [UnsafeHashSet]):
@nogc nothrow pure @safe unittest {
    alias NonZero = long;
    alias Zero = void[0];
    static assert(UnsafeHashMap!(char, Zero).sizeof < UnsafeHashMap!(char, NonZero).sizeof);
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

/// Sligthly more advanced example with `require` and `update`:
@nogc nothrow @safe unittest {
    import core.stdc.ctype : isalnum;
    import eris.util : empty;

    bool isAnagram(const(string) a, const(string) b) {
        // count letter frequencies in A
        HashMap!(char, long) letters;
        foreach (c; a) {
            if (!c.isalnum) continue;
            const freq = letters.require(c, () => 0L);
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

/// [clear|Clear]s and frees the table's internal storage.
void dispose(K, V)(ref UnsafeHashMap!(K,V) self) nothrow @system
out (; self.capacity == 0)
{
    self.clear();
    assert(self.allocated == self.buckets.length);
    static if (V.sizeof > 0) self.values.deallocate(self.allocated);
    self.buckets.ptr.deallocate(self.allocated);
    self = UnsafeHashMap!(K,V).init;
}

/// Consider using `scope(exit)` to ensure hash table memory doesn't leak.
@nogc nothrow unittest {
    UnsafeHashMap!(char, long) outer;
    {
        UnsafeHashMap!(char, long) inner;
        scope(exit) inner.dispose();
        outer = inner; // but be careful with byref-like copies
    }
    // outer.dispose(); // would have caused a double free: `dispose` is unsafe!
}

/// Initializes a hash table.
private err_t initialize(K, V)(out UnsafeHashMap!(K,V) self, size_t capacity) nothrow
in (self.buckets.ptr == null)
out (; self.length == 0)
{
    if (capacity == 0) return 0;

    // adjust allocation size based on max load factor and round to power of two
    const requestedCapacity = capacity;
    capacity = cast(size_t)(capacity / maxLoadFactor);
    if (capacity < requestedCapacity) { // overflow check
        return ENOMEM;
    } else if (capacity < minAllocatedSize) {
        capacity = minAllocatedSize;
        static assert(
            minAllocatedSize.isPowerOf2,
            "min allocated size must be a power of 2"
        );
    } else if (!capacity.isPowerOf2) {
        import std.math.algebraic : nextPow2;
        capacity = nextPow2(capacity);
        if (capacity == 0) return ENOMEM;
    }
    assert(capacity >= minAllocatedSize && capacity.isPowerOf2);
    if (capacity * maxLoadFactor.numerator < capacity) // overflow check
        return ENOMEM;

    // allocate bucket (and value) array
    auto buffer = allocate!(Bucket!K)(capacity);
    if (buffer == null) return ENOMEM;
    () @trusted { self.buckets = buffer[0 .. capacity]; }();
    static if (V.sizeof > 0) {
        self.values = allocate!V(capacity);
        if (self.values == null) {
            () @trusted { buffer.deallocate(capacity); }();
            self.buckets = null;
            return ENOMEM;
        }
    }

    // initialize buckets' state
    foreach (ref bucket; self.buckets) {
        bucket.isOccupied = false;
        bucket.wasDeleted = false;
    }
    self.occupied = 0;
    self.used = 0;

    return 0;
}

/++
Rehashes the table.

Manual rehashes may make future lookups more efficient.
This is also the only way to reduce a hash table's memory footprint.
Nothing happens to the table in case of failure.

Params:
    self = Hash table.
    newCapacity = Min number of pre-allocated entries, must be enough to fit current entries.

Returns:
    Zero on success, non-zero on failure (on OOM, overflow or an invalid capacity).
+/
err_t rehash(K, V)(ref UnsafeHashMap!(K,V) self, size_t newCapacity) nothrow @system
in (newCapacity >= self.length, "table capacity must be enough to fit its current entries")
out (error; error || self.capacity >= newCapacity)
{
    if (newCapacity < self.length) return EINVAL;

    // edge case: rehash empty table to zero capacity
    if (newCapacity == 0 && self.length == 0) {
        self.dispose();
        const error = self.initialize(0);
        assert(!error, "zero capacity doesn't allocate and thus can't fail");
        return 0;
    }

    // otherwise, pretend that we're initializing a new table
    UnsafeHashMap!(K,V) newTable;
    const error = newTable.initialize(newCapacity);
    if (error) return error;

    // relocate every in-use entry to a newly-computed bucket
    assert(newTable.allocated >= self.used);
    size_t filled = 0;
    foreach (size_t i, ref oldBucket; self.buckets) {
        if (!oldBucket.isOccupied || oldBucket.wasDeleted) continue;
        const k = newTable.buckets.probeFor(oldBucket.key);
        auto newBucket = &newTable.buckets[k];
        newBucket.isOccupied = true;
        newBucket.wasDeleted = false;
        moveEmplace(oldBucket.key, newBucket.key);
        static if (V.sizeof > 0) moveEmplace(*self.valueAt(i), *newTable.valueAt(k));
        filled++;
    }
    assert(filled == self.used);
    newTable.occupied = filled;
    newTable.used = filled;

    // finally, free the old table and replace it with the new one
    self.dispose();
    self = newTable;
    return 0;
}

/// ditto
err_t rehash(K, V)(ref UnsafeHashMap!(K,V) self) {
    enum targetLoadFactor = Rational!size_t(1, 2);
    enum allocationAdjustment = maxLoadFactor / targetLoadFactor;
    static assert(allocationAdjustment >= 1.0);
    auto newCapacity = cast(size_t)(self.length * allocationAdjustment);
    newCapacity = newCapacity < self.length ? self.length : newCapacity; // overflow check
    return self.rehash(newCapacity);
}

private pragma(inline) bool _get(K, V)(
    ref inout(UnsafeHashMap!(K,V)) self,
    auto ref const(K) find,
    out inout(Bucket!K)* bucket,
    out inout(V)* value,
)
@trusted // due to cast from Key* to Bucket*
{
    auto key = find in self;
    if (key == null) return false;
    static assert(
        Bucket!(K).key.offsetof == 0,
        "bucket layout must ensure safe cast to key"
    );
    bucket = cast(inout(Bucket!K)*) key;
    const size_t k = bucket - self.buckets.ptr;
    value = self.valueAt(k);
    return true;
}

/++
Looks up an entry in the table's internal storage.

Yields pointers to the hash table's internal storage, which may be invalidated by any [rehash]es.

Params:
    self = Backing hash table.
    find = Key which designates the entry being looked up.
    keyp = Set to entry key's address (or `null` when not found).
    valp = Set to entry value's address (or `null` when it is a zero-sized type).

Returns: Whether or not the entry was found in the table.
+/
bool get(K, V)(
    ref inout(UnsafeHashMap!(K,V)) self,
    auto ref const(K) find,
    out inout(K)* keyp,
    out inout(V)* valp
)
out (found; (found && *keyp in self) || (!found && keyp == null))
{
    inout(Bucket!K)* bucket;
    const found = self._get!(K,V)(find, bucket, valp);
    if (!found) return false;
    keyp = &bucket.key;
    return true;
}

/// ditto
bool get(K, V)(
    ref inout(UnsafeHashMap!(K,V)) self,
    auto ref const(K) find,
    out inout(K)* keyp
) {
    inout(V)* valp;
    return self.get(find, keyp, valp);
}

/++
Removes a key's entry from the table.

This procedure will also call `destroy` on both key and value.

Returns: Whether or not the key had an entry to begin with.
+/
bool remove(K, V)(ref UnsafeHashMap!(K,V) self, auto ref const(K) key) nothrow
out (; key !in self)
{
    Bucket!(K)* bucket;
    V* valp;
    const found = self._get(key, bucket, valp);
    if (!found) return false;
    // on deletion, we simply mark the bucket and decrease entry count
    destroy!false(bucket.key);
    static if (V.sizeof > 0) destroy!false(*valp);
    bucket.wasDeleted = true;
    self.used--;
    return true;
}

/// [remove|Remove]s all elements from the hash table, without changing its capacity.
void clear(K, V)(ref UnsafeHashMap!(K,V) self) nothrow
out (; self.length == 0)
{
    size_t toBeCleared = self.length;
    foreach (size_t k, ref bucket; self.buckets) {
        if (!bucket.isOccupied || bucket.wasDeleted) continue;
        destroy!false(bucket.key);
        static if (V.sizeof > 0) destroy!false(*self.valueAt(k));
        bucket.isOccupied = false;
        bucket.wasDeleted = false;
        --toBeCleared;
        if (toBeCleared == 0) break;
    }
    self.occupied = 0;
    self.used = 0;
}

/++
Looks up a key's entry in the table, then either updates it or creates a new one (may [rehash]).

Params:
    self = Hash table.
    key = Key being looked up and stored in the table.
    create = Called to construct a new value if the key isn't in the table.
    update = Called to update the value of an entry, if it was found.
    error = Set to zero on success, non-zero otherwise.

Returns: The entry's final value (or its `.init` in case of failure).
+/
pragma(inline) V update(K, V, Create, Update)(
    ref UnsafeHashMap!(K,V) self,
    K key,
    scope auto ref const(Create) create,
    scope auto ref const(Update) update,
    out err_t error
) nothrow
if (is(ReturnType!Create == V)
    && Parameters!Create.length == 0
    && is(ReturnType!Update == V)
    && Parameters!Update.length == 1
    && is(Parameters!Update[0] == V))
{
    // check whether a load factor increase needs to trigger a rehash
    if (self.occupied + 1 > self.capacity) {
        size_t newCapacity = self.capacity * 2;
        if (newCapacity == 0) {
            newCapacity = cast(size_t)(minAllocatedSize * maxLoadFactor);
            static assert(
                minAllocatedSize * maxLoadFactor > 0,
                "min allocation size " ~ minAllocatedSize.stringof ~
                " and max load factor " ~ maxLoadFactor.stringof ~
                " are incompatible: their product must be greater than zero"
            );
        } else if (newCapacity < self.capacity) { // overflow check
            error = ENOMEM;
            return V.init;
        }
        assert(newCapacity > self.capacity);
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
    if (!hadEntry) {
        self.used++;
        moveEmplace(key, bucket.key);
        V newValue = create();
        static if (V.sizeof > 0) {
            moveEmplace(newValue, *self.valueAt(k));
            return *self.valueAt(k);
        } else {
            return newValue;
        }
    } else /* hadEntry */ {
        swap(key, bucket.key);
        static if (V.sizeof > 0) {
            V newValue = update(*self.valueAt(k));
            swap(newValue, *self.valueAt(k));
            return *self.valueAt(k);
        } else {
            V oldValue = V.init;
            return update(oldValue);
        }
    }
}

/// ditto
V update(K, V, Create, Update)(
    ref UnsafeHashMap!(K,V) self,
    K key,
    scope auto ref const(Create) create,
    scope auto ref const(Update) update
)
if (is(ReturnType!Create == V)
    && Parameters!Create.length == 0
    && is(ReturnType!Update == V)
    && Parameters!Update.length == 1
    && is(Parameters!Update[0] == V))
{
    err_t ignored;
    return self.update(key, create, update, ignored);
}

/++
Looks up a key's entry, inserting one if not found (may [rehash]).

Params:
    self = Hash table.
    key = Key being looked up and stored in the table.
    create = Called to construct a new value if the key isn't in the table.
    error = Set to zero on success, non-zero otherwise.

Returns: The entry's final value (or its `.init` in case of failure).
+/
V require(K, V, Create)(
    ref UnsafeHashMap!(K,V) self,
    K key,
    scope auto ref const(Create) create,
    out err_t error
)
if (is(ReturnType!Create == V) && Parameters!Create.length == 0)
{
    return self.update(key, create, (ref V x) => x, error);
}

/// ditto
V require(K, V, Create)(
    ref UnsafeHashMap!(K,V) self,
    K key,
    auto ref const(Create) create
)
if (is(ReturnType!Create == V) && Parameters!Create.length == 0)
{
    err_t ignored;
    return self.require(key, create, ignored);
}

private mixin template UnsafeRangeBoilerplate(K, V) {
    private const(UnsafeHashMap!(K,V))* table;
    private size_t index;

    private this(const(UnsafeHashMap!(K,V))* t) {
        this.table = t;
        this.updateIndexFrom(0);
    }

    private void updateIndexFrom(size_t i) {
        for (; i < this.table.buckets.length; ++i) {
            const bucket = &this.table.buckets[i];
            if (bucket.isOccupied && !bucket.wasDeleted) break;
        }
        this.index = i;
    }

    invariant {
        if (this.index < this.table.buckets.length) {
            auto bucket = &this.table.buckets[this.index];
            assert(
                bucket.isOccupied && !bucket.wasDeleted,
                "tried using an invalidated hash table range"
            );
        }
    }

    public bool empty() const {
        return this.index >= this.table.buckets.length;
    }

    public void popFront() in (!this.empty) {
        this.updateIndexFrom(this.index + 1);
    }
}

/++
Can be used to iterate over this table's entries (but iteration order is unspecified ).

NOTE: Mutating a table silently invalidates any ranges over it.
    Also, ranges must NEVER outlive their backing tables if they are unsafe (this is OK only for the refcounted versions).
+/
auto byKey(K, V)(ref const(UnsafeHashMap!(K,V)) self) {
    struct ByKey {
        mixin UnsafeRangeBoilerplate!(K,V);
        public ref const(K) front() const in (!this.empty) {
            return this.table.buckets[this.index].key;
        }
    }
    return ByKey(&self);
}

/// ditto
auto byValue(K, V)(ref const(UnsafeHashMap!(K,V)) self) if (V.sizeof > 0) {
    struct ByValue {
        mixin UnsafeRangeBoilerplate!(K,V);
        public ref const(V) front() const in (!this.empty) {
            return this.table.values[this.index];
        }
    }
    return ByValue(&self);
}

/// ditto
auto byKeyValue(K, V)(ref const(UnsafeHashMap!(K,V)) self) {
    struct ByKeyValue {
        mixin UnsafeRangeBoilerplate!(K,V);
        public const(KeyValue) front() const in (!this.empty) {
            auto bucket = &this.table.buckets[this.index];
            static if (V.sizeof > 0)
                return KeyValue(bucket.key, this.table.values[this.index]);
            else
                return KeyValue(bucket.key);
        }
        struct KeyValue {
            const(K) key;
            static if (V.sizeof > 0) const(V) value;
            else                     enum value = V.init;
        }
    }
    return ByKeyValue(&self);
}

///
@nogc nothrow pure @safe unittest {
    static assert(
        !__traits(compiles, // assuming -dip1000
            () @safe {
                UnsafeHashMap!(char, long) table;
                return table.byKeyValue; // <- escapes ref to local
            }
        ),
        "must not allow a range to outlive its backing hash table"
    );
}

/++
Creates an independent copy of a hash table.

Elements are copied by simple assignment, which may translate into a shallow copy.

Params:
    self = Hash table to be copied.
    error = Set to zero on success, non-zero otherwise.

Returns: A shallow copy of the given hash table, or an empty table in case of failure (OOM).
+/
UnsafeHashMap!(K,V) dup(K, V)(ref const(UnsafeHashMap!(K,V)) self, out err_t error) nothrow
out (copy; (!error && copy.length == self.length) || (error && copy.length == 0))
{
    UnsafeHashMap!(K,V) copy;
    error = copy.initialize(self.length);
    if (error) return copy;
    foreach (entry; self.byKeyValue) {
        error = (copy[entry.key] = entry.value);
        assert(!error, "memory already reserved, so insertion can't fail");
    }
    return copy;
}

/// ditto
UnsafeHashMap!(K,V) dup(K, V)(ref const(UnsafeHashMap!(K,V)) self) {
    err_t ignored;
    return self.dup(ignored);
}


/++
Unordered hash set.

See_Also: The safer [HashSet]
+/
alias UnsafeHashSet = ApplyRight!(UnsafeHashMap, Unit);

///
@nogc nothrow @safe unittest {
    static immutable long[6] list = [0, 1, 42, 32_767, -32_768, 0];
    enum N = list.length;

    HashSet!long a, b;
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
Adds an element to the hash set; may [rehash].

Returns: Zero on success, non-zero on failure (e.g. OOM or overflow).
+/
pragma(inline) err_t add(K, V)(ref UnsafeHashMap!(K, V) self, K element) if (V.sizeof == 0) {
    return (self[element] = V.init);
}


/++
Safe version of [UnsafeHashMap]; same API.

Uses reference counting to avoid manual deallocation problems (i.e. double free) and never exposes references to its internal storage (so the API is actually just slightly different).
Again, this type uses reference counting, so cycles must be avoided to ensure memory doesn't leak.
+/
struct HashMap(Key, Value) {
 private:
    // a safe versions of our hash table needs to ensure two things:
    // 1) `dispose` is never called twice on a hash table + its copies (i.e. double frees don't happen):
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
    // which ensures he destructor is only called once (so we mark it as @trusted)
    import std.typecons : RefCountedAutoInitialize;
    RefCountedTrusted!(RAIIUnsafeHashMap, RefCountedAutoInitialize.no) rc;

    // as for (2), we manually review the hash table API to only ever expose functionality
    // which does not leak references to the hash table's internal storage
    // and then mark as @trusted any operation which could rehash (that's safe now)
    pragma(inline) @safe {
        @property bool isInitialized() const {
            return this.rc.refCountedStore.isInitialized;
        }

        void ensureInitialized() {
            this.rc.refCountedStore.ensureInitialized();
        }

        @property ref inout(UnsafeHashMap!(Key, Value)) impl() inout @trusted {
            assert(this.isInitialized);
            return this.rc.refCountedPayload.table;
        }
    }

 public pragma(inline):
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

    auto opEquals(ref const(HashMap) other) const {
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

    // changed to safely return a bool instead of internal pointer to key
    bool opBinaryRight(string op : "in")(auto ref const(Key) key) const {
        if (!this.isInitialized) return false;
        return (key in this.impl) != null;
    }

    inout(Value) opIndex()(auto ref const(Key) key) inout {
        if (!this.isInitialized) return Value.init;
        return this.impl[key];
    }

    auto opIndexAssign(Value value, Key key) @trusted {
        this.ensureInitialized();
        return (this.impl[key] = value);
    }
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

pragma(inline) {
    // removed: dispose

    auto rehash(K, V)(ref HashMap!(K,V) self, size_t newCapacity) @trusted {
        self.ensureInitialized();
        return self.impl.rehash(newCapacity);
    }

    auto rehash(K, V)(ref HashMap!(K,V) self) @trusted {
        self.ensureInitialized();
        return self.impl.rehash();
    }

    // removed: get

    auto remove(K, V)(ref HashMap!(K,V) self, auto ref const(K) key) {
        self.ensureInitialized();
        return self.impl.remove(key);
    }

    auto clear(K, V)(ref HashMap!(K,V) self) {
        self.ensureInitialized();
        return self.impl.clear();
    }

    auto update(K, V, Args...)(ref HashMap!(K,V) self, K find, Args args) @trusted {
        self.ensureInitialized();
        return self.impl.update(find, args);
    }

    auto require(K, V, Args...)(ref HashMap!(K,V) self, K find, Args args) @trusted {
        self.ensureInitialized();
        return self.impl.require(find, args);
    }

    private mixin template RangeBoilerplate(K, V) {
        private const(HashMap!(K,V)) table;
        private size_t index;

        private this(ref const(HashMap!(K,V)) t) {
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

        invariant {
            if (this.table.isInitialized && this.index < this.table.impl.buckets.length) {
                auto bucket = &this.table.impl.buckets[this.index];
                assert(
                    bucket.isOccupied && !bucket.wasDeleted,
                    "tried using an invalidated hash table range"
                );
            }
        }

        public bool empty() const {
            return !this.table.isInitialized || this.index >= this.table.impl.buckets.length;
        }

        public void popFront() in (!this.empty) {
            this.updateIndexFrom(this.index + 1);
        }

        public typeof(this) save() {
            return this;
        }
    }

    auto byKey(K, V)(ref const(HashMap!(K,V)) self) {
        struct ByKey {
            mixin RangeBoilerplate!(K,V);
            public const(K) front() const in (!this.empty) {
                return this.table.impl.buckets[this.index].key;
            }
        }
        return ByKey(self);
    }

    auto byValue(K, V)(ref const(HashMap!(K,V)) self) if (V.sizeof > 0) {
        struct ByValue {
            mixin RangeBoilerplate!(K,V);
            public const(V) front() const in (!this.empty) {
                return *this.table.impl.valueAt(this.index);
            }
        }
        return ByValue(self);
    }

    auto byKeyValue(K, V)(ref const(HashMap!(K,V)) self) {
        struct ByKeyValue {
            mixin RangeBoilerplate!(K,V);
            public const(KeyValue) front() const in (!this.empty) {
                auto bucket = &this.table.impl.buckets[this.index];
                static if (V.sizeof > 0)
                    return KeyValue(bucket.key, *this.table.impl.valueAt(this.index));
                else
                    return KeyValue(bucket.key);
            }
            struct KeyValue {
                const(K) key;
                static if (V.sizeof > 0) const(V) value;
                else                     enum value = V.init;
            }
        }
        return ByKeyValue(self);
    }

    HashMap!(K,V) dup(K, V)(ref const(HashMap!(K,V)) self, out err_t error) @trusted {
        if (!self.isInitialized) return HashMap!(K,V).init;
        HashMap!(K,V) copy;
        copy.ensureInitialized();
        copy.impl = self.impl.dup(error);
        return copy;
    }

    HashMap!(K,V) dup(K, V)(ref const(HashMap!(K,V)) self) {
        err_t ignored;
        return self.dup(ignored);
    }

    auto add(K, V)(ref HashMap!(K, V) self, K element) @trusted if (V.sizeof == 0) {
        return (self[element] = V.init);
    }
}

/// Safe version of [UnsafeHashSet].
alias HashSet = ApplyRight!(HashMap, Unit);
