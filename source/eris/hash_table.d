/// This module provides simple but efficient hash table data structures with deterministic memory usage (not reliant on the GC), as an alternative to the built-in associative arrays (AAs).
module eris.hash_table;

import core.stdc.errno : ENOMEM, EINVAL;
import std.math.traits : isPowerOf2;
import std.traits : Parameters, ReturnType;

import eris.core : allocate, deallocate, err_t, Unit, hash_t;
import eris.rational : Rational;


private {
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

    enum maxLoadFactor = Rational!size_t(3, 4);
    static assert(
        maxLoadFactor > 0.0 && maxLoadFactor < 1.0,
        "invalid max load factor " ~ maxLoadFactor.stringof ~
        ": must be greater than zero and less than one"
    );

    enum size_t minAllocatedSize = 8;
    static assert(
        minAllocatedSize * maxLoadFactor > 0,
        "min allocation size " ~ minAllocatedSize.stringof ~
        " and max load factor " ~ maxLoadFactor.stringof ~
        " are incompatible: their product must be greater than zero"
    );

    /// Returns the index where the given key is or would be placed.
    size_t probeFor(K)(const(Bucket!(K)[]) buckets, ref const(K) key)
    in (buckets.length > 0, "can't probe an empty table")
    in (buckets.length.isPowerOf2, "table size is not a power of two")
    {
        // number of buckets must be a power of 2 so that we may swap modulos for bitmasks
        const n = buckets.length;
        const size_t mask = n - 1U;

        // step 1: start at index hash(key) % n, check for a hit or free slot
        const hash_t hash = key.hashOf;
        size_t index = hash & mask;
        auto bucket = &buckets[index];
        if (!bucket.isOccupied || (!bucket.wasDeleted && bucket.key == key))
            return index;

        // step 2: collision detected, use the upper hash bits to jump elsewhere
        index = (index + (hash >> (hash_t.sizeof * 8U / 2U))) & mask;

        // step 3: sequentially probe buckets, looking for deleted ones along the way.
        // this procedure is correct as long as probing is deterministic (i.e.
        // insert(k) -> ... -> lookup(k) find the same bucket), and it terminates
        // because at least one bucket must be free and we eventually try them all.
        //
        // we increment by j, where j grows by 1 every iteration, to implement a
        // quadratic probe sequence over the triangular numbers; since we modulo by
        // a power of two, every probed bucket is different (for a proof of this,
        // see http://www.chilton-computing.org.uk/acl/literature/reports/p012.htm )
        static assert(maxLoadFactor < 1.0); // ensures free buckets
        enum notFound = size_t.max; // impossible index because it's always > n
        assert(notFound > n);
        size_t recycled = notFound;
        for (size_t j = 1;; ++j) {
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
Dense hash map acting as a mostly-compatible AA replacement.

The mechanism used to override hashing and comparison functions is [the same as for standard AAs](https://dlang.org/spec/hash-map.html#using_struct_as_key).
Unlike AA's, however, this hash table does NOT guarantee that references to its internal storage will be kept stable between rehashes.
Other than explicit calls to [rehash](#rehash), only insertions may invalidate such references.

See_Also: [HashSet](#HashSet)
+/
struct HashMap(Key, Value) {
 private:
    alias Bucket = .Bucket!Key;

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
        public string toString() const {
            import std.array : appender;
            import std.conv : to;
            import std.string : format;

            auto result = appender!string;
            const n = this.length;
            result.reserve(2U + n*8U + n*(Key.sizeof + Value.sizeof));
            result ~= "{";

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

    pragma(inline, true) {
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

 public:
    /// Returns the structural hash of this table.
    size_t toHash() const {
        // entry order does not matter in a hash table, so we accumulate with XOR
        // for each entry, we use a noncommutative operation, scaled by a Fibonacci number
        hash_t tableHash = 0;
        foreach (entry; this.byKeyValue) {
            enum size_t scale = 2654435771UL; // approx. 2^32 / phi
            tableHash ^= (entry.key.hashOf - entry.value.hashOf) * scale;
        }
        return tableHash;
    }

    /// Structural equality comparison.
    bool opEquals(ref const(HashMap) other) const {
        if (other.length != this.length) return false;
        foreach (entry; this.byKeyValue) {
            if (entry.key !in other || entry.value != other[entry.key]) return false;
        }
        return true;
    }

    /++
    Returns the number of entries currently being used in the hash table.

    See_Also: [capacity](#HashMap.capacity)
    +/
    pragma(inline) @property size_t length() const {
        return this.used;
    }

    /++
    Returns the number of entries this table can hold without being rehashed.

    See_Also: [length](#HashMap.length)
    +/
    pragma(inline) @property size_t capacity() const {
        return cast(size_t)(this.allocated * maxLoadFactor);
    }

    /++
    Returns a pointer to a matching KEY in the table, or `null` if there isn't one.

    See_Also: [get](#get)
    +/
    inout(Key)* opBinaryRight(string op : "in")(auto ref const(Key) key) inout {
        if (this.allocated == 0) return null;
        const k = this.buckets.probeFor!(Key)(key);
        auto bucket = &this.buckets[k];
        return bucket.isOccupied && !bucket.wasDeleted ? &bucket.key : null;
    }

    /++
    Returns the value associated with a given key, or its `.init` if there isn't one.

    See_Also: [require](#require), [get](#get)
    +/
    inout(Value) opIndex()(auto ref const(Key) key) inout
    out (value; key in this || value == Value.init)
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
    Upserts a `<key,value>` entry in the hash table. May cause a [rehash](#rehash).

    Returns: Zero on success, non-zero on failure (e.g. OOM or overflow).

    See_Also: [update](#update)
    +/
    err_t opIndexAssign(Value value, Key key)
    out (error; error || this[key] == value)
    {
        err_t error;
        this.update(key, () => value, (ref Value old) => value, error);
        return error;
    }
}

@nogc nothrow pure @safe unittest {
    alias NonZero = long;
    alias Zero = void[0];
    static assert(HashMap!(char, Zero).sizeof < HashMap!(char, NonZero).sizeof);
}

/// Frees all resources allocated by the hash table.
void dispose(bool initialize = true, K, V)(ref HashMap!(K,V) self)
out (; !initialize || self.length == 0)
out (; !initialize || self.buckets is null)
{
    assert(self.allocated == self.buckets.length);
    static if (V.sizeof > 0) self.values.deallocate(self.allocated);
    self.buckets.ptr.deallocate(self.allocated);
    static if (initialize) self = HashMap!(K,V).init;
}

/// Consider using `scope(exit)` to ensure hash table memory doesn't leak.
@nogc nothrow unittest {
    HashMap!(char, long) outer;
    {
        HashMap!(char, long) inner;
        scope(exit) inner.dispose();
        outer = inner; // but be careful with byref-like copies
    }
    // outer.dispose(); // would have caused a double-free: `dispose` is unsafe!
}

/// Initializes a hash table.
private err_t initialize(K, V)(out HashMap!(K,V) self, size_t capacity)
@trusted // due to deallocate and pointer slicing
in (self.buckets.ptr == null)
out (; self.length == 0)
{
    if (capacity == 0) return 0;

    // adjust allocation size based on max load factor and round to power of two
    capacity = cast(size_t)(capacity / maxLoadFactor);
    if (capacity < minAllocatedSize) {
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

    // allocate bucket (and value) array
    Bucket!(K)* buffer = allocate!(Bucket!K)(capacity);
    if (buffer == null) return ENOMEM;
    self.buckets = buffer[0 .. capacity];
    static if (V.sizeof > 0) {
        self.values = allocate!V(capacity);
        if (self.values == null) {
            self.buckets = null;
            buffer.deallocate(capacity);
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
err_t rehash(K, V)(ref HashMap!(K,V) self, size_t newCapacity)
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
    self.dispose();
    self = newTable;
    return 0;
}

/// ditto
err_t rehash(K, V)(ref HashMap!(K,V) self) {
    enum targetLoadFactor = Rational!size_t(1, 2);
    enum allocationAdjustment = maxLoadFactor / targetLoadFactor;
    static assert(allocationAdjustment >= 1.0);
    const newCapacityAdjusted = cast(size_t)(self.length * allocationAdjustment);
    return self.rehash(newCapacityAdjusted);
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
    ref inout(HashMap!(K,V)) self,
    auto ref const(K) find,
    out inout(K)* keyp,
    out inout(V)* valp
)
@trusted // due to cast from Bucket* to Key*
out (found; (found && *keyp in self) || (!found && keyp == null))
{
    auto key = find in self;
    if (key == null) return false;
    static assert(
        Bucket!(K).key.offsetof == 0,
        "bucket layout must ensure safe cast to key"
    );
    const k = cast(inout(Bucket!K)*)(key) - self.buckets.ptr;
    keyp = key;
    valp = self.valueAt(k);
    return true;
}

/// ditto
bool get(K, V)(
    ref inout(HashMap!(K,V)) self,
    auto ref const(K) find,
    out inout(K)* keyp
) {
    inout(V)* valp;
    return self.get(find, keyp, valp);
}

/++
Removes a key's entry from the table.

Returns: Whether or not the key had an entry to begin with.
+/
bool remove(K, V)(ref HashMap!(K, V) self, auto ref const(K) key)
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

/// Removes all elements from the hash table without changing its capacity.
void clear(K, V)(ref HashMap!(K, V) self)
out (; self.length == 0)
{
    foreach (ref bucket; self.buckets) {
        bucket.isOccupied = false;
        bucket.wasDeleted = false;
    }
    self.occupied = 0;
    self.used = 0;
}

///
@nogc nothrow unittest {
    HashMap!(char, long) table;
    scope(exit) table.dispose();
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

    const cap = table.capacity;
    table.clear(); // preserves capacity
    assert(table.length == 0);
    assert(table.capacity == cap);
}

/++
Looks up a key's entry in the table, then either updates it or creates a new one.

If a new entry needs to be created, a [rehash](#rehash) may happen.

Params:
    self = Hash table.
    key = Key being looked up (only stored when a new entry is created).
    create = Called to construct a new value if the key isn't in the table.
    update = Called to update the value of an entry, if it was found.
    error = Set to zero on success, non-zero otherwise.

Returns: The entry's final value (or its `.init` in case of failure).
+/
pragma(inline) V update(K, V, Create, Update)(
    ref HashMap!(K,V) self,
    K key,
    auto ref const(Create) create,
    auto ref const(Update) update,
    out err_t error
)
if (is(ReturnType!Create == V)
    && Parameters!Create.length == 0
    && is(ReturnType!Update == V)
    && Parameters!Update.length == 2
    && is(Parameters!Update[0] == K)
    && is(Parameters!Update[1] == V))
out (value; (error && value == V.init) || (!error && self[key] == value))
{
    // check whether a load factor increase needs to trigger a rehash
    if (self.occupied + 1 > self.capacity) {
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
            newValue = update(bucket.key, *self.valueAt(k));
        } else {
            V oldValue = V.init;
            newValue = update(bucket.key, oldValue);
        }
    }
    static if (V.sizeof > 0) *self.valueAt(k) = newValue;
    return newValue;
}

/// ditto
V update(K, V, Create, Update)(
    ref HashMap!(K,V) self,
    K key,
    auto ref const(Create) create,
    auto ref const(Update) update
)
if (is(ReturnType!Create == V)
    && Parameters!Create.length == 0
    && is(ReturnType!Update == V)
    && Parameters!Update.length == 2
    && is(Parameters!Update[0] == K)
    && is(Parameters!Update[1] == V))
{
    err_t ignored;
    return self.update(key, create, update, ignored);
}

/// ditto
pragma(inline) V update(K, V, Create, Update)(
    ref HashMap!(K,V) self,
    K key,
    auto ref const(Create) create,
    auto ref const(Update) update,
    out err_t error
)
if (is(ReturnType!Create == V)
    && Parameters!Create.length == 0
    && is(ReturnType!Update == V)
    && Parameters!Update.length == 1
    && is(Parameters!Update[0] == V))
{
    return self.update(key, create, (ref K k, ref V v) => update(v), error);
}

/// ditto
V update(K, V, Create, Update)(
    ref HashMap!(K,V) self,
    K key,
    auto ref const(Create) create,
    auto ref const(Update) update
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
Looks up a key, inserting an entry if there isn't any (may [rehash](#rehash)).

Params:
    self = Hash table.
    key = Key being looked up (only stored when a new entry is created).
    create = Called to construct a new value if the key isn't in the table.
    error = Set to zero on success, non-zero otherwise.

Returns: The entry's final value (or its `.init` in case of failure).
+/
V require(K, V, Create)(
    ref HashMap!(K,V) self,
    K key,
    auto ref const(Create) create,
    out err_t error
)
if (is(ReturnType!Create == V) && Parameters!Create.length == 0)
{
    return self.update(key, create, (ref V x) => x, error);
}

/// ditto
V require(K, V, Create)(
    ref HashMap!(K,V) self,
    K key,
    auto ref const(Create) create
)
if (is(ReturnType!Create == V) && Parameters!Create.length == 0)
{
    err_t ignored;
    return self.require(key, create, ignored);
}

///
@nogc nothrow @safe unittest {
    import core.stdc.ctype : isalnum;
    import eris.util : empty;

    bool isAnagram(string a, string b) @nogc nothrow @trusted {
        // count letter frequencies in A
        HashMap!(char, long) letters;
        scope(exit) letters.dispose();
        foreach (c; a) {
            if (!c.isalnum) continue;
            const freq = letters.require(c, () => 0L);
            letters[c] = freq + 1;
        }
        // check if they match B's
        foreach (c; b) {
            if (!c.isalnum) continue;
            const freq = letters.update(c, () => -1L, (ref long f) => f - 1);
            if (freq < 0) return false;
            else if (freq == 0) letters.remove(c);
        }
        return letters.empty;
    }

    assert(  isAnagram("tom marvolo riddle", "i am lord voldemort") );
    assert(  isAnagram("123", "3 2 1")                              );
    assert( !isAnagram("aabaa", "bbabb")                            );
}

private mixin template RangeBoilerplate(HashTable) {
    private HashTable* table;
    private size_t index;

    private this(HashTable* t, size_t i = 0) {
        table = t;
        for (index = i; index < table.buckets.length; ++index) {
            const bucket = &table.buckets[index];
            if (bucket.isOccupied && !bucket.wasDeleted) break;
        }
    }

    public bool empty() const {
        return index >= table.buckets.length;
    }

    public void popFront() {
        auto bucket = &table.buckets[index];
        assert(bucket.isOccupied && !bucket.wasDeleted);
        this = typeof(this)(table, index + 1);
    }

    public inout(typeof(this)) save() inout {
        return this;
    }
}

/++
Can be used to iterate over this table's entries (in an unspecified order).

NOTE: These must NEVER outlive their backing hash table.
    Furthermore, mutating a table invalidates any ranges over it.
+/
auto byKey(K, V)(ref const(HashMap!(K,V)) self) {
    struct ByKey {
        mixin RangeBoilerplate!(const(HashMap!(K,V)));
        public ref const(K) front() const {
            auto bucket = &table.buckets[index];
            return bucket.key;
        }
    }
    return ByKey(&self);
}

/// ditto
auto byValue(K, V)(ref const(HashMap!(K,V)) self) if (V.sizeof > 0) {
    struct ByValue {
        mixin RangeBoilerplate!(const(HashMap!(K,V)));
        public ref const(V) front() const {
            return *table.valueAt(index);
        }
    }
    return ByValue(&self);
}

/// ditto
auto byKeyValue(K, V)(ref const(HashMap!(K,V)) self) {
    struct KeyValue {
        const(K) key;
        static if (V.sizeof > 0) const(V) value;
        else                     enum value = V.init;
    }
    struct ByKeyValue {
        mixin RangeBoilerplate!(const(HashMap!(K,V)));
        public const(KeyValue) front() const {
            auto bucket = &table.buckets[index];
            static if (V.sizeof > 0)
                return KeyValue(bucket.key, *table.valueAt(index));
            else
                return KeyValue(bucket.key);
        }
    }
    return ByKeyValue(&self);
}

///
@nogc nothrow pure @safe unittest {
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
HashMap!(K,V) dup(K, V)(ref const(HashMap!(K,V)) self, out err_t error)
out (copy) {
    if (!error) {
        assert(copy.length == self.length);
        foreach (entry; self.byKeyValue)
            assert(entry.key in copy && copy[entry.key] == entry.value);
    } else {
        assert(copy.length == 0);
    }
} do {
    HashMap!(K,V) copy;
    error = copy.initialize(self.length);
    if (error) return copy;
    foreach (entry; self.byKeyValue) {
        error = (copy[entry.key] = entry.value);
        assert(!error, "memory already reserved, so insertion won't fail");
    }
    return copy;
}

/// ditto
HashMap!(K,V) dup(K, V)(ref const(HashMap!(K,V)) self) {
    err_t ignored;
    return self.dup(ignored);
}


/++
Unordered hash set.

See_Also: [HashMap](#HashMap)
+/
struct HashSet(T) {
    HashMap!(T, Unit) _table;
    alias _table this;

    version (D_BetterC) {} else {
        string toString() const {
            return this._table.toString;
        }
    }
}

/++
Adds an element to the set, possibly causing a [rehash](#rehash).

Returns: Zero on success, non-zero on failure (e.g. OOM or overflow).
+/
pragma(inline) err_t add(T)(ref HashSet!T self, T key)
out (error; error || key in self)
{
    return (self[key] = Unit.init);
}

///
nothrow unittest {
    import std.algorithm : each;

    HashSet!long a, b;
    scope(exit) {
        a.dispose();
        b.dispose();
    }

    () @nogc {
        static immutable long[6] list = [0, 1, 42, 32_767, -32_768, 0];
        enum N = list.length;
        a.rehash(N);
        assert(a.capacity == N);
        list.each!(n => a.add(n));
        assert(a.length == N - 1); // one less because of the duplicate 0

        assert(a != b);
        b = a.dup;
        assert(a == b); // structural equality works
    }();

    HashMap!(HashSet!long, string) stringified;
    scope(exit) stringified.dispose();
    stringified[a] = a.toString();
    assert(b in stringified); // structural hashing as well

    b.remove(0);
    b.add(-1);
    assert(a != b);
    assert(b !in stringified); // but be careful with mutability
}
