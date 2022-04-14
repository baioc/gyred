/++
Hash-based sets in a standalone (and single-file) module.

License: Zlib
Authors: [Gabriel B. Sant'Anna](baiocchi.gabriel@gmail.com)
+/
module gyre.set;

import std.traits : isPointer, PointerTarget;
import std.range.primitives : ElementType, isInputRange, isInfinite;


/++
Generic hash-based set.

The mechanism used to override hashing and comparison functions is [the same as for standard AAs](https://dlang.org/spec/hash-map.html#using_struct_as_key).
Unlike AAs, however, **storing pointer types will call the pointed-to-type's custom hash function** instead (if it has one).

NOTE: Like AAs, Sets should be treated as a reference type (even if it's a struct).
+/
struct Set(T) {
    private {
        // this is essentially a wrapper around a classic AA trick, but with a twist
        alias Unit = void[0];
        enum unit = Unit.init;
        static if (isPointer!T) alias Key = HashablePointer!(PointerTarget!T);
        else                    alias Key = T;
        Unit[Key] _aa;
    }
    nothrow pure @safe {
        /// Adds an element to the set.
        void add(T x)
        out {
            assert(x in this, "added element should be in the set");
        } do {
            Key key = x;
            this._aa[key] = unit;
        }

        /++
        Removes an element from the set.
        Returns: Whether or not the element was present in the set.
        +/
        bool remove()(auto ref T x)
        out {
            assert(x !in this, "removed element should not be in the set");
        } do {
            Key key = x;
            return this._aa.remove(key);
        }

        /// Checks if an element is present in the set. Equivalent to the expression `x in set`
        bool contains()(auto ref T x) const {
            Key key = x;
            return (key in this._aa) != null;
        }

        /// ditto
        bool opBinaryRight(string op)(auto ref T lhs) const if (op == "in") {
            return this.contains(lhs);
        }

        /// Returns the number of elements in the set.
        @property size_t length() const @nogc {
            return this._aa.length;
        }

        /// Returns a forward range which will iterate over the set's elements.
        auto byKey() const @nogc {
            return this._aa.byKey;
        }
    }

    /// Rehashes the set in place (so that lookups are more efficient).
    auto rehash() nothrow pure {
        return this._aa.rehash();
    }

    /// Returns an independent duplicate of this set.
    Set!T dup()() const // templated for attribute inference
    out (result) {
        assert(result.length == this.length, "duplicate set should have the same size as the original");
        foreach (ref T x; this) assert(x in result, "every element in the original should be in the new set");
    } do {
        import std.traits : hasMember;
        import std.algorithm : map;
        return this.byKey.map!((T x) {
            static if (hasMember!(T, "dup")) return x.dup;
            else                             return x;
        }).set;
    }

    /// Can be used to iterate over this set's elements with a `foreach` loop.
    int opApply(F)(F iter) const { // templated for attribute inference
        foreach (ref T x; this.byKey) {
            int stop = iter(x);
            if (stop) return 1;
        }
        return 0;
    }
}

///
nothrow pure unittest {
    import std.algorithm;

    bool usingCustomHash = false;
    struct MyInt {
        int value;
     @nogc nothrow pure @safe:
        size_t toHash() const {
            debug usingCustomHash = true;
            return value * value;
        }
        bool opEquals(ref const MyInt other) const {
            return this.value == other.value;
        }
    }

    immutable list = [0, 1, 42, int.max, int.min, 0];
    enum N = list.length;
    Set!(MyInt*) s = list.map!(n => new MyInt(n)).set;
    assert(s.length == N-1); // one less because of the duplicate (0)
    s.add(null);
    assert(s.length == N);

    // structural equality works
    auto duplicate = s.dup;
    s.rehash;
    assert(s == duplicate);

    auto forty2 = new MyInt(42); // notice the different allocation
    assert(forty2 in s);
    assert(s.remove(forty2) == true); // actually removes it
    assert(s.length == N-1);
    assert(s != duplicate);
    assert(forty2 !in s);
    assert(s.remove(forty2) == false); // does nothing, it was already removed

    foreach (MyInt* i; s) {
        if (i != null) assert(list.canFind(i.value));
    }
    assert(usingCustomHash);
}

/// Builds a [Set] from a finite input range.
static Set!(ElementType!Range) set(Range)(Range inputs)
if (isInputRange!Range && !isInfinite!Range)
{
    alias T = ElementType!Range;
    Set!T set;
    foreach (x; inputs) set.add(x);
    return set;
}


/++
Generic pointer-like wrapper used to forward overloads to its pointed-to object.

This behaviour can be useful when one wishes to use references as hash table keys: whereas the default hash for pointers is solely based on the address being pointed to, using this wrapper as a key will call the pointed-to-type's custom hash function instead (if it is defined).
There is no overhead associated with using this wrapper.
+/
struct HashablePointer(T) if (!isPointer!T) {
    T* ptr;
    alias ptr this; // dispatches most pointer-like behaviour to actual pointer
    static assert((HashablePointer!T).sizeof == (T*).sizeof, "HashablePointer!T should have the sizeof a T*");

 nothrow pure @safe:
    inout this(inout(T)* ptr) @nogc {
        this.ptr = ptr;
    }

    size_t toHash() const {
        return ptr == null ? 0 : typeid(T).getHash(ptr);
    }

    bool opEquals(ref const HashablePointer!T rhs) const {
        if (this.ptr == rhs.ptr) return true;
        else return this.ptr != null && rhs.ptr != null && *this.ptr == *rhs.ptr;
    }

    bool opEquals(const(T)* rhs) const @nogc {
        return this.ptr == rhs;
    }
}

///
@nogc nothrow pure unittest {
    struct Foo {
        bool baz = false;
        string bar(const(Foo)* f) const @nogc nothrow { return "ok"; }
    }

    // a HashablePointer!T works just like a T* would
    Foo x;
    HashablePointer!Foo p = &x;
    assert(p == &x);
    assert(*p == x);
    assert(p.baz == x.baz);
    assert(p.bar(p) == x.bar(&x)); // implicit conversion
    p = null;
    assert(p is null);
}
