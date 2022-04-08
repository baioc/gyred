/++
Hash-based sets in a standalone (and single-file) module.

License: Zlib
Authors: [Gabriel B. Sant'Anna](baiocchi.gabriel@gmail.com)
+/
module set;

import std.algorithm : map;
import std.range.primitives : ElementType, isInputRange, isInfinite;
import std.traits : hasMember, isPointer;


/++
Generic hash-based set.

The mechanism used to override hashing and comparison functions is [the same as for standard AAs](https://dlang.org/spec/hash-map.html#using_struct_as_key).
Unlike AAs, however, storing pointer types will call the pointed-to-type's custom hash function instead (if it has one).
+/
struct Set(T) {
private:
    // this is essentially a wrapper around a classic AA trick, but with a twist
    alias Unit = void[0];
    enum unit = Unit.init;
    static if (isPointer!T) alias Key = HashablePointer!(typeof(*T));
    else                    alias Key = T;
    Unit[Key] aa;

public:
    /// Adds an element to the set.
    void add()(auto ref T x) nothrow pure @safe
    out {
        assert(x in this);
    } do {
        Key key = x;
        this.aa[key] = unit;
    }

    /++
    Removes an element from the set.
    Returns: Whether or not the element was present in the set.
    +/
    bool remove()(auto ref T x) nothrow pure @safe
    out {
        assert(x !in this);
    } do {
        Key key = x;
        return this.aa.remove(key);
    }

    /// Checks if an element is present in the set. Equivalent to the expression `x in set`
    bool contains()(auto ref T x) const nothrow pure @safe {
        Key key = x;
        return (key in this.aa) != null;
    }

    bool opBinaryRight(string op)(auto ref T lhs) const nothrow pure @safe if (op == "in") {
        return this.contains(lhs);
    }

    /// Returns the number of elements in the set.
    @property size_t length() const @nogc nothrow pure @safe {
        return this.aa.length;
    }

    /// Returns an independent duplicate of this set.
    Set!T dup() const
    out (result) {
        assert(result.length == this.length);
        foreach (x; result.byKey) assert(x in this);
    } do {
        return this.byKey.map!((T x) {
            static if (hasMember!(T, "dup")) return x.dup;
            else                             return x;
        }).set;
    }

    /// Rehashes the set in place (so that lookups are more efficient).
    auto rehash() nothrow pure {
        return this.aa.rehash();
    }

    /// Returns a forward range which will iterate over the set's elements.
    auto byKey() const @nogc nothrow pure @safe {
        return this.aa.byKey();
    }
}

///
nothrow pure unittest {
    import std.algorithm;

    bool usingCustomHash = false;
    struct MyInt {
        int value;
        size_t toHash() const @nogc nothrow pure @safe {
            debug usingCustomHash = true;
            return value * value;
        }
        bool opEquals(ref const MyInt other) const @nogc nothrow pure @safe {
            return this.value == other.value;
        }
    }

    auto list = [0, 1, 42, int.max, int.min, 0];
    Set!(MyInt*) s = list.map!(n => new MyInt(n)).set;
    assert(s.length == list.length - 1); // one less because of the duplicate (0)
    s.add(null);
    assert(s.length == list.length);

    // structural equality works
    auto duplicate = s.dup();
    s.rehash();
    assert(s == duplicate);

    auto forty2 = new MyInt(42); // notice the different allocation
    assert(forty2 in s);
    assert(s.remove(forty2) == true); // actually removes it
    assert(s.length == list.length - 1);
    assert(s != duplicate);
    assert(forty2 !in s);
    assert(s.remove(forty2) == false); // does nothing, it was already removed

    foreach (MyInt* key; s.byKey) {
        if (key != null) assert(list.canFind(key.value));
    }

    assert(usingCustomHash == true);
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
    static assert((HashablePointer!T).sizeof == (T*).sizeof);

    this(return inout(T)* ptr) inout @nogc nothrow pure @safe {
        this.ptr = ptr;
    }

    static if (hasMember!(T, "toHash")) {
        size_t toHash() const nothrow pure @safe {
            return ptr == null ? 0 : ptr.toHash();
        }

        bool opEquals(ref const(HashablePointer!T) rhs) const nothrow pure @safe {
            if (this.ptr == rhs.ptr) return true;
            return this.ptr != null && rhs.ptr != null && *this.ptr == *rhs.ptr;
        }
    }
}

///
unittest {
    struct Foo {
        bool bar(Foo* f) { return true; }
        bool baz = false;
    }

    // HashablePointer!T works just like a T* would
    Foo x;
    HashablePointer!Foo p = &x;
    assert(p == &x);
    assert(*p == x);
    assert(p.bar(p) == x.bar(&x)); // implicit conversion
    assert(p.baz == x.baz);
    p = null;
}
