/// Miscellaneous utilities.
module eris.util;

import std.traits : isPointer;


/// Free-function `empty`, which does the expected thing whenever `arg.length` works.
pragma(inline) bool empty(T)(ref const(T) arg) if (is(typeof(arg.length) : size_t)) {
    static if (__traits(hasMember, T, "empty")) return arg.empty;
    else                                        return arg.length == 0;
}

///
@nogc nothrow pure @safe unittest {
    struct S { size_t length = 0; }
    S s;
    assert(s.empty);
}


/++
Generic pointer-like wrapper used to forward hash table operations to its pointed-to object.

This behaviour can be useful when one wishes to use references as hash table keys: whereas the default hash for pointers is solely based on the address it carries, using this wrapper as a key will call the pointed-to-type's custom hash and equality functions instead (if defined).
Equality works similarly to [object references](https://dlang.org/spec/operatoroverloading.html#equals): two wrappers always compare equal when their pointers are equal, and the object's `opEquals` only gets called when that's not the case.
+/
struct HashablePointer(T) if (!isPointer!T) {
    T* ptr = null;
    alias ptr this; // dispatches most pointer-like behaviour to actual pointer
    static assert((HashablePointer!T).sizeof == (T*).sizeof);

 pragma(inline):
    this(inout(T)* ptr) inout {
        this.ptr = ptr;
    }

    size_t toHash() const {
        return ptr == null ? 0 : hashOf(*ptr);
    }

    bool opEquals(ref const(HashablePointer!T) rhs) const {
        if (this.ptr == rhs.ptr) return true;
        if (this.ptr == null || rhs.ptr == null) return false;
        return *this.ptr == *rhs.ptr;
    }

    bool opEquals(const(T*) rhs) const {
        const HashablePointer!T other = rhs;
        return this == other;
    }
}

///
nothrow pure @safe unittest {
    static bool usingCustomHash = false;
    struct S {
        enum baz = false;
        string bar(S* f) { return "ok"; }
        size_t toHash() const {
            debug usingCustomHash = true;
            return 42;
        }
        bool opEquals(ref const(S) rhs) const {
            return false; // <- always false
        }
    }

    // a HashablePointer!T mostly works like a T* would
    S x;
    HashablePointer!S ptr = &x;
    assert(ptr == &x);
    assert(ptr.baz == x.baz);
    assert(ptr.bar(ptr) == x.bar(&x)); // implicit conversion

    // however, equality checks may forward to the pointed-to element
    HashablePointer!S sameRef = ptr;
    assert(sameRef == ptr);
    assert(*sameRef != *ptr); // see S.opEquals, above

    // the same holds for custom hash functions
    bool[S*] aaDefault;
    aaDefault[&x] = false;
    debug assert(!usingCustomHash);
    // ~~~
    bool[HashablePointer!S] aaHashable;
    aaHashable[ptr] = true;
    debug assert(usingCustomHash);
}
