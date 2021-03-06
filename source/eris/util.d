/// Miscellaneous utilities.
module eris.util;

import std.traits : isPointer;
import std.typecons : RefCountedAutoInitialize;

import eris.core : allocate, deallocate;


/// Free-function `empty`, which does the expected thing whenever `arg.length` works.
pragma(inline) bool empty(T)(ref const(T) arg)
if (is(typeof(arg.length) : size_t) && !__traits(hasMember, T, "empty"))
{
    return arg.length == 0;
}

///
@nogc nothrow pure @safe unittest {
    struct S { size_t length; }

    S a = { length: 0 };
    assert(a.empty);

    S b  = { length: 1 };
    assert(!b.empty);
}


/++
Generic pointer-like wrapper used to forward hash table operations to its pointed-to object.

This behaviour can be useful when one wishes to use references as hash table keys: whereas the default hash for pointers is solely based on the address it carries, using this wrapper as a key will call the pointed-to-type's custom hash and equality functions instead (if defined).
Equality works similarly to [object references](https://dlang.org/spec/operatoroverloading.html#equals): two wrappers always compare equal when their pointers are equal, and the object's `opEquals` only gets called when that's not the case.
+/
struct HashablePointer(T) if (!isPointer!T) {
    T* ptr = null;
    alias ptr this; // dispatches most pointer-like behaviour to actual pointer
    static assert((HashablePointer).sizeof == (T*).sizeof);

 pragma(inline):
    this(inout(T)* ptr) inout {
        this.ptr = ptr;
    }

    size_t toHash() const {
        return this.ptr == null ? 0 : hashOf(*this.ptr);
    }

    bool opEquals(ref const(HashablePointer) rhs) const {
        if (this.ptr == rhs.ptr) return true;
        if (this.ptr == null || rhs.ptr == null) return false;
        return *this.ptr == *rhs.ptr;
    }

    bool opEquals(const(T*) rhs) const {
        const HashablePointer other = rhs;
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

    // equality checks may forward to the pointed-to element
    HashablePointer!S sameRef = ptr;
    assert(sameRef == ptr);
    assert(*sameRef != *ptr); // see S.opEquals, above

    // default raw pointer behaviour:
    bool[S*] withRaw;
    withRaw[&x] = true;
    debug assert(!usingCustomHash);

    // hashable pointer behaviour:
    bool[HashablePointer!S] withHashable;
    withHashable[ptr] = true;
    debug assert(usingCustomHash);
}


/++
Adapted [RefCounted](https://dlang.org/library/std/typecons/ref_counted.html#1) with a `@trusted` destructor.

Version:
    XXX: See related [bug reports](https://issues.dlang.org/show_bug.cgi?id=17867) and [pull requests](https://github.com/dlang/phobos/pull/8368).
+/
struct RefCountedTrusted(T, RefCountedAutoInitialize autoInit = RefCountedAutoInitialize.yes)
if (!is(T == class) && !(is(T == interface)))
{
    /// Protects a pointer to some reference counted payload.
    struct RefCountedStore {
     private:
        struct Impl {
            T payload;
            size_t _refCount;
            @disable this(this);
        }
        Impl* store = null;

        void allocateStore()
        out (; this.store != null, "memory allocator failed when we assumed it never would")
        {
            this.store = allocate!Impl;
        }

        void deallocateStore()
        in (this.store == null || this.store._refCount == 0, "double free detected!")
        out (; this.store == null)
        {
            deallocate(this.store);
            this.store = null;
        }

        void initialize(A...)(auto ref A args) nothrow {
            import core.lifetime : emplace, forward;
            this.allocateStore();
            emplace(&this.store.payload, forward!args);
            this.store._refCount = 1;
        }

     public pragma(inline):
        ///
        @property bool isInitialized() const {
            static assert(__traits(compiles, { static T t; }),
                "Cannot automatically initialize `" ~ fullyQualifiedName!T ~
                "` because `" ~ fullyQualifiedName!T ~
                ".this()` is annotated with `@disable`.");
            return this.store != null;
        }

        ///
        void ensureInitialized() out (; this.isInitialized) {
            if (!this.isInitialized) initialize();
        }
    }

    // public API mostly just managed the internal store
    private RefCountedStore _refCounted;

    this(A...)(auto ref A args) if (A.length > 0) {
        import core.lifetime : forward;
        this._refCounted.initialize(forward!args);
    }

    this(this) {
        if (!this._refCounted.isInitialized) return;
        this._refCounted.store._refCount++;
    }

    /// Can be `@trusted` as long as this type is used correctly.
    ~this() nothrow @trusted {
        if (!this._refCounted.isInitialized) return;
        assert(this._refCounted.store._refCount > 0, "double free detected!");
        this._refCounted.store._refCount -= 1;
        if (this._refCounted.store._refCount > 0) return;
        .destroy(this._refCounted.store.payload);
        this._refCounted.deallocateStore();
    }

    void opAssign(typeof(this) rhs) {
        import std.algorithm.mutation : swap;
        swap(this._refCounted.store, rhs._refCounted.store);
    }

    /// Accesses the refcounted store, usually to check if (or ensure that) it is initialized.
    @property ref inout(RefCountedStore) refCountedStore() inout {
        return this._refCounted;
    }

    static if (autoInit == RefCountedAutoInitialize.yes) {
        /++
        These are the only ways to access the refcounted payload (but the store MUST be initialized)

        More importantly, safe code must NEVER escape references to the payload.
        +/
        @property ref T refCountedPayload() @system {
            this._refCounted.ensureInitialized();
            return this._refCounted.store.payload;
        }
    }
    /// ditto
    @property ref inout(T) refCountedPayload() inout @system {
        assert(this._refCounted.isInitialized, "can't access uninitialized payload");
        return this._refCounted.store.payload;
    }
}

///
@nogc nothrow @safe unittest {
    static uint nDestroyed = 0;
    struct Resource {
        string name;
        this(string name) { this.name = name; }
        @disable this(this);
        ~this() { debug ++nDestroyed; }
    }

    {
        auto rc1 = RefCountedTrusted!Resource("thing");
        assert(rc1.refCountedStore.isInitialized);
        rc1.refCountedStore.ensureInitialized();

        {
            auto rc2 = rc1;
            RefCountedTrusted!Resource rc3;
            rc3 = rc2;
            () @trusted { assert(rc3.refCountedPayload.name == "thing"); }();
        }

        // ~rc2 and ~rc3 didn't destroy the resource: there's still one ref
        debug assert(nDestroyed == 0);
    }

    // now the last reference is removed and the resource is destroyed
    debug assert(nDestroyed == 1);
}
