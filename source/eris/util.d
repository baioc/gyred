/// Miscellaneous utilities.
module eris.util;

import std.traits : isPointer;
import std.typecons : RefCountedAutoInitialize;

import eris.core : allocate, deallocate;


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
        }
        Impl* store = null;

        void allocateStore()
        out (; this.store != null, "memory allocator failed when we assumed it never would")
        {
            this.store = allocate!Impl();
        }

        void deallocateStore()
        in (this.store == null || this.store._refCount == 0, "double free detected!")
        out (; this.store == null)
        {
            deallocate(this.store);
            this.store = null;
        }

        void initialize(A...)(auto ref A args) nothrow out (; this.isInitialized) {
            import core.lifetime : emplace, forward;
            this.allocateStore();
            emplace(&this.store.payload, forward!args);
            this.store._refCount = 1;
        }

        void move(ref T source) nothrow {
            import std.algorithm.mutation : moveEmplace;
            this.allocateStore();
            moveEmplace(source, this.store.payload);
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

    this(A...)(auto ref A args)
    if (A.length > 0)
    out (; refCountedStore.isInitialized)
    {
        import core.lifetime : forward;
        this._refCounted.initialize(forward!args);
    }

    this(T val) {
        this._refCounted.move(val);
    }

    this(this) {
        if (!this._refCounted.isInitialized) return;
        this._refCounted.store._refCount++;
    }

    ~this() nothrow @trusted {
        if (!this._refCounted.isInitialized) return;
        assert(this._refCounted.store._refCount > 0);
        if (--this._refCounted.store._refCount) return;
        .destroy(this._refCounted.store.payload);
        this._refCounted.deallocateStore();
    }

    void opAssign(typeof(this) rhs) {
        import std.algorithm.mutation : swap;
        swap(this._refCounted.store, rhs._refCounted.store);
    }

    void opAssign(T rhs) {
        import std.algorithm.mutation : move;
        this._refCounted.ensureInitialized();
        move(rhs, this._refCounted.store.payload);
    }

    /// Accesses the refcounted store (usually to check or ensure it is initialized).
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
    @property ref inout(T) refCountedPayload() inout return @system {
        assert(this._refCounted.isInitialized, "attempted to access payload");
        return this._refCounted.store.payload;
    }
}

///
@nogc nothrow @safe unittest {
    static uint nDestroyed = 0;
    struct Resource {
        string name;
        @disable this(this);
        ~this() { debug ++nDestroyed; }
    }

    {
        RefCountedTrusted!Resource rc;
        assert(!rc.refCountedStore.isInitialized);
        rc.refCountedStore.ensureInitialized();
        assert(rc.refCountedStore.isInitialized);
        () @trusted { rc.refCountedPayload.name = "thing"; }();

        {
            auto rc2 = rc;
            auto rc3 = rc2;
            () @trusted { assert(rc3.refCountedPayload.name == "thing"); }();
        }

        // rc2 and rc3 didn't destroy the resource: there's still one ref
        debug assert(nDestroyed == 0);
    }

    // now the last reference goes out of scope and the resource is destroyed
    debug assert(nDestroyed == 1);
}
