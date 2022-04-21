/// Core types, templates and procedures.
module gyre.core;

import core.stdc.stdlib : malloc, free;


/++
A (signed integer) type for error codes, should be zero on success.

Rationale: Compatible with C (and with D's `opApply` delegate parameter).
+/
alias err_t = int;

/++
Default zero-sized type. Carries no information at all.

Make sure not to use this in `extern (C)` function signatures, as the ABI is unspecified.
+/
alias Unit = void[0];


/// Whether or not the given type is a managed reference.
template isManaged(Type) {
    enum bool isManaged = is(Type == class) || is(Type == interface);
}

///
@nogc nothrow pure @safe unittest {
    class C {}
    interface I {}
    struct S;
    assert(  isManaged!C        );
    assert(  isManaged!I        );
    assert( !isManaged!S        );
    assert( !isManaged!ubyte    );
    assert( !isManaged!(void[]) );
}


/++
Allocates enough memory for a given number of elements of a certain type. **Must be [free](#free)d later**.

If the GC is enabled, the allocated memory block will be registered for GC scanning.

Params:
    n = Number of contiguous elements to allocate.

Returns:
    The allocated memory block, or null in case of failure, zero size or overflow.

See_Also: [free](#free)
+/
T* allocate(T)(size_t n = 1) @nogc nothrow @trusted {
    import core.checkedint : mulu;

    bool overflow = false;
    const size_t totalBytes = mulu(n, T.sizeof, overflow);
    if (overflow) return null;

    void* ptr = malloc(totalBytes);
    version (D_BetterC) {} else {
        import core.memory : GC;
        if (ptr == null) return null;
        GC.addRange(ptr, totalBytes);
    }
    return cast(T*)(ptr);
}

/++
Frees previously [allocate](#allocate)d memory block.

Params:
    ptr = Pointer to [allocate](#allocate)d memory block (or null, in which case nothing happens).
    n = Must match the parameter used to [allocate](#allocate) the given block.

See_Also: [allocate](#allocate)
+/
void free(T)(T* ptr, size_t n = 1) @nogc nothrow {
    version (D_BetterC) {} else {
        import core.memory : GC;
        GC.removeRange(ptr);
    }
    free(ptr);
}

/// Consider using `scope(exit)` to ensure deallocation.
@nogc nothrow unittest {
    auto cacheLine = allocate!ubyte(64);
    scope(exit) free(cacheLine);
}
