/// Common typedefs, templates and helper procedures for D as betterC.
module eris.core;

import core.stdc.stdlib : malloc, free;
import std.traits : hasIndirections;


/++
Default zero-sized type. Carries no information at all.

Make sure not to use this in `extern (C)` function signatures, as the ABI is unspecified.
+/
alias Unit = void[0];

/// D uses `size_t` for hash values.
alias hash_t = size_t;

/++
A (signed integer) type for error codes, should be zero on success.

Rationale: Compatible with C (and with D's `opApply` delegate parameter).
+/
alias err_t = int;


/++
Allocates enough memory for a given number of elements of a certain type. Must be [deallocate](#deallocate)d later.

If the GC is enabled, the allocated memory block will be registered for GC scanning.

Params:
    n = Number of contiguous elements to allocate.

Returns:
    The allocated memory block, or null in case of failure, zero size or overflow.

See_Also: [deallocate](#free)
+/
pragma(inline) T* allocate(T)(size_t n = 1) @nogc nothrow
@trusted // only because of the cast
{
    import core.checkedint : mulu;

    bool overflow = false;
    const size_t totalBytes = mulu(n, T.sizeof, overflow);
    if (overflow) return null;

    void* ptr = malloc(totalBytes);
    version (D_BetterC) {} else {
        static if (hasIndirections!T) {
            import core.memory : GC;
            if (ptr != null) GC.addRange(ptr, totalBytes);
        }
    }
    return cast(T*)(ptr);
}

/++
Frees previously [allocate](#allocate)d memory block.

If the GC is enabled, the memory block will be unregistered from GC scanning.

Params:
    ptr = Pointer to [allocate](#allocate)d memory block (or null, in which case nothing happens).
    n = Must match the parameter used to [allocate](#allocate) the given block.
+/
pragma(inline) void deallocate(T)(T* ptr, size_t n = 1) @nogc nothrow {
    version (D_BetterC) {} else {
        static if (hasIndirections!T) {
            import core.memory : GC;
            GC.removeRange(ptr);
        }
    }
    free(ptr);
}

/// Consider using `scope(exit)` to ensure deallocation (but beware of double-free!).
@nogc nothrow unittest {
    auto cacheLine = allocate!ubyte(64);
    scope(exit) deallocate(cacheLine);
}


/// Free-function `opCmp`, useful to compare primitive scalar types in generic code.
pragma(inline) int opCmp(T)(T lhs, T rhs) if (__traits(isScalar, T)) {
    if      (lhs < rhs) return -1;
    else if (lhs > rhs) return  1;
    else                return  0;
}

///
@nogc nothrow pure @safe unittest {
    assert( 2.opCmp(3)  < 0 );
    assert( 3.opCmp(2)  > 0 );
    assert( 2.opCmp(2) == 0 );
    assert( 2.opCmp(3) != 0 );
}
