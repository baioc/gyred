/// Core type definitions, templates and helper procedures for D as betterC.
module eris.core;

import core.stdc.stdlib : malloc, calloc, free;
import std.traits : hasIndirections;


/++
Default zero-sized type. Carries no information at all.

NOTE: Make sure not to use this in `extern (C)` function signatures, as the ABI is unspecified.
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
Allocates enough memory for a given number of elements of a certain type.

The allocated memory must be later [deallocate](#deallocate)d.
It will also be registered for GC scanning iff the GC is enabled.

Params:
    n = Number of contiguous elements to allocate.

Returns:
    Pointer to the allocated memory, or null in case of OOM, overflow or zero-sized allocation.

See_Also: [deallocate](#deallocate)

XXX: It would have been nice to parameterize this by global structs following the same duck-typed interface of the [core std.experimental allocators](https://dlang.org/phobos/std_experimental_allocator.html), but they don't seem to be linked in when compiling in betterC mode.
+/
T* allocate(T)(size_t n = 1) @nogc nothrow
@trusted // because malloc and friends can be trusted (there's also the cast)
{
    import core.checkedint : mulu;

    bool overflow = false;
    const size_t totalBytes = mulu(n, T.sizeof, overflow);
    if (overflow) return null;

    version (D_BetterC) {
        void* ptr = malloc(totalBytes);
    } else {
        void* ptr = calloc(n, T.sizeof);
        static if (hasIndirections!T) {
            import core.memory : GC;
            if (ptr != null) GC.addRange(ptr, totalBytes);
        }
    }

    return cast(T*)(ptr);
}

/++
Frees previously [allocate](#allocate)d memory block.

Params:
    ptr = Pointer to previously [allocate](#allocate)d memory block (or null, in which case nothing happens).
    n = Must match the parameter used to [allocate](#allocate) the given block.
+/
void deallocate(T)(T* ptr, size_t n = 1) @nogc nothrow @system {
    version (D_BetterC) {} else {
        static if (hasIndirections!T) {
            import core.memory : GC;
            GC.removeRange(ptr);
        }
    }
    free(ptr);
}

/// Consider using `scope(exit)` to ensure deallocation (but beware of double frees).
@nogc nothrow unittest {
    auto cacheLine = allocate!ubyte(64);
    scope(exit) deallocate(cacheLine, 64);
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
