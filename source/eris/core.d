/// Core type definitions, templates and helper procedures for D as betterC.
module eris.core;

import core.stdc.stdlib : malloc, calloc, free;
import std.traits : hasIndirections;


/++
Zero-sized type carrying no information at all.

NOTE: Make sure not to use this in `extern (C)` signatures, as the ABI is unspecified.
+/
alias Unit = void[0];

/// D uses `size_t` for hash values.
alias hash_t = size_t;

/++
Error code signaling; zero is success.

Rationale: Compatible with C (and with D's `opApply` delegate parameter).
+/
alias err_t = int;


/++
Allocates enough memory for a given number of elements of a certain type.

The allocated memory must be later [deallocate]d if one wishes to avoid leaks.
It will also be registered for GC scanning in case this is compiled in a GC-enabled mode (not betterC).

Params:
    n = Number of contiguous elements to allocate.

Returns:
    Allocated memory block (null in case of OOM, overflow or zero-sized allocation).

Version:
    XXX: It would have been nice to parameterize this by global structs following the same duck-typed interface of the [core std.experimental allocators](https://dlang.org/phobos/std_experimental_allocator.html), but they don't seem to be linked in when compiling in betterC mode.
+/
T[] allocate(T)(size_t n) @nogc nothrow
@trusted // because malloc and friends can be trusted (there's also the cast)
{
    import core.checkedint : mulu;

    bool overflow = false;
    const size_t bytes = mulu(n, T.sizeof, overflow);
    if (overflow || bytes == 0) return [];

    version (D_BetterC) {
        void* ptr = malloc(bytes);
    } else {
        void* ptr = calloc(n, T.sizeof);
        static if (hasIndirections!T) {
            import core.memory : GC;
            if (ptr != null) GC.addRange(ptr, bytes);
        }
    }

    debug if (ptr != null) {
        const current = allocated.atomicOp!"+="(bytes);
        version (Eris_VerboseAllocations) {
            printf(
                "+%10luB (total: %10luB) for " ~ T.stringof ~ "[%lu]\n",
                bytes, current, n
            );
        }
    }
    return ptr != null ? (cast(T*)ptr)[0 .. n] : [];
}

/// ditto
T* allocate(T)() @nogc nothrow
@trusted // because of direct ptr access
{
    T[] memory = allocate!T(1);
    return memory.ptr;
}

debug {
    import core.atomic : atomicOp;
    shared size_t allocated = 0;
    version (Eris_VerboseAllocations) {
        import core.stdc.stdio : printf;
    }
}

/++
Frees previously [allocate]d memory block.

Params:
    memory = Previously [allocate]d memory block (or null, in which case nothing happens).
+/
void deallocate(T)(T[] memory) @nogc nothrow @system {
    debug if (memory.ptr != null) {
        const bytes = memory.length * T.sizeof;
        const current = allocated.atomicOp!"-="(bytes);
        version (Eris_VerboseAllocations) {
            printf(
                "-%10luB (total: %10luB) for " ~ T.stringof ~ "[%lu]\n",
                bytes, current, memory.length
            );
        }
    }
    version (D_BetterC) {} else {
        static if (hasIndirections!T) {
            import core.memory : GC;
            GC.removeRange(memory.ptr);
        }
    }
    free(memory.ptr);
}

/// ditto
void deallocate(T)(T* memory) @nogc nothrow @system {
    deallocate(memory[0 .. 1]); // slice .ptr may be null
}

/// Consider using `scope(exit)` to ensure deallocation (but beware of double frees).
@nogc nothrow unittest {
    auto cacheLine = allocate!ubyte(64);
    scope(exit) cacheLine.deallocate();
    assert(cacheLine != null);
}


/// Free-function version of `opCmp`, useful to compare primitive scalar types in generic code.
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
