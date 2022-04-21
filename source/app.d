import core.stdc.stdlib : atoi, rand, srand;
import core.stdc.stdio : printf;
import core.stdc.time : clock, clock_t, CLOCKS_PER_SEC;


version(D_BetterC) {
    extern (C) int main(int argc, const(char)** argv) {
        int n = argc > 1 ? atoi(argv[1]) : 0;
        int reserve = argc > 2 ? atoi(argv[2]) : 0;
        insertionBenchmark(n, reserve);
        return 0;
    }
} else {
    int main(string[] args) {
        import std.algorithm : map;
        import std.array : array;
        import std.string : toStringz;
        auto argc = args.length;
        auto argv = args.map!(s => s.toStringz).array;
        int n = argc > 1 ? atoi(argv[1]) : 0;
        int reserve = argc > 2 ? atoi(argv[2]) : 0;
        insertionBenchmark(n, reserve);
        return 0;
    }
}


void insertionBenchmark(int n, int reserve) {
    n = n > 0 ? n : 10_000_000;
    reserve = reserve >= 0 && reserve <= n ? reserve : 0;

    version(D_BetterC) {
        import gyre.hash : HashMap;
        printf("Using gyre.hash.HashMap\n");
        HashMap!(ulong, int) dict;
        scope(exit) dict.destroy();
    } else {
        printf("Using D's built-in AAs\n");
        int[ulong] dict;
    }

    srand(2166136261U);

    const clock_t begin = clock();
    for (int i = 0; i < n; ++i) {
        const ulong key = rand();
        const int value = i;
        dict[key] = value;
    }
    const clock_t end = clock();

    const float elapsedNs = end * 1e9 / CLOCKS_PER_SEC - begin * 1e9 / CLOCKS_PER_SEC;
    printf("Total: %.3f ms\n", elapsedNs / 1e6);
    printf("Per element: %.0f ns\n", elapsedNs / n);
}
