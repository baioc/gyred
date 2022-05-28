import core.stdc.stdlib : atoi, rand, srand;
import core.stdc.stdio : printf;
import core.stdc.time : clock, clock_t, CLOCKS_PER_SEC;

import eris.hash_table : HashMap;


version (D_BetterC) {
    extern(C) int main(int argc, const(char)** argv) {
        int size = argc > 1 ? atoi(argv[1]) : -1;
        int replications = argc > 2 ? atoi(argv[2]) : -1;
        microBenchmark(size, replications);
        return 0;
    }
} else {
    int main(string[] args) {
        import std.conv : to;
        int size = args.length > 1 ? to!int(args[1]) : -1;
        int replications = args.length > 2 ? to!int(args[2]) : -1;
        microBenchmark(size, replications);
        return 0;
    }
}


void microBenchmark(int n, int replications = 1) {
    n = n > 0 ? n : 10_000_000;
    replications = replications > 0 ? replications : 1;

    version (D_BetterC) {
        debug printf("# With custom hash table\n");
        alias Dict = HashMap!(ulong, int);
    } else {
        debug printf("# Using D's built-in AAs\n");
        alias Dict = int[ulong];
    }

    srand(42);

    double averageMs = 0.0;
    foreach (experiment; 0 .. replications) {
        const clock_t begin = clock();

        Dict dict;
        foreach (i; 0 .. n) {
            const ulong key = rand();
            const int value = i;
            dict[key] = value;
        }

        const clock_t end = clock();
        averageMs += (end - begin) * 1e3 / CLOCKS_PER_SEC;
    }
    averageMs /= replications;

    debug printf("Average (across %d runs) time per element (ns): ", replications);
    printf("%.3f\n", averageMs * 1e6 / n);
}
