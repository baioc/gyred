/++
Gyre is a compiler IR designed as a practical "linguistic switchbox", or UNCOL.

Overview:
Gyre is not particularly innovative, aiming instead to consolidate features from existing designs.
It's a graph-based IR, heavily influenced by [Click's sea of nodes](https://www.oracle.com/technetwork/java/javase/tech/c2-ir95-150110.pdf).
We take a more functional approach to SSA form by mixing [MLIR-style extended basic blocks](https://mlir.llvm.org/docs/Rationale/Rationale/#block-arguments-vs-phi-nodes) and [Thorin-style CPS-on-a-graph](https://anydsl.github.io/Thorin.html).
Explicit concurrency comes with the addition of a [standard memory consistency model](https://five-embeddev.com/riscv-isa-manual/latest/a.html#atomics) and a message-passing mechanism from the [join calculus](https://www.microsoft.com/en-us/research/publication/join-calculus-language-distributed-mobile-programming/).
Several other features are "mashed up" in Gyre's design, coming from an extensive survey on compilers and portable IRs.

Design_Principles:
### Expressivity:
    The IR must be able to represent, up to some level of detail, the essential properties of any program.
    Software which is not portable is also of interest, even if only to indicate where and how it uses machine-specific constructs and assumptions, or when compiling it to a compatible architecture.
### Efficiency:
    The IR's wire format should be fast to decode and validate.
    At the same time, the IR itself must not introduce unreasonable costs to transformations, nor impose unnecessary restrictions to program structure.
### Progressivity:
    Premature lowering decreases optimization potential, so the IR must be able to preserve "high-level" structure and information for as long as it is desirable to do so.
### Parsimony:
    The IR must not expand uncontrollably to accommodate new languages or machines.
    Instead, it ought to contain a well-defined "core" which is small, yet expressive.
### Extensibility:
    The IR should be amenable to extensions, both from users and to its own specification.
    These must to be clearly signaled for the sake of compatibility.
    This principle complements the previous one.

See_Also:
[Gyre graphs](./gyre.graph.html), [UNCOL](https://www.osdata.com/topic/language/uncol.htm)
+/
module gyre;

public import gyre.graph;
