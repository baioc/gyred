/++
Gyre is a compiler IR designed as a practical "linguistic switchbox", or [UNCOL](https://en.wikipedia.org/wiki/UNCOL).

Gyre is not particularly innovative, aiming instead to consolidate various existing techniques under a unified design.
It's a graph-based IR, heavily influenced by [Click's sea of nodes](https://www.oracle.com/technetwork/java/javase/tech/c2-ir95-150110.pdf), although we take a more functional approach to SSA form by mixing Extended Basic Blocks with [Thorin-style-CPS](https://anydsl.github.io/Thorin.html).
Explicit concurrency comes with the addition of a [standard memory consistency model](https://five-embeddev.com/riscv-isa-manual/latest/a.html#atomics) and a message-passing mechanism from the [join calculus](https://www.microsoft.com/en-us/research/publication/join-calculus-language-distributed-mobile-programming/).
Several other features are "mashed up" in Gyre's design, coming from an extensive survey on compilers, portable IRs and the UNCOL solution to the "compiler construction problem".

$(BLOCKQUOTE
    "The language designer should be familiar with many alternative features designed by others ...
    One thing he should not do is to include untried ideas of his own.
    His task is consolidation, not innovation."
    - [Tony Hoare, 1989](https://dl.acm.org/doi/abs/10.5555/63445.C1104368)
)


[gyre.graph|Click here] for more information on the IR's structure (albeit mixed with implementation details).


Design_Principles:

$(LIST
    * Expressivity: The IR must be able to represent, up to some level of detail, the essential properties of any program. Software which is not portable is also of interest, even if only to indicate where and how it uses machine-specific constructs and assumptions, or when compiling it to a compatible architecture (something which ought to be supported).
    * Efficiency: The IL format should be fast to decode and validate. At the same time, the IR itself must not introduce unreasonable costs to code transformations, nor impose additional restrictions (unnecessary from a logical standpoint) to its programs.
    * Progressivity: An optimizing compiler should prefer to retain, rather than recover, in- formation about a program. Premature lowering decreases optimization potential, so the IR must be able to preserve "high-level" structure for as long as it is desirable to do so.
    * Parsimony: The IR must not expand uncontrollably to accommodate new languages or machines. Instead, it ought to contain a well-defined core which is simple, yet expressive.
    * Extensibility: The IL should be amenable to extensions, both from users and to its own specification. These must be clearly signaled (possibly at different levels of program granularity) for the sake of compatibility. This principle complements the previous one.
)
+/
module gyre;
