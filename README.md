# symex-formally-formalized
Coq formalization of [Symbolic Execution Formally Explained](https://link.springer.com/article/10.1007/s00165-020-00527-y).

## Build
The included Makefile (created for Coq 8.16.1) should allow just
```sh
make
```

To update the Makefile use
```sh
coq_makefile -f _CoqProject -o Makefile
```

## Table of Contents
### Formalization of de Boer et al.
 - [BasicConcrete](./BasicConcrete.v) formalizes section **2. Basic symbolic execution** for simple arithmetic and boolean expression with integer valuations.
    - Syntax and notation for expressions is in [Expr](./Expr.v)
    - Notation and lemmas about maps used for substitution and valuation are in [Maps](./Maps.v)
 - [Recursion](./Recursion.v) formalizes **3. Recursion** – an extension of the basic language with procedure calls.
 - [OOP](./Oop.v) contains an incomplete formalization of **4. Object orientation.**

The approach to syntax and transition relation semantics is based on [Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/index.html)

### Extensions
- [Trace Semantics](./TraceSemantics.v) introduces trace semantics for the language with procedures
  - Notation and lemmas about traces are in [Traces](./Traces.v)
  - Some examples of programs and their traces are found in [examples](./Trace_examples.v)
- [Parallel Traces](./ParallelTraces.v) adds a parallel composition operator to the base language with trace semantics.
Additionally contains some preliminary results about reduction of trace sets.
    - The base language with a parallel operator is in [Parallel](./Parallel.v)
- [Context Reduction](./ContextReduction) contains an alternative approach to syntax based on reductions in a context inspired by [Mechanized Semantics](https://github.com/xavierleroy/cdf-mech-sem)
- [Partial Order Reduction](./PartialOrderReduction.v) formalizes [partial order reduction](https://rdcu.be/c58yn) of symbolic execution in the context reduction style
  - Some examples of programs and their traces with and without POR are found in [examples](./POR_examples.v)
- [Program Logics](./ProgramLogics.v) contains some notes on program logics for [Parallel](./Parallel.v). In particular the DL from sympaths and Einar's simple parallel logic

### Other
- [PLACES](./PLACES) contains a talk proposal to [PLACES 2023](https://places-workshop.github.io/2023/)
