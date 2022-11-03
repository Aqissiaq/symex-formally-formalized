# symex-formally-formalized
Coq formalization of [Symbolic Execution Formally Explained](https://link.springer.com/article/10.1007/s00165-020-00527-y).

## Build
The included Makefile should allow just
```sh
make
```
To update the Makefile use
```sh
coq_makefile -f _CoqProject -o Makefile
```

## Structure
 - [BasicConcrete](./BasicConcrete.v) formalizes section **2. Basic symbolic execution** for simple arithmetic and boolean expression with integer valuations.
    - Syntax and notation for expressions is in [Expr](./Expr.v)
    - Notation and lemmas about maps used for substitution and valuation are in [Maps](./Maps.v)
 - [Recursion](./Recursion.v) formalizes **3. Recursion** – an extension of the basic language with procedure calls.
 - [OOP](./Oop.v) contains an incomplete formalization of **4. Object orientation.**

The approach to syntax and transition relation semantics is based on [Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/index.html)
