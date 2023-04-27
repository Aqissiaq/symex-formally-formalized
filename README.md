# Compositional SPOR
Coq development for "Compositional Correctness and Completeness for Symbolic Partial Order Reduction" for CONCUR23

## Build
The included Makefile (created for Coq 8.16.1) allows
```sh
make
```

To update the Makefile use
```sh
coq_makefile -f _CoqProject -o Makefile
```

## Table of Contents
### Prerequisites
    - [Maps](./Maps.v): generic notation for and results about maps
    - [Expr](./Expr.v): syntax/semantics of boolean and arithmetic expressions
    - [Parallel](./Parallel.v): syntax of statements with parallel composition and contexts
    - [Traces](./Traces.v): generic notation and results about traces and trace equivalence

### Symbolic Partial Order Reduction
    - [TraceSemantics](./TraceSemantics.v): semantics of concrete and symbolic execution and their bisimulation (**Section 2**)
    - [PartialOrderReduction](./PartialOrderReduction.v): semantics of POR for both symbolic and concrete case (**Section 4**) as well as compositions (**Section 5**)

### Examples
    - [InterferenceFreedom](./InterferenceFreedom.v): an example of POR by permuting interference free events (**Section 3.1**)
    - [PORExamples](./PORExamples): some example computations using POR semantics
