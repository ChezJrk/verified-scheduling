# Verified ATL Framework

This repository contains the Coq implementation of ATL: a functional,
high-performance tensor programming language. It also contains the verified
scheduling tactic framework used to optimize ATL programs via a series of
high-level source-to-source rewrites. We provide a set of examples to run and 
demonstrate the performance capability of such framework. Additionally, this 
repository separately contains a proof of correctness for the lowering algorithm 
used to compile ATL programs to imperative loop nests in C.

## Repository Structure

The repo structure is as follows:
```
atl
└── src
    ├── examples
    ├── verified_lowering
    │   ├── inferpad
    │   ├── proof
    │   └── stringify
    │       ├── lib
    │       └── test
    └── verified_scheduling
        ├── atl
        ├── c
        │   ├── lib
        │   └── test
        └── codegen
```

# Verified Scheduling

The modules defining the ATL language, its rewrite framework, and select example programs are in `atl/src/verified_scheduling`.
The `atl/src/verified_scheduling/codegen` directory contains the original Ltac
lowering process that takes shallowly
embedded ATL programs and emits C code in the `atl/src/verified_scheduling/c`
directory for performance and correctness testing.

## Sanity-testing
To generate and run equivalence checks between outputs of lowering ATL code using the verified scheduling framework, you can run `make testsXb` in `atl/src/verified_scheduling/`.
This should display a list of the pairwise tests that were run along with a `passed` symbol meaning that all assertions of equivalence in the test passed.

## Evaluation
The evaluation can be split into two parts; the first of which pertains to the correctness proof for the optimizations described in our evaluation section and the second that concerns the benchmarking of the rescheduled ATL blur program against Halide.

### Proof-producing scheduling transformations
The evaluation in our paper mentions three verified scheduling-rewrite transformations: the Im2col optimization, the gather-to-scatter optimization, and the two-stage to tiled blur transformation.

The starting programs in the optimizations are defined and their rescheduled counterparts are constructed using the `Derive` command, providing both a name for the produced proof and the rescheduled program.

| Example | File | Starting Program | Proof Object | Rescheduled Program |
| ----------- | ----------- | ----------- | ----------- | ----------- |
| Im2col | `atl/src/Im2col.v` | `im2col` | `im2col_sched` | `im2col_lifted` |
| Scatter-to-Gather | `atl/src/GatherScatter.v` | `scatter_full` | `gather_sched` | `gather_full` |
| Two-stage Blur |  `Blur.v` | `blur` | `twostagepart` | `blurtwostage` |
| Tiled Blur | `Blur.v` | `blur` | `total_tiled` | `blurtiled` |

These proofs can be compiled simply by running `make` in `atl/src`. You can also `touch` the files above to force the recompilation of these proofs.
A small `Assumptions.v` module is provided that prints all assumptions that each of the given three proof-producing transformations depends on.
This output can be seen by compiling the module by running `make -B assumptions` in `atl/src`.
This output should show that the only axioms assumed are functional extensionality (`FunctionalExtensionality.functional_extensionality_dep`) and decidability of nonemptiness for natural-number predicates (`ClassicalDedekindReals.sig_forall_dec`).

### Performance benchmarking
Once the example modules have been built above, you can generate and build the C library containing the example programs.
The C programs are each defined as a function in their own file dumped in `atl/src/verified_scheduling/c/lib`.
When tested, these files were linked into one static library `libscheds.a` that was linked in the benchmarking driver in the Halide directory.

| ATL Program | C File (in `atl/src/clib`) | Halide file (in `Halide/apps/atl_benchmark`) |
| ----------- | ----------- |----------- |
| `blurtwostage` | `blurtwostage.c` | `blur_twostage.cpp` |
| `blurtiled` | `blurtiled.c` | `blur_tiled.cpp` |

This should output a table like the one below, similar to the table in our paper.

```
Framework   Program Time (ms) 
Halide  two-stage blur   4.0
ATL two-stage blur  4.0
Halide    tiled blur   2.0
ATL   tiled blur   2.0
```
## Verified Lowering

The `verified_lowering` directory contains the proof and formalizations of a deeply embedded ATL definition
and the verification of the lowering algorithm
used to generate C code in `atl/src/verified_lowering/proof`. 
This includes a pad type system used to enforce well-formedness conditions in
programs that are input to the compiler.
The `atl/src/verified_lowering/infer_pad` directory contains the tactic
machinery used to statically and
automatically type-check ATL programs according to the pad type system mentioned
above.
Finally the `atl/src/verified_lowering/stringify` directory contains tests of
the full verified pipeline (lowering to imperative code and pad-type inference)
on ATL programs derived from the ATL verified rewrite framework.

These test programs can be found in the `examples` directory.
This is a set of ATL example programs optimized using the verified rewrite
program. 

## How to Run
To compile the compiler correctness proof and the full framework including
optimizations and lowering and run all
tests, simply run the following from inside the `src` directory:
``` make all```
This build can take several minutes.

To compile only the ATL language and rewrite framework:
```make atl```

To compile only the verification of lowering run:
```make low```

To run the testing of the pad type inference tactic system run:
```make padtest```

To run the testing of the full verified compilation pipeline of lowering and
pad-type inferece pipeline on verified-rewrite derived programs run:
```make lowtest```
