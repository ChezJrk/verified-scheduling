# Verified ATL Scheduling Framework

This repository contains the implementation and demonstrations of the verified
ATL user-scheduling framework. It is compatible with Coq 8.15.0.

# Directories
The important details of the directory structure starting from the user's home directory is shown below.
```
~
|-- atl
|   `-- src
|       |-- clib
|       `-- ctest
```
The modules defining the ATL language, its rewrite framework, and select example programs are in `atl/src`.
The generated C code for these example programs sits in `atl/src/clib`.
The tests of correctness that run the generated C programs against each other (with assertions of equivalence) can be found in `atl/src/ctest`.

## Sanity-testing
You can run `atl/src/ctest/run_tests.sh`, which checks equivalence between outputs of ATL-generated code.
This should display a list of the pairwise tests that were run along with a `passed` symbol meaning that all assertions of equivalence in the test passed.

# Rebuilding
To rebuild the ATL language and framework, you can run `make clean` and then `make` in the `atl/src` directory.
This builds the ATL language, scheduling-rewrite theorems, rescheduled example proofs, their proof-producing scheduling scripts, and all associated tactics in this directory.
This build can take several minutes.

To regenerate and rebuild the library of C implementations generated from the lowering of ATL source programs, you can run `make clib` in the `atl/src` directory. 
This target depends on the the modules of the ATL library itself, so it will rebuild those as needed.
This target generates `libscheds.a`, the static library of ATL programs as well as all of their corresponding header files that are linked against in `atl/src/ctest` and `Halide/apps/atl_benchmark`.
This build takes about a minute to run.

To regenerate and rebuild the suite of C tests that run checks of equivalence between ATL programs, you can run `make ctest` in the `atl/src` directory.
This target similarly depends on the modules of the ATL library itself and builds those as needed accordingly.
However, this target also tries to link against the static library and header files generated in `atl/src/clib`, so this target must be built first.
This build should only take a few seconds to run.
This target generates several tests of equivalence that can be run with the `atl/src/ctest/run_tests.sh` script as described in the previous section.

# Claims
The following table matches claims and constructs mentioned in the paper with their proofs/implementation in the artifact codebase.

| Definition / Theorem | Paper | File |
| ----------- | ----------- | ----------- |
| Simple Halide pipeline code | Page 3, line 99 | Halide/apps/atl_benchmark/simple.cpp |
| Simple ATL pipeline | Page 3, Line 121 | atl/src/Simple.v, Line 15, `simple` |
| Simple ATL pipeline generated C code | Page 3, Line 137 | atl/src/clib/simple_atl.c |
| Simple pipeline rescheduling tactic script | Page 4, Line 167 | atl/src/Simple.v, Line 29 |
| `rw` tactic | Page 4, Line 169 | atl/src/CommonTactics.v, Line 730 (all variants) |
| Rescheduled simple pipeline generated C code | Page 4, Line 190 | atl/src/clib/simpl_resched_atl.c |
| Core ATL semantics | Page 7, Figure 2 | atl/src/ATL.v, Line 81|
| Get from Gen theorem | Page 8, Line 380 | atl/src/Common.v, Line 365, `get_gen_some` |
| Tensor generation equivalence | Page 9, Line 409 | atl/src/ContextDive.v, Line 214, `gen_eq_bound` |
| Iverson guard equivalence | Page 9, Line 439 | atl/src/ContextDive.v, Line 83, `iverson_in` |
| Normalization lemma | Page 12, Line 542 | atl/src/Normalize.v, Line 71, `normalize_bin` |
| Normalization lemma | Page 12, Line 569 | atl/src/Normalize.v, Line 61, `normalize_gen` |
| Code generation | Page 13, Figure 3 | atl/src/CodeGen.v, Line 687, `L` |
| Reshape operator definitions | Page 16, Figure 4 | atl/src/ReshapeOperators.v |
| Reshape operator compilation | Page 16, Figure 6 | atl/src/CodeGen.v, Line 992, `L` |
| Concatenation gen splitting | Page 16, Line 769 | atl/src/Reshape.v, Line 891, `split_gen` |
| True Iverson theorem | Page 16, Line 783 | atl/src/Consistency.v, Line 174, `true_iverson` |
| `simpl_guard` tactic | Page 16, Line 779 | atl/src/CommonTactics.v, Line 697, `simpl_guard` |
| Dual introduction rules | Page 19, Figure 7 | atl/src/Reshape.v, Line 24 |
| Consistency and shape | Page 19, Section 7.1 | atl/src/Consistency.v; atl/src/CommonTactics.v, Line 24, `consistent_shape` |
| `check_safe` tactic | Page 20, Section 7.2 | atl/src/CheckSafe.v, Line 82, `check_safe` |
| Two-stage blur program | Page 21, Figure 8 | atl/src/Blur.v, Line , `blurtwostage` |
| Tiled blur program | Page 22, Figure 9 | atl/src/Blur.v, Line , `blurtiled` |
| Scatter-to-gather transformation | Page 23, Figure 11 | atl/src/GatherScatter.v, Line 27, `gather_sched` |
| Im2col transformation | Page 25, Figure 12 | atl/src/Im2col.v, Line 55, `im2col_sched` |

# Evaluation
The evaluation can be split into two parts; the first of which pertains to the correctness proof for the optimizations described in our evaluation section and the second that concerns the benchmarking of the rescheduled ATL blur program against Halide.

## Proof-producing scheduling transformations
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

## Performance benchmarking
Once the example modules have been built above, you can generate and build the C library containing the example programs.
This is done by running `make clib` in `atl/src` \*.
The C programs are each defined as a function in their own file dumped in `atl/src/clib`.
These files have all been linked into one static library `libscheds.a` that is linked in the benchmarking driver in the Halide directory.

| ATL Program | C File (in `atl/src/clib`) | Halide file (in `Halide/apps/atl_benchmark`) |
| ----------- | ----------- |----------- |
| `blurtwostage` | `blurtwostage.c` | `blur_twostage.cpp` |
| `blurtiled` | `blurtiled.c` | `blur_tiled.cpp` |

The driver that benchmarks the ATL-generated blur code against Halide is `Halide/apps/atl_benchmark/run.cpp`.
To build this, run `make` in the `Halide/apps/atl_benchmark` directory \** .
To run the benchmark run `Halide/apps/atl_benchmark/run`.
This should output a table like the one below, similar to the table in our paper.

```
Framework   Program Time (ms) 
Halide  two-stage blur   4.0
ATL two-stage blur  4.0
Halide    tiled blur   2.0
ATL   tiled blur   2.0
```
# Additional Description
In the `atl/src` repo the modules are roughly structured into ones that define ATL, ones that define the scheduling rewrites, ones that implement tactics for the framework, and ones that demonstrate scheduling proofs on examples.

## ATL Framework Modules
`ATL.v` contains the definitions for the core language constructs of ATL. 
It also contains the typeclass definition for ATL types as well as the tensor and scalar instances of this type.

`ReshapeOperators.v` contains the definitions for the reshape operators in ATL.

`ContextDive.v` contains the context-producing lemmas for each core language construct and reshape operator.
These are used in the rewrite tactic and many of the like in `CommonTactics.v` to rewrite under binders with more information-rich environments.

`Common.v` contains the common theorems used in scheduling proofs (as well as used in proofs for other rewriting theorems).

`Div.v` contains a number of useful arithmetic lemmas that our automation makes use of in discharging index arithmetic goals.

`Consistency.v` contains the shape-inferring lemmas for each language construct.

`Tactics.v` contains a number of tactics defined to aid in the proof of some rewrite theorems within `Common.v`. 

`CommonTactics.v` contains much of the machinery used to implement the general rewrite tactic and its variations used in our framework for optimization programs.
This module contains the definitions of the rewrite tactic and the guard simplifying tactic.

`Reshape.v` primarily contains the dual-introducing, identity-pair theorems for introducing reshape operators into a program. 
It also contains additional theorems for commuting reshape operators with other language constructs.

`LetLifting.v` contains the theorems for lifting let-bindings throught the different ATL language constructs.

`GenPushout.v` contains rewriting theorems for transposing the Iverson bracket with other ATL language constructs.

## Example Program Modules
`Simple.v` contains the simple pipeline program used in the introduction of and carried throughout our paper as the guiding example.

`Im2col.v` contains the im2col programs and scheduling proof script to implement the optimization described in Section 8.3.

`GatherScatter.v` contains the scatter and gather programs and the scheduling proof script to transformation them as described in Section 8.2

`Blur.v` contains the two-stage and tiled blur programs and the scheduling proof script to transform them as described in Section 8.1.

`Convolution.v` contains a simple reduction of a program produced from reverse-mode differentiation of a 1D convolution.

## Code-Generation Modules
`CodeGen.v` contains the tactic for compiling ATL programs into C code (prints the lowered program as a string).

`CheckSafe.v` contains the `check_safe` tactic that ensures all accesses in a given program are in bounds.

`Normalize.v` contains the normalizing theorems described in Section 5.1.

`IdentParsing.v` contains tactic machinery for reification (turning a Gallina variable name into a string).

`IntToString.v` contains the tactic for turning integers into strings.

`NatToString.v` contains the tactic for turning natural numbers into strings.

## Output-Producing Modules
`GenLib.v` determines which programs to compile and output in C. 
This module's output is processed and dumped into `atl/src/clib`.
This file also invokes `check_safe` and `normalize` before compilation.

`GenTest.v` generates simple C equivalence tests between programs.
This module's output is processed and dumped into `atl/src/ctest`.
