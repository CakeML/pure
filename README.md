# PureCake: A verified compiler for a lazy functional language

## Getting Started Guide

This [Docker](https://www.docker.com/) image contains a pre-built version of
the PureCake compiler.  That is, all HOL4 theories are already built, and the
PureCake compiler has already been verifiably bootstrapped.

To start the container:
```bash
docker load --input pure-pldi23-docker.tar.gz
docker run -it pure-pldi23
```

You can verify that all theories have been built and the compiler bootstrapped
by executing:
```bash
cd ~/pure/compiler/binary && Holmake
```

You can re-compile the sample PureLang programs in [`examples`](examples) by
executing:
```bash
cd ~/pure/examples && make clean && make check
```


## Step-by-Step instructions


### Examining HOL4 theories

All of the PureCake project is developed within the
[HOL4](http://hol-theorem-prover.org/) interactive theorem prover.  Any results
stated in the paper have been mechanically verified within HOL4's logic.
Therefore, we envisage the bulk of in-depth evaluation of this artifact will be
via inspection of the theorems we have proved.  To aid this, we have written a
[`correspondences.md`](correspondences.md) document which links each part of
the paper to the corresponding mechanisation.  The [project
structure](#project-structure) section below also gives a high-level overview
of the PureCake project structure.

**We recommend reading `Theory.sig` files.**
Each `...Script.sml` development file has such a `...Theory.sig` file: a build
artifact concisely summarising of all its definitions and theorems.  Readers
familiar with HOL4 can also inspect the `...Script.sml` development files, or
use HOL4's `emacs` or `vim` interaction (both are set up) to step through the
files.


### Examining and compiling programs

The [`examples`](examples) directory contains sample programs which reviewers
can examine and compile. The file [`syntax.hs`](examples/syntax.hs) file
contains a near-exhaustive demonstration of PureLang's concrete syntax. The
other `.hs` files are non-trivial programs written in PureLang.

#### Compiling sample programs using PureCake

The [`Makefile`](examples/Makefile) enables compilation of all sample
programs. To compile and execute `foo.hs`:
```bash
cd examples
make foo.exe
./out/foo.exe
```
Note that executables are placed in the `examples/out` directory.

The first time you run `make`, it will:
 - copy in `../compiler/binary/pure.S` (the PureCake compiler); and
 - build the compiler executables `pure` and `cake`, and the FFI object
   `basis_ffi.o`.

Running `make` without arguments produces `factorials.exe`. Running `make
clean` removes all generated files, including `lib/pure.S`. Running `make
check` compiles all `.hs` files.


#### PureCake's "prelude"

The [`examples/prelude`](examples/prelude) directory is inspired by its
namesake in Haskell: it is a (work-in-progress) collection of useful functions
on basic data types. PureCake does not yet have an import system, so the
functions are not directly usable. However, they can be a useful set of
"building blocks" when creating larger PureLang programs.

To build and run files in the `prelude` directory:
```bash
cd examples
make prelude/bar.exe
./out/prelude/bar.exe
```
Note that no files in `prelude` will have observable effects when executed.
They are compiled and typechecked only.


### Re-building HOL4 theories and the PureCake binary

**NB: this will take ~5 hrs and require ~8 GB RAM (16 GB recommended). We do
not believe it is necessary for evaluation of this artifact.**

To produce this Docker image, we:
 1. Installed a prerequisite: PolyML
 2. Copied in the `hol`, `cakeml`, and `pure` directories (HOL4, CakeML, and
    PureCake respectively)
 3. Set environment variables: `HOLDIR=~/hol`, `CAKEMLDIR=~/cakeml`,
    `PUREDIR=~/pure`, `PATH=$HOLDIR:$PATH`
 3. Built HOL4: `cd hol && poly < tools/smart-configure.sml && ./bin/build`
 4. Built the PureCake theories and compiler binary: `cd pure && Holmake`

You can redo step 4 as follows:
```bash
cd ~/pure
Holmake -r cleanAll                # clean all theory files
rm ~/pure/compiler/binary/pure.S   # delete the PureCake binary
Holmake                            # rebuild all theories and the binary
```


## Project structure

[COPYING](COPYING):
  PureCake Copyright Notice, License, and Disclaimer.

[compiler](compiler):
  A verified compiler from PureLang to CakeML, with the components below.
  - [backend](compiler/backend):
    the compiler backend, with the following subdirectories.
    - [languages](compiler/backend/languages):
      intermediate languages, their semantics, and derived properties.
    - [passes](compiler/backend/passes):
      compilation passes and their proofs of correctness.
  - [binary](compiler/binary):
    verified (in-logic) bootstrapping of a compiler binary.
  - [parsing](compiler/parsing):
    lexing and parsing expression grammar (PEG) parsing.
  - [proofs](compiler/proofs)
    overall proofs of correctness.
  - [pure_compilerScript.sml](compiler/pure_compilerScript.sml):
    the compiler's top-level definition.

[examples](examples):
  Examples of PureLang code, how to invoke the PureCake compiler on them, and how to measure their performance.

[language](language):
  Definitions concerning PureLang and its semantics, including built-in
  operations.

[meta-theory](meta-theory):
  PureLang's meta-theory.
  In particular, PureLang's equational theory and associated proofs (*e.g.*
  soundness of alpha- and beta-equivalence, and coincidence with contextual
  equivalence), and a formalisation of strictness (*demands*).

[misc](misc):
  Miscellaneous lemmas.

[typing](typing):
  PureCake's type system: proof of type soundness and a verified type
  inferencer.


## Extending PureCake

PureCake is readily extensible, either by enriching its features or building on
it as-is.  Below are some pointers on how to get started.

### Meta-theory

- **Derive useful identities and rules in our equational theory.**
  For example, formalising textbook equations on Haskell code.
  The proofs in the following files provide some starting points:
    [`pure_congruenceScript.sml`](meta-theory/pure_congruenceScript.sml) (latter half),
    [`pure_congruence_lemmasScript.sml`](meta-theory/pure_congruence_lemmasScript.sml),
    [`meta-theory/pure_letrec_congScript.sml`](meta-theory/pure_letrec_congScript.sml).
- **Mechanise improvement theory over PureLang semantics.**
  This would take inspiration from literature, e.g.
  [this](https://doi.org/10.1145/292540.292547). An instructive starting point
  is the mechanisation of our [equational
  theory](meta-theory/pure_exp_relScript.sml) and its [proofs of
  congruence](meta-theory/pure_congruenceScript.sml).

### Compiler front end

- **Enriching PureLang's concrete syntax.**
  Parsing of concrete syntax is found in
  [`compiler/parsing`](compiler/parsing), and transforms concrete syntax first
  into AST and then into the `cexp` datatype (PureLang compiler expressions).
  Some useful features (from easier to harder to implement) are:
    permitting underscores when pattern-matching don't-care arguments;
    adding syntactic sugar for Haskell-like record types;
    enabling pattern-matching on left-hand-sides of equations (for e.g. tuples)
    by desugaring into `case`-statements;
    enabling multiple clauses in function definitions by desugaring into single
    clauses.
  The parser requires its [well-formedness
  proof](compiler/parsing/purePEGScript.sml) to be updated.
- **Improving type inference.**
  Our [implementation](typing/pure_inferenceScript.sml) of type inference is
  proof-of-concept and can be improved by porting features from [this
  work](https://www.open.ou.nl/bhr/TopQuality.pdf). For example: enforcing
  user-defined type signatures, using efficient data structures to store
  constraints, implementing better solving strategies. Modifying constraint
  generation changes require updates to implementation, [declarative
  rules](typing/pure_inference_modelScript.sml), and [soundness
  proofs](typing/pure_inferenceProofScript.sml).  Modifying solving requires
  updating only implementation and soundness proofs.
- **New front end features.**
  Some features require modifying both parsing and type inference, e.g. adding
  type class support.  This can be considered at the `cexp` level first, by
  modifying [typing rules](typing/pure_typingScript.sml) independently of type
  inference to account for a context of type classes.  Parsing must handle
  declarations, and accumulate the context to pass to type inference (similar
  to the current [context of data
  types](compiler/parsing/ast_to_cexpScript.sml)).  Inference must also
  elaborate type classes appropriately.
- **Demand analysis.**
  Demand analysis is currently over-eager in inserting `seq`, and can be
  improved to find demands better around data types and pattern-matching.
  [Implementation](compiler/backend/passes/pure_demands_analysisScript.sml) and
  [proofs](compiler/backend/passes/proofs/pure_demands_analysisProofScript.sml)
  will require updating.

### Compiler back end

- **Augmenting intermediate languages.**
  Semantics expressions and semantics can be modified in
  `compiler/backend/languages/semantics/*{Lang,_semantics}.sml`. Syntax of
  compiler expressions can be modified in
  `compiler/backend/languages/*_cexpScript.sml`. Proofs of invariants and
  well-formedness predicates will need to be updated in
  `compiler/backend/lanugages/properties`.
- **Adding optimisation passes.**
  Implementing a verifying a new optimisation consists of the several steps
  below (using the `state_app_unit` pass as a running example).
  1. define one or more syntactic compiler relations between expressions and
     prove they preserve semantics
     ([`state_app_unit_1ProofScript.sml`](compiler/backend/passes/proofs/state_app_unit_1ProofScript.sml)
     and
     [`state_app_unit_2ProofScript.sml`](compiler/backend/passes/proofs/state_app_unit_2ProofScript.sml)
  2. implement the code transformation
     ([`state_app_unitScript.sml`](compiler/backend/passes/state_app_unitScript.sml))
  3. prove that the code transformation inhabits the syntactic relation and
     satisfies bookkeeping invariants
     ([`state_app_unitProofScript.ml`](compiler/backend/passes/proofs/state_app_unitProofScript.sml))
  4. integrate into PureCake's [back end](compiler/backend/passes/pure_to_cakeScript.sml)
     and update
     [proofs](compiler/backend/passes/proofs/pure_to_cakeProofScript.sml)

  Simpler passes can omit definition of compiler relations, instead proving
  correctness directly over compiler implementation. For example, the
  `state_names*Script.sml` files implement and verify such a pass.
- **Reasoning principles for ThunkLang.**
  Implementing an equational theory for ThunkLang would simplify proofs greatly.
  This can take inspiration from [PureLang's
  theory](meta-theory/pure_congruenceScript.sml), but will be simplified by
  ThunkLang's call-by-value semantics.

### Using PureCake as-is

- **Creating real-world PureLang programs and testing them.**
  The various `.hs` files in [`examples`](examples), (particularly
  [`syntax.hs`](examples/syntax.hs) and the ["prelude"](examples/prelude))
  provide useful reference material.
- **Verifying PureLang programs.**
  Verification of simple Haskell-like programs can use either PureLang's
  equational theory, or reason directly about semantics. A simple example of
  such a proof is found at the bottom of
  [`pure_beta_equivScript.sml`](meta-theory/pure_beta_equivScript.sml). This
  reasoning can then be transported down to machine code by appealing to
  [compiler correctness proofs](compiler/proofs).
- **Differential analysis with GHC.**
  Compilation of safety-critical Haskell code by GHC can be made more
  trustworthy by testing against PureCake. By writing programs in the common
  subset accepted by both PureCake and GHC, input fuzzing can identify bugs
  introduced by compilation by searching for differences between the two
  compilers.
- **Re-using PureCake's compiler backend.**
  Compiling to PureLang's untyped AST permits straightforward reuse of its
  end-to-end verification down to machine code. The untyped AST must satisfy
  the preconditions of
  [`pure_to_cake_correct`](compiler/backend/passes/proofs/pure_to_cakeProofScript.sml)
  to permit composition with the correctness theorem.

