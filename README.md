# PureCake: A verified compiler for a lazy functional language

### Getting Started Guide

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


### Step-by-Step instructions


#### Examining HOL4 theories

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


#### Examining and compiling programs

The [`examples`](examples) directory contains several sample PureCake programs.
Reviewers can examine and compile these programs.  Refer to
[`examples/README.md`](examples/README.md) for more details.


#### Re-building HOL4 theories and the PureCake binary

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


### Project structure

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

