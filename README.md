# PureCake
## A verified compiler for a lazy functional language

PureCake is a verified implementation of a small, Haskell-like language known as PureLang.
It targets [CakeML](https://github.com/cakeml/cakeml), a verified implementation of a significant subset of Standard ML.
PureCake is developed within the [HOL4 interactive theorem prover](http://hol-theorem-prover.org).


### Quick start

```bash
docker run -it ghcr.io/cakeml/pure:master
```
This [Docker](https://www.docker.com/) image contains a pre-built version of the PureCake compiler.


### Quick start without Docker

```bash
git clone https://github.com/cakeml/pure
cd pure/examples && make download
```
This downloads the latest pre-built version of the PureCake compiler from GitHub.
You can now compile PureLang programs without building the compiler yourself, as described in [`examples/README.md`](examples/README.md).


### Slow start

Follow the build process described by our [`Dockerfile`](/.github/Dockerfile).
In summary: install PolyML; build HOL4; clone the PureCake and CakeML repositories; run `Holmake` in the top-level of the PureCake repository.
Building the entire PureCake project (including the bootstrapped compiler) will take several hours and require considerable compute resources.


### Repository structure

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
  Definitions concerning PureLang and its semantics, including built-in operations.

[meta-theory](meta-theory):
  PureLang's meta-theory.
  In particular, PureLang's equational theory and associated proofs (*e.g.* soundness of alpha- and beta-equivalence, and coincidence with contextual equivalence), and a formalisation of strictness (*demands*).

[misc](misc):
  Miscellaneous lemmas.

[typing](typing):
  PureCake's type system: proof of type soundness and a verified type inferencer.
