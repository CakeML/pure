# Sample PureLang programs and benchmarks

This directory contains sample PureLang programs which showcase its expressivity, and benchmarks to evaluate performance.
The file [`syntax.hs`](syntax.hs) contains a near-exhaustive demonstration of PureLang's concrete syntax.
The other `.hs` files are non-trivial programs written in PureLang.


## Compiling sample programs using PureCake

The [`Makefile`](Makefile) in this directory enables compilation of all sample programs.
To compile and execute `foo.hs`:
```bash
make foo.exe
./out/foo.exe
```
Note that executables are placed in the `out` directory.

The first time you run `make`, it will:
 - download a prebuilt `cake.S` (the CakeML compiler);
 - copy in the PureCake compiler (`pure.S`): either from `../compiler/binary` if it has been built, or from our GitHub releases if not.
 - build the compiler executables `pure` and `cake`, and the FFI object `basis_ffi.o`.

Running `make` without arguments produces `factorials.exe`.
Running `make clean` removes all generated files, including `lib/{pure.S,cake.S}`.
Running `make check` compiles all `.hs` files.
Running `make download` will download a prebuilt `pure.S` from our GitHub releases.

### Using your own versions of the PureCake/CakeML compilers

You can replace `lib/{pure.S,cake.S}` with your own versions.


## PureCake's "prelude"

The [`prelude`](prelude) directory is inspired by its namesake in Haskell: it is a (work-in-progress) collection of useful functions on basic data types.
PureCake does not yet have an import system, so the functions are not directly usable.
However, they can be a useful set of "building blocks" when creating larger PureLang programs.

To build and run file in the `prelude` directory:
```bash
make prelude/bar.exe
./out/prelude/bar.exe
```
Note that no files in `prelude` will have observable effects when executed.
They are compiled and typechecked only.


## Benchmarking

The [`benchmark`](benchmark) directory allows simple benchmarking of PureCake as follows:
```bash
git apply benchmark/benchmark.patch
touch lib/basis_ffi.c # ensure PureCake's FFI is rebuilt with debug output enabled
cd benchmark
benchmark.py # takes ~4 hrs with supplied configuration
benchmark.py --mode plot
```
This will:
1. Patch some programs to make them suitable for benchmarking:
   remove functional quicksort from [`quicksort.hs`](quicksort.hs) and remove polymorphic usages of functions (these will not typecheck if binding group analysis is disabled).
2. Compile and run the benchmarks as specified in [`bench.config`](benchmark/bench.config), collecting data on timings and heap allocations into `benchmark/data.csv`.
3. Plot graphs from the collected data, saving them to `benchmark/data.pdf`.
   These show base-2 logarithm of runtime speedup and reduction in heap allocations.

### [`bench.config`](benchmark/bench.config)

This specifies the benchmarking configuration for [`benchmark.py`](benchmark/benchmark.py):
- `settings.iterations`: number of iterations to run each program/flag combination.
- `settings.heap`: CakeML heap size in bytes.
- `programs`: key-value pairs of benchmark names (without the `.hs` suffix) and their commandline inputs.
- `flags`: key-value pairs of names and sets of flags used when invoking PureCake.

Each program will be compiled and run with each set of supplied flags.
Possible flags are:
- `-sort`: binding group analysis in PureLang
- `-clean`: deadcode elimination in PureLang
- `-inline_depth=N`, `inline_size=N`: inlining in PureLang
- `-demands`: demand analysis in PureLang
- `-mk_delay`: `mk_delay` smart constructor in ThunkLang
- `-dlam`: split delayed `lambda`s under `letrec`s in ThunkLang
- `-let_force`: common subexpression elimination of `force (var v)` in ThunkLang
- `-unit`: pushing in applications to `unit` in StateLang

**NB for boolean flags, supplying the flag *disables* the corresponding optimisation**.
Graphs produced by [`benchmark.py`](benchmark/benchmark.py) therefore show the improvements made when *removing* the flags specified.

### [`benchmark.py`](benchmark/benchmark.py)

**Dependencies:** `python3`, [`parse`](https://pypi.org/project/parse/), [`matplotlib`](https://pypi.org/project/matplotlib/), [`pandas`](https://pypi.org/project/pandas/).
Run `benchmark.py -h` for usage information.
By default, it will read/write `data.{csv,pdf}` - you can change this with e.g. `benchmark.py --filestem foo` to read/write `foo.{csv,pdf}`.
To compile all benchmarks specified in [`bench.config`](benchmark/bench.config) *without* running them, use `benchmark.py --mode compile`.

## Compiling programs with GHC

PureLang resembles a subset of Haskell, so PureLang programs are accepted by GHC with minimal changes.
The diff [`ghc.patch`](./ghc.patch) demonstrates these changes on some examples, and can be applied as follows:
```
git apply ghc.patch
```
The changes mostly:
- reconcile PureLang/GHC I/O and monads, including converting PureLang's `Array` to GHC's `IOArray`
- adapt PureLang primitives to GHC - including appropriate casts between `Int`/`Integer`
- use functions from GHC's `Prelude` rather than manually defining them

