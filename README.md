# Verified Inlining and Specialisation for PureCake

## Getting started

This [Docker](https://www.docker.com/) image contains a pre-built version of
the PureCake compiler, with our inliner installed.  That is, all HOL4 theories
are already built, and the PureCake compiler has already been bootstrapped.

To start the container:
```bash
docker load --input pure-esop24-docker.tar.gz
docker run -it pure-esop24
```

You can verify that all theories have been built and the compiler bootstrapped
by executing:
```bash
cd ~/pure/compiler/binary && Holmake
```


## Step-by-step instructions


### Examining HOL4 theories

All of the PureCake project (including our inliner) is developed within the
[HOL4](http://hol-theorem-prover.org/) interactive theorem prover.  Any results
stated in the paper have been mechanically verified within HOL4's logic.
Therefore, we envisage the bulk of in-depth examination of this artifact will
be via inspection of the theorems we have proved.  To aid this, we have written
a [`CORRESPONDENCES.txt`](CORRESPONDENCES.txt) document which links each part
of the paper to the corresponding mechanisation.

**We recommend reading `Theory.sig` files.**
Each `...Script.sml` development file has such a `...Theory.sig` file: a build
artifact concisely summarising of all its definitions and theorems.  Readers
familiar with HOL4 can also inspect the `...Script.sml` development files, or
use HOL4's `emacs` or `vim` interaction (both are set up) to step through the
files.


### Benchmarking programs

The [`examples`](examples) directory contains sample programs which readers can
compile and benchmark.


#### Compiling sample programs

The [`Makefile`](examples/Makefile) enables compilation of all sample programs.
To compile and execute `foo.hs`:
```bash
cd examples
make foo.exe
./out/foo.exe <input>
```
Note that executables are placed in the `examples/out` directory.
All current examples expect integer input.

The first time you run `make`, it will:
 - copy in `../compiler/binary/pure.S` (the PureCake compiler); and
 - build the compiler executables `pure` and `cake`, and the FFI object
   `basis_ffi.o`.

Running `make` without arguments produces `factorials.exe`. Running `make
clean` removes all generated files, including `lib/pure.S`. Running `make
check` compiles all `.hs` files.

#### Benchmarking programs

The [`benchmark`](examples/benchmark) directory allows simple benchmarking of
our inliner as follows:
```bash
cd examples
patch -u -i benchmark/benchmark.patch
touch lib/basis_ffi.c # ensure PureCake's FFI is rebuilt with debug output enabled
cd benchmark
benchmark.py # takes ~1 hr with supplied configuration
benchmark.py --mode plot
```
This will:
1. Apply PureCake's benchmarking patches to some sample programs.
2. Compile and run the benchmarks as specified in
   [`bench.config`](examples/benchmark/bench.config), collecting data on
   timings and heap allocations into `benchmark/data.csv`.
3. Plot graphs from the collected data, saving them to `benchmark/data.pdf`.
   These show base-2 logarithm of runtime speedup and reduction in heap
   allocations.

##### [`bench.config`](examples/benchmark/bench.config)

This specifies the benchmarking configuration for
[`benchmark.py`](examples/benchmark/benchmark.py):
- `settings.iterations`: number of iterations to run each program/flag
  combination.
- `settings.heap`: CakeML heap size in bytes.
- `programs`: key-value pairs of benchmark names (without the `.hs` suffix) and
  their commandline inputs.
- `flags`: key-value pairs of names and sets of flags used when invoking
  PureCake.

Each program will be compiled and run with each set of supplied flags.
PureCake has several available flags, but we consider only those relevant to
our inliner:
- `-inline_depth=N`: recursion limit for the inliner
- `-inline_size=N`: heuristic governing size of inlinable code

**NB by default PureCake runs with `-inline_depth=5000 -inline_size=10000`.**
The graphs produced by [`benchmark.py`](examples/benchmark/benchmark.py)
therefore show the improvements made when *enabling* our inliner.

##### [`benchmark.py`](examples/benchmark/benchmark.py)

Run `benchmark.py -h` for usage information.  By default, it will read/write
`data.{csv,pdf}` - you can change this with e.g. `benchmark.py --filestem foo`
to read/write `foo.{csv,pdf}`.  To compile all benchmarks specified in
[`bench.config`](examples/benchmark/bench.config) *without* running them, use
`benchmark.py --mode compile`.

The data shown in the paper is in
[`fig-3-blue.csv`](examples/benchmark/fig-3-blue.csv) and
[`fig-4-red.csv`](examples/benchmark/fig-4-red.csv).
The first can be reproduced by running `benchmark.py` as-is.
To reproduce the second, we have included a pre-built PureCake compiler
([`pure.inline-after-demands.S`](examples/lib/pure.inline-after-demands.S))
which can be used instead of `pure.S`:
```bash
cd examples
cp lib/pure.S.inline-after-demands.S lib/pure.S
```
Then continue with the benchmarking instructions as before (i.e. starting with
`patch -u -i ...` above).

To produce this alternative version of PureCake, we modified and rebuilt the
compiler using the commands below. Note that this version is unverified.
**NB: this will take ~5 hrs and require ~8 GB RAM (16 GB recommended). We do
not believe it is necessary for examination of this artifact.**
```bash
cd ~/pure/compiler
patch -u -i ../examples/benchmark/inline-after-demands.patch
cd binary
Holmake
```
This will produce `compiler/binary/pure.S`.


### Re-building HOL4 theories and the PureCake binary

**NB: this will take ~5 hrs and require ~8 GB RAM (16 GB recommended). We do
not believe it is necessary for examination of this artifact.**

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
This will produce `compiler/binary/pure.S`.

