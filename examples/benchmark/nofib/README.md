# A nofib-Inspired Benchmark Suite for PureLang

## What this project is *not*

This is **not** a port of [nofib](https://gitlab.haskell.org/ghc/nofib), the
Haskell benchmark suite. No program in this repository should be described as
"the nofib `X` benchmark, ported to PureLang." This document explains what we
are doing instead.

## What this project actually does

We adopt nofib's **methodology**, not its **programs**:

-   **Tiering.** Benchmarks are organized into Real / Spectral / Imaginary
    analogues, using nofib's own criteria for what belongs in each tier
    (genuine task vs. algorithmic kernel vs. toy/smoke-test). Given PureLang's
    current feature set, our Real tier will necessarily be thin or aspirational
    at first --- this is stated explicitly rather than papered over.

-   **PureLang-native programs.** Each benchmark is written idiomatically *for*
    PureLang, working within its actual constraints (shallow pattern matching,
    packed-byte strings, no typeclasses), rather than forced through a
    translation of a Haskell original. Where a benchmark is clearly *inspired
    by* a specific nofib program, we say so explicitly and name the source ---
    but we do not call it a port.

-   **Same-language comparison only.** Like nofib, this suite is scoped to
    comparing different PureCake configurations against each other (e.g.
    optimization passes enabled vs. disabled), not PureLang against Haskell.
    Cross-language timing claims are out of scope for the same reasons nofib
    gives for declining them.

-   **No single figure of merit.** Results are reported per-benchmark
    (execution time, heap allocation), following PureCake's own §7.1
    methodology, not collapsed into one aggregate score.

-   **Raw result disclosure.** Following nofib's reporting rule, any published
    claim from this suite is accompanied by the complete raw results for every
    benchmark, not a curated subset.

## Relationship to `../benchmark.py`

`../benchmark.py` measures the effect of individual PureCake *optimisation
flags* (timing and heap allocation) on a handful of programs. This suite is
complementary: a broader, output-checked set of programs for tracking
whole-compiler correctness and performance, in the style of GHC `nofib`. Per
the `nofib` reporting rules, raw per-benchmark results should be published
before any derived summary figures.

## What's here

The layout mirrors the GHC `nofib` repository: a top-level `Makefile`, an `mk/`
boilerplate layer, and per-subset / per-benchmark `Makefile`s.

    nofib/
      Makefile                   # recurses into the subset directories
      mk/
        boilerplate.mk           # shared variables (mode, HEAP, paths)
        subdir.mk                # recursion over $(SUBDIRS)
        target.mk                # per-benchmark build / run / check / accept rules
      imaginary/
        Makefile                 # SUBDIRS = the imaginary benchmarks
        <name>/
          Makefile               # PROG + FAST_ARG / NORM_ARG / SLOW_ARG
          <name>.hs              # the benchmark (one self-contained file)
          <name>.faststdout      # expected output for `fast`
          <name>.stdout          # expected output for `norm`
          <name>.slowstdout      # expected output for `slow`
      spectral/<name>/ ...

## The benchmarks

| Subset | Name | Arg | Computes | Notes vs. GHC nofib |
|--------------|--------------------|-----------|-------------|----------------------|
| imaginary | `tak` | n | `tak (3n) (2n) n` (Takeuchi) | n=8 ⇒ classic `tak 24 16 8` |
| imaginary | `rfib` | n | `nfib n` | original returns `Double`; here integer `nfib` |
| imaginary | `exp3_8` | n | `3^n` via Peano numerals | n=8 ⇒ 6561; `slow` needs a large heap |
| imaginary | `primes` | n | n-th prime, two methods | from `examples/primes.hs`: lazy sieve + divisor test |
| imaginary | `queens` | n | \# solutions to n-queens | from `examples/queens.hs` (brute force) |
| imaginary | `gen_regexps` | rx | size of a generalised-regexp expansion | prints char count (RJE variant); `slow` needs a large heap |
| imaginary | `digits-of-e1` | n | n digits of e (continued fraction) | prints the digits |
| imaginary | `digits-of-e2` | n | n digits of e (factorial base) | strict `case` ⇒ explicit base case; 2n-budget keeps it correct |
| imaginary | `wheel-sieve1` | n | n-th prime (lazy wheel sieve) | first multiple kept lazy to untie the `primes` knot |
| imaginary | `paraffins` | n | radical / paraffin counts ≤ n | `Array` memo replaced by a lazy self-referential list |
| imaginary | `bernouilli` | n | n-th Bernoulli number | `Data.Ratio` replaced by `(num, den)` pairs |
| spectral | `life` | n | Conway's Game of Life, n generations | from `examples/gameOfLife.hs`; fixed 100×100 circuit (5 Gosper guns) |
| spectral | `primetest` | p | is `2^p − 1` (Mersenne) prime? | Miller-Rabin (fixed witnesses) modular exponentiation |
| spectral | `sorting` | n | quicksort of `[n..0]`, list & in-place array | from `examples/quicksort.hs`; checks both outputs are sorted |

The `primes`, `queens`, `sorting` and `life` programs are the existing
hand-written PureLang demos from `examples/`, brought into the suite (see the
attribution header in each `.hs`).

**Not ported:** `integrate`, `kahan`, `x2n1` (floating point); `wheel-sieve2`
(relies on a lazy infinite `roll`/`dropWhile` spiral that PureLang's strict
`case` cannot express cleanly --- `wheel-sieve1` covers the same algorithm
family); the entire `real` subset.

## Running

Everything is driven by `make` (run from this directory, or any subset /
benchmark directory):

``` bash
make runtests                  # build, run and check everything at mode=norm
make mode=fast runtests        # the quick workloads (good for a smoke test)
make mode=slow runtests        # the heavy workloads
make all                       # just build every benchmark
make -C imaginary/tak runtests # only one benchmark
make -C imaginary runtests     # only one subset
make list                      # list the benchmarks
make clean
```

Each benchmark prints `PASS` / `FAIL` (or `NOREF` if no reference exists yet)
with the argument used. `runtests` never aborts, so a full run reports the
whole suite. `PUREOPT` is forwarded to the PureCake frontend
(`make PUREOPT=-no_demands runtests`), and `HEAP` sets the CakeML heap size in
MB (default 4096; the `slow` modes of `exp3_8` and `gen_regexps` need a few
GB).

### Toolchain note

Compilation needs a working PureCake `pure.S` and a **compatible** CakeML
`cake`. The serialised-AST format shared between them changes over time, so a
freshly `make download`ed `pure.S` and the *latest* CakeML release do **not**
agree: `pure.S` emits sexp the newer `cake` rejects (`Parsing of sexp syntax
failed`). The latest `cake` additionally calls an `fficustom` symbol that older
copies of `../../lib/basis_ffi.c` did not define — this repo's `basis_ffi.c`
now provides it as a no-op, but an out-of-tree `basis_ffi.c` may still fail to
link `lib/cake` (`undefined reference to 'fficustom'`).

The PureCake `pure.S` currently published on GitHub is release `v2024.09.10`
(it pins CakeML commit `3b5f1f0`, Sept 2024) and is the latest pure release.
It builds and runs cleanly with CakeML release **v2648** (Oct 2024):

``` bash
wget https://github.com/cakeml/cakeml/releases/download/v2648/cake-x64-64.tar.gz
tar -xzf cake-x64-64.tar.gz cake-x64-64/cake.S
cp cake-x64-64/cake.S ../../lib/cake.S        # replace the downloaded `latest`
```

**Caveats on this pin:**

-   **It is approximate, not exact.** v2648 is the first CakeML *release* after
    the commit `pure.S` was built against (`3b5f1f0`, Sept 10), so there is a
    ~1-month drift window. The whole suite passes with it, but if you ever hit
    an unexplained codegen or parse failure, this skew is the first suspect ---
    try the CakeML release closest to `3b5f1f0`.

-   **It is fragile.** `lib/cake.S` is a downloaded, git-ignored artifact, and
    `make download` / `make clean` (in `examples/`) silently re-fetch the
    *latest* CakeML release, reintroducing the skew. The cp above must be
    repeated whenever that happens. The pin lives nowhere in version control.

-   **Durable alternatives** (pick one before relying on this long-term):
    (a) build `pure.S` locally from `../../../compiler/binary` against a CakeML
    checkout and use that same checkout's `cake` --- a multi-hour `Holmake`
    bootstrap, but an exact match; or (b) change `examples/Makefile` to fetch a
    *pinned* CakeML release tag instead of `latest`, so the matching `cake.S` is
    reproducible.

This version-skew is a pre-existing property of `examples/`, not specific to
this suite.

## Regenerating reference outputs

`make accept` runs each benchmark at the current mode and overwrites the
matching reference file. After editing a benchmark or changing its sizes:

``` bash
make -C imaginary/tak mode=fast accept   # rewrite tak.faststdout
make -C imaginary/tak accept             # rewrite tak.stdout (norm)
make -C imaginary/tak mode=slow accept   # rewrite tak.slowstdout
make accept                              # regenerate every norm reference
```

## Adding a benchmark

1.  `mkdir <subset>/<name>` and write a self-contained `<name>.hs` taking one
    command-line argument (copy the I/O helper block from any existing
    benchmark).

2.  Add a `Makefile`:

    ``` makefile
    TOP = ../..
    include $(TOP)/mk/boilerplate.mk
    PROG     = <name>
    FAST_ARG = ...      # target roughly <0.2 s
    NORM_ARG = ...      #   "      "      1–2 s
    SLOW_ARG = ...      #   "      "      5–10 s
    include $(TOP)/mk/target.mk
    ```

3.  Add `<name>` to the subset's `Makefile` `SUBDIRS`.

4.  Record references: `make -C <subset>/<name> mode=fast accept` (and `norm`,
    `slow`), then `make -C <subset>/<name> runtests` to confirm it passes.
