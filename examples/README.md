# Sample PureLang programs

This directory contains sample PureLang programs which showcase its expressivity.
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
 - download `pure.tar.gz` into the `lib` directory;
 - extract prebuilt `pure.S` and `cake.S` files (the PureCake and CakeML compilers); and
 - build the compiler executables `pure` and `cake`, and the FFI object `basis_ffi.o`.

Running `make` without arguments produces `factorials.exe`.
Running `make clean` removes all generated files except `pure.tar.gz`, and `make cleanAll` further removes `pure.tar.gz`.

