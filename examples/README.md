# Sample PureCake programs and compiling them

This directory contains sample PureCake programs and a `Makefile` that enables compiling them.

You can compile and execute a source file `foo.hs` as follows:
```bash
make foo.exe
./foo.exe
```

The first time you run `make`, it will:
 - download `pure.tar.gz`;
 - extract prebuilt `pure.S` and `cake.S` files (the PureCake and CakeML compilers); and
 - build the compiler executables `pure` and `cake`.

Running `make` without arguments produces `factorials.exe`.
Running `make clean` removes all generated files except `pure.tar.gz`, and `make cleanAll` further removes `pure.tar.gz`.

