# Sample PureCake programs and compiling them

This directory contains sample PureCake programs and a set up that enables compiling them.

By running `make`, you:
 - download prebuilt files `pure.S` and `cake.S` (the PureCake and CakeML compilers);
 - build compilers `pure` and `cake`;
 - compile sample program `factorials.hs`.

Once make has been run, the `purecake.sh` script can be used to create executables from `.hs` source files:
```
$ ./purecake.sh foo.hs
```
This will produce executable `foo`.
