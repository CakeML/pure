#!/bin/bash

# USAGE:
#   ./purecake.sh foo.hs
# Outputs object `foo` in the current directory.

stem=$(basename "$1" .hs)
obj=$stem.S
cat "$1" | ./pure | ./cake --skip_type_inference=true --exclude_prelude=true --sexp=true > $obj
if [ $(uname) == "Darwin" ]
then
    CCOPT="-arch x86_64"
fi

gcc $CCOPT $obj basis_ffi.o -o $stem
