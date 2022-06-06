#!/bin/sh
cat build-list |\
    grep --invert-match --line-regexp --regexp="^#.*" --regexp="^$" |\
    xargs -I % sh -c "cd % && Holmake -k"
