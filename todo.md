
TO-DO list
==========

Minor tweaks
------------

 - change `Letrec` to use `bind_all`
 - define `subst` in terms of `subst_all`
 - change name of `pure_io` to something like `pure_semantics`
 - define `freevars` directly as `freevars : exp -> vname set`?
 - define a quotient type for `exp` so that `Letrec : (vname |-> exp) -> exp -> exp`?
 - add `Seq` to primitive ops next to `If`, so that:

```
  eval (Prim Seq [x; y]) = if eval x = Diverge then eval x else eval y
```


Global refactorings that need discussion
----------------------------------------

We should organise the files better. Let's discuss:

 - how to avoid clash-prone theory names
 - use of directories like in CakeML repo, i.e. something like:
    - `semantics` has definition of syntax and semantics for PureCake
    - `semantics/proofs` has properties about the source syntax and semantics
    - `compiler` has top-level compiler definition
    - `compiler/proofs` proofs of top-level theorems
    - `compiler/backend{,/proofs}` compilation from PureCake to CakeML
    - `compiler/parsing{,/proofs}` parsing of PureCakeML concrete syntax
    - `compiler/inference{,/proofs}` type inference for PureCake
    - `compiler/bootstrap...` for turning the compiler into a binary
