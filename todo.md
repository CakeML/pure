
TO-DO list
==========

To discuss
----------

 - Should we switch to a simpler `eval'` definition of the language from `meta-theory/pure_eval_altTheory`? *Yes on a branch.*


Wish list
---------

 - a set of target Haskell programs (concrete syntax) in a subset that we want to support
   (initially avoid Haskell's "where")

 - clarity on what the lexer should produce

```
input:
  foo:
    hello
    there
  bar:

output(?):
  FOO INDENT hello BR there DEDENT BAR
```


Minor tweaks
------------

 - [X] change `Letrec` to use `bind_all`
 - [X] define `subst` in terms of `subst_all`
 - [X] change name of `pure_io` to something like `pure_semantics`
 - [ ] add `Seq` to primitive ops next to `If`, so that:

```
  eval (Prim Seq [x; y]) = if eval x = Diverge then eval x else eval y
```

Might be needed
---------------

 - in the future might need to add siblings info to IsCons

```
      | IsEq string num ((string * num) list)  (* compare cons tag and num of args *)
```


Global refactorings that need discussion
----------------------------------------

We should organise the files better. Let's discuss:

 - how to avoid clash-prone theory names
 - use of directories like in CakeML repo, i.e. something like:
    - `language` has definition of syntax, semantics for PureCake
    - `meta-theory` has properties of PureCake (incl. exp_eq, congruence, alpa equiv)
    - `compiler` has top-level compiler definition
    - `compiler/proofs` proofs of top-level theorems
    - `compiler/parsing{,/proofs}` parsing of PureCakeML concrete syntax
    - `compiler/inference{,/proofs}` type inference for PureCake
    - `compiler/backend{,/semantics,/proofs}` compilation from PureCake to CakeML
    - `compiler/bootstrap...` for turning the compiler into a binary

    compiler/bootrap/compilation/x64/proofs
    compiler/bootrap/compilation/ag32/proofs




Decision
--------

 - we decided against defining `freevars` directly as `freevars : exp -> vname set`
 - for now decided against defining a quotient type for `exp` so that `Letrec : (vname |-> exp) -> exp -> exp`?


Random junk
-----------

```
 PureCake (type defs + a giant letrec)

  --> directly convert to CakeML for type inference

  --> compile call-by-name preserving way to untyped CakeML
```

 - Should we remove `Letrec` from the language formalisation?
     - This suggestion is based on a stuck proof in `pure_congruenceTheory`, where `Howe` doesn't (and can't) follow the `eval_to` expansion of the `Letrec`.
     - We could instead define `Letrec` as a macro that expands to Curry's *Y combinator*, i.e. `λf. (λx. f (x x)) (λx. f (x x))` but as `App`, `Lam` and `Var`.
