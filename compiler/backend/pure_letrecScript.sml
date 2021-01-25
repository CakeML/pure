(*
  Simplification of Letrec
*)
open HolKernel Parse boolLib bossLib term_tactic;
open pure_expTheory pure_miscTheory;

val _ = new_theory "pure_letrec";

(*

  The motivation for these Letrec simplifications is that the parser
  will produce a giant Letrec holding all the top-level functions. It
  makes sense to split this up and clean it up as much as possible early.

  Plan for the Letrec simplifications:

    1. make a pass that ensures, for every Letrec xs y, that
       ALL_DISTINCT (MAP FST xs)

    2. split every Letrec according to top_sort_any, i.e. each Letrec becomes
       one or more nested Letrecs

    3. clean up pass:
        - remove any Letrec xs y that only bind variables that are not free in y
        - change any Letrec [(v,x)] y into Let v x y, when v not free in x

*)

Definition make_distinct_def:
  (* this could be written in a more efficient way, but perhaps this is good
     for the proofs, i.e. the implementation version might be different *)
  make_distinct [] = [] ∧
  make_distinct ((n:string,x)::xs) =
    if MEM n (MAP FST xs) then make_distinct xs else (n,x)::make_distinct xs
End

Definition distinct_def:
  distinct (Letrec xs y) =
    Letrec (make_distinct (MAP (λ(n,x). (n, distinct x)) xs)) y ∧
  distinct (Lam n x) = Lam n (distinct x) ∧
  distinct (Prim p xs) = Prim p (MAP distinct xs) ∧
  distinct (App x y) = App (distinct x) (distinct y) ∧
  distinct res = res
Termination
  WF_REL_TAC ‘measure exp_size’ >> rw [] >>
  Induct_on `xs` >> rw[] >> gvs[exp_size_def]
End

val _ = export_theory();
