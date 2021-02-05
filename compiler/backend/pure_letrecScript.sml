(*
  Simplification of Letrec
*)
open HolKernel Parse boolLib bossLib term_tactic;
open pure_expTheory pure_miscTheory top_sortTheory;

val _ = new_theory "pure_letrec";

(*
  The motivation for these Letrec simplifications is that the parser
  will produce a giant Letrec holding all the top-level functions. It
  makes sense to split this up and clean it up as much as possible early.
*)

(*******************)

Definition letrec_recurse_def:
  letrec_recurse f (Letrec xs y) =
    f (MAP (λ(n,x). n, letrec_recurse f x) xs) (letrec_recurse f y) ∧
  letrec_recurse f (Lam n x) = Lam n (letrec_recurse f x) ∧
  letrec_recurse f (Prim p xs) = Prim p (MAP (letrec_recurse f) xs) ∧
  letrec_recurse f (App x y) = App (letrec_recurse f x) (letrec_recurse f y) ∧
  letrec_recurse f res = res
Termination
  WF_REL_TAC ‘measure (exp_size o SND)’ >> rw [] >>
  Induct_on `xs` >> rw[] >> gvs[exp_size_def]
End

(*******************)

(*
  1. a pass that ensures, for every Letrec xs y, that ALL_DISTINCT (MAP FST xs)
*)

Definition make_distinct_def:
  (* this could be written in a more efficient way, but perhaps this is good
     for the proofs, i.e. the implementation version might be different *)
  make_distinct [] = [] ∧
  make_distinct ((n:string,x)::xs) =
    if MEM n (MAP FST xs) then make_distinct xs else (n,x)::make_distinct xs
End

Definition distinct_def:
  distinct e = letrec_recurse (λfns e. Letrec (make_distinct fns) e) e
End


(*
  2. split every Letrec according to top_sort_any, i.e. each Letrec becomes
     one or more nested Letrecs
*)

Definition make_Letrecs_def:
  make_Letrecs [] e = e ∧
  make_Letrecs (fns::rest) e = Letrec fns (make_Letrecs rest e)
End

Definition split_one_def:
  split_one fns =
    let deps = MAP (λ(fn,body). (fn, freevars body)) fns in
    let sorted = top_sort_any deps in
    MAP (λl. MAP (λs. (s, THE (ALOOKUP fns s))) l) sorted
End

Definition split_all_def:
  split_all e = letrec_recurse (λfns e. make_Letrecs (split_one fns) e) e
End


(*
  3. clean up pass:
     - remove any Letrec xs y that only bind variables that are not free in y
     - change any Letrec [(v,x)] y into Let v x y, when v not free in x
*)

Definition clean_one_def:
  clean_one fns e =
    if DISJOINT (set (MAP FST fns)) (freevars e) then e else
    case fns of
      [(v,x)] => if v ∈ freevars x then Letrec fns e else Let v x e
    | _ => Letrec fns e
End

Definition clean_all_def:
  clean_all e = letrec_recurse clean_one e
End


(*
    Putting it all together:
*)

Definition simplify_def:
  simplify e =
    let d = distinct e in
    let s = split_all d in
    let c = clean_all s in
    c
End

(*******************)

val _ = export_theory();
