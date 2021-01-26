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
  distinct (Letrec xs y) =
    Letrec (make_distinct (MAP (λ(n,x). (n, distinct x)) xs)) (distinct y) ∧
  distinct (Lam n x) = Lam n (distinct x) ∧
  distinct (Prim p xs) = Prim p (MAP distinct xs) ∧
  distinct (App x y) = App (distinct x) (distinct y) ∧
  distinct res = res
Termination
  WF_REL_TAC ‘measure exp_size’ >> rw [] >>
  Induct_on `xs` >> rw[] >> gvs[exp_size_def]
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
  split_all (Letrec xs y) =
    (let xs1 = MAP (λ(fn,e). (fn, split_all e)) xs in
     make_Letrecs (split_one xs) (split_all y)) ∧
  split_all (Lam n x) = Lam n (split_all x) ∧
  split_all (Prim p xs) = Prim p (MAP split_all xs) ∧
  split_all (App x y) = App (split_all x) (split_all y) ∧
  split_all res = res
Termination
  WF_REL_TAC `measure exp_size` >> rw [] >>
  Induct_on `xs` >> rw[] >> gvs[exp_size_def]
End


(*
  3. clean up pass:
     - remove any Letrec xs y that only bind variables that are not free in y
     - change any Letrec [(v,x)] y into Let v x y, when v not free in x
*)

Definition clean_all_def:
  clean_all (Letrec xs y) = (
    let y' = clean_all y in
    if DISJOINT (set (MAP FST xs)) (freevars y) then y' else
    case xs of
      [(v,x)] => if v ∈ freevars x then Letrec xs y else Let v x y'
    | _ => Letrec xs y'
    ) ∧
  clean_all (Lam n x) = Lam n (clean_all x) ∧
  clean_all (Prim p xs) = Prim p (MAP clean_all xs) ∧
  clean_all (App x y) = App (clean_all x) (clean_all y) ∧
  clean_all res = res
Termination
  WF_REL_TAC `measure exp_size` >> rw [] >>
  Induct_on `xs` >> rw[] >> gvs[exp_size_def]
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

val _ = export_theory();
