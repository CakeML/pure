(*
  Simplification of Letrec for cexp
*)
open HolKernel Parse boolLib bossLib term_tactic;
open listTheory pairTheory;
open pure_cexpTheory pure_letrecTheory pure_beta_equivTheory;

val _ = new_theory "pure_letrec_cexp";

(*
  TODO: improve efficiency by using freevar sets, and avoiding recomputation
  of freevars (perhaps by using annotations at cexp AST nodes)
*)

(*******************)

Definition letrec_recurse_cexp_def:
  letrec_recurse_cexp f (Letrec c xs y) =
    f c (MAP (λ(n,x). n, letrec_recurse_cexp f x) xs) (letrec_recurse_cexp f y) ∧
  letrec_recurse_cexp f (Lam c ns x) = Lam c ns (letrec_recurse_cexp f x) ∧
  letrec_recurse_cexp f (Prim c p xs) = Prim c p (MAP (letrec_recurse_cexp f) xs) ∧
  letrec_recurse_cexp f (App c x ys) =
    App c (letrec_recurse_cexp f x) (MAP (letrec_recurse_cexp f) ys) ∧
  letrec_recurse_cexp f (Var c v) = Var c v ∧
  letrec_recurse_cexp f (Let c n x y) =
    Let c n (letrec_recurse_cexp f x) (letrec_recurse_cexp f y) ∧
  letrec_recurse_cexp f (Case c x n ys) =
    Case c (letrec_recurse_cexp f x) n
      (MAP (λ(n,ns,e). (n,ns,letrec_recurse_cexp f e)) ys)
Termination
  WF_REL_TAC `measure (cexp_size (K 0) o SND)` >> rw [] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[cexp_size_def]
End

(********** pure_letrecTheory **********)

(*
  1. a pass that ensures, for every Letrec xs y, that ALL_DISTINCT (MAP FST xs)
*)

Definition distinct_cexp_def:
  distinct_cexp ce =
    letrec_recurse_cexp (λc fns e. Letrec c (make_distinct fns) e) ce
End


(*
  2. split every Letrec according to top_sort_any, i.e. each Letrec becomes
     one or more nested Letrecs
*)

Definition make_Letrecs_cexp_def:
  make_Letrecs_cexp c [] e = e ∧
  make_Letrecs_cexp c (fns::rest) e = Letrec c fns (make_Letrecs_cexp c rest e)
End

Definition split_one_cexp_def:
  split_one_cexp fns =
    let deps = MAP (λ(fn,body). (fn, freevars_cexp_l body)) fns in
    let sorted = top_sort_any deps in
    MAP (λl. MAP (λs. (s, THE (ALOOKUP fns s))) l) sorted
End

Definition split_all_cexp_def:
  split_all_cexp e =
    letrec_recurse_cexp (λc fns e. make_Letrecs_cexp c (split_one_cexp fns) e) e
End


(*
  3. clean up pass:
     - remove any Letrec xs y that only bind variables that are not free in y
     - change any Letrec [(v,x)] y into Let v x y, when v not free in x
*)

Definition clean_one_cexp_def:
  clean_one_cexp c fns e =
    if DISJOINT (set (MAP FST fns)) (freevars_cexp e) then e else
    case fns of
      [(v,x)] => if v ∈ freevars_cexp x then Letrec c fns e else Let c v x e
    | _ => Letrec c fns e
End

Definition clean_all_cexp_def:
  clean_all_cexp e = letrec_recurse_cexp clean_one_cexp e
End


(********** pure_letrec_lamTheory **********)

Definition cl_cexp_def:
  cl_cexp c = Prim c (Cons "") []
End

(* We should never hit the `Lam _ [] _`, `App _ _ []` cases. *)
Definition make_apps_cexp_def:
  make_apps_cexp c [] = FEMPTY ∧
  make_apps_cexp c ((v,Lam _ [] e)::fs) = make_apps_cexp c ((v,e)::fs) ∧
  make_apps_cexp c ((_,Lam _ _ _)::fs) = make_apps_cexp c fs ∧
  make_apps_cexp c ((v,App _ e [])::fs) = make_apps_cexp c ((v,e)::fs) ∧
  make_apps_cexp c ((v,e)::fs) =
    make_apps_cexp c fs |+ (v, App c (Var c v) [cl_cexp c])
End

Definition lambdify_one_cexp_def:
  lambdify_one_cexp c letrec_c fns e =
    let apps = make_apps_cexp c fns in
    let fresh = fresh_var "x" (MAP FST fns ++ FLAT (MAP (freevars_cexp_l o SND) fns)) in
    let fns' = MAP (λ(v,f).
                if v ∈ FDOM apps then (v, Lam c [fresh] (substc apps f))
                else (v,substc apps f)) fns in
    Letrec letrec_c fns' (substc apps e)
End

Definition lambdify_all_cexp_def:
  lambdify_all_cexp c e = letrec_recurse_cexp (lambdify_one_cexp c) e
End

(*******************)

(*
    Putting it all together:
*)

Definition transform_cexp_def:
  transform_cexp cfg e =
    let d = distinct_cexp e in
    let s = split_all_cexp d in
    let c = clean_all_cexp s in
    let l = lambdify_all_cexp cfg c in
    l
End

(*******************)

val _ = export_theory();

