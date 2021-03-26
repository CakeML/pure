(*
  Simplification of Letrec for cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open listTheory pairTheory;
open pure_cexpTheory pure_letrecTheory pure_varsTheory balanced_mapTheory;

val _ = new_theory "pure_letrec_cexp";

(* TODO: combine passes into one big pass to reduce duplicated traversals *)

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
  WF_REL_TAC `measure $ cexp_size (K 0) o SND` >> rw[] >> gvs[] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[cexp_size_def]
End

(* A version of letrec_recurse_cexp which patches up freevars sets behind itself *)
Definition letrec_recurse_fvs_def:
  letrec_recurse_fvs f (Letrec c xs y : var_set cexp) =
    (let xs' = MAP (λ(n,x). n, letrec_recurse_fvs f x) xs in
     let y' = letrec_recurse_fvs f y in
     let c' = list_delete
                (list_union (get_info y' :: MAP (λ(f,e). get_info e) xs'))
                (MAP FST xs')
     in f c' xs' y') ∧
  letrec_recurse_fvs f (Lam c ns x) =
    (let x' = letrec_recurse_fvs f x in
     Lam (list_delete (get_info x') ns) ns x') ∧
  letrec_recurse_fvs f (Prim c p xs) =
    (let xs' = MAP (letrec_recurse_fvs f) xs in
     Prim (list_union (MAP get_info xs')) p xs') ∧
  letrec_recurse_fvs f (App c x ys) =
    (let ys' = MAP (letrec_recurse_fvs f) ys in
     let x' = letrec_recurse_fvs f x in
     App (list_union (MAP get_info (x'::ys'))) x' ys') ∧
  letrec_recurse_fvs f (Var c v) = Var (insert empty v ()) v ∧
  letrec_recurse_fvs f (Let c n x y) =
    (let x' = letrec_recurse_fvs f x in
     let y' = letrec_recurse_fvs f y in
     Let (union (get_info x') (delete (get_info y') n)) n x' y') ∧
  letrec_recurse_fvs f (Case c x n ys) =
    (let x' = letrec_recurse_fvs f x in
     let ys' = MAP (λ(cn,vs,e). (cn,vs,letrec_recurse_fvs f e)) ys in
     let c' =
        union (get_info x')
          (delete (list_union (MAP (λ(cn,vs,e). list_delete (get_info e) vs) ys')) n)
    in Case c' x' n ys')
Termination
  WF_REL_TAC `measure $ cexp_size (K 0) o SND` >> rw[] >> gvs[] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[cexp_size_def]
End

(********************)

(*
  A pass that ensures, for every Letrec xs y, that ALL_DISTINCT (MAP FST xs).
  No need to patch up freevars here as the pass doesn't rely on them.
*)

Definition distinct_cexp_def:
  distinct_cexp ce =
    letrec_recurse_cexp (λc fns e. Letrec c (make_distinct fns) e) ce
End


(*
  Split every Letrec according to top_sort_any, i.e. each Letrec becomes
  one or more nested Letrecs.
  Need to keep track of freevars here.
*)

Definition make_Letrecs_cexp_def:
  make_Letrecs_cexp [] e = e ∧
  make_Letrecs_cexp (fns::rest) e =
    let rest' = make_Letrecs_cexp rest e in
    let c = list_delete
              (list_union (get_info rest' :: MAP (λ(f,e). get_info e) fns))
              (MAP FST fns)
    in Letrec c fns rest'
End

Definition split_one_cexp_def:
  split_one_cexp fns =
    let deps = MAP (λ(fn,e). (fn, MAP FST (toAscList $ get_info e))) fns in
    let sorted = top_sort_any deps in
    MAP (λl. MAP (λs. (s, THE (ALOOKUP fns s))) l) sorted
End

Definition split_all_cexp_def:
  split_all_cexp (e : var_set cexp) =
    letrec_recurse_fvs (λc fns e. make_Letrecs_cexp (split_one_cexp fns) e) e
End


(*
  Clean up resulting Letrecs:
   - remove any Letrec xs y that only bind variables that are not free in y
   - change any Letrec [(v,x)] y into Let v x y, when v not free in x
*)

Definition clean_one_cexp_def:
  clean_one_cexp c fns (e : var_set cexp) =
    if EVERY (λf. lookup (get_info e) f = NONE) (MAP FST fns) then e else
    case fns of
      [(v,x)] => if lookup (get_info x) v = NONE then Let c v x e
                 else Letrec c fns e
    | _ => Letrec c fns e
End

Definition clean_all_cexp_def:
  clean_all_cexp e = letrec_recurse_fvs clean_one_cexp e
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
    c
End

(*******************)

val _ = export_theory();

