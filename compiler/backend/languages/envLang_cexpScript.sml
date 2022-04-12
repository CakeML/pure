(*
  Expressions for envLang as seen by the compiler
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory pred_setTheory rich_listTheory finite_mapTheory;
open pure_expTheory;

val _ = new_theory "envLang_cexp";

Datatype:
  cop = Cons string
      | AtomOp atom_op
End

Datatype:
  cexp = Var 'a vname
       | Prim 'a cop (cexp list)
       | App 'a cexp (cexp list)
       | Lam 'a (vname list) cexp
       | Letrec 'a ((vname # cexp) list) cexp
       | Let 'a (vname option) cexp cexp
       | If 'a cexp cexp cexp
       | Delay 'a cexp
       | Box 'a cexp
       | Force 'a cexp
       | Case 'a cexp vname ((vname # (vname list) # cexp) list)
End

Definition freevars_cexp_def[simp]:
  freevars_cexp (Var c v) = {v} ∧
  freevars_cexp (Prim c op es) = BIGUNION (set (MAP freevars_cexp es)) ∧
  freevars_cexp (App c e es) =
    freevars_cexp e ∪ BIGUNION (set (MAP freevars_cexp es)) ∧
  freevars_cexp (Lam c vs e) = freevars_cexp e DIFF set vs ∧
  freevars_cexp (Letrec c fns e) =
    freevars_cexp e ∪ BIGUNION (set (MAP (λ(fn,e). freevars_cexp e) fns))
      DIFF set (MAP FST fns) ∧
  freevars_cexp (Let c NONE e1 e2) = freevars_cexp e1 ∪ freevars_cexp e2 ∧
  freevars_cexp (Let c (SOME v) e1 e2) = freevars_cexp e1 ∪ (freevars_cexp e2 DELETE v) ∧
  freevars_cexp (If c e e1 e2) =
    freevars_cexp e ∪ freevars_cexp e1 ∪ freevars_cexp e2 ∧
  freevars_cexp (Delay c e) = freevars_cexp e ∧
  freevars_cexp (Box c e) = freevars_cexp e ∧
  freevars_cexp (Force c e) = freevars_cexp e ∧
  freevars_cexp (Case c e v css) = freevars_cexp e ∪
    (BIGUNION (set (MAP (λ(_,vs,ec). freevars_cexp ec DIFF set vs) css)) DELETE v)
Termination
  WF_REL_TAC `measure (cexp_size (K 0))` >> rw [] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

Definition get_info_def:
  get_info (Var c _) = c ∧
  get_info (Prim c _ _) = c ∧
  get_info (App c _ _) = c ∧
  get_info (Lam c _ _) = c ∧
  get_info (Letrec c _ _) = c ∧
  get_info (Let c _ _ _) = c ∧
  get_info (If c _ _ _) = c ∧
  get_info (Delay c _) = c ∧
  get_info (Box c _ ) = c ∧
  get_info (Force c _ ) = c ∧
  get_info (Case c _ _ _) = c
End

val _ = export_theory();
