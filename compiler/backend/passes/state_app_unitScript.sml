(*
  Compiler from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_miscTheory pure_configTheory state_cexpTheory;

val _ = new_theory "state_app_unit";

val _ = set_grammar_ancestry ["state_cexp"];

Definition unit_apps_def:
  unit_apps k x = if k = 0n then (x:cexp) else unit_apps (k-1) (app x Unit)
End

Definition push_app_unit_def:
  push_app_unit l ((Var v):cexp) =
    unit_apps l (Var v) ∧
  push_app_unit l (App op xs) =
    (if op = AppOp ∧ LENGTH xs = 2 then
       if EL 1 xs = Unit then
         push_app_unit (l+1n) (EL 0 xs)
       else unit_apps l $ App op (MAP (push_app_unit 0) xs)
     else unit_apps l $ App op (MAP (push_app_unit 0) xs)) ∧
  push_app_unit l (Lam vn x) =
    (if l ≠ 0 ∧ vn = NONE then
       push_app_unit (l-1n) x
     else unit_apps l  (Lam vn (push_app_unit 0 x))) ∧
  push_app_unit l (Letrec funs x) =
    Letrec (MAP (λ(f,v,y). (f,v,push_app_unit 0 y)) funs) (push_app_unit l x) ∧
  push_app_unit l (Let vn x y) =
    Let vn (push_app_unit 0 x) (push_app_unit l y) ∧
  push_app_unit l (If x y z) =
    If (push_app_unit 0 x) (push_app_unit l y) (push_app_unit l z) ∧
  push_app_unit l (Case x v rows) =
    unit_apps l
      (Case (push_app_unit 0 x) v (MAP (λ(v,vs,y). (v,vs,push_app_unit 0 y)) rows)) ∧
  push_app_unit l (Raise x) =
    unit_apps l (Raise (push_app_unit 0 x)) ∧
  push_app_unit l (Handle x v y) =
    unit_apps l (Handle (push_app_unit 0 x) v (push_app_unit 0 y)) ∧
  push_app_unit l (HandleApp x y) =
    unit_apps l (HandleApp (push_app_unit 0 x) (push_app_unit 0 y))
Termination
  WF_REL_TAC ‘measure (cexp_size o SND)’
  \\ gvs [LENGTH_EQ_NUM_compute,PULL_EXISTS,cexp_size_eq,list_size_def]
End

Triviality push_app_unit_test:
  push_app_unit 0 (App AppOp [Let NONE (Var w) (Lam NONE (Var v)); Unit]) =
  Let NONE (Var w) (Var v)
Proof
  EVAL_TAC
QED

val _ = export_theory ();
