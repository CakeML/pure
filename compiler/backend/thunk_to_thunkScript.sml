(*
  A compiler from thunkLang with substitution-based semantics to thunkLang
  with envrionment-based semantics.
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     thunkLang_primitivesTheory thunkLangTheory thunkLang_substTheory;

val _ = new_theory "thunk_to_thunk";

Definition compile_exp_def:
  compile_exp (Var n: thunkLang_subst$exp) = Var n : thunkLang$exp ∧
  compile_exp (Prim op xs) = Prim op (MAP compile_exp xs) ∧
  compile_exp (App x y) = App (compile_exp x) (compile_exp y) ∧
  compile_exp (Lam s x) = Lam s (compile_exp x) ∧
  compile_exp (Let n x y) = Let n (compile_exp x) (compile_exp y) ∧
  compile_exp (Letrec f x) =
    Letrec (MAP (λ(fn,x). (fn, compile_exp x)) f) (compile_exp x) ∧
  compile_exp (If x y z) =
    If (compile_exp x) (compile_exp y) (compile_exp z) ∧
  compile_exp (Delay x) = Delay (compile_exp x) ∧
  compile_exp (Box x) = Box (compile_exp x) ∧
  compile_exp (Force x) = Force (compile_exp x) ∧
  compile_exp (Value v) = Lam "%dummy%" (Var "%dummy%") ∧
  compile_exp (MkTick x) = Lam "%dummy%" (Var "%dummy%")
Termination
  WF_REL_TAC ‘measure exp_size’ \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [thunkLang_substTheory.exp_size_def]
End

Definition rce_def:
  rce (Var n: thunkLang$exp) = Var n : thunkLang_subst$exp ∧
  rce (Prim op xs) = Prim op (MAP rce xs) ∧
  rce (App x y) = App (rce x) (rce y) ∧
  rce (Lam s x) = Lam s (rce x) ∧
  rce (Let n x y) = Let n (rce x) (rce y) ∧
  rce (Letrec f x) = Letrec (MAP (λ(fn,x). (fn,rce x)) f) (rce x) ∧
  rce (If x y z) = If (rce x) (rce y) (rce z) ∧
  rce (Delay x) = Delay (rce x) ∧
  rce (Box x) = Box (rce x) ∧
  rce (Force x) = Force (rce x)
Termination
  WF_REL_TAC ‘measure exp_size’ \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [thunkLangTheory.exp_size_def]
End

val _ = export_theory ();

