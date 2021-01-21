(*
  A compiler from thunkLang with substitution-based semantics to thunkLang
  with envrionment-based semantics.
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     thunkLang_primitivesTheory thunkLangTheory thunkLang_substTheory;

val _ = new_theory "thunk_to_thunk";

Definition compile_exp_def:
  compile_exp (Var n) = Var n ∧
  compile_exp (Prim op xs) = Prim op (MAP compile_exp xs) ∧
  compile_exp (App x y) = App (compile_exp x) (compile_exp y) ∧
  compile_exp (Letrec f x) =
    Letrec (MAP (λ(fn, vn, x). (fn, vn, compile_exp x)) f) (compile_exp x) ∧
  compile_exp (If x y z) =
    If (compile_exp x) (compile_exp y) (compile_exp z) ∧
  compile_exp (Delay x) = Delay (compile_exp x) ∧
  compile_exp (Force x) = Force (compile_exp x) ∧
  compile_exp (Value v) = Var ""
Termination
  WF_REL_TAC ‘measure exp_size’ \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [thunkLang_substTheory.exp_size_def]
End

val _ = export_theory ();

