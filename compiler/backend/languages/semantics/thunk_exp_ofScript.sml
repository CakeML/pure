(*
  Definition of cexp -> exp function for thunkLang
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory combinTheory
     thunkLangTheory thunk_cexpTheory;

val _ = new_theory "thunk_exp_of";

val _ = set_grammar_ancestry ["thunkLang", "thunk_cexp"];

Definition lets_for_def:
  lets_for l cn v [] b = (b:thunkLang$exp) ∧
  lets_for l cn v ((n,w)::ws) b =
    Seq (If (IsEq cn l T (Var v)) Unit Fail) $
      Let (SOME w) (Proj cn n (Var v)) $
        lets_for l cn v ws b
End

Definition rows_of_def:
  rows_of v k [] = (k:thunkLang$exp) ∧
  rows_of v k ((cn,vs,b)::rest) =
    If (IsEq cn (LENGTH vs) T (Var v))
      (lets_for (LENGTH vs) cn v (MAPi (λi v. (i,v)) vs) b) (rows_of v k rest)
End

Definition op_of_def[simp]:
  op_of (Cons m) = Cons (explode m) ∧
  op_of (AtomOp a) = AtomOp a
End

Definition exp_of_def[simp]:
  exp_of (Var n)         = Var (explode n):thunkLang$exp ∧
  exp_of (Prim p xs)     = Prim (op_of p) (MAP exp_of xs) ∧
  exp_of (Let w x y)     = Let (OPTION_MAP explode w) (exp_of x) (exp_of y) ∧
  exp_of (App f xs)      = Apps (exp_of f) (MAP exp_of xs) ∧
  exp_of (Lam vs x)      = Lams (MAP explode vs) (exp_of x) ∧
  exp_of (Letrec rs x)   = Letrec (MAP (λ(n,x). (explode n,exp_of x)) rs) (exp_of x) ∧
  exp_of (Case v rs opt) =
      rows_of
        (explode v)
        (case opt of NONE => Fail | SOME e => exp_of e)
        (MAP (λ(c,vs,x). (explode c,MAP explode vs,exp_of x)) rs) ∧
  exp_of (Force x)       = Force (exp_of x) ∧
  exp_of (Delay x)       = Delay (exp_of x) ∧
  exp_of (Box x)         = Box (exp_of x)
Termination
  WF_REL_TAC ‘measure cexp_size’ >> rw [cexp_size_eq]
End

val _ = export_theory ();
