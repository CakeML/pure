(*
  Definition of thunk_to_env compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory;
open thunk_cexpTheory env_cexpTheory;

val _ = new_theory "thunk_to_env";

val _ = set_grammar_ancestry ["thunk_cexp", "env_cexp"]

Definition Lams_def:
  Lams [] x = x ∧
  Lams (y::ys) x = env_cexp$Lam y (Lams ys x)
End

Definition Apps_def:
  Apps x [] = x ∧
  Apps x (y::ys) = Apps (env_cexp$App x y) ys
End

Definition get_arg_def:
  get_arg n [] = env_cexp$Prim (Cons (strlit "")) [] ∧
  get_arg n (x::xs) = if n = 0:num then x else get_arg (n-1) xs
End

Definition remove_Delay_def[simp]:
  remove_Delay (env_cexp$Delay x) = x ∧
  remove_Delay y = y
End

Definition op_to_env_def:
  op_to_env (thunk_cexp$AtomOp a) = env_cexp$AtomOp a ∧
  op_to_env (Cons n) = Cons n
End

Definition to_env_def:
  to_env ((Var v):thunk_cexp$cexp) = Var v:env_cexp$cexp ∧
  to_env (Let opt x y) = Let opt (to_env x) (to_env y) ∧
  to_env (Lam vs x) = Lams vs (to_env x) ∧
  to_env (App x xs) = Apps (to_env x) (MAP to_env xs) ∧
  to_env (Delay x) = Delay (to_env x) ∧
  to_env (Force x) = Force (to_env x) ∧
  to_env (Letrec fs x) = Letrec (REVERSE (MAP (λ(n,x). (n,to_env x)) fs)) (to_env x) ∧
  to_env (Case v rows d) = Case v (MAP (λ(n,p,x). (n,p,to_env x)) rows)
                            (case d of NONE => NONE | SOME (a,e) => SOME (a,to_env e)) ∧
  to_env (Prim p xs) = Prim (op_to_env p) (MAP to_env xs) ∧
  to_env (Monad mop xs) =
    let ys = MAP to_env xs in
    let y0 = get_arg 0 ys in
    let y1 = get_arg 1 ys in
    let y2 = get_arg 2 ys in
    case mop of
    | Ret    => Ret y0
    | Raise  => Raise y0
    | Bind   => Bind y0 y1
    | Handle => Handle y0 y1
    | Act    => Act y0
    | Length => Length y0
    | Alloc  => Alloc y0 y1
    | Deref  => Deref y0 y1
    | Update => Update y0 y1 y2
Termination
  WF_REL_TAC ‘measure cexp_size’
End

val _ = export_theory ();
