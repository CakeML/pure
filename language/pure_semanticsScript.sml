
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory pure_evalTheory io_treeTheory;

val _ = new_theory "pure_semantics";


(* definitions *)

Datatype:
  result = SilentDivergence
         | Termination
         | Error
End

Datatype:
  next_res = Act 'e (exp list) | Ret | Div | Err
End

Inductive next:
  (∀e stack a.
    eval_wh e = wh_Atom a ⇒
    next (wh_Constructor "Act" [e], stack) (Act a stack))
  ∧
  (∀m f stack res.
    next (eval_wh m, f::stack) res ⇒
    next (wh_Constructor "Bind" [m; f], stack) res)
  ∧
  (∀stack.
    next (wh_Diverge, stack) Div)
  ∧
  (∀v.
    next (wh_Constructor "Ret" [v], []) Ret)
  ∧
  (∀f n e x stack res.
    dest_wh_Closure (eval_wh f) = SOME (n,e) ∧
    next (eval_wh (bind n x e), stack) res ⇒
    next (wh_Constructor "Ret" [x], f::stack) res)
  ∧
  (∀f x stack.
    eval_wh f = wh_Diverge ⇒
    next (wh_Constructor "Ret" [x], f::stack) Div)
  ∧
  (∀v stack.
    (v ≠ wh_Diverge) ∧
    (∀e. v = wh_Constructor "Act" [e] ⇒
         ∀a. eval_wh e ≠ wh_Atom a) ∧
    (∀e. v = wh_Constructor "Ret" [e] ⇒
         stack ≠ [] ∧
         ∀f fs. stack = f :: fs ⇒ eval_wh f ≠ wh_Diverge ∧
                                  dest_wh_Closure (eval_wh f) = NONE) ∧
    (∀m f. v ≠ wh_Constructor "Bind" [m; f]) ⇒
    next (v, stack) Err)
End

Definition next_action_def:
  next_action (wh, stack) =
    case some res. next (wh, stack) res of
    | SOME res => res
    | NONE => Div
End

Definition continue_def:
  continue [] k = INL T ∧
  continue (f::stack) k =
    case dest_wh_Closure (eval_wh f) of
    | NONE => INL F
    | SOME (n,e) => INR (eval_wh (bind n (Lit k) e), stack)
End

Definition interp'_def:
  interp' =
    io_unfold
      (λ(v,stack). case next_action (v,stack) of
                   | Ret => Ret' Termination
                   | Err => Ret' Error
                   | Div => Ret' SilentDivergence
                   | Act a new_stack =>
                       Vis' a (λy. (wh_Constructor "Ret" [Lit y], new_stack)))
End

Definition interp_def:
  interp v stack = interp' (v, stack)
End

Theorem interp_def:
  interp wh stack =
    case next_action (wh,stack) of
    | Ret => Ret Termination
    | Div => Ret SilentDivergence
    | Err => Ret Error
    | Act a new_stack =>
        Vis a (λy. interp (wh_Constructor "Ret" [Lit y]) new_stack)
Proof
  fs [Once interp_def,interp'_def]
  \\ once_rewrite_tac [io_unfold] \\ fs []
  \\ Cases_on ‘next_action (wh,stack)’ \\ fs []
  \\ fs [combinTheory.o_DEF,FUN_EQ_THM] \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [interp_def,interp'_def]
  \\ simp [Once io_unfold] \\ fs []
QED

Definition semantics_def:
  semantics e binds = interp (eval_wh e) binds
End


(* descriptive lemmas *)

Overload Ret = “λx. Cons "Ret" [x]”
Overload Act = “λx. Cons "Act" [x]”
Overload Bind = “λx y. Cons "Bind" [x;y]”

Theorem semantics_Ret:
  semantics (Ret x) [] = Ret Termination
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_cases]
QED

Theorem semantics_Ret_App:
  semantics (Ret x) (f::fs) = semantics (App f x) fs
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_cases]
  \\ Cases_on ‘dest_wh_Closure (eval_wh f)’ \\ fs []
  THEN1
    (fs [eval_wh_thm]
     \\ Cases_on ‘eval_wh f = wh_Diverge’ \\ fs []
     \\ simp [Once interp_def]
     \\ fs [next_action_def]
     \\ simp [Once next_cases])
  \\ rename [‘_ = SOME xx’] \\ PairCases_on ‘xx’ \\ fs []
  \\ fs [eval_wh_thm]
  \\ Cases_on ‘eval_wh f = wh_Diverge’ \\ fs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
QED

Theorem semantics_Bottom:
  semantics Bottom xs = Ret SilentDivergence
Proof
  fs [semantics_def,eval_wh_Bottom]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_cases]
QED

Theorem semantics_Bind:
  semantics (Bind x f) fs = semantics x (f::fs)
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_cases]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
QED

Theorem semantics_Act:
  semantics (Act x) fs =
    case eval x of
    | Atom a => Vis a (λy. semantics (Ret (Lit y)) fs)
    | _      => Ret Error
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_cases,eval_wh_Lit]
  \\ Cases_on ‘∃a. eval_wh x = wh_Atom a’ \\ fs []
  \\ fs [eval_def,Once v_unfold]
  \\ Cases_on ‘eval_wh x’ \\ fs []
QED


val _ = export_theory();
