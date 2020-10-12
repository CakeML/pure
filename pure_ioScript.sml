
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory pure_langTheory io_treeTheory;

val _ = new_theory "pure_io";

Datatype:
  result = SilentDivergence
         | Termination
         | Error
End

Datatype:
  next_res = Act 'e ((('a,'b) v) list) | Ret | Div | Err
End

Inductive next:
  (∀e stack.
    next (Constructor "Act" [e], stack) (Act e stack))
  ∧
  (∀m f stack res.
    next (m, f::stack) res ⇒
    next (Constructor "Bind" [m; f], stack) res)
  ∧
  (∀stack.
    next (Diverge, stack) Div)
  ∧
  (∀v.
    next (Constructor "Ret" [v], []) Ret)
  ∧
  (∀v f n c e x stack res.
    dest_Closure f = SOME (n,e) ∧ eval c x = v ∧
    next (eval c (bind [(n,x)] e), stack) res ⇒
    next (Constructor "Ret" [v], f::stack) res)
  ∧
  (∀v stack.
    (v ≠ Diverge) ∧
    (∃e. v ≠ Constructor "Act" [e]) ∧
    (∃e. v ≠ Constructor "Ret" [e]) ∧
    (∃m f. v ≠ Constructor "Bind" [m; f]) ⇒
    next (v, stack) Err)
End

Definition next_action_def:
  next_action (v, stack) =
    case some res. next (v, stack) res of
    | SOME res => res
    | NONE => Div
End

Definition continue_def:
  continue c [] k = INL T ∧
  continue c (f::stack) k =
    case dest_Closure f of
    | NONE => INL F
    | SOME (n,e) => INR (eval c (bind [(n,Lit k)] e), stack)
End

Definition interp'_def:
  interp' c =
    io_unfold
      (λi. case i of
           | INL T => Ret' Termination
           | INL F => Ret' Error
           | INR (v, stack) =>
             case next_action (v,stack) of
             | Ret => Ret' Termination
             | Err => Ret' Error
             | Div => Ret' SilentDivergence
             | Act a new_stack => Vis' a (continue c new_stack))
End

Definition interp_def:
  interp c v stack = interp' c (INR (v, stack))
End

Theorem interp_def:
  interp c v stack =
    case next_action (v,stack) of
    | Ret => Ret Termination
    | Div => Ret SilentDivergence
    | Err => Ret Error
    | Act a new_stack =>
        Vis a (λk. case continue c new_stack k of
                   | INL b => Ret (if b then Termination else Error)
                   | INR (v,stack) => interp c v stack)
Proof
  fs [Once interp_def,interp'_def]
  \\ once_rewrite_tac [io_unfold] \\ fs []
  \\ Cases_on ‘next_action (v,stack)’ \\ fs []
  \\ fs [combinTheory.o_DEF,FUN_EQ_THM] \\ rw []
  \\ Cases_on ‘continue c l k’ \\ fs []
  THEN1
   (once_rewrite_tac [io_unfold] \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  \\ CASE_TAC \\ fs []
  \\ fs [Once interp_def,interp'_def]
QED

Definition semantics_def:
  semantics c e binds = interp c (eval c e) (MAP (eval c) binds)
End

(* TODO: derive nice equations for reasoning about semantics *)

val _ = export_theory();
