
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

Definition next_def:
  next (k:num) v stack =
    case v of
    | wh_Constructor s es =>
       (if s = "Ret" ∧ LENGTH es = 1 then
          (case stack of
           | [] => Ret
           | (f::fs) =>
               if eval_wh f = wh_Diverge then Div else
                 case dest_wh_Closure (eval_wh f) of
                 | NONE => Err
                 | SOME (n,e) => if k = 0 then Div else
                                   next (k-1) (eval_wh (bind1 n (HD es) e)) fs)
        else if s = "Act" ∧ LENGTH es = 1 then
          (case eval_wh (HD es) of
           | wh_Atom a => Act a stack
           | _ => Err)
        else if s = "Bind" ∧ LENGTH es = 2 then
          (let m = EL 0 es in
           let f = EL 1 es in
             if k = 0 then Div else next (k-1) (eval_wh m) (f::stack))
        else Err)
    | wh_Diverge => Div
    | _ => Err
End

Definition next_action_def:
  next_action wh stack =
    case some k. next k wh stack ≠ Div of
    | NONE => Div
    | SOME k => next k wh stack
End

Definition interp'_def:
  interp' =
    io_unfold
      (λ(v,stack). case next_action v stack of
                   | Ret => Ret' Termination
                   | Err => Ret' Error
                   | Div => Ret' SilentDivergence
                   | Act a new_stack =>
                       Vis' a (λy. (wh_Constructor "Ret" [Lit y], new_stack)))
End

Definition interp:
  interp v stack = interp' (v, stack)
End

Theorem interp_def:
  interp wh stack =
    case next_action wh stack of
    | Ret => Ret Termination
    | Div => Ret SilentDivergence
    | Err => Ret Error
    | Act a new_stack =>
        Vis a (λy. interp (wh_Constructor "Ret" [Lit y]) new_stack)
Proof
  fs [Once interp,interp'_def]
  \\ once_rewrite_tac [io_unfold] \\ fs []
  \\ Cases_on ‘next_action wh stack’ \\ fs []
  \\ fs [combinTheory.o_DEF,FUN_EQ_THM] \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [interp,interp'_def]
  \\ simp [Once io_unfold] \\ fs []
QED

Definition semantics_def:
  semantics e binds = interp (eval_wh e) binds
End


(* basic lemmas *)

Theorem next_less_eq:
  ∀k1 x fs. next k1 x fs ≠ Div ⇒ ∀k2. k1 ≤ k2 ⇒ next k1 x fs = next k2 x fs
Proof
  ho_match_mp_tac next_ind \\ rw []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [next_def]
  \\ Cases_on ‘x’ \\ fs []
  \\ Cases_on ‘s = "Bind"’ THEN1 (fs [] \\ rw [])
  \\ Cases_on ‘s = "Act"’ THEN1 (fs [] \\ rw [])
  \\ Cases_on ‘s = "Ret"’ \\ fs [] \\ rw []
  \\ Cases_on ‘fs’ \\ fs []
  \\ fs [AllCaseEqs()]
  \\ Cases_on ‘dest_wh_Closure (eval_wh h)’ \\ fs []
  \\ PairCases_on ‘x’ \\ gvs []
QED

Theorem next_next:
  next k1 x fs ≠ Div ∧ next k2 x fs ≠ Div ⇒
  next k1 x fs = next k2 x fs
Proof
  metis_tac [LESS_EQ_CASES, next_less_eq]
QED

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
  \\ simp [Once next_def]
  \\ simp [Once next_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs []
QED

Theorem semantics_Ret_App:
  semantics (Ret x) (f::fs) = semantics (App f x) fs
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ once_rewrite_tac [interp_def]
  \\ rpt AP_THM_TAC \\ rpt AP_TERM_TAC
  \\ fs [next_action_def]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [next_def])) \\ fs []
  \\ Cases_on ‘eval_wh f = wh_Diverge’ \\ fs [eval_wh_thm]
  THEN1 (simp [Once next_def])
  \\ Cases_on ‘dest_wh_Closure (eval_wh f)’ \\ fs []
  THEN1
   (simp [Once next_def]
    \\ DEEP_INTRO_TAC some_intro \\ fs []
    \\ simp [Once next_def])
  \\ rename [‘_ = SOME xx’] \\ PairCases_on ‘xx’ \\ fs []
  \\ rpt (DEEP_INTRO_TAC some_intro \\ fs [])
  \\ reverse (rw [] \\ fs [AllCaseEqs()])
  THEN1 (qexists_tac ‘x'+1’ \\ fs [])
  \\ match_mp_tac next_next \\ gvs []
QED

Theorem semantics_Bottom:
  semantics Bottom xs = Ret SilentDivergence
Proof
  fs [semantics_def,eval_wh_thm]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_def]
QED

Theorem semantics_Bind:
  semantics (Bind x f) fs = semantics x (f::fs)
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ qsuff_tac ‘next_action (wh_Constructor "Bind" [x; f]) fs =
                next_action (eval_wh x) (f::fs)’
  THEN1 (rw [] \\ once_rewrite_tac [EQ_SYM_EQ] \\ simp [Once interp_def])
  \\ fs [next_action_def]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [next_def])) \\ fs []
  \\ rpt (DEEP_INTRO_TAC some_intro \\ fs [])
  \\ rw [] \\ fs [AllCaseEqs()]
  THEN1 (match_mp_tac next_next \\ gvs [])
  \\ qexists_tac ‘x'+1’ \\ gvs []
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
  \\ simp [Once next_def,CaseEq"wh"]
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ simp [Once next_def,CaseEq"wh"]
  \\ fs [eval_def]
  \\ once_rewrite_tac [v_unfold]
  \\ Cases_on ‘eval_wh x’ \\ fs []
QED

val _ = export_theory();
