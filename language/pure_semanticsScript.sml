
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory pure_evalTheory io_treeTheory;

val _ = new_theory "pure_semantics";

(*

TODO:
 - add Alloc[len,init], Update[loc,i,v], Deref[loc,i], Length[loc]

*)


(* definitions *)

Datatype:
  result = SilentDivergence
         | Termination
         | Error
End

Datatype:
  cont = Done        (* nothing left to do *)
       | BC exp cont (* RHS of Bind, rest *)
       | HC exp cont (* RHS of Handle, rest *)
End

Type state[pp] = “:(wh list) list”;

Datatype:
  next_res = Act 'e cont state | Ret | Div | Err
End

Definition get_atoms_def:
  get_atoms [] = SOME [] ∧
  get_atoms (wh_Atom a :: xs) = OPTION_MAP (λas. a::as) (get_atoms xs) ∧
  get_atoms _ = NONE
End

Definition with_atoms_def:
  with_atoms es f =
    let vs = MAP eval_wh es in
      if MEM wh_Error vs then Err else
      if MEM wh_Diverge vs then Div else
        case get_atoms vs of
        | SOME as => f as
        | NONE => Err
End

Definition with_atom_def:
  with_atom es f = with_atoms es (λvs. f (HD vs))
End

Definition with_atom2_def:
  with_atom2 es f = with_atoms es (λvs. f (EL 0 vs) (EL 1 vs))
End

Definition next_def:
  next (k:num) v stack (state:state) =
    case v of
    | wh_Constructor s es =>
       (if s = "Ret" ∧ LENGTH es = 1 then
          (case stack of
           | Done => Ret
           | BC f fs =>
              (if eval_wh f = wh_Diverge then Div else
                 case dest_wh_Closure (eval_wh f) of
                 | NONE => Err
                 | SOME (n,e) =>
                     if k = 0 then Div
                     else next (k-1) (eval_wh (bind n (HD es) e)) fs state)
           | HC f fs => if k = 0 then Div else next (k-1) v fs state)
        else if s = "Raise" ∧ LENGTH es = 1 then
          (case stack of
           | Done => Ret
           | BC f fs => if k = 0 then Div else next (k-1) v fs state
           | HC f fs =>
              (if eval_wh f = wh_Diverge then Div else
                 case dest_wh_Closure (eval_wh f) of
                 | NONE => Err
                 | SOME (n,e) =>
                    if k = 0 then Div
                    else next (k-1) (eval_wh (bind n (HD es) e)) fs state))
        else if s = "Act" ∧ LENGTH es = 1 then
          (with_atom es (λa.
             case a of
             | Msg channel content => Act (channel, content) stack state
             | _ => Err))
        else if s = "Bind" ∧ LENGTH es = 2 then
          (let m = EL 0 es in
           let f = EL 1 es in
             if k = 0 then Div else next (k-1) (eval_wh m) (BC f stack) state)
        else if s = "Handle" ∧ LENGTH es = 2 then
          (let m = EL 0 es in
           let f = EL 1 es in
             if k = 0 then Div else next (k-1) (eval_wh m) (HC f stack) state)
        else Err)
    | wh_Diverge => Div
    | _ => Err
End

Definition next_action_def:
  next_action wh stack state =
    case some k. next k wh stack state ≠ Div of
    | NONE => Div
    | SOME k => next k wh stack state
End

Definition interp'_def:
  interp' =
    io_unfold
      (λ(v,stack,state).
        case next_action v stack state of
        | Ret => Ret' Termination
        | Err => Ret' Error
        | Div => Ret' SilentDivergence
        | Act a new_stack new_state =>
            Vis' a (λy. (wh_Constructor "Ret" [Lit (Str y)],
                    new_stack, new_state)))
End

Definition interp:
  interp v stack state = interp' (v, stack, state)
End

Theorem interp_def:
  interp wh stack state =
    case next_action wh stack state of
    | Ret => Ret Termination
    | Div => Ret SilentDivergence
    | Err => Ret Error
    | Act a new_stack new_state =>
        Vis a (λy. interp (wh_Constructor "Ret" [Lit (Str y)]) new_stack new_state)
Proof
  fs [Once interp,interp'_def]
  \\ once_rewrite_tac [io_unfold] \\ fs []
  \\ Cases_on ‘next_action wh stack state’ \\ fs []
  \\ fs [combinTheory.o_DEF,FUN_EQ_THM] \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [interp,interp'_def]
  \\ simp [Once io_unfold] \\ fs []
QED

Definition semantics_def:
  semantics e stack state = interp (eval_wh e) stack state
End

Definition itree_of_def:
  itree_of e = semantics e Done []
End


(* basic lemmas *)

Theorem next_less_eq:
  ∀k1 x fs st. next k1 x fs st ≠ Div ⇒ ∀k2. k1 ≤ k2 ⇒ next k1 x fs st = next k2 x fs st
Proof
  ho_match_mp_tac next_ind \\ rw []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [next_def]
  \\ Cases_on ‘x’ \\ fs []
  \\ Cases_on ‘s = "Bind"’ THEN1 (fs [] \\ rw [])
  \\ Cases_on ‘s = "Act"’ THEN1 (fs [] \\ rw [])
  \\ Cases_on ‘s = "Raise"’
  THEN1
   (fs [] \\ rw [] \\ Cases_on ‘fs’ \\ fs []
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    \\ rw [] \\ fs [] \\ PairCases_on ‘x’ \\ gvs [] \\ rw [] \\ fs [])
  \\ Cases_on ‘s = "Ret"’
  THEN1
   (fs [] \\ rw [] \\ Cases_on ‘fs’ \\ fs []
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    \\ rw [] \\ fs [] \\ PairCases_on ‘x’ \\ gvs [] \\ rw [] \\ fs [])
  \\ rw [] \\ fs []
QED

Theorem next_next:
  next k1 x fs st ≠ Div ∧ next k2 x fs st ≠ Div ⇒
  next k1 x fs st = next k2 x fs st
Proof
  metis_tac [LESS_EQ_CASES, next_less_eq]
QED


(* descriptive lemmas *)

Overload Ret = “λx. Cons "Ret" [x]”
Overload Raise = “λx. Cons "Raise" [x]”
Overload Act = “λx. Cons "Act" [x]”
Overload Bind = “λx y. Cons "Bind" [x;y]”
Overload Handle = “λx y. Cons "Handle" [x;y]”

Theorem semantics_Ret:
  semantics (Ret x) Done s = Ret Termination
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_def]
  \\ simp [Once next_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs []
QED

Theorem semantics_Raise:
  semantics (Raise x) Done s = Ret Termination
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_def]
  \\ simp [Once next_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs []
QED

Theorem semantics_Ret_HC:
  semantics (Ret x) (HC f fs) s = semantics (Ret x) fs s
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ once_rewrite_tac [interp_def]
  \\ ntac 4 AP_THM_TAC \\ AP_TERM_TAC
  \\ simp [Once next_action_def]
  \\ once_rewrite_tac [next_def] \\ fs []
  \\ simp [Once next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ rw [] \\ rw [] \\ fs []
  \\ imp_res_tac next_next
  \\ qexists_tac ‘x'+1’ \\ fs []
QED

Theorem semantics_Raise_BC:
  semantics (Raise x) (BC f fs) s = semantics (Raise x) fs s
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ once_rewrite_tac [interp_def]
  \\ ntac 4 AP_THM_TAC \\ AP_TERM_TAC
  \\ simp [Once next_action_def]
  \\ once_rewrite_tac [next_def] \\ fs []
  \\ simp [Once next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ rw [] \\ rw [] \\ fs []
  \\ imp_res_tac next_next
  \\ qexists_tac ‘x'+1’ \\ fs []
QED

Theorem semantics_Ret_BC:
  semantics (Ret x) (BC f fs) s = semantics (App f x) fs s
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
  semantics Bottom xs s = Ret SilentDivergence
Proof
  fs [semantics_def,eval_wh_thm]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_def]
QED

Theorem semantics_Bind:
  semantics (Bind x f) fs s = semantics x (BC f fs) s
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ qsuff_tac ‘next_action (wh_Constructor "Bind" [x; f]) fs s =
                next_action (eval_wh x) (BC f fs) s’
  THEN1 (rw [] \\ once_rewrite_tac [EQ_SYM_EQ] \\ simp [Once interp_def])
  \\ fs [next_action_def]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [next_def])) \\ fs []
  \\ rpt (DEEP_INTRO_TAC some_intro \\ fs [])
  \\ rw [] \\ fs [AllCaseEqs()]
  THEN1 (match_mp_tac next_next \\ gvs [])
  \\ qexists_tac ‘x'+1’ \\ gvs []
QED

Theorem semantics_Handle:
  semantics (Handle x f) fs s = semantics x (HC f fs) s
Proof
  fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ qsuff_tac ‘next_action (wh_Constructor "Handle" [x; f]) fs s =
                next_action (eval_wh x) (HC f fs) s’
  THEN1 (rw [] \\ once_rewrite_tac [EQ_SYM_EQ] \\ simp [Once interp_def])
  \\ fs [next_action_def]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [next_def])) \\ fs []
  \\ rpt (DEEP_INTRO_TAC some_intro \\ fs [])
  \\ rw [] \\ fs [AllCaseEqs()]
  THEN1 (match_mp_tac next_next \\ gvs [])
  \\ qexists_tac ‘x'+1’ \\ gvs []
QED

Theorem semantics_Act:
  eval_wh x = wh_Atom (Msg c t) ⇒
  semantics (Act x) fs s = Vis (c,t) (λy. semantics (Ret (Lit (Str y))) fs s)
Proof
  strip_tac
  \\ fs [semantics_def,eval_wh_Cons]
  \\ simp [Once interp_def]
  \\ fs [next_action_def]
  \\ simp [Once next_def,CaseEq"wh",with_atom_def,with_atoms_def,get_atoms_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ simp [Once next_def,CaseEq"wh",with_atom_def,with_atoms_def,get_atoms_def]
QED

val _ = export_theory();
