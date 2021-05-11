(*
  This stage removes all suspended ticks introduced by thunk_subst_unthunk,
  and any other stage that has tampered with thunks.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     thunkLang_primitivesTheory dep_rewrite;
open pure_miscTheory;

val _ = new_theory "thunk_subst_untickProof";

val _ = numLib.prefer_num ();

Inductive exp_rel:
[~Var:]
  (∀n.
     exp_rel (Var n) (Var n)) ∧
[~Value:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Value v) (Value w)) ∧
[~Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys)) ∧
[~App:]
  (∀f x g y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f x) (App g y)) ∧
[~Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y)) ∧
[~Letrec:]
  (∀f g x y.
     LIST_REL (λ(f,x) (g,y). f = g ∧ exp_rel x y) f g ∧
     exp_rel x y ⇒
     exp_rel (Letrec f x) (Letrec g y)) ∧
[~Let:]
  (∀s x1 y1 x2 y2.
     exp_rel x1 y1 ∧
     exp_rel x2 y2 ⇒
       exp_rel (Let s x1 x2) (Let s y1 y2)) ∧
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     LIST_REL exp_rel [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[~Delay:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Delay x) (Delay y)) ∧
[~Box:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Box x) (Box y)) ∧
[~Force:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Force x) (Force y)) ∧
[~MkTick:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (MkTick x) y) ∧
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ⇒
       v_rel (Closure s x) (Closure s y)) ∧
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(f,x) (g,y). f = g ∧ exp_rel x y) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Thunk_INL:]
  (∀x y.
     exp_rel x y ⇒
       v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_Thunk_INR:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INL v)) (Thunk (INL w))) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x)) ∧
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) w)
End

Theorem SUM_REL_def[simp] = quotient_sumTheory.SUM_REL_def;

Theorem exp_rel_subst:
  ∀x y vs ws.
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    exp_rel x y ⇒
      exp_rel (subst vs x) (subst ws y)
Proof
  cheat (* Induction from thunk_subst_unthunk *)
  (*
  >- ((* Var *)
    simp [subst_def]
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) n) (ALOOKUP (REVERSE ws) n)’
      by cheat (* TODO LIST_REL_OPTREL theorem from unthunk *)
    \\ gs [OPTREL_def, exp_rel_Var]
    \\ irule exp_rel_Value \\ simp [])
  >- ((* Value *)
    simp [subst_def, exp_rel_Value])
  >- ((* Prim *)
    simp [subst_def]
    \\ irule exp_rel_Prim
    \\ gs [EVERY2_MAP]
    \\ irule LIST_REL_mono
    \\ last_assum (irule_at Any)
    \\ simp [])
  >- ((* App *)
    simp [subst_def]
    \\ irule exp_rel_App
    \\ gs [])
  >- ((* Lam *)
    simp [subst_def]
    \\ irule exp_rel_Lam
    \\ simp []
  *)
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ⇒
      ∃j. ($= +++ v_rel) (eval_to k x) (eval_to (k + j) y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def])
  >- ((* Var *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def])
  >- ((* App *)
    rename1 ‘App x1 y1’
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ rw [eval_to_def]
    \\ first_x_assum (drule_then (qx_choose_then ‘j2’ assume_tac))
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ cheat)
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ rw [Once exp_rel_cases])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (drule_then (qx_choose_then ‘j2’ assume_tac))
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ rename1 ‘exp_rel x1 y1’
    \\ rename1 ‘exp_rel x2 y2’
    \\ cheat)
  >- ((* Let SOME *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ rename1 ‘exp_rel x1 y1’
    \\ rename1 ‘exp_rel x2 y2’
    \\ cheat)
  >- ((* If *)
    rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ rename1 ‘exp_rel z1 z2’
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ cheat)
  >- ((* Letrec *)
    cheat)
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def, Once exp_rel_cases])
  >- ((* Box *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def, Once exp_rel_cases]
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ rename1 ‘exp_rel x y’
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j1 + k) y’ \\ gs []
    \\ rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x y’
    \\ simp [Once eval_to_def]
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to k x’ \\ gs []
    >- (
      simp [Once eval_to_def]
      \\ qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (k + j1) y’ \\ gs [])
    \\ cheat)
  >- ((* MkTick *)
    rw [Once exp_rel_cases]
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ simp [eval_to_def]
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j1 + k) y’ \\ gs []
    \\ rw [Once exp_rel_cases])
  >- ((* Prim *)
    cheat)
QED

Theorem exp_rel_eval:
  exp_rel x y ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  rw [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ drule_then
      (qspec_then ‘MAX k j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
    \\ ‘eval_to k x = eval_to (MAX k j) x’
      by (rw [Once EQ_SYM_EQ]
          \\ irule eval_to_subst_mono
          \\ simp [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to j y = eval_to (MAX k j + m) y’
      by (rw [Once EQ_SYM_EQ]
          \\ irule eval_to_subst_mono
          \\ simp [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ drule_then
      (qspec_then ‘j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
    \\ Cases_on ‘eval_to (m + j) y’ \\ gvs []
    \\ Cases_on ‘∃err. eval_to j y = INL err’ \\ gvs []
    >- (
      Cases_on ‘err’ \\ gs []
      \\ ‘eval_to j y ≠ INL Diverge’ by gs []
      \\ drule_then (qspec_then ‘j + m’ assume_tac) eval_to_subst_mono \\ gs [])
    \\ Cases_on ‘eval_to j y’ \\ gs []
    \\ ‘eval_to j y ≠ INL Diverge’ by gs []
    \\ drule_then (qspec_then ‘j + m’ assume_tac) eval_to_subst_mono \\ gs [])
  \\ rename1 ‘_ (eval_to k x)’
  \\ drule_then (qspec_then ‘k’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
  \\ Cases_on ‘eval_to (m + k) y’ \\ gvs []
QED

val _ = export_theory ();

