(*
  Adding and removing clock-ticks in pureLang.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory dep_rewrite
     relationTheory;
open pure_miscTheory pure_evalTheory pure_expTheory pure_exp_relTheory
     pure_congruenceTheory;

val _ = new_theory "pure_ticksProof";

Overload Tick = “λx: pure_exp$exp. Letrec [] x”;

Inductive TickRel:
[~Var:]
  (∀v.
     TickRel (Var v) (Tick (Var v))) ∧
[~Prim:]
  (∀op xs ys.
     LIST_REL TickRel xs ys ⇒
       TickRel (Prim op xs) (Tick (Prim op ys))) ∧
[~App:]
  (∀f x g y.
     TickRel x y ∧
     TickRel f g ⇒
       TickRel (App f x) (Tick (App g y))) ∧
[~Lam:]
  (∀s x y.
     TickRel x y ⇒
       TickRel (Lam s x) (Tick (Lam s y))) ∧
[~Letrec:]
  (∀f x g y.
     LIST_REL (λ(f, x) (g, y). f = g ∧ TickRel x y) f g ∧
     TickRel x y ⇒
       TickRel (Letrec f x) (Tick (Letrec g y)))
End

Definition TickIntro_def:
  TickIntro = RTC TickRel
End

Theorem Tick_exp_eq:
  Tick x ≅ x
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [eval_wh_thm, subst_def, subst_funs_def, bind_def, FUPDATE_LIST_THM]
QED

Theorem TickIntro_exp_eq:
  ∀x y. TickIntro x y ⇒ x ≅ y
Proof
  simp [TickIntro_def]
  \\ ho_match_mp_tac RTC_ind
  \\ simp [exp_eq_refl, GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  \\ ho_match_mp_tac TickRel_ind \\ rw []
  >- (
    irule exp_eq_trans
    \\ simp [exp_eq_sym]
    \\ irule_at Any Tick_exp_eq
    \\ simp [])
  >-(
    irule exp_eq_trans
    \\ simp [exp_eq_sym]
    \\ irule_at Any Tick_exp_eq
    \\ irule exp_eq_trans
    \\ first_assum (irule_at Any)
    \\ irule exp_eq_trans
    \\ irule_at Any Tick_exp_eq
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Tick_exp_eq
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_Prim_cong
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ rw []
    \\ first_assum (irule_at Any)
    \\ simp [exp_eq_refl])
  >- (
    irule exp_eq_trans
    \\ simp [exp_eq_sym]
    \\ irule_at Any Tick_exp_eq
    \\ irule exp_eq_trans
    \\ first_assum (irule_at Any)
    \\ irule exp_eq_trans
    \\ irule_at Any Tick_exp_eq
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Tick_exp_eq
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_App_cong
    \\ first_x_assum (irule_at Any)
    \\ first_x_assum (irule_at Any)
    \\ simp [exp_eq_refl])
  >- (
    irule exp_eq_trans
    \\ simp [exp_eq_sym]
    \\ irule_at Any Tick_exp_eq
    \\ irule exp_eq_trans
    \\ first_assum (irule_at Any)
    \\ irule exp_eq_trans
    \\ irule_at Any Tick_exp_eq
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Tick_exp_eq
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_Lam_cong
    \\ first_x_assum (irule_at Any)
    \\ simp [exp_eq_refl])
  >- (
    irule exp_eq_trans
    \\ simp [exp_eq_sym]
    \\ irule_at Any Tick_exp_eq
    \\ irule exp_eq_trans
    \\ first_assum (irule_at Any)
    \\ irule exp_eq_trans
    \\ irule_at Any Tick_exp_eq
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Tick_exp_eq
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_Letrec_cong
    \\ irule_at Any LIST_EQ
    \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY, SF CONJ_ss]
    \\ first_x_assum (irule_at Any)
    \\ simp [exp_eq_refl])
QED

Theorem TickIntro_freevars:
  ∀x y. TickIntro x y ⇒ freevars x = freevars y
Proof
  simp [TickIntro_def]
  \\ ho_match_mp_tac RTC_ind
  \\ simp [GSYM PULL_FORALL, GSYM AND_IMP_INTRO]
  \\ ho_match_mp_tac TickRel_ind
  \\ rw [] \\ gs []
  >- (
    pop_assum (SUBST1_TAC o SYM)
    \\ simp [EXTENSION, MEM_EL, EL_MAP, SF CONJ_ss]
    \\ rw [EQ_IMP_THM] \\ gvs [LIST_REL_EL_EQN]
    \\ metis_tac [])
  >- (
    metis_tac [])
  >- (
    metis_tac [])
  >- (
    pop_assum (SUBST1_TAC o SYM)
    \\ simp [EXTENSION, MEM_EL, EL_MAP, SF CONJ_ss]
    \\ rw [EQ_IMP_THM] \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY]
    \\ metis_tac [])
QED

Theorem TickIntro_closed:
  TickIntro x y ⇒ closed x = closed y
Proof
  rw [closed_def]
  \\ drule TickIntro_freevars \\ rw []
QED

Theorem TickIntro_app_bisimilarity:
  TickIntro x y ∧ closed x ⇒ x ≃ y
Proof
  strip_tac
  \\ drule_then assume_tac TickIntro_closed
  \\ gs [app_bisimilarity_eq]
  \\ irule TickIntro_exp_eq
  \\ gs []
QED

val _ = export_theory ();

