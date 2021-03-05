(*
   This file proves that bisimilar (≃) expressions lead to equal (=)
   observational semantics:

       ∀x y. x ≃ y ⇒ semantics x [] = semantics y []

*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite io_treeTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_exp_relTheory pure_semanticsTheory
     pure_congruenceTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "pure_obs_sem_equal";

Triviality eval_wh_Cons:
  wh_Constructor n es = eval_wh x ∧ x ≃ y ⇒
  ∃es1. eval_wh y = wh_Constructor n es1 ∧ LIST_REL (≃) es es1
Proof
  fs [Once app_bisimilarity_iff]
  \\ Cases_on ‘eval_wh x’ \\ fs []
  \\ rw [] \\ gvs []
  \\ fs [LIST_REL_EL_EQN]
QED

Definition res_rel_def:
  res_rel Ret Ret = T ∧
  res_rel Div Div = T ∧
  res_rel Err Err = T ∧
  res_rel (Act a xs) (Act b ys) = (a = b ∧ LIST_REL (≃) xs ys) ∧
  res_rel _ _ = F
End

Theorem next_lemma[local]:
  ∀k x xs y ys.
    x ≃ y ∧ LIST_REL (≃) xs ys ⇒
    res_rel (next k (eval_wh x) xs) (next k (eval_wh y) ys)
Proof
  gen_tac \\ completeInduct_on ‘k’ \\ rw [] \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ once_rewrite_tac [next_def] \\ fs []
  \\ Cases_on ‘eval_wh x = wh_Diverge’
  THEN1 (imp_res_tac app_bisimilarity_diverge \\ fs [res_rel_def])
  \\ qpat_x_assum ‘x ≃ y’ mp_tac
  \\ simp [Once app_bisimilarity_iff] \\ strip_tac
  \\ Cases_on ‘eval_wh x’ \\ fs [res_rel_def]
  \\ Cases_on ‘s = "Act"’ \\ fs []
  THEN1
   (imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rw [] \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute,res_rel_def]
    \\ qpat_x_assum ‘_ ≃ _’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh h’
    \\ Cases_on ‘eval_wh h'’ \\ fs [res_rel_def])
  \\ Cases_on ‘s = "Bind"’ \\ fs []
  THEN1
   (imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rw [] \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute,res_rel_def])
  \\ reverse IF_CASES_TAC
  THEN1 (imp_res_tac LIST_REL_LENGTH \\ fs [] \\ fs [res_rel_def])
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ Cases_on ‘xs’ \\ gvs [res_rel_def]
  \\ assume_tac symmetric_app_bisimilarity
  \\ fs [symmetric_def]
  \\ ‘eval_wh h' = wh_Diverge ⇔ eval_wh y' = wh_Diverge’
        by metis_tac [app_bisimilarity_diverge]
  \\ fs [] \\ IF_CASES_TAC \\ fs [res_rel_def]
  \\ Cases_on ‘dest_wh_Closure (eval_wh h')’ \\ fs []
  THEN1
   (qsuff_tac ‘dest_wh_Closure (eval_wh y') = NONE’
    THEN1 (fs[res_rel_def])
    \\ qpat_x_assum ‘h' ≃ _’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ rw []
    \\ Cases_on ‘eval_wh h'’ \\ fs [])
  \\ rename [‘_ = SOME yy’] \\ PairCases_on ‘yy’
  \\ Cases_on ‘eval_wh h'’ \\ gvs []
  \\ rename [‘eval_wh h1 = wh_Closure s1 e1’]
  \\ rename [‘dest_wh_Closure (eval_wh h2)’]
  \\ ‘∃s2 e2. eval_wh h2 = wh_Closure s2 e2’ by
    (qpat_x_assum ‘h1 ≃ _’ mp_tac
     \\ simp [Once app_bisimilarity_iff] \\ rw [] \\ fs [])
  \\ fs [] \\ rw [res_rel_def]
  \\ first_x_assum irule \\ fs []
  \\ fs [app_bisimilarity_eq]
  \\ pop_assum kall_tac
  \\ drule_all eval_wh_Closure_closed \\ pop_assum mp_tac
  \\ drule_all eval_wh_Closure_closed
  \\ rpt (disch_then assume_tac)
  \\ reverse conj_tac
  THEN1 (rw [bind_def] \\ irule IMP_closed_subst \\ fs [])
  \\ ‘Lam s1 e1 ≃ Lam s2 e2’ by
    (‘h1 ≃ h2’ by fs [app_bisimilarity_eq]
     \\ pop_assum mp_tac
     \\ once_rewrite_tac [app_bisimilarity_iff]
     \\ fs [eval_wh_Lam])
  \\ ‘Lam s1 e1 ≅ Lam s2 e2’ by fs [app_bisimilarity_eq]
  \\ fs [exp_eq_Lam] \\ fs [bind1_def]
QED

Theorem symmetric_LIST_REL:
  ∀xs ys R. symmetric R ∧ LIST_REL R xs ys ⇒ LIST_REL R ys xs
Proof
  Induct \\ fs [PULL_EXISTS] \\ rw [symmetric_def]
QED

Theorem bisimilarity_IMP_semantics_eq:
  ∀x y. x ≃ y ⇒ semantics x [] = semantics y []
Proof
  qsuff_tac ‘∀x y xs ys. x ≃ y ∧ LIST_REL (≃) xs ys ⇒
                         semantics x xs = semantics y ys’
  THEN1 (rw [] \\ first_x_assum match_mp_tac)
  \\ fs [io_el_eqv] \\ fs [PULL_FORALL] \\ rpt gen_tac
  \\ EVERY (map qid_spec_tac [‘ys’,‘xs’,‘y’,‘x’])
  \\ completeInduct_on ‘LENGTH path’ \\ rw [] \\ fs [PULL_FORALL]
  \\ fs [semantics_def]
  \\ once_rewrite_tac [interp_def]
  \\ qsuff_tac ‘
    next_action (eval_wh x) xs = next_action (eval_wh y) ys ∨
    ∃a new1 new2.
      next_action (eval_wh x) xs = Act a new1 ∧
      next_action (eval_wh y) ys = Act a new2 ∧
      LIST_REL (≃) new1 new2’
  THEN1
   (strip_tac \\ fs []
    \\ Cases_on ‘path’ \\ fs [io_el_def]
    \\ ‘wh_Constructor "Ret" [Lit h] = eval_wh (Ret (Lit h))’ by fs [eval_wh_thm]
    \\ fs [] \\ first_x_assum irule \\ fs []
    \\ match_mp_tac reflexive_app_bisimilarity \\ fs [])
  \\ qsuff_tac ‘res_rel (next_action (eval_wh x) xs) (next_action (eval_wh y) ys)’
  THEN1
   (Cases_on ‘next_action (eval_wh x) xs’
    \\ Cases_on ‘next_action (eval_wh y) ys’
    \\ fs [res_rel_def])
  \\ qpat_x_assum ‘∀x. _’ kall_tac
  \\ fs [next_action_def]
  \\ rpt (DEEP_INTRO_TAC some_intro \\ fs []) \\ fs [] \\ reverse (rw [])
  \\ fs [res_rel_def]
  \\ drule_all next_lemma
  THEN1 (disch_then (qspec_then ‘x'’ mp_tac) \\ fs [])
  THEN1 (disch_then (qspec_then ‘x'’ mp_tac) \\ fs [])
  \\ dxrule next_less_eq
  \\ dxrule next_less_eq
  \\ disch_then (qspec_then ‘x'+x''’ assume_tac)
  \\ disch_then (qspec_then ‘x'+x''’ assume_tac) \\ fs []
QED

val _ = export_theory();
