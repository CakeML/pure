(*
   This file proves that bisimilar (≃) expressions lead to equal (=)
   observational semantics:

       ∀x y. x ≃ y ⇒ semantics x Done [] = semantics y Done []

*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite io_treeTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_exp_relTheory pure_semanticsTheory
     pure_congruenceTheory;

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

Definition cont_rel_def[simp]:
  cont_rel Done Done = T ∧
  cont_rel (BC f fs) (BC g gs) = (f ≃ g ∧ cont_rel fs gs) ∧
  cont_rel (HC f fs) (HC g gs) = (f ≃ g ∧ cont_rel fs gs) ∧
  cont_rel _ _ = F
End

Definition res_rel_def:
  res_rel Ret Ret = T ∧
  res_rel Div Div = T ∧
  res_rel Err Err = T ∧
  res_rel (Act a xs st) (Act b ys st') =
    (a = b ∧ cont_rel xs ys ∧ LIST_REL (LIST_REL (≃)) st st') ∧
  res_rel _ _ = F
End

Theorem next_lemma[local]:
  ∀k x xs y ys st st'.
    x ≃ y ∧ cont_rel xs ys ∧ LIST_REL (LIST_REL (≃)) st st' ⇒
    res_rel (next k (eval_wh x) xs st) (next k (eval_wh y) ys st')
Proof
  gen_tac \\ completeInduct_on ‘k’ \\ rw [] \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ once_rewrite_tac [next_def] \\ fs []
  \\ Cases_on ‘eval_wh x = wh_Diverge’
  THEN1 (imp_res_tac app_bisimilarity_diverge \\ fs [res_rel_def])
  \\ qpat_x_assum ‘x ≃ y’ mp_tac
  \\ simp [Once app_bisimilarity_iff] \\ strip_tac
  \\ Cases_on ‘eval_wh x’ \\ fs [res_rel_def]
  \\ Cases_on ‘s = "Act"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rw [] \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute,res_rel_def]
    \\ fs [with_atom_def,with_atoms_def]
    \\ qpat_x_assum ‘_ ≃ _’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ fs [with_atom_def,with_atoms_def]
    \\ Cases_on ‘eval_wh h’
    \\ Cases_on ‘eval_wh h'’ \\ fs [res_rel_def,get_atoms_def]
    \\ gvs [] \\ Cases_on ‘l’ \\ fs [res_rel_def])
  \\ Cases_on ‘s = "Bind"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_rel_def]
    \\ first_x_assum irule \\ fs [])
  \\ Cases_on ‘s = "Handle"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_rel_def]
    \\ first_x_assum irule \\ fs [])
  \\ Cases_on ‘s = "Ret"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [res_rel_def]
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_rel_def]
    \\ reverse (Cases_on ‘xs’) \\ gvs []
    THEN1
     (Cases_on ‘ys’ \\ gvs []
      \\ rw [] \\ fs [res_rel_def]
      \\ first_x_assum (qspecl_then [‘k-1’,‘x’] mp_tac)
      \\ gvs [] \\ ‘x ≃ y’ by simp [Once app_bisimilarity_iff]
      \\ disch_then drule_all \\ fs [])
    \\ Cases_on ‘ys’ \\ gvs [res_rel_def]
    \\ fs [apply_closure_def]
    \\ assume_tac symmetric_app_bisimilarity
    \\ fs [symmetric_def]
    \\ ‘eval_wh e = wh_Diverge ⇔ eval_wh e' = wh_Diverge’
      by metis_tac [app_bisimilarity_diverge]
    \\ fs [] \\ IF_CASES_TAC \\ fs [res_rel_def]
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    THEN1
     (qsuff_tac ‘dest_wh_Closure (eval_wh e') = NONE’
      THEN1 (fs[res_rel_def])
      \\ qpat_x_assum ‘e ≃ _’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw []
      \\ Cases_on ‘eval_wh e’ \\ fs [])
    \\ rename [‘_ = SOME yy’] \\ PairCases_on ‘yy’ \\ gvs []
    \\ Cases_on ‘eval_wh e’ \\ gvs []
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
    \\ fs [exp_eq_Lam] \\ fs [bind1_def])
  \\ Cases_on ‘s = "Raise"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [res_rel_def]
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_rel_def]
    \\ Cases_on ‘xs’ \\ gvs []
    THEN1 (Cases_on ‘ys’ \\ fs [res_rel_def])
    THEN1
     (Cases_on ‘ys’ \\ gvs []
      \\ rw [] \\ fs [res_rel_def]
      \\ first_x_assum (qspecl_then [‘k-1’,‘x’] mp_tac)
      \\ gvs [] \\ ‘x ≃ y’ by simp [Once app_bisimilarity_iff]
      \\ disch_then drule_all \\ fs [])
    \\ Cases_on ‘ys’ \\ gvs [res_rel_def]
    \\ fs [apply_closure_def]
    \\ assume_tac symmetric_app_bisimilarity
    \\ fs [symmetric_def]
    \\ ‘eval_wh e = wh_Diverge ⇔ eval_wh e' = wh_Diverge’
      by metis_tac [app_bisimilarity_diverge]
    \\ fs [] \\ IF_CASES_TAC \\ fs [res_rel_def]
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    THEN1
     (qsuff_tac ‘dest_wh_Closure (eval_wh e') = NONE’
      THEN1 (fs[res_rel_def])
      \\ qpat_x_assum ‘e ≃ _’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw []
      \\ Cases_on ‘eval_wh e’ \\ fs [])
    \\ rename [‘_ = SOME yy’] \\ PairCases_on ‘yy’ \\ gvs []
    \\ Cases_on ‘eval_wh e’ \\ gvs []
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
    \\ fs [exp_eq_Lam] \\ fs [bind1_def])
  \\ Cases_on ‘s = "Length"’
  THEN1
   (pop_assum mp_tac \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ rpt strip_tac \\ gvs [res_rel_def]
    \\ rename [‘e ≃ e'’]
    \\ gvs [res_rel_def,with_atom_def,with_atoms_def]
    \\ qpat_x_assum ‘_ ≃ _’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e’
    \\ Cases_on ‘eval_wh e'’ \\ fs [res_rel_def,get_atoms_def]
    \\ gvs [] \\ Cases_on ‘l’ \\ fs [res_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ rw [] \\ fs [res_rel_def]
    \\ gvs [GSYM NOT_LESS]
    \\ ‘LENGTH (EL n st) = LENGTH (EL n st')’ by fs [LIST_REL_EL_EQN]
    \\ gvs [] \\ qpat_abbrev_tac ‘i = Int _’
    \\ first_x_assum (qspecl_then [‘k-1’,‘Cons "Ret" [Lit i]’,‘xs’,
                                         ‘Cons "Ret" [Lit i]’,‘ys’] mp_tac)
    \\ gvs [pure_evalTheory.eval_wh_Cons]
    \\ disch_then irule \\ fs []
    \\ irule reflexive_app_bisimilarity \\ fs [])
  \\ Cases_on ‘s = "Update"’
  THEN1
   (pop_assum mp_tac \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ rpt strip_tac \\ gvs [res_rel_def]
    \\ gvs [res_rel_def,with_atom2_def,with_atoms_def]
    \\ rename [‘e1 ≃ e1'’] \\ qpat_x_assum ‘_ ≃ _’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ rename [‘e2 ≃ e2'’] \\ qpat_x_assum ‘_ ≃ _’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e1’ \\ Cases_on ‘eval_wh e1'’ \\ fs [res_rel_def,get_atoms_def]
    \\ Cases_on ‘eval_wh e2’ \\ Cases_on ‘eval_wh e2'’ \\ fs [res_rel_def,get_atoms_def]
    \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_rel_def]
    \\ TOP_CASE_TAC \\ gvs [res_rel_def]
    \\ TOP_CASE_TAC \\ gvs [res_rel_def]
    \\ Cases_on ‘k=0’ \\ gvs [res_rel_def]
    \\ ‘LENGTH (EL n st) = LENGTH (EL n st')’ by fs [LIST_REL_EL_EQN] \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_rel_def]
    \\ first_assum (qspecl_then [‘k-1’,‘Cons "Raise" [Cons "Subscript" []]’,‘xs’,
                                 ‘Cons "Raise" [Cons "Subscript" []]’,‘ys’,
                                 ‘st’,‘st'’] mp_tac)
    \\ TRY (impl_tac THEN1 (fs [] \\ irule reflexive_app_bisimilarity \\ fs []))
    \\ rw [] \\ gvs [pure_evalTheory.eval_wh_Cons]
    \\ rename [‘res_rel (_ (LUPDATE (LUPDATE y1 (Num i) (EL n st)) n st))
                        (_ (LUPDATE (LUPDATE y2 (Num i) (EL n st')) n st'))’]
    \\ first_assum (qspecl_then [‘k-1’,‘Cons "Ret" [Cons "" []]’,‘xs’,
                                 ‘Cons "Ret" [Cons "" []]’,‘ys’,
                                 ‘(LUPDATE (LUPDATE y1 (Num i) (EL n st)) n st)’,
                                 ‘(LUPDATE (LUPDATE y2 (Num i) (EL n st')) n st')’] mp_tac)
    \\ reverse impl_tac THEN1 fs [pure_evalTheory.eval_wh_Cons]
    \\ rw [] THEN1 (irule reflexive_app_bisimilarity \\ fs [])
    \\ irule EVERY2_LUPDATE_same \\ gvs []
    \\ irule EVERY2_LUPDATE_same \\ gvs []
    \\ fs [LIST_REL_EL_EQN])
  \\ Cases_on ‘s = "Deref"’
  THEN1
   (pop_assum mp_tac \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ rpt strip_tac \\ gvs [res_rel_def]
    \\ gvs [res_rel_def,with_atom2_def,with_atoms_def]
    \\ rename [‘e1 ≃ e1'’] \\ qpat_x_assum ‘_ ≃ _’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ rename [‘e2 ≃ e2'’] \\ qpat_x_assum ‘_ ≃ _’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e1’ \\ Cases_on ‘eval_wh e1'’ \\ fs [res_rel_def,get_atoms_def]
    \\ Cases_on ‘eval_wh e2’ \\ Cases_on ‘eval_wh e2'’ \\ fs [res_rel_def,get_atoms_def]
    \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_rel_def]
    \\ TOP_CASE_TAC \\ gvs [res_rel_def]
    \\ TOP_CASE_TAC \\ gvs [res_rel_def]
    \\ Cases_on ‘k=0’ \\ gvs [res_rel_def]
    \\ ‘LENGTH (EL n st) = LENGTH (EL n st')’ by fs [LIST_REL_EL_EQN] \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_rel_def]
    \\ first_assum (qspecl_then [‘k-1’,‘Cons "Raise" [Cons "Subscript" []]’,‘xs’,
                                 ‘Cons "Raise" [Cons "Subscript" []]’,‘ys’,
                                 ‘st’,‘st'’] mp_tac)
    \\ TRY (impl_tac THEN1 (fs [] \\ irule reflexive_app_bisimilarity \\ fs []))
    \\ rw [] \\ gvs [pure_evalTheory.eval_wh_Cons]
    \\ first_assum (qspecl_then [‘k-1’,‘Cons "Ret" [EL (Num i) (EL n st)]’,‘xs’,
                                 ‘Cons "Ret" [EL (Num i) (EL n st')]’,
                                 ‘ys’,‘st’,‘st'’] mp_tac)
    \\ reverse impl_tac THEN1 fs [pure_evalTheory.eval_wh_Cons]
    \\ rw [] \\ fs [app_bisimilarity_eq]
    \\ ‘Num i < LENGTH (EL n st')’ by intLib.COOPER_TAC
    \\ fs [LIST_REL_EL_EQN]
    \\ irule exp_eq_Prim_cong \\ gvs [])
  \\ Cases_on ‘s = "Alloc"’
  THEN1
   (pop_assum mp_tac \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ rpt strip_tac \\ gvs [res_rel_def]
    \\ rename [‘e ≃ e'’]
    \\ gvs [res_rel_def,with_atom_def,with_atoms_def]
    \\ qpat_x_assum ‘_ ≃ _’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e’
    \\ Cases_on ‘eval_wh e'’ \\ fs [res_rel_def,get_atoms_def]
    \\ gvs [] \\ Cases_on ‘l’ \\ fs [res_rel_def]
    \\ IF_CASES_TAC \\ fs [res_rel_def]
    \\ gvs [] \\ qpat_abbrev_tac ‘n = if i < 0 then _ else _’
    \\ first_x_assum (qspecl_then [‘k-1’,‘Cons "Ret" [Lit (Loc (LENGTH st'))]’,‘xs’,
                                         ‘Cons "Ret" [Lit (Loc (LENGTH st'))]’,‘ys’] mp_tac)
    \\ gvs [pure_evalTheory.eval_wh_Cons]
    \\ disch_then irule \\ fs []
    \\ fs [LIST_REL_EL_EQN,EL_REPLICATE]
    \\ irule reflexive_app_bisimilarity \\ fs [])
  \\ fs [res_rel_def]
QED

Theorem symmetric_LIST_REL:
  ∀xs ys R. symmetric R ∧ LIST_REL R xs ys ⇒ LIST_REL R ys xs
Proof
  Induct \\ fs [PULL_EXISTS] \\ rw [symmetric_def]
QED

Theorem bisimilarity_IMP_semantics_eq:
  ∀x y. x ≃ y ⇒ semantics x Done [] = semantics y Done []
Proof
  qsuff_tac ‘∀x y xs ys st st'.
    x ≃ y ∧ cont_rel xs ys ∧ LIST_REL (LIST_REL (≃)) st st' ⇒
    semantics x xs st = semantics y ys st'’
  THEN1 (rw [] \\ first_x_assum match_mp_tac)
  \\ fs [io_el_eqv] \\ fs [PULL_FORALL] \\ rpt gen_tac
  \\ EVERY (map qid_spec_tac [‘st'’,‘st’,‘ys’,‘xs’,‘y’,‘x’])
  \\ completeInduct_on ‘LENGTH path’ \\ rw [] \\ fs [PULL_FORALL]
  \\ fs [semantics_def]
  \\ once_rewrite_tac [interp_def]
  \\ qsuff_tac ‘
    next_action (eval_wh x) xs st = next_action (eval_wh y) ys st' ∨
    ∃a new1 new2 s1 s2.
      next_action (eval_wh x) xs st = Act a new1 s1 ∧
      next_action (eval_wh y) ys st' = Act a new2 s2 ∧
      cont_rel new1 new2 ∧ LIST_REL (LIST_REL (≃)) s1 s2’
  THEN1
   (strip_tac \\ fs []
    \\ Cases_on ‘path’ \\ fs [io_el_def]
    \\ ‘wh_Constructor "Ret" [Lit (Str h)] = eval_wh (Ret (Lit (Str h)))’ by fs [eval_wh_thm]
    \\ fs [] \\ first_x_assum irule \\ fs []
    \\ match_mp_tac reflexive_app_bisimilarity \\ fs [])
  \\ qsuff_tac ‘res_rel (next_action (eval_wh x) xs st) (next_action (eval_wh y) ys st')’
  THEN1
   (Cases_on ‘next_action (eval_wh x) xs st’
    \\ Cases_on ‘next_action (eval_wh y) ys st'’
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
