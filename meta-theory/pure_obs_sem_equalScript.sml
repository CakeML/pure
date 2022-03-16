(*
   This file proves that bisimilar (≃) expressions lead to equal (=)
   observational semantics:

       ∀x y. x ≃ y ⇒ semantics x Done [] = semantics y Done []

*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite io_treeTheory intLib;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_exp_relTheory pure_semanticsTheory
     pure_congruenceTheory;

val _ = new_theory "pure_obs_sem_equal";

Triviality eval_wh_Cons:
  wh_Constructor n es = eval_wh x ∧ (x ≃ y) b ⇒
  ∃es1. eval_wh y = wh_Constructor n es1 ∧ LIST_REL (λx y. (x ≃ y) b) es es1
Proof
  fs [Once app_bisimilarity_iff]
  \\ Cases_on ‘eval_wh x’ \\ fs []
  \\ rw [] \\ gvs []
  \\ fs [LIST_REL_EL_EQN]
QED

Definition cont_REL_def[simp]:
  (cont_REL R Done Done = T) ∧
  (cont_REL R (BC e1 c1) (BC e2 c2) = (R e1 e2 ∧ cont_REL R c1 c2)) ∧
  (cont_REL R (HC e1 c1) (HC e2 c2) = (R e1 e2 ∧ cont_REL R c1 c2)) ∧
  (cont_REL _ _ _ = F)
End

Overload "cont_rel" = “cont_REL (λf g. ((f ≃ g) T))”

Definition res_REL_def:
  res_REL R b Ret Ret = T ∧
  res_REL R b Div Div = T ∧
  res_REL R b Err Err = T ∧
  res_REL R b Div Err = b ∧
  res_REL R b Err Div = b ∧
  res_REL R _ (Act a xs st) (Act b ys st') =
    (a = b ∧ cont_REL R xs ys ∧ LIST_REL (LIST_REL R) st st') ∧
  res_REL R _ _ _ = F
End

Overload "res_rel" = “res_REL (λf g. ((f ≃ g) T)) F”

Theorem next_lemma[local]:
  ∀k x xs y ys st st'.
    (x ≃ y) T ∧ cont_rel xs ys ∧ LIST_REL (LIST_REL (λx y. (x ≃ y) T)) st st' ⇒
    res_rel (next k (eval_wh x) xs st) (next k (eval_wh y) ys st')
Proof
  gen_tac \\ completeInduct_on ‘k’ \\ rw [] \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ once_rewrite_tac [next_def] \\ fs []
  \\ Cases_on ‘eval_wh x = wh_Diverge’
  THEN1 (imp_res_tac app_bisimilarity_diverge \\ fs [res_REL_def])
  \\ qpat_x_assum ‘(x ≃ y) T’ mp_tac
  \\ simp [Once app_bisimilarity_iff] \\ strip_tac
  \\ Cases_on ‘eval_wh x’ \\ fs [res_REL_def]
  \\ Cases_on ‘s = "Act"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rw [] \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute,res_REL_def]
    \\ fs [with_atom_def,with_atoms_def]
    \\ qpat_x_assum ‘(_ ≃ _) T’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ fs [with_atom_def,with_atoms_def]
    \\ Cases_on ‘eval_wh h’
    \\ Cases_on ‘eval_wh h'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs [] \\ Cases_on ‘l’ \\ fs [res_REL_def])
  \\ Cases_on ‘s = "Bind"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_REL_def]
    \\ first_x_assum irule \\ fs [])
  \\ Cases_on ‘s = "Handle"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_REL_def]
    \\ first_x_assum irule \\ fs [])
  \\ Cases_on ‘s = "Ret"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [res_REL_def]
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_REL_def]
    \\ reverse (Cases_on ‘xs’) \\ gvs []
    THEN1
     (Cases_on ‘ys’ \\ gvs []
      \\ rw [] \\ fs [res_REL_def]
      \\ first_x_assum (qspecl_then [‘k-1’,‘x’] mp_tac)
      \\ gvs [] \\ ‘(x ≃ y) T’ by simp [Once app_bisimilarity_iff]
      \\ disch_then drule_all \\ fs [])
    \\ Cases_on ‘ys’ \\ gvs [res_REL_def]
    \\ fs [apply_closure_def]
    \\ qspecl_then [‘T’] assume_tac symmetric_app_bisimilarity
    \\ fs [symmetric_def]
    \\ ‘eval_wh e = wh_Diverge ⇔ eval_wh e' = wh_Diverge’
      by metis_tac [app_bisimilarity_diverge]
    \\ fs [] \\ IF_CASES_TAC \\ fs [res_REL_def]
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    THEN1
     (qsuff_tac ‘dest_wh_Closure (eval_wh e') = NONE’
      THEN1 (fs[res_REL_def])
      \\ qpat_x_assum ‘(e ≃ _) T’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw []
      \\ Cases_on ‘eval_wh e’ \\ fs [])
    \\ rename [‘_ = SOME yy’] \\ PairCases_on ‘yy’ \\ gvs []
    \\ Cases_on ‘eval_wh e’ \\ gvs []
    \\ rename [‘eval_wh h1 = wh_Closure s1 e1’]
    \\ rename [‘dest_wh_Closure (eval_wh h2)’]
    \\ ‘∃s2 e2. eval_wh h2 = wh_Closure s2 e2’ by
      (qpat_x_assum ‘(h1 ≃ _) T’ mp_tac
       \\ simp [Once app_bisimilarity_iff] \\ rw [] \\ fs [])
    \\ fs [] \\ rw [res_REL_def]
    \\ first_x_assum irule \\ fs []
    \\ fs [app_bisimilarity_eq]
    \\ pop_assum kall_tac
    \\ drule_all eval_wh_Closure_closed \\ pop_assum mp_tac
    \\ drule_all eval_wh_Closure_closed
    \\ rpt (disch_then assume_tac)
    \\ reverse conj_tac
    THEN1 (rw [bind_def] \\ irule IMP_closed_subst \\ fs [FLOOKUP_UPDATE])
    \\ ‘(Lam s1 e1 ≃ Lam s2 e2) T’ by
      (‘(h1 ≃ h2) T’ by fs [app_bisimilarity_eq]
       \\ pop_assum mp_tac
       \\ once_rewrite_tac [app_bisimilarity_iff]
       \\ fs [eval_wh_Lam])
    \\ ‘Lam s1 e1 ≅ Lam s2 e2’ by fs [app_bisimilarity_eq]
    \\ fs [exp_eq_Lam, bind1_def, closed_def]
    \\ first_x_assum irule \\ simp []
    \\ metis_tac [exp_eq_refl, exp_eq_sym, exp_eq_trans, exp_eq_Tick_cong])
  \\ Cases_on ‘s = "Raise"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [res_REL_def]
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_REL_def]
    \\ Cases_on ‘xs’ \\ gvs []
    THEN1 (Cases_on ‘ys’ \\ fs [res_REL_def])
    THEN1
     (Cases_on ‘ys’ \\ gvs []
      \\ rw [] \\ fs [res_REL_def]
      \\ first_x_assum (qspecl_then [‘k-1’,‘x’] mp_tac)
      \\ gvs [] \\ ‘(x ≃ y) T’ by simp [Once app_bisimilarity_iff]
      \\ disch_then drule_all \\ fs [])
    \\ Cases_on ‘ys’ \\ gvs [res_REL_def]
    \\ fs [apply_closure_def]
    \\ assume_tac symmetric_app_bisimilarity
    \\ fs [symmetric_def]
    \\ ‘eval_wh e = wh_Diverge ⇔ eval_wh e' = wh_Diverge’
      by metis_tac [app_bisimilarity_diverge]
    \\ fs [] \\ IF_CASES_TAC \\ fs [res_REL_def]
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    THEN1
     (qsuff_tac ‘dest_wh_Closure (eval_wh e') = NONE’
      THEN1 (fs[res_REL_def])
      \\ qpat_x_assum ‘(e ≃ _) T’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw []
      \\ Cases_on ‘eval_wh e’ \\ fs [])
    \\ rename [‘_ = SOME yy’] \\ PairCases_on ‘yy’ \\ gvs []
    \\ Cases_on ‘eval_wh e’ \\ gvs []
    \\ rename [‘eval_wh h1 = wh_Closure s1 e1’]
    \\ rename [‘dest_wh_Closure (eval_wh h2)’]
    \\ ‘∃s2 e2. eval_wh h2 = wh_Closure s2 e2’ by
      (qpat_x_assum ‘(h1 ≃ _) T’ mp_tac
       \\ simp [Once app_bisimilarity_iff] \\ rw [] \\ fs [])
    \\ fs [] \\ rw [res_REL_def]
    \\ first_x_assum irule \\ fs []
    \\ fs [app_bisimilarity_eq]
    \\ pop_assum kall_tac
    \\ drule_all eval_wh_Closure_closed \\ pop_assum mp_tac
    \\ drule_all eval_wh_Closure_closed
    \\ rpt (disch_then assume_tac)
    \\ reverse conj_tac
    THEN1 (rw [bind_def] \\ irule IMP_closed_subst \\ fs [FLOOKUP_UPDATE])
    \\ ‘(Lam s1 e1 ≃ Lam s2 e2) T’ by
      (‘(h1 ≃ h2) T’ by fs [app_bisimilarity_eq]
       \\ pop_assum mp_tac
       \\ once_rewrite_tac [app_bisimilarity_iff]
       \\ fs [eval_wh_Lam])
    \\ ‘Lam s1 e1 ≅ Lam s2 e2’ by fs [app_bisimilarity_eq]
    \\ fs [exp_eq_Lam] \\ fs [bind1_def, closed_def]
    \\ first_x_assum irule \\ simp []
    \\ metis_tac [exp_eq_refl, exp_eq_sym, exp_eq_trans, exp_eq_Tick_cong])
  \\ Cases_on ‘s = "Length"’
  THEN1
   (pop_assum mp_tac \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ rpt strip_tac \\ gvs [res_REL_def]
    \\ rename [‘(e ≃ e') T’]
    \\ gvs [res_REL_def,with_atom_def,with_atoms_def]
    \\ qpat_x_assum ‘(_ ≃ _) T’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e’
    \\ Cases_on ‘eval_wh e'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs [] \\ Cases_on ‘l’ \\ fs [res_REL_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ rw [] \\ fs [res_REL_def]
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
    \\ rpt strip_tac \\ gvs [res_REL_def]
    \\ gvs [res_REL_def,with_atom2_def,with_atoms_def]
    \\ qmatch_goalsub_rename_tac ‘[eval_wh e1; eval_wh e2]’
    \\ rename1 ‘(e1 ≃ e1') T’ \\ qpat_x_assum ‘(e1 ≃ _) T’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ rename1 ‘(e2 ≃ e2') T’ \\ qpat_x_assum ‘(e2 ≃ _) T’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e1’ \\ Cases_on ‘eval_wh e1'’ \\ fs [res_REL_def,get_atoms_def]
    \\ Cases_on ‘eval_wh e2’ \\ Cases_on ‘eval_wh e2'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ Cases_on ‘k=0’ \\ gvs [res_REL_def]
    \\ ‘LENGTH (EL n st) = LENGTH (EL n st')’ by fs [LIST_REL_EL_EQN] \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
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
    \\ rpt strip_tac \\ gvs [res_REL_def]
    \\ gvs [res_REL_def,with_atom2_def,with_atoms_def]
    \\ rename [‘(e1 ≃ e1') T’] \\ qpat_x_assum ‘(_ ≃ _) T’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ rename [‘(e2 ≃ e2') T’] \\ qpat_x_assum ‘(_ ≃ _) T’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e1’ \\ Cases_on ‘eval_wh e1'’ \\ fs [res_REL_def,get_atoms_def]
    \\ Cases_on ‘eval_wh e2’ \\ Cases_on ‘eval_wh e2'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ Cases_on ‘k=0’ \\ gvs [res_REL_def]
    \\ ‘LENGTH (EL n st) = LENGTH (EL n st')’ by fs [LIST_REL_EL_EQN] \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
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
    \\ rpt strip_tac \\ rgs [res_REL_def] \\ rw []
    \\ rename [‘(e ≃ e') T’]
    \\ gvs [res_REL_def,with_atom_def,with_atoms_def]
    \\ qpat_x_assum ‘(_ ≃ _) T’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e’
    \\ Cases_on ‘eval_wh e'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs [] \\ Cases_on ‘l’ \\ fs [res_REL_def]
    \\ IF_CASES_TAC \\ fs [res_REL_def]
    \\ gvs [] \\ qpat_abbrev_tac ‘n = if i < 0 then _ else _’
    \\ first_x_assum (qspecl_then [‘k-1’,‘Cons "Ret" [Lit (Loc (LENGTH st'))]’,‘xs’,
                                         ‘Cons "Ret" [Lit (Loc (LENGTH st'))]’,‘ys’] mp_tac)
    \\ gvs [pure_evalTheory.eval_wh_Cons]
    \\ disch_then irule \\ fs []
    \\ fs [LIST_REL_EL_EQN,EL_REPLICATE]
    \\ irule reflexive_app_bisimilarity \\ fs [])
  \\ fs [res_REL_def]
QED

Theorem symmetric_LIST_REL:
  ∀xs ys R. symmetric R ∧ LIST_REL R xs ys ⇒ LIST_REL R ys xs
Proof
  Induct \\ fs [PULL_EXISTS] \\ rw [symmetric_def]
QED

Theorem bisimilarity_IMP_all_semantics_eq:
  ∀x y xs ys st st'.
    (x ≃ y) T ∧ cont_rel xs ys ∧ LIST_REL (LIST_REL (λx y. (x ≃ y) T)) st st'
  ⇒ semantics x xs st = semantics y ys st'
Proof
  fs [io_el_eqv] \\ fs [PULL_FORALL] \\ rpt gen_tac
  \\ EVERY (map qid_spec_tac [‘st'’,‘st’,‘ys’,‘xs’,‘y’,‘x’])
  \\ completeInduct_on ‘LENGTH path’ \\ rw [] \\ fs [PULL_FORALL]
  \\ fs [semantics_def]
  \\ once_rewrite_tac [interp_def]
  \\ qsuff_tac ‘
    next_action (eval_wh x) xs st = next_action (eval_wh y) ys st' ∨
    ∃a new1 new2 s1 s2.
      next_action (eval_wh x) xs st = Act a new1 s1 ∧
      next_action (eval_wh y) ys st' = Act a new2 s2 ∧
      cont_rel new1 new2 ∧ LIST_REL (LIST_REL (λx y. (x ≃ y) T)) s1 s2’
  THEN1
   (strip_tac \\ fs []
    \\ Cases_on ‘path’ \\ fs [io_el_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[] \\ rename1 `Str h`
    \\ ‘wh_Constructor "Ret" [Lit (Str h)] = eval_wh (Ret (Lit (Str h)))’ by fs [eval_wh_thm]
    \\ fs [] \\ first_x_assum irule \\ fs []
    \\ match_mp_tac reflexive_app_bisimilarity \\ fs [])
  \\ qsuff_tac ‘res_rel (next_action (eval_wh x) xs st) (next_action (eval_wh y) ys st')’
  THEN1
   (Cases_on ‘next_action (eval_wh x) xs st’
    \\ Cases_on ‘next_action (eval_wh y) ys st'’
    \\ fs [res_REL_def])
  \\ qpat_x_assum ‘∀x. _’ kall_tac
  \\ fs [next_action_def]
  \\ rpt (DEEP_INTRO_TAC some_intro \\ fs []) \\ fs [] \\ reverse (rw [])
  \\ fs [res_REL_def]
  \\ drule_all next_lemma
  THEN1 (disch_then (qspec_then ‘x'’ mp_tac) \\ fs [])
  THEN1 (disch_then (qspec_then ‘x'’ mp_tac) \\ fs [])
  \\ dxrule next_less_eq
  \\ dxrule next_less_eq
  \\ disch_then (qspec_then ‘x'+x''’ assume_tac)
  \\ disch_then (qspec_then ‘x'+x''’ assume_tac) \\ fs []
QED

Theorem bisimilarity_IMP_semantics_eq:
  ∀x y. (x ≃ y) T ⇒ semantics x Done [] = semantics y Done []
Proof
  rw[] >> irule bisimilarity_IMP_all_semantics_eq >> simp[]
QED

Theorem safe_itree_Error[simp]:
  safe_itree (Ret Error) = F
Proof
  rw[Once safe_itree_cases]
QED

Theorem safe_itree_bind_pres:
  safe_itree (semantics e cs st) ∧
  eval_wh e = wh_Constructor "Bind" [e1; e2] ⇒
  safe_itree (semantics e1 (BC e2 cs) st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  rw[] >>
  simp[semantics_def] >>
  simp[Once interp_def,next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (gvs[some_def] >>
      qhdtm_x_assum ‘safe_itree’ mp_tac >>
      qmatch_goalsub_abbrev_tac ‘if a1 then _ else _’ >>
      ‘a1’
        by(unabbrev_all_tac >>
           Q.REFINE_EXISTS_TAC ‘SUC _’ >> simp[] >>
           first_x_assum (irule_at Any)) >>
      SELECT_ELIM_TAC >>
      conj_tac >- metis_tac[markerTheory.Abbrev_def] >>
      rw[] >>
      metis_tac[next_next]) >>
  rw[Once safe_itree_cases]
QED

Theorem safe_itree_handle_pres:
  safe_itree (semantics e cs st) ∧
  eval_wh e = wh_Constructor "Handle" [e1; e2] ⇒
  safe_itree (semantics e1 (HC e2 cs) st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  rw[] >>
  simp[semantics_def] >>
  simp[Once interp_def,next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (gvs[some_def] >>
      qhdtm_x_assum ‘safe_itree’ mp_tac >>
      qmatch_goalsub_abbrev_tac ‘if a1 then _ else _’ >>
      ‘a1’
        by(unabbrev_all_tac >>
           Q.REFINE_EXISTS_TAC ‘SUC _’ >> simp[] >>
           first_x_assum (irule_at Any)) >>
      SELECT_ELIM_TAC >>
      conj_tac >- metis_tac[markerTheory.Abbrev_def] >>
      rw[] >>
      metis_tac[next_next]) >>
  rw[Once safe_itree_cases]
QED

Theorem safe_itree_ret_pres:
  safe_itree (semantics e (HC c cs) st) ∧
  eval_wh e = wh_Constructor "Ret" [e1] ⇒
  safe_itree (semantics e cs st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  rw[] >>
  simp[semantics_def] >>
  simp[Once interp_def,next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (gvs[some_def] >>
      qhdtm_x_assum ‘safe_itree’ mp_tac >>
      qmatch_goalsub_abbrev_tac ‘if a1 then _ else _’ >>
      ‘a1’
        by(unabbrev_all_tac >>
           Q.REFINE_EXISTS_TAC ‘SUC _’ >> simp[] >>
           first_x_assum (irule_at Any)) >>
      SELECT_ELIM_TAC >>
      conj_tac >- metis_tac[markerTheory.Abbrev_def] >>
      rw[] >>
      metis_tac[next_next]) >>
  rw[Once safe_itree_cases]
QED

Theorem safe_itree_ret_call_pres:
  safe_itree (semantics x (BC h1 c) st) ∧
  eval_wh x = wh_Constructor "Ret" [x'] ∧
  eval_wh h1 = wh_Closure s1 e1
  ⇒
  safe_itree (semantics (bind1 s1 x' e1) c st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def] >> rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[] >>
  rename1 ‘next n’ >>
  last_x_assum(qspec_then ‘SUC n’ assume_tac) >> gvs[]
QED

Theorem safe_itree_raise_pres:
  safe_itree (semantics x (BC e c) st) ∧
  eval_wh x = wh_Constructor "Raise" [x']
  ⇒
  safe_itree (semantics x c st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def] >> rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[] >>
  rename1 ‘next n’ >>
  last_x_assum(qspec_then ‘SUC n’ assume_tac) >> gvs[]
QED

Theorem safe_itree_raise_call_pres:
  safe_itree (semantics x (HC h1 c) st) ∧
  eval_wh x = wh_Constructor "Raise" [x'] ∧
  eval_wh h1 = wh_Closure s1 e1
  ⇒
  safe_itree (semantics (bind1 s1 x' e1) c st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def] >> rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[] >>
  rename1 ‘next n’ >>
  last_x_assum(qspec_then ‘SUC n’ assume_tac) >> gvs[]
QED

Theorem safe_itree_length_pres:
  safe_itree (semantics x xs st) ∧
  eval_wh x = wh_Constructor "Length" [e] ∧
  eval_wh e = wh_Atom (Loc n)
  ⇒
  safe_itree (semantics (Ret (Lit (Int (&LENGTH (EL n st))))) xs st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def,with_atom_def,with_atoms_def] >> rw[] >> gvs[] >>
  gvs[get_atoms_def] >>
  Cases_on ‘LENGTH st ≤ n’
  >- gvs[case_someT] >>
  gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (gvs[eval_wh_thm] >>
          dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[eval_wh_thm] >>
  rename1 ‘next clk’ >>
  last_x_assum(qspec_then ‘SUC clk’ assume_tac) >> gvs[]
QED

Theorem safe_itree_update_ret_pres:
  safe_itree (semantics x xs st) ∧
  eval_wh x = wh_Constructor "Update" [e1; e2; x''] ∧
  eval_wh e1 = wh_Atom (Loc n) ∧
  eval_wh e2 = wh_Atom (Int i) ∧
  ¬(LENGTH st ≤ n) ∧
  0 ≤ i ∧
  i < &LENGTH (EL n st)
  ⇒
  safe_itree (semantics (Ret (Cons "" [])) xs (LUPDATE (LUPDATE x'' (Num i) (EL n st)) n st))
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def,with_atom_def,with_atoms_def,with_atom2_def] >> rw[] >> gvs[] >>
  gvs[get_atoms_def] >>
  gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (
      simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (gvs[eval_wh_thm] >>
          dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[eval_wh_thm] >>
  rename1 ‘next clk’ >>
  last_x_assum(qspec_then ‘SUC clk’ assume_tac) >> gvs[]
QED

Theorem safe_itree_update_raise_pres:
  safe_itree (semantics x xs st) ∧
  eval_wh x = wh_Constructor "Update" [e1; e2; x''] ∧
  eval_wh e1 = wh_Atom (Loc n) ∧
  eval_wh e2 = wh_Atom (Int i) ∧
  ¬(LENGTH st ≤ n) ∧
  ¬(0 ≤ i)
  ⇒
  safe_itree (semantics (Raise (Cons "Subscript" [])) xs st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def,with_atom_def,with_atoms_def,with_atom2_def] >> rw[] >> gvs[] >>
  gvs[get_atoms_def] >>
  gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (
      simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (gvs[eval_wh_thm] >>
          dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[eval_wh_thm] >>
  rename1 ‘next clk’ >>
  last_x_assum(qspec_then ‘SUC clk’ assume_tac) >> gvs[]
QED

Theorem safe_itree_update_raise_pres2:
  safe_itree (semantics x xs st) ∧
  eval_wh x = wh_Constructor "Update" [e1; e2; x''] ∧
  eval_wh e1 = wh_Atom (Loc n) ∧
  eval_wh e2 = wh_Atom (Int i) ∧
  ¬(LENGTH st ≤ n) ∧
  ¬(i < &LENGTH (EL n st))
  ⇒
  safe_itree (semantics (Raise (Cons "Subscript" [])) xs st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def,with_atom_def,with_atoms_def,with_atom2_def] >> rw[] >> gvs[] >>
  gvs[get_atoms_def] >>
  gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (
      simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (gvs[eval_wh_thm] >>
          dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[eval_wh_thm] >>
  rename1 ‘next clk’ >>
  last_x_assum(qspec_then ‘SUC clk’ assume_tac) >> gvs[]
QED

Theorem safe_itree_deref_ret_pres:
  safe_itree (semantics x xs st) ∧
  eval_wh x = wh_Constructor "Deref" [e2; e1] ∧
  eval_wh e2 = wh_Atom (Loc n) ∧
  eval_wh e1 = wh_Atom (Int i) ∧
  ¬(LENGTH st ≤ n) ∧
  0 ≤ i ∧
  i < &LENGTH (EL n st)
  ⇒
  safe_itree (semantics (Ret (EL (Num i) (EL n st))) xs st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def,with_atom_def,with_atoms_def,with_atom2_def] >> rw[] >> gvs[] >>
  gvs[get_atoms_def] >>
  gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (
      simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (gvs[eval_wh_thm] >>
          dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[eval_wh_thm] >>
  rename1 ‘next clk’ >>
  last_x_assum(qspec_then ‘SUC clk’ assume_tac) >> gvs[]
QED

Theorem safe_itree_deref_raise_pres:
  safe_itree (semantics x xs st) ∧
  eval_wh x = wh_Constructor "Deref" [e2; e1] ∧
  eval_wh e2 = wh_Atom (Loc n) ∧
  eval_wh e1 = wh_Atom (Int i) ∧
  ¬(LENGTH st ≤ n) ∧
  ¬(0 ≤ i)
  ⇒
  safe_itree (semantics (Raise (Cons "Subscript" [])) xs st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def,with_atom_def,with_atoms_def,with_atom2_def] >> rw[] >> gvs[] >>
  gvs[get_atoms_def] >>
  gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (
      simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (gvs[eval_wh_thm] >>
          dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[eval_wh_thm] >>
  rename1 ‘next clk’ >>
  last_x_assum(qspec_then ‘SUC clk’ assume_tac) >> gvs[]
QED

Theorem safe_itree_deref_raise_pres2:
  safe_itree (semantics x xs st) ∧
  eval_wh x = wh_Constructor "Deref" [e2; e1] ∧
  eval_wh e2 = wh_Atom (Loc n) ∧
  eval_wh e1 = wh_Atom (Int i) ∧
  ¬(LENGTH st ≤ n) ∧
  ¬(i < &LENGTH (EL n st))
  ⇒
  safe_itree (semantics (Raise (Cons "Subscript" [])) xs st)
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def,with_atom_def,with_atoms_def,with_atom2_def] >> rw[] >> gvs[] >>
  gvs[get_atoms_def] >>
  gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (
      simp[semantics_def, Once interp_def,next_action_def] >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (gvs[eval_wh_thm] >>
          dxrule_then drule next_next >> rw[]) >>
      simp[Once safe_itree_cases]) >>
  simp[semantics_def, Once interp_def, next_action_def] >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[eval_wh_thm] >>
  rename1 ‘next clk’ >>
  last_x_assum(qspec_then ‘SUC clk’ assume_tac) >> gvs[]
QED

Theorem safe_itree_alloc_pres:
  safe_itree (semantics x xs st) ∧
  eval_wh x = wh_Constructor "Alloc" [e; y''] ∧
  eval_wh e = wh_Atom (Int i)
  ⇒
  safe_itree
  (semantics (Ret (Lit (Loc (LENGTH st)))) xs
   (st ++ [REPLICATE (if i < 0 then 0 else Num i) y'']))
Proof
  simp[SimpL“$==>”,semantics_def,Once interp_def,next_action_def] >>
  rw[] >> gvs[] >>
  rpt(pop_assum mp_tac) >> once_rewrite_tac[next_def] >>
  simp[apply_closure_def,with_atom_def,with_atoms_def,with_atom2_def] >> rw[] >> gvs[] >>
  gvs[get_atoms_def] >>
  gvs[] >>
  rpt(pop_assum mp_tac) >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  (rw[]
   >- (simp[semantics_def, Once interp_def,next_action_def] >>
       rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
       rw[]
       >- (gvs[eval_wh_thm] >>
           dxrule_then drule next_next >> rw[]) >>
       simp[Once safe_itree_cases]) >>
   simp[semantics_def, Once interp_def, next_action_def] >>
   rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
   rw[eval_wh_thm] >>
   rename1 ‘next clk’ >>
   last_x_assum(qspec_then ‘SUC clk’ assume_tac) >> gvs[]
  )
QED

Theorem next_F_lemma[local]:
  ∀k x xs y ys st st'.
    (x ≃ y) F ∧ cont_REL (λx y. (x ≃ y) F) xs ys ∧ LIST_REL (LIST_REL (λx y. (x ≃ y) F)) st st' ∧
    safe_itree(semantics x xs st) ∧ safe_itree(semantics y ys st')
    ⇒
    res_REL (λx y. (x ≃ y) F) T (next k (eval_wh x) xs st) (next k (eval_wh y) ys st')
Proof
  gen_tac \\ completeInduct_on ‘k’ \\ rw [] \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ once_rewrite_tac [next_def] \\ fs []
  \\ Cases_on ‘eval_wh x = wh_Diverge’
  THEN1 (simp[]
         \\ qpat_x_assum ‘(x ≃ y) F’ mp_tac
         \\ simp [Once app_bisimilarity_iff] \\ strip_tac
         \\ PURE_TOP_CASE_TAC >> gvs[]
         \\ simp[res_REL_def])
  \\ qpat_x_assum ‘(x ≃ y) F’ mp_tac
  \\ simp [Once app_bisimilarity_iff] \\ strip_tac
  \\ reverse(Cases_on ‘eval_wh x’) \\ fs [res_REL_def]
  THEN1
    (spose_not_then kall_tac >>
     gvs[semantics_def] >>
     qpat_x_assum ‘safe_itree (interp wh_Error _ _)’ mp_tac >>
     simp[Once interp_def,next_action_def] >>
     once_rewrite_tac[next_def] >> simp[case_someT])
  \\ Cases_on ‘s = "Act"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rw [] \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute,res_REL_def]
    \\ fs [with_atom_def,with_atoms_def]
    \\ qpat_x_assum ‘(_ ≃ _) F’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ fs [with_atom_def,with_atoms_def]
    \\ Cases_on ‘eval_wh h’
    \\ Cases_on ‘eval_wh h'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs []
    >- (Cases_on ‘l’ \\ fs [res_REL_def]) >>
    rpt(qpat_x_assum ‘safe_itree _’ mp_tac) >>
    simp[semantics_def] >>
    once_rewrite_tac[interp_def] >>
    simp[next_action_def] >>
    once_rewrite_tac[next_def] >>
    simp[with_atom_def,with_atoms_def,case_someT])
  \\ Cases_on ‘s = "Bind"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_REL_def]
    \\ first_x_assum irule \\ fs []
    \\ gvs[]
    \\ imp_res_tac safe_itree_bind_pres
    \\ simp[])
  \\ Cases_on ‘s = "Handle"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_REL_def]
    \\ first_x_assum irule \\ fs []
    \\ imp_res_tac safe_itree_handle_pres
    \\ simp[]
    )
  \\ Cases_on ‘s = "Ret"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [res_REL_def]
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_REL_def]
    \\ reverse (Cases_on ‘xs’) \\ gvs []
    THEN1
     (Cases_on ‘ys’ \\ gvs []
      \\ rw [] \\ fs [res_REL_def]
      \\ first_x_assum (qspecl_then [‘k-1’,‘x’] mp_tac)
      \\ gvs [] \\ ‘(x ≃ y) F’ by simp [Once app_bisimilarity_iff]
      \\ disch_then drule \\ simp[]
      \\ disch_then match_mp_tac
      \\ simp[]
      \\ imp_res_tac safe_itree_ret_pres \\ simp[])
    \\ Cases_on ‘ys’ \\ gvs [res_REL_def]
    \\ fs [apply_closure_def]
    \\ qspecl_then [‘T’] assume_tac symmetric_app_bisimilarity
    \\ fs [symmetric_def]
    \\ IF_CASES_TAC
    THEN1
     (qpat_x_assum ‘(e ≃ _) F’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw [res_REL_def]
      \\ Cases_on ‘eval_wh e'’ \\ rw[res_REL_def])
    \\ IF_CASES_TAC
    THEN1
     (qpat_x_assum ‘(e ≃ _) F’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw [res_REL_def]
      \\ Cases_on ‘eval_wh e’ \\ rw[res_REL_def])
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    THEN1
     (qsuff_tac ‘dest_wh_Closure (eval_wh e') = NONE’
      THEN1 (fs[res_REL_def])
      \\ qpat_x_assum ‘(e ≃ _) F’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw []
      \\ Cases_on ‘eval_wh e’ \\ fs []
      \\ Cases_on ‘eval_wh e'’ \\ fs [])
    \\ rename [‘_ = SOME yy’] \\ PairCases_on ‘yy’ \\ gvs []
    \\ Cases_on ‘eval_wh e’ \\ gvs []
    \\ rename [‘eval_wh h1 = wh_Closure s1 e1’]
    \\ rename [‘dest_wh_Closure (eval_wh h2)’]
    \\ ‘∃s2 e2. eval_wh h2 = wh_Closure s2 e2’ by
      (qpat_x_assum ‘(h1 ≃ _) F’ mp_tac
       \\ simp [Once app_bisimilarity_iff] \\ rw [] \\ fs [])
    \\ fs [] \\ rw [res_REL_def]
    \\ first_x_assum irule \\ fs []
    \\ conj_tac >- imp_res_tac safe_itree_ret_call_pres
    \\ conj_tac >- imp_res_tac safe_itree_ret_call_pres
                                (* HERE *)
    \\ fs [app_bisimilarity_eq]
    \\ pop_assum kall_tac
    \\ drule_all eval_wh_Closure_closed \\ pop_assum mp_tac
    \\ drule_all eval_wh_Closure_closed
    \\ rpt (disch_then assume_tac)
    \\ reverse conj_tac
    THEN1 (rw [bind_def] \\ irule IMP_closed_subst \\ fs [FLOOKUP_UPDATE])
    \\ ‘(Lam s1 e1 ≃ Lam s2 e2) F’ by
      (‘(h1 ≃ h2) F’ by fs [app_bisimilarity_eq]
       \\ pop_assum mp_tac
       \\ once_rewrite_tac [app_bisimilarity_iff]
       \\ fs [eval_wh_Lam])
    \\ ‘(Lam s1 e1 ≅? Lam s2 e2) F’ by fs [app_bisimilarity_eq]
    \\ fs [exp_eq_Lam, bind1_def, closed_def]
    \\ first_x_assum irule \\ simp []
    \\ metis_tac [exp_eq_refl, exp_eq_sym, exp_eq_trans, exp_eq_Tick_cong])
  \\ Cases_on ‘s = "Raise"’
  THEN1
   (asm_rewrite_tac [CONS_11] \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [res_REL_def]
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ strip_tac \\ rw [res_REL_def]
    \\ Cases_on ‘xs’ \\ gvs []
    THEN1 (Cases_on ‘ys’ \\ fs [res_REL_def])
    THEN1
     (Cases_on ‘ys’ \\ gvs []
      \\ rw [] \\ fs [res_REL_def]
      \\ first_x_assum (qspecl_then [‘k-1’,‘x’] mp_tac)
      \\ gvs [] \\ ‘(x ≃ y) F’ by simp [Once app_bisimilarity_iff]
      \\ rpt(disch_then drule)
      \\ impl_tac
      THEN1
        (imp_res_tac safe_itree_raise_pres >> simp[])
      \\ fs [])
    \\ Cases_on ‘ys’ \\ gvs [res_REL_def]
    \\ fs [apply_closure_def]
    \\ IF_CASES_TAC
    THEN1
     (qpat_x_assum ‘(e ≃ _) F’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw [res_REL_def]
      \\ Cases_on ‘eval_wh e'’ \\ rw[res_REL_def])
    \\ IF_CASES_TAC
    THEN1
     (qpat_x_assum ‘(e ≃ _) F’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw [res_REL_def]
      \\ Cases_on ‘eval_wh e’ \\ rw[res_REL_def])
    \\ Cases_on ‘dest_wh_Closure (eval_wh e)’ \\ fs []
    THEN1
     (qsuff_tac ‘dest_wh_Closure (eval_wh e') = NONE’
      THEN1 (fs[res_REL_def])
      \\ qpat_x_assum ‘(e ≃ _) F’ mp_tac
      \\ simp [Once app_bisimilarity_iff] \\ rw []
      \\ Cases_on ‘eval_wh e’ \\ fs []
      \\ Cases_on ‘eval_wh e'’ \\ fs [])
    \\ rename [‘_ = SOME yy’] \\ PairCases_on ‘yy’ \\ gvs []
    \\ Cases_on ‘eval_wh e’ \\ gvs []
    \\ rename [‘eval_wh h1 = wh_Closure s1 e1’]
    \\ rename [‘dest_wh_Closure (eval_wh h2)’]
    \\ ‘∃s2 e2. eval_wh h2 = wh_Closure s2 e2’ by
      (qpat_x_assum ‘(h1 ≃ _) F’ mp_tac
       \\ simp [Once app_bisimilarity_iff] \\ rw [] \\ fs [])
    \\ fs [] \\ rw [res_REL_def]
    \\ first_x_assum irule \\ fs []
    \\ conj_tac >- imp_res_tac safe_itree_raise_call_pres
    \\ conj_tac >- imp_res_tac safe_itree_raise_call_pres
    \\ fs [app_bisimilarity_eq]
    \\ pop_assum kall_tac
    \\ drule_all eval_wh_Closure_closed \\ pop_assum mp_tac
    \\ drule_all eval_wh_Closure_closed
    \\ rpt (disch_then assume_tac)
    \\ reverse conj_tac
    THEN1 (rw [bind_def] \\ irule IMP_closed_subst \\ fs [FLOOKUP_UPDATE])
    \\ ‘(Lam s1 e1 ≃ Lam s2 e2) F’ by
      (‘(h1 ≃ h2) F’ by fs [app_bisimilarity_eq]
       \\ pop_assum mp_tac
       \\ once_rewrite_tac [app_bisimilarity_iff]
       \\ fs [eval_wh_Lam])
    \\ ‘(Lam s1 e1 ≅? Lam s2 e2) F’ by fs [app_bisimilarity_eq]
    \\ fs [exp_eq_Lam] \\ fs [bind1_def, closed_def]
    \\ first_x_assum irule \\ simp []
    \\ metis_tac [exp_eq_refl, exp_eq_sym, exp_eq_trans, exp_eq_Tick_cong])
  \\ Cases_on ‘s = "Length"’
  THEN1
   (pop_assum mp_tac \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ rpt strip_tac \\ gvs [res_REL_def]
    \\ rename [‘(e ≃ e') F’]
    \\ gvs [res_REL_def,with_atom_def,with_atoms_def]
    \\ qpat_x_assum ‘(_ ≃ _) F’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e’
    \\ Cases_on ‘eval_wh e'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs [] \\ Cases_on ‘l’ \\ fs [res_REL_def]
    \\ rw [] \\ fs [res_REL_def]
    \\ gvs [GSYM NOT_LESS]
    \\ ‘LENGTH (EL n st) = LENGTH (EL n st')’ by fs [LIST_REL_EL_EQN]
    \\ gvs [] \\ qpat_abbrev_tac ‘i = Int _’
    \\ first_x_assum (qspecl_then [‘k-1’,‘Cons "Ret" [Lit i]’,‘xs’,
                                         ‘Cons "Ret" [Lit i]’,‘ys’] mp_tac)
    \\ gvs [pure_evalTheory.eval_wh_Cons]
    \\ disch_then irule \\ fs []
    \\ conj_tac
    THEN1
     (unabbrev_all_tac >> imp_res_tac safe_itree_length_pres \\ gvs[])
    \\ conj_tac
    THEN1
     (unabbrev_all_tac >> imp_res_tac safe_itree_length_pres \\ gvs[])
    \\ irule reflexive_app_bisimilarity \\ fs [])
  \\ Cases_on ‘s = "Update"’
  THEN1
   (pop_assum mp_tac \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ rpt strip_tac \\ gvs [res_REL_def]
    \\ gvs [res_REL_def,with_atom2_def,with_atoms_def]
    \\ qmatch_goalsub_rename_tac ‘[eval_wh e1; eval_wh e2]’
    \\ rename1 ‘(e1 ≃ e1') F’ \\ qpat_x_assum ‘(e1 ≃ _) F’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ rename1 ‘(e2 ≃ e2') F’ \\ qpat_x_assum ‘(e2 ≃ _) F’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e1’ \\ Cases_on ‘eval_wh e1'’ \\ fs [res_REL_def,get_atoms_def]
    \\ Cases_on ‘eval_wh e2’ \\ Cases_on ‘eval_wh e2'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ Cases_on ‘k=0’ \\ gvs [res_REL_def]
    \\ ‘LENGTH (EL n st) = LENGTH (EL n st')’ by fs [LIST_REL_EL_EQN] \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ first_assum (qspecl_then [‘k-1’,‘Cons "Raise" [Cons "Subscript" []]’,‘xs’,
                                 ‘Cons "Raise" [Cons "Subscript" []]’,‘ys’,
                                 ‘st’,‘st'’] mp_tac)
    \\ TRY (impl_tac
            THEN1 ((* slow *)
                   fs [reflexive_app_bisimilarity] >>
                   conj_tac >> imp_res_tac safe_itree_update_raise_pres >>
                   imp_res_tac safe_itree_update_raise_pres2 >>
                   gvs[])
           )
    \\ rw [] \\ gvs [pure_evalTheory.eval_wh_Cons]
    \\ rename [‘res_REL _ _ (_ (LUPDATE (LUPDATE y1 (Num i) (EL n st)) n st))
                        (_ (LUPDATE (LUPDATE y2 (Num i) (EL n st')) n st'))’]
    \\ first_assum (qspecl_then [‘k-1’,‘Cons "Ret" [Cons "" []]’,‘xs’,
                                 ‘Cons "Ret" [Cons "" []]’,‘ys’,
                                 ‘(LUPDATE (LUPDATE y1 (Num i) (EL n st)) n st)’,
                                 ‘(LUPDATE (LUPDATE y2 (Num i) (EL n st')) n st')’] mp_tac)
    \\ reverse impl_tac THEN1 fs [pure_evalTheory.eval_wh_Cons]
    \\ simp[reflexive_app_bisimilarity]
    \\ reverse conj_tac >- (imp_res_tac safe_itree_update_ret_pres >> fs[])
    \\ irule EVERY2_LUPDATE_same \\ gvs []
    \\ irule EVERY2_LUPDATE_same \\ gvs []
    \\ fs [LIST_REL_EL_EQN])
  \\ Cases_on ‘s = "Deref"’
  THEN1
   (pop_assum mp_tac \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ rpt strip_tac \\ gvs [res_REL_def]
    \\ gvs [res_REL_def,with_atom2_def,with_atoms_def]
    \\ rename [‘(e1 ≃ e1') F’] \\ qpat_x_assum ‘(_ ≃ _) F’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ rename [‘(e2 ≃ e2') F’] \\ qpat_x_assum ‘(_ ≃ _) F’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e1’ \\ Cases_on ‘eval_wh e1'’ \\ fs [res_REL_def,get_atoms_def]
    \\ Cases_on ‘eval_wh e2’ \\ Cases_on ‘eval_wh e2'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
    \\ Cases_on ‘k=0’ \\ gvs [res_REL_def]
    \\ ‘LENGTH (EL n st) = LENGTH (EL n st')’ by fs [LIST_REL_EL_EQN] \\ gvs []
    \\ TOP_CASE_TAC \\ gvs [res_REL_def]
                                (* here *)
    \\ first_assum (qspecl_then [‘k-1’,‘Cons "Raise" [Cons "Subscript" []]’,‘xs’,
                                 ‘Cons "Raise" [Cons "Subscript" []]’,‘ys’,
                                 ‘st’,‘st'’] mp_tac)
    \\ TRY (impl_tac THEN1 (fs [reflexive_app_bisimilarity] \\
                            imp_res_tac safe_itree_deref_raise_pres \\
                            imp_res_tac safe_itree_deref_raise_pres2 \\
                            fs[]))
    \\ rw [] \\ gvs [pure_evalTheory.eval_wh_Cons]
    \\ first_assum (qspecl_then [‘k-1’,‘Cons "Ret" [EL (Num i) (EL n st)]’,‘xs’,
                                 ‘Cons "Ret" [EL (Num i) (EL n st')]’,
                                 ‘ys’,‘st’,‘st'’] mp_tac)
    \\ reverse impl_tac THEN1 fs [pure_evalTheory.eval_wh_Cons]
    \\ simp[]
    \\ ‘Num i < LENGTH (EL n st')’ by intLib.COOPER_TAC
    \\ fs [LIST_REL_EL_EQN]
    \\ first_x_assum (qspec_then ‘n’ mp_tac)
    \\ simp[]
    \\ disch_then drule
    \\ strip_tac
    \\ conj_tac >- (gvs[app_bisimilarity_eq] >> match_mp_tac exp_eq_Prim_cong >> simp[])
    \\ imp_res_tac safe_itree_deref_ret_pres \\ gvs[])
  \\ Cases_on ‘s = "Alloc"’
  THEN1
   (pop_assum mp_tac \\ simp_tac (srw_ss()) []
    \\ imp_res_tac LIST_REL_LENGTH \\ asm_rewrite_tac []
    \\ IF_CASES_TAC \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [LENGTH_EQ_NUM_compute]
    \\ rpt strip_tac \\ rgs [res_REL_def] \\ rw []
    \\ rename [‘(e ≃ e') F’]
    \\ gvs [res_REL_def,with_atom_def,with_atoms_def]
    \\ qpat_x_assum ‘(_ ≃ _) F’ mp_tac
    \\ simp [Once app_bisimilarity_iff] \\ strip_tac
    \\ Cases_on ‘eval_wh e’
    \\ Cases_on ‘eval_wh e'’ \\ fs [res_REL_def,get_atoms_def]
    \\ gvs [] \\ Cases_on ‘l’ \\ fs [res_REL_def]
    \\ IF_CASES_TAC \\ fs [res_REL_def]
    \\ gvs [] \\ qpat_abbrev_tac ‘n = if i < 0 then _ else _’
    \\ first_x_assum (qspecl_then [‘k-1’,‘Cons "Ret" [Lit (Loc (LENGTH st'))]’,‘xs’,
                                         ‘Cons "Ret" [Lit (Loc (LENGTH st'))]’,‘ys’] mp_tac)
    \\ gvs [pure_evalTheory.eval_wh_Cons]
    \\ disch_then irule \\ fs []
    \\ conj_tac >- (imp_res_tac safe_itree_alloc_pres >> fs[Abbr ‘n’] >> metis_tac[])
    \\ conj_tac >- (imp_res_tac safe_itree_alloc_pres >> fs[Abbr ‘n’] >> metis_tac[])
    \\ fs [LIST_REL_EL_EQN,EL_REPLICATE]
    \\ irule reflexive_app_bisimilarity \\ fs [])
  \\ fs [res_REL_def]
QED

Theorem no_err_exp_eq_IMP_sem_eq:
  ∀ e1 e2 c1 c2 s1 s2.
    LIST_REL (LIST_REL (λx y. (x ≃ y) F)) s1 s2 ∧
    cont_REL (λx y. (x ≃ y) F) c1 c2 ∧
    (λx y. (x ≃ y) F) e1 e2 ∧
    safe_itree(semantics e1 c1 s1) ∧ safe_itree(semantics e2 c2 s2)
    ⇒
    semantics e1 c1 s1 = semantics e2 c2 s2
Proof
  fs [io_el_eqv] \\ fs [PULL_FORALL] \\ rpt gen_tac
  \\ EVERY (map qid_spec_tac [‘s1’,‘s2’,‘c2’,‘c1’,‘e2’,‘e1’])
  \\ completeInduct_on ‘LENGTH path’ \\ rw [] \\ fs [PULL_FORALL]
  \\ fs [semantics_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ once_rewrite_tac [interp_def]
  \\ rpt strip_tac
  \\ qsuff_tac ‘
    next_action (eval_wh e1) c1 s1 = next_action (eval_wh e2) c2 s2 ∨
    ∃a new1 new2 s1' s2'.
      next_action (eval_wh e1) c1 s1 = Act a new1 s1' ∧
      next_action (eval_wh e2) c2 s2 = Act a new2 s2' ∧
      cont_REL (λx y. (x ≃ y) F) new1 new2 ∧
      LIST_REL (LIST_REL (λx y. (x ≃ y) F)) s1' s2'’
  THEN1
   (strip_tac \\ fs []
    \\ Cases_on ‘path’ \\ fs [io_el_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rename1 `Str h`
    \\ ‘wh_Constructor "Ret" [Lit (Str h)] = eval_wh (Ret (Lit (Str h)))’ by fs [eval_wh_thm]
    \\ fs [] \\ first_x_assum irule \\ fs []
    \\ simp[reflexive_app_bisimilarity]
    \\ qhdtm_x_assum ‘safe_itree’ (strip_assume_tac o ONCE_REWRITE_RULE[safe_itree_cases])
    \\ gvs[]
    \\ qhdtm_x_assum ‘safe_itree’ (strip_assume_tac o ONCE_REWRITE_RULE[safe_itree_cases])
    \\ gvs[]
    \\ rpt(first_x_assum(qspec_then ‘INR h’ mp_tac))
    \\ simp[])
  \\ drule_then (drule_then drule) next_F_lemma
  \\ disch_then(mp_tac o Ho_Rewrite.REWRITE_RULE[GSYM PULL_FORALL])
  \\ impl_tac
  >- (simp[semantics_def] >> rw[] >> once_rewrite_tac[interp_def] >> simp[])
  \\ disch_then assume_tac
  \\ simp[next_action_def]
  \\ rpt(DEEP_INTRO_TAC some_intro >> gvs[])
  \\ rw[]
  >- (rename1 ‘next ck1 _ _ _ = next ck2 _ _ _’
      \\ ‘ck1 ≤ ck2 ∨ ck2 ≤ ck1’ by DECIDE_TAC
      >- (drule_then drule next_less_eq >>
          rw[] >>
          first_x_assum(qspec_then ‘ck2’ mp_tac) >>
          Cases_on ‘next ck2 (eval_wh e1) c1 s1’
          \\ Cases_on ‘next ck2 (eval_wh e2) c2 s2’
          \\ gvs[res_REL_def]) >>
      drule_then drule next_less_eq >>
      rw[] >>
      first_x_assum(qspec_then ‘ck1’ mp_tac) >>
      Cases_on ‘next ck1 (eval_wh e1) c1 s1’
      \\ Cases_on ‘next ck1 (eval_wh e2) c2 s2’
      \\ gvs[res_REL_def])
  >- (first_x_assum (qspec_then ‘x’ mp_tac) >>
      Cases_on ‘next x (eval_wh e1) c1 s1’ >>
      Cases_on ‘next x (eval_wh e2) c2 s2’ >>
      gvs[res_REL_def] >>
      rw[] >> qexists_tac ‘x’ >> simp[] >>
      gvs[next_action_def] >>
      qpat_x_assum ‘safe_itree _’ mp_tac >>
      rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
      rw[]
      >- (drule next_next >>
          disch_then(qspec_then ‘x’ mp_tac) >>
          rw[]) >>
      first_x_assum(qspec_then ‘x’ mp_tac) >> simp[]) >>
  ntac 2 (first_x_assum(qspec_then ‘x’ mp_tac)) >>
  rw[] >>
  Cases_on ‘next x (eval_wh e1) c1 s1’ >> gvs[res_REL_def] >>
  gvs[next_action_def] >>
  qpat_x_assum ‘safe_itree _’ kall_tac >>
  qpat_x_assum ‘safe_itree _’ mp_tac >>
  rpt(DEEP_INTRO_TAC some_intro >> gvs[]) >>
  rw[]
  >- (drule next_next >>
      disch_then(qspec_then ‘x’ mp_tac) >>
      rw[]) >>
  first_x_assum(qspec_then ‘x’ mp_tac) >> simp[]
QED

Overload  "safe_exp" = “λx. safe_itree (itree_of x)”;

Theorem safe_exp_app_bisim_F_IMP_same_itree:
  ∀e1 e2.
  safe_exp e1 ∧
  safe_exp e2 ∧
  (e1 ≃ e2) F ⇒
  itree_of e1 = itree_of e2
Proof
  rw[itree_of_def] >>
  match_mp_tac no_err_exp_eq_IMP_sem_eq >>
  simp[]
QED

val _ = export_theory();
