(*
  Correctness for compilation that inserts names for Lam NONE and
  replaces HandleApp by a Handle and an App.
 *)
Theory state_namesProof
Ancestors
  string option sum pair list alist finite_map pred_set
  rich_list arithmetic state_cexp mlstring
  state_names state_names_1Proof stateLang[qualified]
Libs
  BasicProvers dep_rewrite


Theorem LESS_EQ_list_max[local]:
  ∀xs n. n ≤ list_max xs ⇔ n = 0 ∨ ∃x. MEM x xs ∧ n ≤ x
Proof
  Induct \\ fs [list_max_def]
  \\ metis_tac []
QED

Theorem give_names_freevars:
  ∀x e n.
    give_names x = (e,n) ⇒
    ∀v. v IN freevars (exp_of x) ⇒ max_name (implode v) ≤ n
Proof
  ho_match_mp_tac give_names_ind \\ rpt strip_tac
  >~ [‘Var’] >-
   (gvs [give_names_def])
  >~ [‘Raise’] >-
   (gvs [give_names_def] \\ pairarg_tac \\ fs [])
  >~ [‘Lam’] >-
   (gvs [give_names_def] \\ pairarg_tac \\ gvs [AllCaseEqs()])
  >~ [‘Let’] >-
   (gvs [give_names_def] \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()]))
  >~ [‘Handle’] >-
   (gvs [give_names_def] \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()]))
  >~ [‘HandleApp’] >-
   (gvs [give_names_def] \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()]))
  >~ [‘If’] >-
   (gvs [give_names_def] \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()]))
  >~ [‘App’] >-
   (gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ metis_tac [PAIR])
  >~ [‘Letrec’] >-
   (gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ res_tac \\ fs [] \\ metis_tac [PAIR])
  >~ [‘Case’] >-
   (gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ gvs [AllCaseEqs()]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [give_names_def,MEM_MAP,LESS_EQ_list_max,PULL_EXISTS,EXISTS_PROD]
    \\ metis_tac [LESS_EQ_REFL,PAIR])
QED

Theorem isStringThere_aux_lemma[local]:
  ∀xs ts ys.
    LENGTH xs ≤ LENGTH ys ⇒
    (isStringThere_aux (strlit (ts ++ xs)) (strlit (ts ++ ys))
        (LENGTH ts) (LENGTH ts) (STRLEN xs) ⇔
     isStringThere_aux (strlit xs) (strlit ys) 0 0 (STRLEN xs))
Proof
  Induct \\ fs [isStringThere_aux_def]
  \\ gen_tac \\ gen_tac
  \\ Cases \\ fs []
  \\ strip_tac \\ fs [EL_LENGTH_APPEND]
  \\ rename [‘LENGTH xs ≤ LENGTH ys’]
  \\ last_x_assum drule \\ strip_tac
  \\ last_assum $ qspec_then ‘[h]’ mp_tac
  \\ last_x_assum $ qspec_then ‘ts ++ [h]’ mp_tac
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [] \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ Cases_on ‘h = h'’ \\ fs []
QED

Theorem isPrefix_thm:
  isPrefix s t ⇔ isPREFIX (explode s) (explode t)
Proof
  fs [isPrefix_def]
  \\ Cases_on ‘s’ \\ Cases_on ‘t’ \\ fs []
  \\ rename [‘LENGTH xs ≤ LENGTH ys’]
  \\ Cases_on ‘LENGTH ys < LENGTH xs’ \\ fs []
  >-
   (CCONTR_TAC \\ fs []
    \\ imp_res_tac rich_listTheory.IS_PREFIX_LENGTH \\ fs [])
  \\ fs [NOT_LESS]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘xs’
  \\ Induct
  \\ fs [isStringThere_aux_def]
  \\ strip_tac \\ Cases \\ fs []
  \\ Cases_on ‘h = h'’ \\ fs []
  \\ gvs [] \\ rw []
  \\ last_x_assum $ drule_then $ rewrite_tac o single o GSYM
  \\ drule isStringThere_aux_lemma
  \\ disch_then $ qspec_then ‘[h]’ mp_tac
  \\ fs []
QED

Theorem max_name_make_name:
  n < max_name (make_name n)
Proof
  fs [make_name_def,max_name_def,isPrefix_thm]
  \\ fs [concat_def]
QED

Theorem compile_rel_give_names:
  ∀x e n.
    give_names x = (e,n) ⇒
    compile_rel (exp_of x) (exp_of e)
Proof
  ho_match_mp_tac give_names_ind \\ rpt strip_tac
  >~ [‘Var’] >-
   (gvs [give_names_def]
    \\ simp [Once compile_rel_cases])
  >~ [‘Let’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases]
    \\ CCONTR_TAC \\ fs []
    \\ drule_all give_names_freevars
    \\ fs [GSYM NOT_LESS,max_name_make_name])
  >~ [‘Lam’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases]
    \\ CCONTR_TAC \\ fs []
    \\ drule_all give_names_freevars
    \\ fs [GSYM NOT_LESS,max_name_make_name])
  >~ [‘Handle’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases])
  >~ [‘HandleApp’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases]
    \\ CCONTR_TAC \\ fs []
    \\ drule_all give_names_freevars
    \\ fs [GSYM NOT_LESS,max_name_make_name])
  >~ [‘If’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases])
  >~ [‘Raise’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases])
  >~ [‘App’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases,MAP_MAP_o]
    \\ simp [pure_miscTheory.LIST_REL_MAP_MAP]
    \\ simp [EVERY_MEM] \\ rw []
    \\ Cases_on ‘give_names x’ \\ fs [])
  >~ [‘Letrec’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ simp [Once compile_rel_cases]
    \\ Induct_on ‘fs’ \\ fs [SF DNF_ss,FORALL_PROD]
    \\ rw [] \\ fs [UNCURRY]
    \\ rpt $ last_x_assum drule
    \\ fs [] \\ rw []
    \\ simp [Once compile_rel_cases,MAP_MAP_o]
    \\ Cases_on ‘give_names p_2’ \\ fs [])
  >~ [‘Case’] >-
   (gvs [give_names_def]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ gvs [AllCaseEqs()]
    \\ simp [Once compile_rel_cases]
    \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
    \\ Induct_on ‘rows’ \\ fs [SF DNF_ss,FORALL_PROD]
    \\ rw [] \\ fs [UNCURRY]
    \\ rpt $ last_x_assum drule
    \\ fs [] \\ rw []
    \\ rename [‘give_names pp’]
    \\ Cases_on ‘give_names pp’ \\ fs [])
QED

Theorem itree_of_give_all_names:
  itree_of (exp_of e1) ---> itree_of (exp_of (give_all_names e1))
Proof
  fs [give_all_names_def]
  \\ Cases_on ‘give_names e1’
  \\ drule_then assume_tac compile_rel_give_names
  \\ drule compile_rel_itree_of \\ fs []
QED

Theorem give_names_cexp_wwf:
    ∀x e n.
    give_names x = (e,n) ⇒
    cexp_wwf x ⇒ cexp_wf e
Proof
  ho_match_mp_tac give_names_ind \\ rpt strip_tac
  >~[‘Var’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ rw [cexp_wf_def])
  >~[‘Lam vn’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ pairarg_tac \\ fs []
      \\ Cases_on ‘vn’ \\ fs []
      \\ rw [cexp_wf_def])
  >~[‘Let vn’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ Cases_on ‘vn’ \\ fs [cexp_wf_def]
      \\ pairarg_tac \\ fs [cexp_wf_def]
      \\ pairarg_tac \\ fs [cexp_wf_def]
      \\ rw [cexp_wf_def])
  >~[‘App’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ rw [cexp_wf_def, EVERY_MEM, MEM_MAP]
      \\ last_x_assum $ drule_then assume_tac
      \\ rename1 ‘give_names a’
      \\ Cases_on ‘give_names a’ \\ fs [EVERY_MEM])
  >~[‘Handle’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cexp_wf_def])
  >~[‘HandleApp’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cexp_wf_def, op_args_ok_def])
  >~[‘If’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cexp_wf_def])
  >~[‘Raise’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ pairarg_tac \\ fs []
      \\ rw [cexp_wf_def])
  >~[‘Letrec’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ pairarg_tac \\ fs []
      \\ rw [cexp_wf_def]
      >- (gs [EVERY_EL, EL_MAP, EL_MAP2, MEM_EL, PULL_EXISTS]
          \\ rw []
          \\ last_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      \\ ‘∀l1 l2 : mlstring list. ALL_DISTINCT l1 ∧ l1 = l2 ⇒ ALL_DISTINCT l2’ by simp []
      \\ pop_assum $ dxrule_then irule
      \\ irule LIST_EQ
      \\ simp [EL_MAP, EL_MAP2]
      \\ rw []
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [])
  >~[‘Case _ rows d’]
  >- (fs [give_names_def, cexp_wwf_def]
      \\ Cases_on ‘d’ \\ fs []
      \\ rw [cexp_wf_def]
      >- (Cases_on ‘rows’ \\ fs [])
      >- (‘∀l1 l2 : mlstring list. ALL_DISTINCT l1 ∧ l1 = l2 ⇒ ALL_DISTINCT l2’ by simp []
          \\ pop_assum $ dxrule_then irule
          \\ irule LIST_EQ
          \\ simp [EL_MAP, EL_MAP2]
          \\ rw []
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      >- (gs [EVERY_EL, EL_MAP, EL_MAP2, MEM_EL, PULL_EXISTS]
          \\ rw []
          \\ first_x_assum $ drule_then assume_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cexp_wf_def]
      >- (Cases_on ‘rows’ \\ fs [])
      >- (‘∀l1 l2 : mlstring list. ALL_DISTINCT l1 ∧ l1 = l2 ⇒ ALL_DISTINCT l2’ by simp []
          \\ pop_assum $ dxrule_then irule
          \\ AP_THM_TAC \\ AP_TERM_TAC
          \\ irule LIST_EQ
          \\ simp [EL_MAP, EL_MAP2]
          \\ rw []
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      >- (gs [EVERY_EL, EL_MAP, EL_MAP2, MEM_EL, PULL_EXISTS]
          \\ rw []
          \\ first_x_assum $ drule_then assume_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []))
QED

Theorem give_names_cns_arities:
    ∀x e n.
    give_names x = (e,n) ⇒
    cns_arities e = cns_arities x
Proof
  ho_match_mp_tac give_names_ind \\ rpt strip_tac
  \\ gs [give_names_def]
  >~[‘Lam vn’]
  >- (Cases_on ‘vn’ \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cns_arities_def])
  >~[‘Let vn’]
  >- (Cases_on ‘vn’ \\ fs []
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cns_arities_def])
  >~[‘App’]
  >- (rw [cns_arities_def]
      \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
      \\ irule LIST_EQ
      \\ gs [MEM_EL, PULL_EXISTS, EL_MAP]
      \\ gen_tac \\ strip_tac
      \\ first_x_assum $ drule_then assume_tac
      \\ first_x_assum irule
      \\ irule_at Any $ GSYM PAIR)
  >~[‘Handle’]
  >- (pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cns_arities_def])
  >~[‘HandleApp’]
  >- (pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cns_arities_def, UNION_COMM])
  >~[‘If’]
  >- (pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cns_arities_def])
  >~[‘Raise’]
  >- (pairarg_tac \\ fs []
      \\ rw [cns_arities_def])
  >~[‘Letrec’]
  >- (pairarg_tac \\ fs []
      \\ rw [cns_arities_def]
      \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ AP_TERM_TAC \\ AP_TERM_TAC
      \\ irule LIST_EQ
      \\ gs [MEM_EL, PULL_EXISTS, EL_MAP, EL_MAP2]
      \\ rw []
      \\ first_x_assum $ drule_then assume_tac
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [])
  >~[‘Case _ rows d’]
  >- (Cases_on ‘d’ \\ fs []
      \\ rw [cns_arities_def]
      >- (MK_COMB_TAC
          >- (AP_TERM_TAC \\ fs []
              \\ AP_TERM_TAC
              \\ irule LIST_EQ
              \\ fs [MEM_EL, EL_MAP, EL_MAP2, PULL_EXISTS]
              \\ rw []
              \\ last_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ fs []
              \\ pairarg_tac \\ fs []
              \\ pairarg_tac \\ fs [])
          \\ AP_TERM_TAC \\ AP_TERM_TAC
          \\ irule LIST_EQ
          \\ fs [MEM_EL, EL_MAP, EL_MAP2, PULL_EXISTS]
          \\ rw []
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      \\ CASE_TAC \\ fs []
      \\ pairarg_tac \\ fs []
      \\ rw [cns_arities_def]
      \\ MK_COMB_TAC
      >- (AP_TERM_TAC
          \\ AP_THM_TAC \\ AP_TERM_TAC
          \\ AP_TERM_TAC \\ AP_TERM_TAC
          \\ irule LIST_EQ
          \\ fs [MEM_EL, EL_MAP, EL_MAP2, PULL_EXISTS]
          \\ rw []
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      \\ AP_TERM_TAC \\ AP_TERM_TAC
      \\ irule LIST_EQ
      \\ fs [MEM_EL, EL_MAP, EL_MAP2, PULL_EXISTS]
      \\ rw []
      \\ last_x_assum $ drule_then assume_tac
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [])
QED

Theorem give_all_names_cexp_wf:
  cexp_wwf x ⇒
  cexp_wf (give_all_names x) ∧
  cns_arities (give_all_names x) = cns_arities x
Proof
  fs [give_all_names_def]
  \\ Cases_on ‘give_names x’
  \\ drule_then assume_tac give_names_cexp_wwf
  \\ drule_then assume_tac give_names_cns_arities
  \\ fs []
QED
