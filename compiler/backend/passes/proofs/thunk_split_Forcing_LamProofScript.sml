
Theory thunk_split_Forcing_LamProof
Ancestors
  pair list string option sum pair list alist finite_map pred_set
  rich_list wellorder arithmetic mlmap mlstring var_set
  thunk_cexp pure_misc thunkLangProps thunkLang
  thunkLang_primitives thunk_cexp thunk_exp_of thunk_semantics
  thunk_NRC_Forcing_Lambdas var_set thunk_split_Forcing_Lam
Libs
  term_tactic dep_rewrite


(* TODO move *)
Theorem list_size_MAP:
  ∀l f g. list_size f (MAP g l) = list_size (f o g) l
Proof
  Induct >> gs [list_size_def]
QED

(* TODO move *)
Theorem in_freevars_Disj:
  ∀l n x. x ∈ freevars (Disj n l) ⇒ x = n
Proof
  Induct >> gs [FORALL_PROD, Disj_def, freevars_def] >>
  rw [] >> gs []
QED

(* TODO move *)
Theorem freevars_lets_for:
  ∀l v n x len. freevars (lets_for len v n (MAPi (λi v. (i, v)) l) x) DELETE n = freevars x DIFF (n INSERT set l)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND, freevars_def]
  \\ simp [SET_EQ_SUBSET, SUBSET_DEF]
  \\ rw [] \\ simp []
QED

(* TODO move *)
Theorem freevars_rows_of:
  ∀rows n eopt.
    rows ≠ [] ⇒
    freevars (rows_of n rows eopt) =
    {n}
    ∪ BIGUNION (set (MAP (λ(_, vs, e). freevars e DIFF set vs) rows))
    ∪ (case eopt of NONE => {} | SOME (_, e) => freevars e)
Proof
  Induct >> simp [FORALL_PROD, rows_of_def, freevars_def] >>
  rename1 ‘rows_of _ rows _’ >>
  Cases_on ‘rows = []’
  >- (simp [rows_of_def] >>
      simp [SET_EQ_SUBSET, SUBSET_DEF] >> rw [] >>
      rename1 ‘x = n ∨ _’ >> Cases_on ‘x = n’ >> simp []
      >- (rename1 ‘lets_for (LENGTH l) m n (MAPi _ l) e’ >>
          qspecl_then [‘l’, ‘m’, ‘n’, ‘e’, ‘LENGTH l’] assume_tac freevars_lets_for >>
          gs [SET_EQ_SUBSET, SUBSET_DEF])
      >- (CASE_TAC >> gs [freevars_def] >>
          CASE_TAC >> gs [freevars_def] >>
          dxrule_then assume_tac in_freevars_Disj >> gs [])
      >- (rename1 ‘lets_for (LENGTH l) m n (MAPi _ l) e’ >>
          qspecl_then [‘l’, ‘m’, ‘n’, ‘e’, ‘LENGTH l’] assume_tac freevars_lets_for >>
          gs [SET_EQ_SUBSET, SUBSET_DEF])
      >- (CASE_TAC >> gs [] >>
          CASE_TAC >> gs [freevars_def])) >>
  gs [] >>
  last_x_assum kall_tac >>
  rw [SET_EQ_SUBSET, SUBSET_DEF] >> gs [] >>
  rename1 ‘x = n ∨ _’ >> Cases_on ‘x = n’ >> simp [] >>
  rename1 ‘lets_for (LENGTH l) m n (MAPi _ l) e’ >>
  qspecl_then [‘l’, ‘m’, ‘n’, ‘e’, ‘LENGTH l’] assume_tac freevars_lets_for >>
  gs [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem extract_names_soundness_lemma:
  (∀e. cexp_wf e ⇒
    set_of (extract_names e) = freevars (exp_of e) ∧ vars_ok (extract_names e)) ∧
  (∀s l. vars_ok s ∧ EVERY cexp_wf l ⇒
    set_of (extract_names_list s l) =
      set_of s ∪ BIGUNION (set $ MAP (λce. freevars (exp_of ce)) l) ∧
    vars_ok (extract_names_list s l)) ∧
  (∀s css. vars_ok s ∧ EVERY cexp_wf (MAP (SND o SND) css) ⇒
    set_of (extract_names_rows s css) = set_of s ∪
      BIGUNION (set $
        MAP (λ(cn,vs,ce). freevars (exp_of ce) DIFF set (MAP explode vs)) css) ∧
    vars_ok (extract_names_rows s css))
Proof
  ho_match_mp_tac extract_names_ind >>
  rw[extract_names_def, exp_of_def, freevars_def, cexp_wf_def,
     freevars_Lams, freevars_Apps, freevars_rows_of] >>
  gvs[SF ETA_ss, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  >- (
    `EVERY cexp_wf (MAP SND xs)` by (
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]) >>
    gvs[] >> simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
    )
  >- (
    `EVERY cexp_wf (MAP SND xs)` by (
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]) >>
    gvs[] >> simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
    )
  >- gvs[DELETE_DEF]
  >- (
    `EVERY cexp_wf (MAP (λ(cn,vars,ce). ce) css)` by (
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]) >>
    gvs[] >> Cases_on `eopt` >> gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rpt (pairarg_tac >> gvs[])
    >- (DEP_REWRITE_TAC[set_of_insert_var] >> gvs[] >> rw[Once INSERT_SING_UNION])
    >- (rw[Once INSERT_SING_UNION] >> simp[AC UNION_ASSOC UNION_COMM])
    )
  >- (
    `EVERY cexp_wf (MAP (λ(cn,vars,ce). ce) css)` by (
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]) >>
    DEP_REWRITE_TAC[vars_ok_insert_var] >>
    Cases_on `eopt` >> gvs[] >> PairCases_on `x` >> gvs[]
    )
  >- gvs[AC UNION_ASSOC UNION_COMM]
  >- gvs[AC UNION_ASSOC UNION_COMM]
QED

Theorem thunk_names_soundness:
  cexp_wf e ⇒
    set_of (thunk_names e) = freevars (exp_of e) ∧ vars_ok (thunk_names e)
Proof
  rw[thunk_names_def, extract_names_soundness_lemma]
QED

Theorem boundvars_to_lets_force:
  ∀l e v. v ∈ boundvars e ⇒ v ∈ boundvars (lets_force l e)
Proof
  Induct >> gs [lets_force_def, FORALL_PROD] >>
  rw [] >> last_x_assum irule >>
  simp [boundvars_def]
QED

Theorem freevars_to_lets_force:
  ∀l e v. v ∈ freevars e ⇒ v ∈ freevars (lets_force l e) ∨ v ∈ boundvars (lets_force l e)
Proof
  Induct >> gs [lets_force_def, FORALL_PROD] >>
  rw [] >>
  rename1 ‘Let (SOME p1) (Force (Var p2)) e’ >>
  rename1 ‘v ∈ _’ >>
  Cases_on ‘v ∈ freevars (Let (SOME p1) (Force (Var p2)) e)’ >> gs [] >>
  disj2_tac >>
  irule boundvars_to_lets_force >>
  gs [boundvars_def, freevars_def]
QED

Theorem in_freevars_lets_force:
  ∀l e v. v ∈ freevars (lets_force l e) ⇒ v ∈ freevars e ∨ MEM v (MAP SND l)
Proof
  Induct >> gs [lets_force_def, FORALL_PROD] >>
  rw [] >>
  last_x_assum $ dxrule_then assume_tac >>
  gs [freevars_def]
QED

Theorem FEQUAL:
  ∀a b c. b = c ⇒ a b = a c
Proof
  simp []
QED

Theorem FEQUAL2:
  ∀a b c. b = c ⇒ b a = c a
Proof
  simp []
QED

Theorem IMP_MEM_FILTER_merge_inside:
  ∀l1 bL1 l2 bL2 v.
    MEM v l2 ∧
    LENGTH l1 = LENGTH bL1 ∧
    LENGTH l2 = LENGTH (FILTER FST (ZIP (bL1, l1)))
    ⇒ MEM v (MAP SND (FILTER FST (ZIP (bL1, merge_inside l1 bL1 l2))))
Proof
  Induct >> simp [merge_inside_def] >>
  gen_tac >> Cases >> simp [] >>
  IF_CASES_TAC >> gs []
  >- (Cases >> simp [merge_inside_def, PULL_EXISTS] >>
      rw [] >>
      disj2_tac >> last_x_assum $ drule_then irule >>
      gs []) >>
  simp [merge_inside_def, PULL_EXISTS]
QED

Theorem EQ_LENGTH_FILTER_ZIP:
  ∀bL l1 l2.
    LENGTH l1 = LENGTH l2 ∧ LENGTH bL = LENGTH l1
    ⇒ LENGTH (FILTER FST (ZIP (bL, l1))) = LENGTH (FILTER FST (ZIP (bL, l2)))
Proof
  Induct >> simp [] >>
  Cases >> simp [] >>
  Cases >> simp [] >>
  Cases >> simp []
QED

Theorem find_forcing_soundness:
  ∀l e l1 l2 bL e2 s b1 b2 s2.
    find_forcing l e = (l1, l2, bL, e2, s, b1, b2, s2) ∧ cexp_wf e ⇒
    ∃l3 bL2.
      cexp_wf e2 ∧
      l1 = MAP SND (FILTER FST (ZIP (bL2, l))) ∧
      LENGTH l = LENGTH bL ∧
      (∀v. v ∈ freevars (exp_of e2) ∪ boundvars (exp_of e2) ⇒ v ∈ freevars (exp_of e) ∪ boundvars (exp_of e)) ∧
      (∀v. MEM v l3 ⇒ explode v ∈ boundvars (exp_of e)) ∧
      LIST_REL (λb2 b. b2 ⇒ b) bL2 bL ∧
      LIST_REL (λ(b, b2) v. b ⇒ (b2 ⇔ v ∈ freevars (exp_of e2))) (ZIP (bL, bL2)) (MAP explode l) ∧
      LENGTH l3 = LENGTH (FILTER FST (ZIP (bL, l))) ∧
      vars_ok s2 ∧ set_of s2 = set (MAP explode l3) ∪ set (MAP explode l) ∧
      (b1 ⇔ MEM T bL) ∧
      (b2 ⇒ ALL_DISTINCT (l ++ l3)) ∧
      (exp_of e) = lets_force (REVERSE (ZIP (MAP explode $ MAP SND (FILTER FST (ZIP (bL, l2))),
                                             MAP explode $ MAP SND (FILTER FST (ZIP (bL, l))))))
                               (exp_of e2) ∧
      set_of s = freevars (exp_of e2) ∧ vars_ok s ∧
      l2 = merge_inside l bL l3
Proof
  Induct
  >- (Cases >> gs [find_forcing_def, lets_force_def, thunk_names_soundness, merge_inside_def, cexp_wf_def]) >>
  gen_tac >> Cases >> rpt gen_tac >> strip_tac >>
  gvs [find_forcing_def, lets_force_def, thunk_names_soundness, merge_inside_def,
      thunk_Forcing_LambdasTheory.FILTER_FST_ZIP_K_F, merge_inside_K_F, cexp_wf_def, PULL_EXISTS]
  >>~-([‘LIST_REL _ _ (MAP (K F) l)’], qexists_tac ‘MAP (K F) l’ >>
               gs [thunk_Forcing_LambdasTheory.FILTER_FST_ZIP_K_F, LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MEM_MAP]) >>
  rename1 ‘find_forcing (h::l) (Let opt x y)’ >>
  Cases_on ‘x’ >>
  gvs [find_forcing_def, lets_force_def, thunk_names_soundness, merge_inside_def,
      thunk_Forcing_LambdasTheory.FILTER_FST_ZIP_K_F, merge_inside_K_F, cexp_wf_def, PULL_EXISTS]
  >>~-([‘LIST_REL _ _ (MAP (K F) l)’], qexists_tac ‘MAP (K F) l’ >>
               gs [thunk_Forcing_LambdasTheory.FILTER_FST_ZIP_K_F, LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MEM_MAP]) >>
  Cases_on ‘opt’ >>
  gvs [find_forcing_def, lets_force_def, thunk_names_soundness, merge_inside_def,
      thunk_Forcing_LambdasTheory.FILTER_FST_ZIP_K_F, merge_inside_K_F, cexp_wf_def, PULL_EXISTS]
  >>~-([‘LIST_REL _ _ (MAP (K F) l)’], qexists_tac ‘MAP (K F) l’ >>
               gs [thunk_Forcing_LambdasTheory.FILTER_FST_ZIP_K_F, LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MEM_MAP]) >>
  rename1 ‘find_forcing (h::l) (Let (SOME h2) (Force e) y)’ >>
  Cases_on ‘e’ >>
  gvs [find_forcing_def, lets_force_def, thunk_names_soundness, merge_inside_def,
      thunk_Forcing_LambdasTheory.FILTER_FST_ZIP_K_F, merge_inside_K_F, cexp_wf_def, PULL_EXISTS]
  >>~-([‘LIST_REL _ _ (MAP (K F) l)’], qexists_tac ‘MAP (K F) l’ >>
               gs [thunk_Forcing_LambdasTheory.FILTER_FST_ZIP_K_F, LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MEM_MAP]) >>
  qpat_x_assum ‘_ _ = (_, _, _, _, _, _, _, _)’ mp_tac >>
  IF_CASES_TAC
  >- (pairarg_tac >> rw [] >>
      last_x_assum $ dxrule_then assume_tac >>
      gs [lets_force_APPEND, lets_force_def, PULL_EXISTS, merge_inside_def] >>
      Q.REFINE_EXISTS_TAC ‘_::_’ >> gs [contains_var_in_set_of, merge_inside_def] >>
      irule_at (Pos last) EQ_REFL >>
      irule_at (Pos hd) EQ_REFL
      >- (simp [freevars_def, boundvars_def] >>
          rw []
          >- (rename1 ‘freevars (lets_force big_list _)’ >>
              dxrule_then (qspec_then ‘big_list’ assume_tac) freevars_to_lets_force >>
              gs [])
          >- (dxrule_then assume_tac boundvars_to_lets_force >> gs [])
          >- (‘∀v : string s1 s2. v ∈ s2 ∧ s1 = s2 ⇒ v ∈ s1’ by simp [] >>
              disj1_tac >> pop_assum irule >>
              irule_at (Pos hd) FEQUAL >>
              irule_at (Pos hd) FEQUAL2 >> irule_at (Pos hd) FEQUAL >>
              irule_at Any REVERSE_ZIP >>
              conj_asm1_tac
              >- (simp [] >>
                  irule EQ_LENGTH_FILTER_ZIP >>
                  simp [LENGTH_merge_inside]) >>
              simp [boundvars_lets_force] >>
              disj2_tac >>
              irule $ iffRL MEM_MAP >> irule_at Any EQ_REFL >>
              irule IMP_MEM_FILTER_merge_inside >>
              simp [])
          >- simp [set_of_insert_var, vars_ok_insert_var, SET_EQ_SUBSET, SUBSET_DEF]
          >- gs [MEM_MAP]
          >- gs [MEM_MAP]
          >- gs [ALL_DISTINCT_APPEND, MEM_MAP])
      >- (simp [freevars_def, boundvars_def] >>
          rw []
          >- (rename1 ‘freevars (lets_force big_list _)’ >>
              dxrule_then (qspec_then ‘big_list’ assume_tac) freevars_to_lets_force >>
              gs [])
          >- (dxrule_then assume_tac boundvars_to_lets_force >> gs [])
          >- (‘∀v : string s1 s2. v ∈ s2 ∧ s1 = s2 ⇒ v ∈ s1’ by simp [] >>
              disj1_tac >> pop_assum irule >>
              irule_at (Pos hd) FEQUAL >>
              irule_at (Pos hd) FEQUAL2 >> irule_at (Pos hd) FEQUAL >>
              irule_at Any REVERSE_ZIP >>
              conj_asm1_tac
              >- (simp [] >>
                  irule EQ_LENGTH_FILTER_ZIP >>
                  simp [LENGTH_merge_inside]) >>
              simp [boundvars_lets_force] >>
              disj2_tac >>
              irule $ iffRL MEM_MAP >> irule_at Any EQ_REFL >>
              irule IMP_MEM_FILTER_merge_inside >>
              simp [])
          >- simp [set_of_insert_var, vars_ok_insert_var, SET_EQ_SUBSET, SUBSET_DEF]
          >- gs [MEM_MAP]
          >- gs [MEM_MAP]
          >- gs [ALL_DISTINCT_APPEND, MEM_MAP]))
  >- (pairarg_tac >> rw [] >> simp [cexp_wf_def, PULL_EXISTS] >>
      last_x_assum $ dxrule_then assume_tac >> gs [merge_inside_def, cexp_wf_def] >>
      irule_at (Pos last) EQ_REFL >> simp [] >>
      irule_at (Pos hd) EQ_REFL >> simp [] >> rw []
      >- (rename1 ‘freevars (lets_force big_list _)’ >>
          dxrule_then (qspec_then ‘big_list’ assume_tac) freevars_to_lets_force >>
          gs [])
      >- (dxrule_then assume_tac boundvars_to_lets_force >> gs [])
      >- simp [SET_EQ_SUBSET, SUBSET_DEF]
      >- gs [contains_var_in_set_of, MEM_MAP]
      >- gs [contains_var_in_set_of, MEM_MAP])
QED

Theorem exp_rel_Lams:
  ∀l s x y. exp_rel s (Lams l x) (Lams l y) ⇔ exp_rel s x y
Proof
  Induct >> gs [exp_rel_def]
QED

Theorem my_function_Let_NONE:
  ∀x y s. my_function s (Let NONE x y) =
          let (s, x) = my_function s x in
            let (s, y) = my_function s y in
              (s, Let NONE x y)
Proof
  Cases >> simp [Once my_function_def]
QED

Definition dest_Lam_def:
  dest_Lam (thunk_cexp$Lam l e) = SOME e ∧
  dest_Lam e = NONE
End

Theorem my_function_test1:
  SND (my_function (insert_vars empty_vars [«f»; «x»; «x2»])
       (Let (SOME «f») (Lam [«x»] (Var «x»)) (Var «f»)))
  = (Let (SOME «f») (Lam [«x»] (Var «x»)) (Var «f»))
Proof
  EVAL_TAC
QED

Theorem find_forcing_test:
  find_forcing (REV [«x»] [])
       (Let (SOME «y») (Force (Var «x»)) (Var «y»))
  = ([],[«y»],[T],Var «y»,(Map compare (Bin 1 «y» () Tip Tip),1),T,T,
     Map compare (Bin 2 «x» () Tip (Bin 1 «y» () Tip Tip)),1)
Proof
  EVAL_TAC
QED

(*Theorem my_function_test:
  SND (my_function (insert_vars empty_vars [«f»; «x»; «y»])
       (Let (SOME «f») (Lam [«x»] (Let (SOME «y») (Force (Var «x»)) (Var «y»))) (Var «f»)))
  = Let (SOME «f») (Lam [«x»] (Let (SOME «y») (Force (Var «x»)) (Var «y»))) (Var «f»)
Proof
  simp [my_function_def, find_forcing_test] >>
  simp [check_hypothesis_def] >>
  simp [REV_REVERSE_LEM, contains_var_def, insert_vars_def, insert_var_def, lookup_def, empty_vars_def] >>
  simp [empty_def, insert_def, balanced_mapTheory.lookup_def, balanced_mapTheory.empty_def,
        balanced_mapTheory.insert_def, compare_def] >>
  simp [compare_aux_def]
   EVAL_TAC
QED*)

Theorem my_function_Let_SOME_dLam_is_NONE:
  ∀x y v s. dest_Lam x = NONE ⇒
          my_function s (Let (SOME v) x y) =
          let (s, x) = my_function s x in
            let (s, y) = my_function s y in
              (s, Let (SOME v) x y)
Proof
  Cases >> simp [Once my_function_def, dest_Lam_def]
QED

Theorem REV_NOT_EMPTY:
  ∀l1 l2. REV l1 l2 = [] ⇒ l1 = [] ∧ l2 = []
Proof
  Induct >> gs [REV_DEF] >>
  rw [] >> strip_tac >>
  last_x_assum $ dxrule_then assume_tac >> gs []
QED

Theorem REV_merge_inside:
  ∀l bL l3.
    merge_inside l bL l3 = [] ∧ LENGTH l3 = LENGTH (FILTER FST (ZIP (bL, l))) ∧ LENGTH l = LENGTH bL ⇒
    l = []
Proof
  Induct >> simp [] >>
  gen_tac >> Cases >> simp [] >>
  IF_CASES_TAC >> simp [merge_inside_def] >>
  Cases >> simp [merge_inside_def]
QED

Theorem exp_rel_Let_Lams_combine_bis:
  ∀set v1 v2 vL vL1 vL2 vL3 vL4 bL bL2 x1 x2 y1 y2 expr1 expr2.
    LENGTH vL = LENGTH bL ∧ MEM T bL ∧
    vL1 = MAP SND (FILTER FST (ZIP (bL, vL))) ∧
    LENGTH vL2 = LENGTH vL1 ∧
    vL3 = MAP SND (FILTER FST (ZIP (bL2, vL))) ∧
    LIST_REL (λ(b, b2) v. b ⇒ (b2 ⇔ v ∈ freevars x1)) (ZIP (bL, bL2)) vL ∧
    LIST_REL (λb2 b. b2 ⇒ b) bL2 bL ∧
    v2 ∉ set ∧
    v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧
    v2 ∉ boundvars x1 ∧ v2 ∉ boundvars y1 ∧
    ALL_DISTINCT (v1::v2::vL ++ vL2) ∧
    vL4 = merge_inside vL bL vL2 ∧
    exp_rel (set ∪ {v2}) x1 x2 ∧ exp_rel (set ∪ {v2}) y1 y2 ∧
    expr1 = (Let (SOME v1)
             (Lams vL (lets_force (ZIP (vL2, vL1)) x1)) y1) ∧
    expr2 = (Let (SOME v2)
             (Lams (vL3 ++ vL4) x2)
             (Let (SOME v1)
              (Lams vL (Apps (Var v2) (MAP Var vL3 ++
                                       MAP2 (λb e. if b then Force e else e)
                                            bL (MAP Var vL)))) y2)) ⇒
    exp_rel set expr1 expr2
Proof
  rw [] >> irule exp_rel_Let_Lams_combine >> simp [] >>
  rpt $ first_x_assum $ irule_at Any >>
  simp []
QED

Theorem exp_rel_lets_force_left:
  ∀l c e set. exp_rel set c (lets_force l e) ⇒ ∃e1. c = lets_force l e1 ∧ exp_rel set e1 e
Proof
  Induct >> gs [lets_force_def, FORALL_PROD] >>
  rw [] >> last_x_assum $ dxrule_then assume_tac >>
  gs [] >>
  rename1 ‘exp_rel _ e1 _’ >>
  Cases_on ‘e1’ >> gs [exp_rel_def]
  >- (rename1 ‘exp_rel _ e1 (Force _)’ >>
      Cases_on ‘e1’ >> gs [exp_rel_def] >>
      rename1 ‘exp_rel _ e1 (Var _)’ >>
      Cases_on ‘e1’ >> gs [exp_rel_def] >>
      metis_tac []) >>
  rename1 ‘Force _ = Lams (l1 ++ merge_inside vL bL vL2) _’ >>
  Cases_on ‘l1’ >> gs [] >>
  Cases_on ‘vL’ >> Cases_on ‘bL’ >> gs []
  >- (Cases_on ‘vL2’ >> gs [merge_inside_def]) >>
  rename1 ‘merge_inside _ (h2::_) vL2’ >>
  Cases_on ‘h2’ >> gs [merge_inside_def] >>
  Cases_on ‘vL2’ >> gs [merge_inside_def]
QED

Theorem MAP_FILTER_ZIP:
  ∀bL vL f. LENGTH bL = LENGTH vL ⇒
            MAP f (MAP SND (FILTER FST (ZIP (bL, vL)))) = MAP SND (FILTER FST (ZIP (bL, MAP f vL)))
Proof
  Induct >> gs [] >>
  Cases >> Cases >> gs []
QED

Theorem merge_inside_APPEND:
  ∀vL bL l2 vL' bL' l2'.
    LENGTH l2 = LENGTH (FILTER FST (ZIP (bL, vL))) ∧ LENGTH bL = LENGTH vL
    ⇒ merge_inside (vL ++ vL') (bL ++ bL') (l2 ++ l2')
      = merge_inside vL bL l2 ++ merge_inside vL' bL' l2'
Proof
  Induct >> gs [merge_inside_def] >>
  gen_tac >> Cases >> gs [] >>
  IF_CASES_TAC >> gs [merge_inside_def] >>
  Cases >> gs [merge_inside_def]
QED

Theorem REVERSE_merge_inside:
  ∀vL bL l2. LENGTH l2 = LENGTH (FILTER FST (ZIP (bL, vL))) ∧ LENGTH bL = LENGTH vL ⇒
             REVERSE (merge_inside vL bL l2) = merge_inside (REVERSE vL) (REVERSE bL) (REVERSE l2)
Proof
  Induct >> gs [merge_inside_def] >>
  gen_tac >> Cases >> gs [] >>
  IF_CASES_TAC >> gs [merge_inside_def]
  >- (Cases >> rw [merge_inside_def] >>
      irule EQ_TRANS >>
      irule_at (Pos last) $ GSYM merge_inside_APPEND >>
      gs [merge_inside_def, GSYM REVERSE_ZIP, FILTER_REVERSE]) >>
  rw [merge_inside_def] >>
  irule EQ_TRANS >>
  irule_at (Pos last) EQ_TRANS >>
  irule_at (Pos hd) $ GSYM merge_inside_APPEND >>
  irule_at (Pos last) FEQUAL >>
  rename1 ‘[h] = merge_inside _ _ _’ >>
  qexists_tac ‘[h]’ >> qexists_tac ‘[]’ >> qexists_tac ‘[F]’ >>
  gs [merge_inside_def, GSYM REVERSE_ZIP, FILTER_REVERSE]
QED

Theorem MAP_merge_inside:
  ∀bL vL l2 f. LENGTH l2 = LENGTH (FILTER FST (ZIP (bL, vL))) ∧ LENGTH bL = LENGTH vL ⇒
               MAP f (merge_inside vL bL l2) = merge_inside (MAP f vL) bL (MAP f l2)
Proof
  Induct >> gs [merge_inside_def] >>
  Cases >> Cases >> gs [merge_inside_def] >>
  Cases >> gs [merge_inside_def]
QED

Theorem check_hypothesis_soundness:
  ∀b v s l1 l2. check_hypothesis b v s ⇒ b ∧ (vars_ok s ⇒ explode v ∉ set_of s)
Proof
  simp [check_hypothesis_def] >>
  rw [] >> gs [contains_var_in_set_of]
QED

Theorem MEM_MAP_ZIP:
  ∀l1 l2 x. MEM x (MAP SND (ZIP (l1, l2))) ∧ LENGTH l1 = LENGTH l2 ⇒ MEM x l2
Proof
  rw [] >> gs [MAP_ZIP]
QED

Theorem my_function_list_lemma:
  ∀l s l2 s2. my_function_list s l = (s2, l2) ∧
              (∀e. cexp_size e < list_size cexp_size l ⇒
                   ∀s. vars_ok s ∧ freevars (exp_of e) ⊆ set_of s ∧ cexp_wf e ∧ boundvars (exp_of e) ⊆ set_of s ⇒
                       ∀s2 e2. (s2, e2) = my_function s e ⇒
                               cexp_wf e2 ∧
                               vars_ok s2 ∧ set_of s ⊆ set_of s2 ∧ boundvars (exp_of e2) ⊆ set_of s2 ∧
                               freevars (exp_of e2) ⊆ set_of s2 ∧
                               (∀s3. DISJOINT s3 (boundvars (exp_of e2) ∪ freevars (exp_of e2))
                                     ⇒ exp_rel s3 (exp_of e) (exp_of e2))) ⇒
              vars_ok s ∧
              EVERY (λe. freevars (exp_of (e)) ⊆ set_of s ∧ cexp_wf e ∧ boundvars (exp_of e) ⊆ set_of s) l
              ⇒ vars_ok s2 ∧ set_of s ⊆ set_of s2 ∧
                EVERY (λe. freevars (exp_of (e)) ⊆ set_of s2 ∧ cexp_wf e ∧ boundvars (exp_of e) ⊆ set_of s2) l2 ∧
                (∀s3. EVERY (λe2. DISJOINT s3 (boundvars (exp_of e2) ∪ freevars (exp_of e2))) l2
                      ⇒ LIST_REL (λe e2. exp_rel s3 (exp_of e) (exp_of e2)) l l2)
Proof
  Induct >> simp [my_function_def, PULL_EXISTS] >>
  rpt $ gen_tac >>
  pairarg_tac >>
  rename [‘my_function_list _ l’, ‘my_function s h = (s', hd')’] >>
  asm_rewrite_tac [PairedLambda.PAIRED_BETA_CONV $
                    Term ‘(λ(s',hd'). (λ(s'',tl'). (s'',hd'::tl')) (my_function_list s' l)) (s',hd')’] >>
  pairarg_tac >>
  last_x_assum $ drule_then assume_tac >>
  rename1 ‘my_function_list s' l = (s'', tl')’ >>
  asm_rewrite_tac [PairedLambda.PAIRED_BETA_CONV $ Term ‘(λ(s'',tl'). (s'',hd'::tl')) (s'', tl')’] >>
  strip_tac >> strip_tac >>
  first_assum $ qspec_then ‘h’ mp_tac >>
  impl_tac >- simp [list_size_def] >>
  disch_then $ qspec_then ‘s’ mp_tac >>
  impl_tac >- simp [] >>
  disch_then $ qspecl_then [‘s'’, ‘hd'’] mp_tac >>
  impl_tac >- simp [] >> strip_tac >>
  qpat_x_assum ‘_ ⇒ _’ mp_tac >> impl_tac
  >- (reverse conj_tac
      >- (gs [EVERY_CONJ, EVERY_MEM] >>
          rpt $ strip_tac >> rpt $ first_x_assum $ drule_then assume_tac >>
          irule SUBSET_TRANS >>
          first_x_assum $ irule_at $ Pos hd >> simp []) >>
      gen_tac >> rename1 ‘cexp_size e < list_size _ _’ >>
      first_x_assum $ qspec_then ‘e’ assume_tac >>
      strip_tac >> qpat_x_assum ‘_ ⇒ _’ mp_tac >> impl_tac
      >- simp [list_size_def] >>
      strip_tac >> gen_tac >> strip_tac >> first_x_assum drule >>
      rename1 ‘my_function s3 e’ >> Cases_on ‘my_function s3 e’ >> simp []) >>
  strip_tac >> gs [] >>
  conj_tac
  >- (irule SUBSET_TRANS >> first_x_assum $ irule_at $ Pos hd >> simp []) >>
  qpat_x_assum ‘_::_ = _’ assume_tac >>
  dxrule_then assume_tac EQ_SYM >>
  simp [] >> gs [EVERY_CONJ, EVERY_MEM] >>
  conj_tac >> irule SUBSET_TRANS >> metis_tac []
QED

Theorem my_function_bind_lemma:
  ∀l s l2 s2. my_function_bind s l = (s2, l2) ∧
              (∀e. cexp_size e < list_size (pair_size mlstring_size cexp_size) l ⇒
                   ∀s. vars_ok s ∧ freevars (exp_of e) ⊆ set_of s ∧ cexp_wf e ∧ boundvars (exp_of e) ⊆ set_of s ⇒
                       ∀s2 e2. (s2, e2) = my_function s e ⇒
                               cexp_wf e2 ∧
                               vars_ok s2 ∧ set_of s ⊆ set_of s2 ∧ boundvars (exp_of e2) ⊆ set_of s2 ∧
                               freevars (exp_of e2) ⊆ set_of s2 ∧
                               (∀s3. DISJOINT s3 (boundvars (exp_of e2) ∪ freevars (exp_of e2))
                                     ⇒ exp_rel s3 (exp_of e) (exp_of e2))) ⇒
           vars_ok s ∧
           EVERY (λ(v, e). freevars (exp_of (e)) ⊆ set_of s ∧ cexp_wf e ∧ boundvars (exp_of e) ⊆ set_of s) l
           ⇒ vars_ok s2 ∧ set_of s ⊆ set_of s2 ∧ MAP FST l = MAP FST l2 ∧
             EVERY (λ(v, e). freevars (exp_of (e)) ⊆ set_of s2 ∧ cexp_wf e ∧ boundvars (exp_of e) ⊆ set_of s2) l2 ∧
             (∀s3. EVERY (λ(v, e2). DISJOINT s3 (boundvars (exp_of e2) ∪ freevars (exp_of e2))) l2
                   ⇒ LIST_REL (λ(v, e) (v2, e2). exp_rel s3 (exp_of e) (exp_of e2)) l l2) ∧
             (EVERY (λ(_,x). cexp_ok_bind x ∧ cexp_wf x) l ⇒ EVERY (λ(_,x). cexp_ok_bind x ∧ cexp_wf x) l2)
Proof
  Induct
  >- simp [my_function_def] >>
  PairCases >> simp [my_function_def, PULL_EXISTS] >>
  rpt $ gen_tac >>
  pairarg_tac >>
  rename [‘my_function_bind _ l’, ‘my_function s h = (s', hd')’, ‘v':: _ = _’] >>
  asm_rewrite_tac [PairedLambda.PAIRED_BETA_CONV $
                    Term ‘(λ(s',hd'). (λ(s'',tl'). (s'',(v, hd')::tl')) (my_function_bind s' l)) (s',hd')’] >>
  pairarg_tac >>
  last_x_assum $ drule_then assume_tac >>
  rename1 ‘my_function_bind s' l = (s'', tl')’ >>
  asm_rewrite_tac [PairedLambda.PAIRED_BETA_CONV $ Term ‘(λ(s'',tl'). (s'',(v, hd')::tl')) (s'', tl')’] >>
  strip_tac >> strip_tac >>
  first_assum $ qspec_then ‘h’ mp_tac >>
  impl_tac >- simp [list_size_def] >>
  disch_then $ qspec_then ‘s’ mp_tac >>
  impl_tac >- simp [] >>
  disch_then $ qspecl_then [‘s'’, ‘hd'’] mp_tac >>
  impl_tac >- simp [] >> strip_tac >>
  qpat_x_assum ‘_ ⇒ _’ mp_tac >> impl_tac
  >- (reverse conj_tac
      >- (gs [EVERY_CONJ, EVERY_MEM, FORALL_PROD] >>
          rpt $ strip_tac >> rpt $ first_x_assum $ drule_then assume_tac >>
          fs [] >> irule SUBSET_TRANS >>
          first_x_assum $ irule_at $ Pos hd >> simp []) >>
      gen_tac >> rename1 ‘cexp_size e < list_size _ _’ >>
      first_x_assum $ qspec_then ‘e’ assume_tac >>
      strip_tac >> qpat_x_assum ‘_ ⇒ _’ mp_tac >> impl_tac
      >- simp [list_size_def] >>
      strip_tac >> gen_tac >> strip_tac >> first_x_assum drule >>
      rename1 ‘my_function s3 e’ >> Cases_on ‘my_function s3 e’ >> simp []) >>
  strip_tac >> gs [] >>
  conj_tac
  >- (irule SUBSET_TRANS >> first_x_assum $ irule_at $ Pos hd >> simp []) >>
  qpat_x_assum ‘_::_ = _’ assume_tac >>
  dxrule_then assume_tac EQ_SYM >>
  simp [] >> gs [EVERY_CONJ, EVERY_MEM] >>
  conj_tac
  >- (conj_tac >> irule SUBSET_TRANS >> metis_tac []) >>
  qpat_x_assum ‘my_function _ _ = _’ mp_tac >>
  rpt $ pop_assum kall_tac >>
  Cases_on ‘h’ >> simp [cexp_ok_bind_def, my_function_def] >>
  pairarg_tac >> rw [] >> simp [cexp_ok_bind_def]
QED


Theorem my_function_row_lemma:
  ∀l s l2 s2. my_function_row s l = (s2, l2) ∧
              (∀e. cexp_size e < list_size (pair_size mlstring_size
                                             (pair_size (list_size mlstring_size) cexp_size)) l ⇒
                   ∀s. vars_ok s ∧ freevars (exp_of e) ⊆ set_of s ∧ cexp_wf e ∧ boundvars (exp_of e) ⊆ set_of s ⇒
                       ∀s2 e2. (s2, e2) = my_function s e ⇒
                               cexp_wf e2 ∧
                               vars_ok s2 ∧ set_of s ⊆ set_of s2 ∧ boundvars (exp_of e2) ⊆ set_of s2 ∧
                               freevars (exp_of e2) ⊆ set_of s2 ∧
                               (∀s3. DISJOINT s3 (boundvars (exp_of e2) ∪ freevars (exp_of e2))
                                     ⇒ exp_rel s3 (exp_of e) (exp_of e2))) ⇒
              vars_ok s ∧
              EVERY (λ(v, vs, e). freevars (exp_of (e)) ⊆ set_of s ∧ boundvars (exp_of e) ⊆ set_of s
                                  ∧ set (MAP explode vs) ⊆ set_of s) l ∧
              EVERY (λ(v, vs, e). cexp_wf e ∧ ALL_DISTINCT vs) l
              ⇒ vars_ok s2 ∧ set_of s ⊆ set_of s2 ∧
                EVERY (λ(v, vs, e). freevars (exp_of (e)) ⊆ set_of s2 ∧ boundvars (exp_of e) ⊆ set_of s2
                                    ∧ set (MAP explode vs) ⊆ set_of s2) l2 ∧
                MAP (FST o SND) l = MAP (FST o SND) l2 ∧
                MAP FST l = MAP FST l2 ∧
                EVERY (λ(v, vs, e). cexp_wf e ∧ ALL_DISTINCT vs) l2 ∧
                (∀s3. EVERY (λ(_, vs, e2). DISJOINT s3 (set (MAP explode vs)
                                                        ∪ boundvars (exp_of e2) ∪ freevars (exp_of e2))) l2
                      ⇒ LIST_REL (λ(_, _, e) (_, _, e2). exp_rel s3 (exp_of e) (exp_of e2)) l l2)
Proof
  Induct
  >- simp [my_function_def] >>
  PairCases >> simp [my_function_def, PULL_EXISTS] >>
  rpt $ gen_tac >> pairarg_tac >>
  rename [‘my_function_row _ l’, ‘my_function s h = (s', hd')’, ‘(v, vs, _)::_’] >>
  asm_rewrite_tac [PairedLambda.PAIRED_BETA_CONV $
                    Term ‘(λ(s',hd'). (λ(s'',tl'). (s'',(v, vs, hd')::tl')) (my_function_row s' l)) (s',hd')’] >>
  pairarg_tac >>
  last_x_assum $ drule_then assume_tac >>
  rename1 ‘my_function_row s' l = (s'', tl')’ >>
  asm_rewrite_tac [PairedLambda.PAIRED_BETA_CONV $ Term ‘(λ(s'',tl'). (s'', (v, vs, hd')::tl')) (s'', tl')’] >>
  strip_tac >> strip_tac >>
  first_assum $ qspec_then ‘h’ mp_tac >>
  impl_tac >- simp [list_size_def] >>
  disch_then $ qspec_then ‘s’ mp_tac >>
  impl_tac >- simp [] >>
  disch_then $ qspecl_then [‘s'’, ‘hd'’] mp_tac >>
  impl_tac >- simp [] >> strip_tac >>
  qpat_x_assum ‘_ ⇒ _’ mp_tac >> impl_tac
  >- (reverse conj_tac
      >- (gs [EVERY_CONJ, EVERY_MEM] >>
          rpt $ strip_tac >> rpt $ first_x_assum $ drule_then assume_tac >>
          pairarg_tac >>
          fs [] >> rpt $ strip_tac >>
          irule SUBSET_TRANS >>
          first_x_assum $ irule_at $ Pos hd >> simp []) >>
      gen_tac >> rename1 ‘cexp_size e < list_size _ _’ >>
      first_x_assum $ qspec_then ‘e’ assume_tac >>
      strip_tac >> qpat_x_assum ‘_ ⇒ _’ mp_tac >> impl_tac
      >- simp [list_size_def] >>
      strip_tac >> gen_tac >> strip_tac >> first_x_assum drule >>
      rename1 ‘my_function s3 e’ >> Cases_on ‘my_function s3 e’ >> simp []) >>
  strip_tac >> gs [] >>
  conj_tac
  >- (irule SUBSET_TRANS >> first_x_assum $ irule_at $ Pos hd >> simp []) >>
  qpat_x_assum ‘_::_ = _’ assume_tac >>
  dxrule_then assume_tac EQ_SYM >>
  simp [] >> gs [EVERY_CONJ, EVERY_MEM] >>
  rpt $ conj_tac >>
  irule SUBSET_TRANS
  >- metis_tac []
  >- metis_tac []
  >- (irule_at Any SUBSET_TRANS >> metis_tac [])
QED

Theorem cexp_ok_bind_soundness:
  ∀e. cexp_wf e ∧ cexp_ok_bind e ⇒ ok_bind (exp_of e)
Proof
  Cases >> simp [cexp_ok_bind_def, cexp_wf_def] >>
  rename1 ‘MAP explode l’ >>
  Cases_on ‘l’ >> gs []
QED

Theorem lets_for_boundvars_freevars:
  ∀l v n x s len. freevars (lets_for len v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ∧ boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x) ⊆ s
              ⇒ freevars x ⊆ s ∧ boundvars x ⊆ s
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw []
  \\ last_x_assum $ dxrule_all_then assume_tac
  \\ gvs [freevars_def, boundvars_def, SUBSET_DEF]
  \\ rw [] \\ metis_tac []
QED

Theorem boundvars_lets_for:
  ∀l v n x len. boundvars (lets_for len v n (MAPi (λi v. (i, v)) l) x) = boundvars x ∪ (set l)
Proof
  Induct using SNOC_INDUCT
  \\ simp [lets_for_def, indexedListsTheory.MAPi_APPEND, SNOC_APPEND, lets_for_APPEND]
  \\ rw [boundvars_def, SET_EQ_SUBSET, SUBSET_DEF] \\ gvs []
QED

Theorem boundvars_Disj:
  ∀pats w e. boundvars (Disj w pats) ⊆ {w} ∪ boundvars e
Proof
  Induct >> simp [FORALL_PROD, Disj_def, boundvars_def]
QED

Theorem boundvars_rows_of_SOME_lemma:
  ∀rows w pats e. boundvars e ⊆ boundvars (thunk_exp_of$rows_of w rows (SOME (pats, e)))
Proof
  Induct \\ gs [FORALL_PROD, thunk_exp_ofTheory.rows_of_def, boundvars_def, boundvars_Disj]
  \\ rw []
  \\ irule SUBSET_TRANS
  \\ pop_assum $ irule_at Any
  \\ rename1 ‘rows_of w _ (SOME (pats, _))’
  \\ qexists_tac ‘w’ \\ qexists_tac ‘pats’ \\ simp []
QED

Theorem boundvars_rows_of_SOME_NONE:
  ∀rows w pats e. boundvars (thunk_exp_of$rows_of w rows (SOME (pats, e))) =
                  boundvars (thunk_exp_of$rows_of w rows NONE) ∪ boundvars e
Proof
  Induct \\ gs [FORALL_PROD, thunk_exp_ofTheory.rows_of_def, boundvars_def]
  >- (gen_tac \\ Induct
      \\ simp [FORALL_PROD, Disj_def, boundvars_def])
  \\ simp [UNION_ASSOC]
QED

Theorem freevars_rows_of_SOME_NONE:
  ∀rows w pats e. freevars (thunk_exp_of$rows_of w rows (SOME (pats, e))) =
                  freevars (thunk_exp_of$rows_of w rows NONE) ∪ freevars e ∪ (if pats = [] then {} else {w})
Proof
  Induct \\ gs [FORALL_PROD, thunk_exp_ofTheory.rows_of_def, freevars_def]
  >- (gen_tac \\ Induct
      \\ simp [FORALL_PROD, Disj_def, freevars_def]
      \\ simp [GSYM UNION_ASSOC]
      \\ pop_assum kall_tac
      \\ gen_tac \\ simp [SET_EQ_SUBSET, SUBSET_DEF] \\ rw [])
  \\ simp [UNION_ASSOC]
QED

Theorem exp_rel_lets_for:
  ∀l n1 n2 x y len s. exp_rel s x y
                ⇒ exp_rel s (lets_for len n1 n2 l x) (lets_for len n1 n2 l y)
Proof
  Induct \\ gvs [lets_for_def, FORALL_PROD]
  \\ rw [] \\ irule exp_rel_Let
  \\ irule_at Any exp_rel_Let
  \\ last_x_assum $ drule_then $ irule_at Any
  \\ gvs [exp_rel_def]
QED

Theorem my_function_soundness:
  ∀s. vars_ok s ∧ freevars (exp_of e) ⊆ set_of s ∧ cexp_wf e ∧ boundvars (exp_of e) ⊆ set_of s ⇒
      ∀s2 e2. (s2, e2) = my_function s e ⇒
              cexp_wf e2 ∧
              vars_ok s2 ∧ set_of s ⊆ set_of s2 ∧ boundvars (exp_of e2) ⊆ set_of s2 ∧
              freevars (exp_of e2) ⊆ set_of s2 ∧
              (∀s3. DISJOINT s3 (boundvars (exp_of e2) ∪ freevars (exp_of e2)) ⇒ exp_rel s3 (exp_of e) (exp_of e2))
Proof
  completeInduct_on ‘cexp_size e’ >>
  Cases >> simp [my_function_def, boundvars_def, freevars_def, cexp_wf_def]
  >- simp [exp_rel_Var]
  >~ [‘Prim _ _’]
  >- (strip_tac >> gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      pairarg_tac >> gvs [] >>
      rename [‘my_function_list s l = (s2, l2)’] >>
      qspecl_then [‘l’, ‘s’, ‘l2’, ‘s2’] mp_tac my_function_list_lemma >>
      asm_rewrite_tac [] >> impl_tac
      >- (gen_tac >> strip_tac >>
          rename1 ‘cexp_size arg < _’ >>
          last_x_assum $ qspec_then ‘cexp_size arg’ mp_tac >>
          simp [] >>
          disch_then $ qspec_then ‘arg’ assume_tac >>
          gs []) >>
      last_x_assum kall_tac >>
      gs [BIGUNION_SUBSET, cexp_wf_def, EVERY_CONJ, EVERY_MEM, MEM_MAP,
          PULL_EXISTS, boundvars_def, freevars_def] >>
      rw []
      >- (pop_assum $ qspec_then ‘{}’ assume_tac >> gs [] >>
          rename1 ‘args_ok c _’ >>
          Cases_on ‘c’ >> gs [LIST_REL_EL_EQN, args_ok_def] >>
          rw [] >> gs [my_function_def] >>
          rpt $ (pairarg_tac >> gvs []))
      >- (irule exp_rel_Prim >>
          rename1 ‘exp_rel s3’ >>
          first_x_assum $ qspec_then ‘s3’ mp_tac >> gs [] >>
          simp [LIST_REL_EL_EQN, EL_MAP]))
  >~ [`Monad _ _`]
  >- (
    strip_tac >> gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    pairarg_tac >> gvs[] >>
    rename [‘my_function_list s l = (s2, l2)’] >>
    qspecl_then [‘l’, ‘s’, ‘l2’, ‘s2’] mp_tac my_function_list_lemma >>
    asm_rewrite_tac [] >> impl_tac
    >- (gen_tac >> strip_tac >>
        rename1 ‘cexp_size arg < _’ >>
        last_x_assum $ qspec_then ‘cexp_size arg’ mp_tac >>
        simp [] >>
        disch_then $ qspec_then ‘arg’ assume_tac >>
        gs []) >>
    last_x_assum kall_tac >>
    gs [BIGUNION_SUBSET, cexp_wf_def, EVERY_CONJ, EVERY_MEM, MEM_MAP,
        PULL_EXISTS, boundvars_def, freevars_def] >>
    rw [] >- (pop_assum $ qspec_then ‘{}’ assume_tac >> gvs[LIST_REL_EL_EQN]) >>
    irule exp_rel_Monad >> rename1 `exp_rel s3` >>
    first_x_assum $ qspec_then ‘s3’ mp_tac >> gs [] >> simp [LIST_REL_EL_EQN, EL_MAP]
    )
  >~[‘Apps _ _’]
  >- (strip_tac >> gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
      rename [‘my_function s e = (s2, e2)’, ‘my_function_list s2 l = (s3, l2)’] >>
      qspecl_then [‘l’, ‘s2’, ‘l2’, ‘s3’] mp_tac my_function_list_lemma >>
      asm_rewrite_tac [] >> impl_tac
      >- (gen_tac >> strip_tac >>
          rename1 ‘cexp_size arg < _’ >>
          last_x_assum $ qspec_then ‘cexp_size arg’ mp_tac >>
          simp [] >>
          disch_then $ qspec_then ‘arg’ assume_tac >>
          gs []) >>
      last_x_assum $ qspec_then ‘cexp_size e’ assume_tac >> gs [] >>
      pop_assum $ qspec_then ‘e’ assume_tac >> gs [] >>
      pop_assum $ drule_then assume_tac >>
      gs [boundvars_Apps, freevars_Apps, BIGUNION_SUBSET, cexp_wf_def, EVERY_CONJ] >>
      impl_tac
      >- (gs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
          irule SUBSET_TRANS >>
          last_x_assum $ drule_then $ irule_at $ Pos hd >> simp []) >>
      rw []
      >- simp [SF ETA_ss]
      >- (strip_tac >> gs [])
      >- gs [SUBSET_DEF]
      >- gs [SUBSET_DEF]
      >- gs [MEM_MAP, EVERY_MEM]
      >- gs [SUBSET_DEF]
      >- gs [MEM_MAP, EVERY_MEM]
      >- (irule exp_rel_Apps >>
          gs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
          first_x_assum $ drule_all_then assume_tac >>
          gs [LIST_REL_EL_EQN, EL_MAP]))
  >~[‘Lams _ _’]
  >- (rename1 ‘cexp_size e’ >> strip_tac >>
      gs [PULL_FORALL] >>
      rpt $ gen_tac >> strip_tac >>
      last_x_assum $ qspec_then ‘e’ assume_tac >> gs [] >>
      last_x_assum $ drule_then assume_tac >> gs [freevars_Lams, boundvars_Lams, DIFF_SUBSET] >>
      pairarg_tac >> gs [freevars_Lams, boundvars_Lams] >>
      strip_tac >> gs [] >>
      rename1 ‘exp_rel s3 _ _’ >> first_x_assum $ qspec_then ‘s3’ mp_tac >>
      simp [] >> impl_tac
      >- (gs [SUBSET_DEF, boundvars_Lams, freevars_Lams, DISJOINT_ALT] >>
          rw [] >>
          last_x_assum $ drule_then assume_tac >> gs []) >>
      rw [exp_rel_Lams, cexp_wf_def]
      >- gs [SUBSET_DEF]
      >- gs [SUBSET_DEF]
      >- (first_x_assum irule >>
          gs [DISJOINT_ALT] >> rw [] >>
          first_x_assum $ dxrule_then assume_tac >>
          rename1 ‘¬MEM x (MAP explode l)’ >>
          Cases_on ‘MEM x (MAP explode l)’ >> gs []))
  >~[‘my_function _ (Let opt x y)’]
  >- (strip_tac >> gs [PULL_FORALL] >>
      rpt $ gen_tac >> strip_tac >> fs [] >> strip_tac >>
      rename1 ‘exp_rel s3’ >>
      rename1 ‘my_function s’ >>
      Cases_on ‘opt’ >> simp []
      >- (last_assum $ qspecl_then [‘x’, ‘s’, ‘FST (my_function s x)’, ‘SND (my_function s x)’, ‘s3’] mp_tac >>
          gs [freevars_def, boundvars_def, my_function_Let_NONE] >>
          strip_tac >>
          last_x_assum $ qspecl_then [‘y’, ‘FST (my_function s x)’, ‘FST (my_function (FST (my_function s x)) y)’,
                                      ‘SND (my_function (FST (my_function s x)) y)’, ‘s3’] mp_tac >>
          simp [] >> strip_tac >>
          pairarg_tac >> gs [] >>
          pairarg_tac >> gvs [SUBSET_DEF, cexp_wf_def, boundvars_def, freevars_def] >>
          rw [] >> gs [] >>
          irule exp_rel_Let >> simp []) >>
      Cases_on ‘dest_Lam x’
      >- (last_assum $ qspecl_then [‘x’, ‘s’, ‘FST (my_function s x)’, ‘SND (my_function s x)’, ‘s3’] mp_tac >>
          gs [freevars_def, boundvars_def, my_function_Let_SOME_dLam_is_NONE] >>
          strip_tac >>
          last_x_assum $ qspecl_then [‘y’, ‘FST (my_function s x)’, ‘FST (my_function (FST (my_function s x)) y)’,
                                      ‘SND (my_function (FST (my_function s x)) y)’, ‘s3’] mp_tac >>
          simp [] >> impl_tac
          >- (gs [SUBSET_DEF] >>
              rw [] >> rename1 ‘v ∈ _’ >>
              rpt $ first_x_assum $ qspec_then ‘v’ assume_tac >> gs [] >>
              rename1 ‘v ≠ explode x2’ >>
              Cases_on ‘v = explode x2’ >> gs []) >>
          simp [] >> strip_tac >>
          pairarg_tac >> gs [] >>
          pairarg_tac >> gvs [SUBSET_DEF, cexp_wf_def, boundvars_def, freevars_def] >>
          rw [] >> gs [] >>
          irule exp_rel_Let >> simp [] >>
          first_x_assum irule >>
          gs [DISJOINT_ALT] >> rw [] >>
          rename [‘explode v1 ∉ s3’, ‘v2 ∈ freevars _’] >>
          Cases_on ‘v2 = explode v1’ >> simp []) >>
      Cases_on ‘x’ >> gs [dest_Lam_def, my_function_def] >>
      pairarg_tac >> gs [] >>
      pairarg_tac >> gs [] >>
      pairarg_tac >> gs [] >>
      rename1 ‘check_hypothesis (b1 ∧ b2) x' s_vars’ >> Cases_on ‘check_hypothesis (b1 ∧ b2) x' s_vars’
      >~[‘¬check_hypothesis _ _ _’]
      >- (rename1 ‘cexp_wf (Lam l x2)’ >>
          last_assum $ qspecl_then [‘Lam l x2’, ‘s’, ‘FST (my_function s (Lam l x2))’,
                                    ‘SND (my_function s (Lam l x2))’, ‘s3’] assume_tac >>
          gs [boundvars_def, freevars_def] >>
          last_x_assum $ qspecl_then [‘y’, ‘FST (my_function s (Lam l x2))’,
                                      ‘FST (my_function (FST (my_function s (Lam l x2))) y)’,
                                      ‘SND (my_function (FST (my_function s (Lam l x2))) y)’, ‘s3’] mp_tac >>
          simp [] >> impl_tac
          >- (gs [SUBSET_DEF] >> rw [] >> rename1 ‘v ∈ _’ >>
              rpt $ first_x_assum $ qspec_then ‘v’ assume_tac >> gs [] >>
              rename1 ‘v ≠ explode x2’ >>
              Cases_on ‘v = explode x2’ >> gs []) >>
          strip_tac >> gs [my_function_def, cexp_wf_def, SUBSET_DEF] >>
          rw [] >> irule_at Any exp_rel_Let >> simp [] >>
          first_x_assum irule >> simp [] >>
          gs [DISJOINT_ALT] >> rw [] >>
          rename [‘explode v1 ∉ s3’, ‘v2 ∈ freevars _’] >>
          Cases_on ‘v2 = explode v1’ >> simp []) >>
      gs [] >> pairarg_tac >> gs [] >>
      rename1 ‘invent_var _ _ = (v2, _)’ >>
      rename1 ‘cexp_wf (Lam l x2)’ >>
      last_assum $ qspecl_then [‘Lam l x2’, ‘s’, ‘FST (my_function s (Lam l x2))’,
                                ‘SND (my_function s (Lam l x2))’, ‘{explode v2} ∪ s3’] assume_tac >>
      gs [boundvars_def, freevars_def] >>
      last_x_assum $ qspecl_then [‘y’, ‘FST (my_function s (Lam l x2))’,
                                  ‘FST (my_function (FST (my_function s (Lam l x2))) y)’,
                                  ‘SND (my_function (FST (my_function s (Lam l x2))) y)’,
                                  ‘{explode v2} ∪ s3’] mp_tac >>
      simp [] >> impl_tac
      >- (gs [SUBSET_DEF] >> rw [] >> rename1 ‘v ∈ _’ >>
          rpt $ first_x_assum $ qspec_then ‘v’ assume_tac >> gs [] >>
          rename1 ‘v ≠ explode x2’ >>
          Cases_on ‘v = explode x2’ >> gs []) >>
      strip_tac >> gs [my_function_def, cexp_wf_def, boundvars_def, boundvars_Lams, boundvars_Apps,
                       freevars_Apps, freevars_Lams, freevars_def] >>
      drule_then assume_tac find_forcing_soundness >>
      gs [] >>
      rw []
      >- (strip_tac >> dxrule_then assume_tac REV_NOT_EMPTY >> fs [] >>
          dxrule_then assume_tac REV_NOT_EMPTY >> fs [] >>
          dxrule_then assume_tac REV_merge_inside >> gs [REV_REVERSE_LEM])
      >- (gs [REV_REVERSE_LEM, GSYM MAP_REVERSE, EVERY_APPEND] >>
          gs [EVERY_EL, EL_MAP, EL_MAP2, cexp_wf_def] >>
          rw [cexp_wf_def])
      >- (strip_tac >> dxrule_then assume_tac REV_NOT_EMPTY >> gs [REV_REVERSE_LEM] >>
          rename1 ‘MAP2 _ (REVERSE bL) l = []’ >>
          Cases_on ‘l’ >> fs [] >> qspec_then ‘bL’ assume_tac SNOC_CASES >> gs [])
      >- (dxrule_then assume_tac invent_var_thm >> gs [])
      >- (dxrule_then assume_tac invent_var_thm >> gs [SUBSET_DEF])
      >- (dxrule_then assume_tac invent_var_thm >> gs [REV_REVERSE_LEM, MAP_REVERSE, SUBSET_DEF] >>
          rw []
          >- (dxrule_then assume_tac $ iffLR MEM_MAP >> gs [] >>
              dxrule_then assume_tac thunk_Forcing_LambdasTheory.MEM_MAP_FILTER_ZIP >>
              gs [MEM_MAP, PULL_EXISTS, MEM_REVERSE])
          >- (gs [MEM_MAP, PULL_EXISTS] >>
              dxrule_then assume_tac MEM_merge_inside >>
              gs [MEM_REVERSE]))
      >- (dxrule_then assume_tac invent_var_thm >> gs [SUBSET_DEF, SF DNF_ss] >>
          rw [] >> first_x_assum $ dxrule_then assume_tac >>
          gs [] >>
          rename1 ‘REV l []’ >> rename1 ‘x ∈ freevars _’ >>
          Cases_on ‘MEM x (MAP explode l)’ >> gs [])
      >- (dxrule_then assume_tac invent_var_thm >> gs [SUBSET_DEF])
      >- (simp [BIGUNION_SUBSET, REV_REVERSE_LEM, MAP_REVERSE, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
          rw [] >> simp [exp_of_def, boundvars_def] >>
          pop_assum mp_tac >> gs [REV_REVERSE_LEM] >>
          simp [MEM_EL, PULL_EXISTS] >>
          rw [EL_MAP2, boundvars_def])
      >- (dxrule_then assume_tac invent_var_thm >> gs [SUBSET_DEF])
      >- (dxrule_then assume_tac invent_var_thm >> gs [SUBSET_DEF])
      >- (dxrule_then assume_tac invent_var_thm >> gs [SUBSET_DEF])
      >- (dxrule_then assume_tac invent_var_thm >> gs [SUBSET_DEF, SF DNF_ss] >>
          rw [] >> first_x_assum $ dxrule_then assume_tac >>
          gs [] >>
          rename1 ‘REV l []’ >> rename1 ‘x ∈ freevars _’ >>
          Cases_on ‘MEM x (MAP explode l)’ >> gs [])
      >- (simp [DIFF_SUBSET, UNION_SUBSET] >>
          conj_tac
          >- (simp [BIGUNION_SUBSET, REV_REVERSE_LEM, MAP_REVERSE, PULL_EXISTS] >>
              rw []
              >- (dxrule_then assume_tac $ iffLR MEM_MAP >> fs [] >>
                  dxrule_then assume_tac $ iffLR MEM_MAP >> fs [] >>
                  dxrule_then assume_tac $ iffLR MEM_MAP >> fs [] >>
                  dxrule_then assume_tac thunk_Forcing_LambdasTheory.MEM_MAP_FILTER_ZIP >>
                  gs [] >> simp [SUBSET_DEF, freevars_def, MEM_MAP]) >>
              pop_assum mp_tac >> simp [MEM_MAP, PULL_EXISTS, MEM_EL, EL_MAP2] >>
              rw [] >> simp [exp_of_def, freevars_def, MEM_MAP, EL_MEM])
          >- (dxrule_then assume_tac invent_var_thm >> gs [SUBSET_DEF]))
      >- (gs [REV_REVERSE_LEM, MAP2_ZIP, GSYM MAP_REVERSE, GSYM FILTER_REVERSE] >>
          irule exp_rel_Let_Lams_combine_bis >>
          gs [exp_rel_Lams, UNION_COMM] >>
          first_x_assum $ irule_at $ Pos last >>
          qpat_x_assum ‘_ ∧ _ ⇒ exp_rel _ _ (lets_force _ _)’ mp_tac >>
          impl_tac
          >- (rw []
              >- (dxrule_then assume_tac invent_var_thm >>
                  strip_tac >> gs [SUBSET_DEF])
              >- (dxrule_then assume_tac invent_var_thm >>
                  strip_tac >> gs [SUBSET_DEF])
              >- (‘∀v : string -> bool s1 s2. DISJOINT s2 v ∧ s1 = s2 ⇒ DISJOINT s1 v’ by simp [] >>
                  pop_assum irule >>
                  irule_at (Pos hd) FEQUAL >>
                  irule_at (Pos hd) FEQUAL2 >> irule_at (Pos hd) FEQUAL >>
                  irule_at Any REVERSE_ZIP >>
                  conj_asm1_tac
                  >- (simp [] >>
                      irule EQ_LENGTH_FILTER_ZIP >>
                      simp [LENGTH_merge_inside]) >>
                  simp [boundvars_lets_force] >>
                  gs [DISJOINT_ALT] >> rw [] >>
                  dxrule_then assume_tac $ iffLR MEM_MAP >> fs [] >>
                  dxrule_then assume_tac thunk_Forcing_LambdasTheory.MEM_MAP_FILTER_ZIP >>
                  ‘∀l y. MEM y l ⇒ MEM (explode y) (MAP explode l)’ by simp [MEM_MAP] >>
                  pop_assum $ dxrule_then assume_tac >> gs [MAP_REVERSE])
              >- (rename1 ‘MEM (explode v2) (MAP explode l)’ >>
                  Cases_on ‘MEM (explode v2) (MAP explode l)’ >> simp [] >>
                  dxrule_then assume_tac invent_var_thm >>
                  strip_tac >> gs [SUBSET_DEF])
              >- (gs [DISJOINT_ALT] >> rpt $ strip_tac >>
                  rename1 ‘x ∉ _ ∨ MEM x (MAP explode l)’ >>
                  Cases_on ‘MEM x (MAP explode l)’ >> simp [] >> strip_tac >>
                  dxrule_then assume_tac in_freevars_lets_force >>
                  gs [MAP_REVERSE]
                  >- (first_x_assum $ dxrule_then assume_tac >> gs []) >>
                  dxrule MEM_MAP_ZIP >> impl_tac
                  >- (simp [] >> irule EQ_LENGTH_FILTER_ZIP >>
                      simp [LENGTH_merge_inside]) >>
                  strip_tac >> dxrule_then assume_tac $ iffLR MEM_MAP >>
                  gs [] >> dxrule_then assume_tac thunk_Forcing_LambdasTheory.MEM_MAP_FILTER_ZIP >>
                  gs [MEM_MAP])) >>
          strip_tac >>
          dxrule_then assume_tac exp_rel_lets_force_left >> gs [] >>
          first_assum $ irule_at $ Pos last >>
          rename1 ‘ZIP (bL, merge_inside (REVERSE l) bL l3)’ >>
          ‘LENGTH bL = LENGTH (merge_inside (REVERSE l) bL l3)’ by gs [LENGTH_merge_inside] >>
          rename1 ‘REVERSE (ZIP (bL2, REVERSE l))’ >>
          ‘LENGTH bL2 = LENGTH l’ by gs [LIST_REL_EL_EQN] >>
          gs [REVERSE_ZIP, MAP_FILTER_ZIP, MAP_REVERSE] >>
          qspecl_then [‘bL’, ‘REVERSE l’, ‘l3’, ‘explode’] mp_tac MAP_merge_inside >>
          impl_tac >- simp [GSYM REVERSE_ZIP, FILTER_REVERSE] >>
          strip_tac >> gs [] >>
          qspecl_then [‘MAP explode (REVERSE l)’, ‘bL’, ‘MAP explode l3’] mp_tac REVERSE_merge_inside >>
          impl_tac
          >- (simp [] >> irule EQ_TRANS >>
              rename1 ‘ZIP (bL, MAP explode (REVERSE l))’ >>
              qspecl_then [‘FILTER FST $ ZIP (bL, MAP explode (REVERSE l))’, ‘SND’] (irule_at Any) LENGTH_MAP >>
              irule_at Any EQ_TRANS >> irule_at (Pos last) FEQUAL >>
              irule_at Any MAP_FILTER_ZIP >>
              simp []) >>
          strip_tac >> gs [MAP_REVERSE] >>
          dxrule_then assume_tac check_hypothesis_soundness >>
          qexists_tac ‘REVERSE (MAP explode l3)’ >>
          qexists_tac ‘MAP explode l’ >>
          qexists_tac ‘REVERSE bL2’ >> qexists_tac ‘REVERSE bL’ >>
          rw []
          >- gs [DISJOINT_SYM]
          >- (dxrule_then assume_tac invent_var_thm >> strip_tac >> gs [SUBSET_DEF])
          >- (gs [DISJOINT_ALT] >> rpt $ strip_tac >>
              rename1 ‘x ∈ freevars (exp_of _)’ >>
              rpt $ first_x_assum $ qspec_then ‘x’ assume_tac >> gs [])
          >- (dxrule_then assume_tac invent_var_thm >> strip_tac >> gs [SUBSET_DEF])
          >- gs [MEM_MAP]
          >- gs [MEM_MAP]
          >- (dxrule_then assume_tac invent_var_thm >> strip_tac >> gs [SUBSET_DEF])
          >- (dxrule_then assume_tac invent_var_thm >> strip_tac >> gs [MEM_MAP, SUBSET_DEF])
          >- gs [ALL_DISTINCT_APPEND, MEM_MAP, PULL_EXISTS]
          >- (dxrule_then assume_tac invent_var_thm >> strip_tac >> gs [boundvars_to_lets_force, SUBSET_DEF])
          >- (dxrule_then assume_tac invent_var_thm >> strip_tac >> gs [SUBSET_DEF])
          >- (dxrule_then assume_tac invent_var_thm >> strip_tac >> gs [SUBSET_DEF])
          >- (dxrule_then assume_tac invent_var_thm >> strip_tac >> gs [SUBSET_DEF] >>
              rename1 ‘_ ∈ freevars  _ ∧ _ ≠ explode x' ⇒ _ ∈ _’ >>
              Cases_on ‘explode v2 = explode x'’ >> gs [])
          >- (AP_THM_TAC >> AP_TERM_TAC >>
              AP_THM_TAC >> AP_TERM_TAC >>
              irule EQ_TRANS >> irule_at (Pos hd) REVERSE_ZIP >>
              simp [] >> irule_at Any EQ_LENGTH_FILTER_ZIP >>
              conj_asm1_tac
              >- (irule LENGTH_merge_inside >> simp [] >>
                  irule_at Any EQ_LENGTH_FILTER_ZIP >> simp []) >>
              simp [] >> AP_TERM_TAC >> simp [] >>
              conj_tac
              >- (‘LENGTH l = LENGTH bL’ by simp [] >> pop_assum mp_tac >>
                  qpat_x_assum ‘LENGTH l3 = LENGTH (FILTER FST (ZIP (bL, REVERSE l)))’ mp_tac >>
                  rpt $ pop_assum kall_tac >>
                  qid_spec_tac ‘l3’ >> qid_spec_tac ‘bL’ >>
                  Induct_on ‘l’ using SNOC_INDUCT >> simp [merge_inside_def, REVERSE_SNOC, SNOC_APPEND] >>
                  gen_tac >> Cases >> simp [] >>
                  IF_CASES_TAC >> simp [merge_inside_def] >>
                  Cases >> simp [merge_inside_def]) >>
              simp [GSYM MAP_REVERSE, GSYM FILTER_REVERSE, REVERSE_ZIP])
          >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> MK_COMB_TAC
              >- (AP_TERM_TAC >> simp [MAP_FILTER_ZIP] >>
                  AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> simp [] >>
                  gs [MAP_MAP_o, combinTheory.o_DEF])
              >- (irule LIST_EQ >> simp [EL_MAP2, EL_MAP, EL_ZIP] >>
                  rw [exp_of_def]))
          >- (irule EQ_TRANS >> irule_at Any LENGTH_REVERSE >>
              once_rewrite_tac [GSYM FILTER_REVERSE] >>
              simp [REVERSE_ZIP, EQ_LENGTH_FILTER_ZIP])
          >- (rpt $ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac >>
              dxrule exp_rel_freevars >>
              rpt $ pop_assum kall_tac >>
              rw [] >> gs [LIST_REL_EVERY_ZIP, GSYM REVERSE_ZIP] >>
              irule $ iffLR EVERY_REVERSE >>
              ‘LENGTH (REVERSE (ZIP (bL, bL2))) = LENGTH (MAP explode l)’ by simp [] >>
              dxrule_then assume_tac REVERSE_ZIP >>
              asm_rewrite_tac [REVERSE_REVERSE])))
  >~[‘Letrec _ _’]
  >- (strip_tac >> gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
      rename [‘my_function s e = (s2, e2)’, ‘my_function_bind s2 l = (s3, l2)’] >>
      qspecl_then [‘l’, ‘s2’, ‘l2’, ‘s3’] mp_tac my_function_bind_lemma >>
      asm_rewrite_tac [] >> impl_tac
      >- (gen_tac >> strip_tac >>
          rename1 ‘cexp_size arg < _’ >>
          last_x_assum $ qspec_then ‘cexp_size arg’ mp_tac >>
          simp [] >>
          disch_then $ qspec_then ‘arg’ assume_tac >>
          gs []) >>
      last_x_assum $ qspec_then ‘cexp_size e’ assume_tac >> gs [] >>
      pop_assum $ qspec_then ‘e’ assume_tac >> gs [] >>
      pop_assum $ drule_then assume_tac >>
      gs [boundvars_def, freevars_def, BIGUNION_SUBSET, cexp_wf_def, EVERY_CONJ] >>
      ‘freevars (exp_of e) ⊆ set_of s’
        by (gs [SUBSET_DEF, SF DNF_ss, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
            gen_tac >> rename1 ‘x ∈ freevars _’ >>
            Cases_on ‘MEM (implode x) (MAP FST l)’
            >- (gs [MEM_MAP, FST_THM] >> pairarg_tac >>
                gvs [] >>
                first_x_assum $ dxrule_then assume_tac >>
                gs [explode_implode]) >>
            strip_tac >> last_x_assum irule >>
            gs [MEM_MAP]) >>
      impl_tac
      >- (gs [EVERY_MEM, SUBSET_DEF, MEM_MAP] >>
          gs [FORALL_PROD, EXISTS_PROD, PULL_EXISTS] >>
          rw []
          >- (rename1 ‘x ∈ set_of _’ >>
              Cases_on ‘MEM (implode x) (MAP FST l)’
              >- (gs [MEM_MAP, FST_THM] >> pairarg_tac >>
                  gvs [] >>
                  first_x_assum $ dxrule_then assume_tac >>
                  gs [explode_implode]) >>
              last_x_assum irule >> last_x_assum irule >>
              gs [MEM_MAP] >> metis_tac [])
          >- (last_x_assum $ drule_then assume_tac >> fs [])
          >- (last_x_assum $ drule_then assume_tac >>
              last_x_assum $ drule_then assume_tac >> gs [])) >>
      strip_tac >>
      rw []
      >- (strip_tac >> gs [])
      >- gs []
      >- gs [SUBSET_DEF]
      >- gs [SUBSET_DEF]
      >- (gs [MEM_MAP, EVERY_MEM] >>
          pairarg_tac >> gs [] >> pairarg_tac >> gvs [] >>
          first_x_assum $ drule_then assume_tac >>
          first_x_assum $ dxrule_then assume_tac >> gs [])
      >- (rename1 ‘MAP FST l = MAP FST l2’ >>
          ‘MAP FST (MAP (λ(n,x'). (explode n,exp_of x')) l) = MAP FST (MAP (λ(n,x'). (explode n,exp_of x')) l2)’
            suffices_by gs [SUBSET_DEF] >>
          irule LIST_EQ >>
          qpat_x_assum ‘MAP _ _ = MAP _ _’ mp_tac >>
          once_rewrite_tac [GSYM LIST_REL_eq] >>
          strip_tac >> dxrule_then assume_tac $ iffLR LIST_REL_EL_EQN >>
          gs [EL_MAP] >> rw [] >>
          pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
          first_x_assum $ drule_then assume_tac >> gs [])
      >- (gs [SUBSET_DEF] >> rw []
          >- gs [] >>
          dxrule_then assume_tac $ iffLR MEM_MAP >> gs [] >>
          dxrule_then assume_tac $ iffLR MEM_MAP >> gs [EVERY_MEM] >>
          first_x_assum $ drule_then kall_tac >>
          first_x_assum $ dxrule_then assume_tac >>
          pairarg_tac >> gs [])
      >- (irule exp_rel_Letrec >>
          conj_tac
          >- (irule LIST_EQ >>
              qpat_x_assum ‘MAP _ _ = MAP _ _’ mp_tac >>
              once_rewrite_tac [GSYM LIST_REL_eq] >>
              strip_tac >> dxrule_then assume_tac $ iffLR LIST_REL_EL_EQN >>
              gs [EL_MAP] >> rw [] >>
              pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
              first_x_assum $ drule_then assume_tac >> gs []) >>
          gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, EVERY_CONJ] >>
          ‘DISJOINT (freevars (exp_of e2) ∪ BIGUNION (set (MAP (λ(p1, p2). freevars (exp_of p2)) l2))) s3'’
            by (gs [DISJOINT_ALT] >>
                rw [] >> rename1 ‘x ∉ s3'’ >>
                Cases_on ‘MEM x (MAP (λ(p1, p2). explode p1) l2)’ >> gs [] >>
                first_x_assum irule >> gs [] >>
                metis_tac []) >>
          qpat_x_assum ‘DISJOINT (_ ∪ _ DIFF _) _’ kall_tac >>
          gs [] >>
          qpat_x_assum ‘∀s3. EVERY _ _ ⇒ LIST_REL _ _ _’ $ qspec_then ‘s3'’ mp_tac >>
          impl_tac
          >- (gs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
              rw [] >> first_x_assum $ drule_then irule) >>
          strip_tac >>
          gs [EVERY_EL, LIST_REL_EL_EQN, EL_MAP] >>
          rw []
          >- (last_x_assum $ drule_then assume_tac >> pairarg_tac >> gs [] >>
              drule_all_then irule cexp_ok_bind_soundness)
          >- (last_x_assum $ drule_then assume_tac >>
              first_x_assum $ drule_then assume_tac >>
              pairarg_tac >> gs [] >>
              pairarg_tac >> gs [] >>
              drule_all_then assume_tac cexp_ok_bind_soundness >>
              rename1 ‘exp_rel _ e_in e_out’ >>
              Cases_on ‘e_in’ >> gs [ok_bind_def, exp_rel_def])
          >- (first_x_assum $ drule_then assume_tac >>
              pairarg_tac >> gs [] >>
              pairarg_tac >> gs [])))
  >~[‘rows_of _ _ _’]

  >- (strip_tac >> gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
      rename [‘my_function_row s row = (s2, row2)’] >>
      qspecl_then [‘row’, ‘s’, ‘row2’, ‘s2’] mp_tac my_function_row_lemma >>
      asm_rewrite_tac [] >> impl_tac
      >- (gen_tac >> strip_tac >>
          rename1 ‘cexp_size arg < _’ >>
          last_x_assum $ qspec_then ‘cexp_size arg’ mp_tac >>
          simp [list_size_MAP] >>
          disch_then $ qspec_then ‘arg’ assume_tac >>
          gs []) >>
      impl_tac
      >- (reverse conj_tac
          >- (gs [EVERY_MEM, FORALL_PROD, SF DNF_ss] >>
              rw [] >> first_x_assum irule >>
              first_x_assum $ irule_at Any) >>
          qpat_x_assum ‘freevars _ ⊆ _’ mp_tac >>
          qpat_x_assum ‘boundvars _ ⊆ _’ mp_tac >>
          rpt $ pop_assum kall_tac >> Induct_on ‘row ’ >>
          simp [FORALL_PROD, rows_of_def, boundvars_def, freevars_def] >>
          rpt gen_tac >> strip_tac >> strip_tac >>
          drule_all_then assume_tac lets_for_boundvars_freevars >>
          simp [] >>
          qpat_x_assum ‘boundvars (lets_for _ _ _ _ _) ⊆ _’ mp_tac >>
          simp [boundvars_lets_for]) >>
      strip_tac >>
      conj_tac
      >- (rw [cexp_wf_def]
          >- (qpat_x_assum ‘EVERY _ row2’ mp_tac >>
              rpt $ pop_assum kall_tac >>
              simp [EVERY_MEM, FORALL_PROD, SF DNF_ss] >>
              rw [] >>
              first_x_assum $ drule_then irule)
          >- (strip_tac >> gs [])
          >- gs []
          >- (rename1 ‘OPTION_ALL _ eopt1’ >>
              Cases_on ‘eopt1’ >> gs [] >>
              pairarg_tac >> gs [] >>
              pairarg_tac >> gvs [])
          >- (qpat_x_assum ‘_ = (_, _)’ mp_tac >>
              CASE_TAC >> simp [] >>
              CASE_TAC >> pairarg_tac >> simp [] >>
              rw [] >> gs [] >>
              rename1 ‘my_function s2 e1 = (s3, e2)’ >>
              last_x_assum $ qspec_then ‘cexp_size e1’ mp_tac >> simp [] >>
              disch_then $ qspec_then ‘e1’ mp_tac >> simp [] >>
              disch_then $ qspec_then ‘s2’ mp_tac >> simp [] >>
              impl_tac
              >- (gs [freevars_rows_of] >>
                  assume_tac boundvars_rows_of_SOME_lemma >>
                  gs [SUBSET_DEF]) >>
              simp [])) >>
      rename1 ‘OPTION_ALL _ eopt1’ >>
      conj_asm1_tac
      >- (Cases_on ‘eopt1’ >> gs [] >> pairarg_tac >> gs [] >>
          pairarg_tac >> gvs [] >>
          rename1 ‘my_function s2 e = (s3, e2)’ >>
          last_x_assum $ qspec_then ‘cexp_size e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘s2’ mp_tac >> simp [] >>
          impl_tac
          >- (gs [freevars_rows_of] >>
              assume_tac boundvars_rows_of_SOME_lemma >>
              gs [SUBSET_DEF]) >>
          simp []) >>
      conj_asm1_tac
      >- (Cases_on ‘eopt1’ >> gs [] >> pairarg_tac >> gs [] >>
          pairarg_tac >> gvs [] >>
          rename1 ‘my_function s2 e = (s3, e2)’ >>
          last_x_assum $ qspec_then ‘cexp_size e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘s2’ mp_tac >> simp [] >>
          impl_tac
          >- (gs [freevars_rows_of] >>
              assume_tac boundvars_rows_of_SOME_lemma >>
              gs [SUBSET_DEF]) >>
          gs [SUBSET_DEF]) >>
      rename1 ‘boundvars (rows_of (explode m) (MAP _ row2) (OPTION_MAP _ eopt')) ⊆ set_of s3’ >>
      ‘set_of s2 ⊆ set_of s3’
        by (Cases_on ‘eopt1’ >> gs [] >>
            pairarg_tac >> gs [] >>
            pairarg_tac >> gs [] >>
            rename1 ‘my_function s2 e = (s3, e')’ >>
            last_x_assum $ qspec_then ‘cexp_size e’ mp_tac >> simp [] >>
            disch_then $ qspec_then ‘e’ mp_tac >> simp [] >>
            disch_then $ qspec_then ‘s2’ mp_tac >> simp [] >>
            impl_tac
            >- (gs [freevars_rows_of] >>
                assume_tac boundvars_rows_of_SOME_lemma >>
                gs [SUBSET_DEF]) >>
            simp []) >>
      conj_asm1_tac
      >- (‘boundvars (rows_of (explode m) (MAP (λ(c,vs,x). (explode c,MAP explode vs,exp_of x)) row2) NONE)
           ⊆ set_of s3’
            by (qpat_x_assum ‘EVERY _ row2’ kall_tac >>
                qpat_x_assum ‘EVERY _ row2’ mp_tac >>
                qpat_x_assum ‘set_of s2 ⊆ set_of s3’ mp_tac >>
                rpt $ pop_assum kall_tac >> Induct_on ‘row2’ >>
                simp [rows_of_def, boundvars_def, FORALL_PROD, boundvars_lets_for] >>
                rw [] >> gs [SUBSET_DEF]) >>
          Cases_on ‘eopt1’ >> gs [] >>
          pairarg_tac >> gs [] >>
          pairarg_tac >> gvs [boundvars_rows_of_SOME_NONE] >>
          rename1 ‘my_function s2 e = (s3, e2)’ >>
          last_x_assum $ qspec_then ‘cexp_size e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘s2’ mp_tac >> simp [] >>
          impl_tac
          >- (gs [freevars_rows_of] >>
              assume_tac boundvars_rows_of_SOME_lemma >>
              gs [SUBSET_DEF]) >>
          simp []) >>
      conj_asm1_tac
      >- (‘freevars (rows_of (explode m) (MAP (λ(c,vs,x). (explode c,MAP explode vs,exp_of x)) row2) NONE)
           ⊆ set_of s3’
            by (qpat_x_assum ‘EVERY _ row2’ kall_tac >>
                qpat_x_assum ‘EVERY _ row2’ mp_tac >>
                ‘explode m ∈ set_of s3’
                  by (Cases_on ‘row’ >> gs [] >>
                      rename1 ‘my_function_row _ (h::_)’ >> PairCases_on ‘h’ >>
                      gs [rows_of_def, freevars_def] >>
                      metis_tac[SUBSET_DEF]) >>
                pop_assum mp_tac >>
                dxrule_then (drule_then mp_tac) SUBSET_TRANS >>
                qpat_x_assum ‘set_of s2 ⊆ set_of s3’ mp_tac >>
                rpt $ pop_assum kall_tac >> Induct_on ‘row2’ >>
                simp [rows_of_def, freevars_def, FORALL_PROD] >>
                rw [SUBSET_DEF] >>
                assume_tac freevars_lets_for >>
                gs [SET_EQ_SUBSET, SUBSET_DEF, SF DNF_ss] >>
                rename1 ‘x ∈ freevars _’ >>
                Cases_on ‘x = explode m’ >> gs [] >>
                last_x_assum $ drule_then assume_tac >>
                gs []) >>
          Cases_on ‘eopt1’ >> gs [] >>
          pairarg_tac >> gs [] >>
          pairarg_tac >> gvs [freevars_rows_of_SOME_NONE] >>
          reverse conj_tac
          >- (qpat_x_assum ‘explode m ∈ _’ mp_tac >>
              rpt $ qpat_x_assum ‘set_of _ ⊆ set_of _’ mp_tac >>
              rpt $ pop_assum kall_tac >> rw [] >>
              gs [SUBSET_DEF]) >>
          rename1 ‘my_function s2 e = (s3, e2)’ >>
          last_x_assum $ qspec_then ‘cexp_size e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘s2’ mp_tac >> simp [] >>
          impl_tac
          >- (gs [freevars_rows_of] >>
              assume_tac boundvars_rows_of_SOME_lemma >>
              gs [SUBSET_DEF]) >>
          simp [])

      >- (rw [] >> rename1 ‘exp_rel s4 _ _’ >>
          first_x_assum $ qspec_then ‘s4’ mp_tac >>
          impl_tac
          >- (pop_assum mp_tac >>
              pop_assum mp_tac >>
              rpt $ pop_assum kall_tac >>
              Induct_on ‘row2’ >>
              simp [FORALL_PROD, rows_of_def, freevars_def, boundvars_def] >>
              rw [] >> gs [boundvars_lets_for] >>
              assume_tac freevars_lets_for >>
              gs [SET_EQ_SUBSET, SUBSET_DEF, SF DNF_ss, DISJOINT_ALT] >>
              rw [] >> rename [‘x ∈ freevars _’, ‘LENGTH p_1'’] >>
              Cases_on ‘MEM x (MAP explode p_1')’ >> gs [] >>
              Cases_on ‘x = explode m’ >> gs []) >>
          Cases_on ‘eopt1’ >> gs []
          >- (qpat_x_assum ‘MAP (FST o SND) _ = MAP (FST o SND) _’ mp_tac >>
              qpat_x_assum ‘MAP FST _ = MAP FST _’ mp_tac >>
              rpt $ pop_assum kall_tac >>
              qid_spec_tac ‘row2’ >>
              Induct_on ‘row’ >> gs [PULL_EXISTS, FORALL_PROD, PULL_FORALL, rows_of_def]
              >- simp [exp_rel_def] >>
              rw [] >>
              irule exp_rel_If >>
              conj_tac >- simp [exp_rel_def] >>
              conj_tac
              >- simp [exp_rel_lets_for]
              >- (last_x_assum irule >> gs [])) >>
          pairarg_tac >> gs [] >>
          pairarg_tac >> gs [] >>
          rename1 ‘my_function s2 e = (s3, e2)’ >>
          last_x_assum $ qspec_then ‘cexp_size e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘e’ mp_tac >> simp [] >>
          disch_then $ qspec_then ‘s2’ mp_tac >> simp [] >>
          impl_tac
          >- (gs [freevars_rows_of] >>
              assume_tac boundvars_rows_of_SOME_lemma >>
              gs [SUBSET_DEF]) >>
          strip_tac >>
          first_x_assum $ qspec_then ‘s4’ mp_tac >>
          gvs [freevars_rows_of_SOME_NONE, boundvars_rows_of_SOME_NONE] >>
          qpat_x_assum ‘MAP (FST o SND) _ = MAP (FST o SND) _’ mp_tac >>
          qpat_x_assum ‘MAP FST _ = MAP FST _’ mp_tac >>
          rpt $ pop_assum kall_tac >>
          qid_spec_tac ‘row2’ >>
          Induct_on ‘row’ >> gs [PULL_EXISTS, FORALL_PROD, PULL_FORALL, rows_of_def]
          >- (simp [exp_rel_def] >> disch_then kall_tac >>
              rename1 ‘Disj _ l’ >>
              Induct_on ‘l’ >> simp [FORALL_PROD, Disj_def, exp_rel_def]) >>
          simp [exp_rel_def, exp_rel_lets_for]))
  >~[‘Delay (exp_of e)’]
  >- (strip_tac >> gs [PULL_FORALL] >>
      last_x_assum $ qspec_then ‘e’ assume_tac >>
      gen_tac >> pairarg_tac >> gs [boundvars_def, freevars_def, exp_rel_def] >>
      gen_tac >> strip_tac >> simp [cexp_wf_def] >>
      last_x_assum $ dxrule_then assume_tac >> gs [])
  >~[‘Force (exp_of e)’]
  >- (strip_tac >> gs [PULL_FORALL] >>
      last_x_assum $ qspec_then ‘e’ assume_tac >>
      gen_tac >> pairarg_tac >> gs [boundvars_def, freevars_def, exp_rel_def] >>
      gen_tac >> strip_tac >> simp [cexp_wf_def] >>
      last_x_assum $ dxrule_then assume_tac >> gs [])
QED

