open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory rich_listTheory alistTheory finite_mapTheory;
open pure_miscTheory pure_configTheory pure_expTheory pure_exp_lemmasTheory
     pure_semanticsTheory pure_evalTheory pure_tcexpTheory pure_tcexp_lemmasTheory
     pure_typingTheory pure_typingPropsTheory;

val _ = new_theory "pure_typingProof";

(* TODO replace existing get_atoms_SOME_SOME_eq *)
Theorem get_atoms_SOME_SOME_eq:
  ∀ls as. get_atoms ls = SOME (SOME as) ⇔ ls = MAP wh_Atom as
Proof
  rw[get_atoms_SOME_SOME_eq] >>
  rw[LIST_EQ_REWRITE, LIST_REL_EL_EQN] >> eq_tac >> gvs[EL_MAP]
QED

Theorem eval_op_type_safe:
  (type_atom_op op ts t ∧ t ≠ Bool ∧
   LIST_REL type_lit ls ts ⇒
  ∃res.
    eval_op op ls = SOME (INL res) ∧
    type_lit res t) ∧
  (type_atom_op op ts Bool ∧
   LIST_REL type_lit ls ts ⇒
  ∃res.
    eval_op op ls = SOME (INR res))
Proof
  rw[type_atom_op_cases, type_lit_cases] >> gvs[type_lit_cases, PULL_EXISTS]
  >- (
    ntac 2 $ last_x_assum mp_tac >> map_every qid_spec_tac [`ts`,`ls`] >>
    Induct_on `LIST_REL` >> rw[] >> gvs[type_lit_cases, concat_def]
    )
  >- (
    ntac 2 $ last_x_assum mp_tac >> map_every qid_spec_tac [`ts`,`ls`] >>
    Induct_on `LIST_REL` >> rw[] >> gvs[type_lit_cases, implode_def]
    )
  >- (IF_CASES_TAC >> gvs[])
QED

Inductive type_wh:
  (type_tcexp ns db st env (Prim (Cons s) ces) t ∧
   MAP exp_of ces = es ⇒
    type_wh ns db st env (wh_Constructor s es) t) ∧

  (type_tcexp ns db st env (Lam [s] ce) t ∧
   exp_of ce = e ⇒
    type_wh ns db st env (wh_Closure s e) t) ∧

  (type_tcexp ns db st env (Prim (AtomOp $ Lit l) []) t ⇒
    type_wh ns db st env (wh_Atom l) t) ∧

  (type_ok (SND ns) db t ⇒ type_wh ns db st env wh_Diverge t)
End

Triviality type_wh_PrimTy_eq_wh_Atom:
  type_wh ns db st env wh (PrimTy pt) ∧ pt ≠ Bool ⇒
    wh = wh_Diverge ∨ ∃a. wh = wh_Atom a
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases] >>
  Cases_on `arg_tys` >> gvs[Functions_def]
QED

Triviality type_wh_PrimTy_Bool_eq_wh_Constructor:
  type_wh ns db st env wh (PrimTy Bool) ⇒
    wh = wh_Diverge ∨ wh = wh_Constructor "True" [] ∨ wh = wh_Constructor "False" []
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases]
  >- (Cases_on `arg_tys` >> gvs[Functions_def])
  >- (gvs[get_PrimTys_def, type_atom_op_cases, type_lit_cases])
QED

Triviality type_wh_Function_eq_wh_Closure:
  type_wh ns db st env wh (Function ft rt) ⇒
    wh = wh_Diverge ∨ ∃x body. wh = wh_Closure x body
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases]
QED

Triviality type_wh_TypeCons_eq_wh_Constructor:
  type_wh ns db st env wh (TypeCons id ts) ⇒
    wh = wh_Diverge ∨ ∃cname es. wh = wh_Constructor cname es
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases, exp_of_def] >>
  Cases_on `arg_tys` >> gvs[Functions_def]
QED

Triviality type_wh_Array_eq_Loc:
  type_wh ns db st env wh (Array t) ⇒
    wh = wh_Diverge ∨ ∃a n. wh = wh_Atom (Loc n) ∧ oEL n st = SOME t
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases] >>
  Cases_on `arg_tys` >> gvs[Functions_def]
QED

Triviality type_wh_Tuple_eq_wh_Constructor:
  type_wh ns db st env wh (Tuple ts) ⇒
    wh = wh_Diverge ∨ ∃es. wh = wh_Constructor "" es
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases, exp_of_def] >>
  Cases_on `arg_tys` >> gvs[Functions_def]
QED

Triviality type_wh_Exception_eq_wh_Constructor:
  type_wh ns db st env wh Exception ⇒
    wh = wh_Diverge ∨ ∃cn es. wh = wh_Constructor cn es
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases, exp_of_def] >>
  Cases_on `arg_tys` >> gvs[Functions_def]
QED

Theorem eval_wh_to_Case_wh_Diverge:
  closed (exp_of e) ∧ eval_wh_to k (exp_of e) = wh_Diverge ∧ es ≠ [] ⇒
  eval_wh_to k (exp_of (Case e v es)) = wh_Diverge
Proof
  rw[exp_of_def, eval_wh_to_def, bind1_def] >>
  Cases_on `es` >> gvs[rows_of_def] >>
  PairCases_on `h` >> gvs[rows_of_def, subst1_def] >>
  rw[eval_wh_to_def] >>
  IF_CASES_TAC >> gvs[] >>
  qsuff_tac `eval_wh_to (k - 3) (exp_of e) = wh_Diverge` >> gvs[] >>
  CCONTR_TAC >> drule eval_wh_inc >> simp[] >> qexists_tac `k` >> simp[]
QED

Theorem eval_wh_to_lets_for:
  ∀vs e k cn v b.
  closed e ∧ vs ≠ [] ∧ ¬ MEM v vs ⇒
  ∃res.
    eval_wh_to k (subst1 v e (lets_for cn ar v (MAPi (λi v. (i,v)) vs) b)) = res ∧
    (res = wh_Diverge ∨
     k ≠ 0 ∧
     res =
      eval_wh_to (k - 1)
      (subst
        (FEMPTY |++ MAPi (λi v. (v, If (IsEq cn ar T e) (Proj cn i e) Bottom)) vs)
        (subst1 v e b)))
Proof
  Induct using SNOC_INDUCT >> rw[SNOC_APPEND, lets_for_def, lets_for_APPEND] >>
  Cases_on `vs = []` >> gvs[]
  >- (
    simp[lets_for_def, bind1_def, subst1_def, eval_wh_to_def, Bottom_def] >>
    IF_CASES_TAC >> gvs[] >> simp[FUPDATE_LIST_THM]
    ) >>
  last_x_assum drule >> disch_then drule >>
  strip_tac >> gvs[] >>
  simp[lets_for_APPEND, indexedListsTheory.MAPi_APPEND, lets_for_def] >>
  pop_assum $ qspecl_then
    [`k`,`cn`,
     `Let x (If (IsEq cn ar T (Var v)) (Proj cn (LENGTH vs) (Var v)) Bottom) b`]
    assume_tac >>
  gvs[] >>
  simp[subst_def, FLOOKUP_UPDATE, DOMSUB_FUPDATE_NEQ] >>
  simp[FUPDATE_LIST_APPEND, GSYM FUPDATE_EQ_FUPDATE_LIST] >>
  qmatch_goalsub_abbrev_tac `FEMPTY |++ m` >>
  simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[] >> simp[bind1_def] >>
  reverse $ rw[DISJ_EQ_IMP] >- gvs[Bottom_def, subst_def] >>
  drule eval_wh_inc >>
  disch_then $ qspec_then `k - 1` $ mp_tac o GSYM >> rw[] >>
  AP_TERM_TAC >> DEP_REWRITE_TAC[subst_subst_FUNION] >> simp[] >> conj_tac
  >- (
    simp[DOMSUB_FUPDATE_LIST] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
    simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, MEM_FILTER] >>
    unabbrev_all_tac >> simp[indexedListsTheory.MEM_MAPi, PULL_EXISTS, Bottom_def]
    ) >>
  AP_THM_TAC >> AP_TERM_TAC >>
  rw[fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM] >>
  every_case_tac >> gvs[Bottom_def, subst_def]
QED

Theorem eval_wh_to_Case:
  ∀css c ce v k e es cname vs.
  eval_wh_to k (exp_of e) = wh_Constructor cname es ∧
  closed (exp_of e) ∧
  ALOOKUP css cname = SOME (vs, ce) ∧
  ¬ MEM v vs ∧
  cname ∉ monad_cns ∧
  LENGTH vs = LENGTH es
  ⇒ ∃res.
      eval_wh_to k (exp_of (Case e v css)) = res ∧
      (res = wh_Diverge ∨
       k ≠ 0 ∧
       res =
        eval_wh_to (k - 1)
          (subst (FEMPTY |++ MAPi (λi v. (v, exp_of (SafeProj cname (LENGTH es) i e))) vs)
            (subst1 v (exp_of e) (exp_of ce))))
Proof
  Induct >> rw[exp_of_def, eval_wh_to_def, bind1_def] >>
  PairCases_on `h` >> gvs[] >> FULL_CASE_TAC >> gvs[] >>
  simp[rows_of_def, subst1_def, eval_wh_to_def] >>
  IF_CASES_TAC >> gvs[] >> simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[] >>
  Cases_on `eval_wh_to (k − 3) (exp_of e) = wh_Diverge` >> gvs[] >>
  drule eval_wh_inc >> disch_then $ qspec_then `k` $ mp_tac o GSYM >> rw[]
  >- (
    Cases_on `h1 = []` >> simp[lets_for_def, FUPDATE_LIST_THM]
    >- (
      rw[DISJ_EQ_IMP] >>
      drule eval_wh_inc >> disch_then $ irule o GSYM >> simp[]
      ) >>
    drule_all eval_wh_to_lets_for >>
    disch_then $ qspecl_then [`LENGTH es`,`k - 2`,`cname`,`exp_of ce`] mp_tac >> gvs[] >>
    rw[] >> gvs[] >> rw[DISJ_EQ_IMP] >>
    drule eval_wh_inc >> disch_then $ irule o GSYM >> simp[]
    )
  >- (
    `eval_wh_to (k - 1) (exp_of e) = wh_Constructor cname es` by (
      drule eval_wh_inc >> simp[]) >>
    last_x_assum drule >> simp[] >> disch_then drule >>
    gvs[exp_of_def, eval_wh_to_def, bind1_def] >>
    rw[] >> gvs[] >> rw[DISJ_EQ_IMP] >>
    drule eval_wh_inc >> disch_then $ irule o GSYM >> simp[]
    )
QED

Triviality MAPi_ID[simp]:
  ∀l. MAPi (λn v. v) l = l
Proof
  Induct >> rw[combinTheory.o_DEF]
QED

Theorem type_soundness_up_to:
  ∀k ce ns db st t.
    namespace_ok ns ∧
    EVERY (type_ok (SND ns) db) st ∧
    type_tcexp ns db st [] ce t
  ⇒ ∃wh. eval_wh_to k (exp_of ce) = wh ∧ type_wh ns db st [] wh t
Proof
  strip_tac >> completeInduct_on `k` >>
  recInduct exp_of_ind >> rw[exp_of_def]
  >- ( (* Var *)
    last_x_assum kall_tac >> gvs[Once type_tcexp_cases]
    )
  >- ( (* Prim *)
    Cases_on `p` >> gvs[pure_cexpTheory.op_of_def]
    >- (
      simp[eval_wh_to_def, type_wh_cases, SF ETA_ss] >>
      goal_assum $ drule_at Any >> simp[]
      )
    >- (
      rgs[Once type_tcexp_cases] >> gvs[]
      >- (simp[Once type_wh_cases] >> simp[Once type_tcexp_cases]) >>
      imp_res_tac get_PrimTys_SOME >>
      gvs[eval_wh_to_def, MAP_MAP_o, combinTheory.o_DEF] >>
      IF_CASES_TAC >> gvs[]
      >- (
        qspec_then `xs` assume_tac $ GEN_ALL get_atoms_MAP_Diverge >>
        reverse $ Cases_on `xs` >> gvs[combinTheory.K_DEF]
        >- simp[type_wh_cases, type_ok] >>
        simp[get_atoms_def] >>
        qspecl_then [`[]`,`pt`,`a`,`[]`]
          assume_tac $ GEN_ALL eval_op_type_safe >> gvs[] >>
        Cases_on `pt = Bool` >> gvs[]
        >- (IF_CASES_TAC >> simp[type_wh_cases] >> simp[Once type_tcexp_cases]) >>
        simp[type_wh_cases] >> simp[Once type_tcexp_cases, get_PrimTys_def] >>
        simp[type_atom_op_cases]
        ) >>
      CASE_TAC >> gvs[] >- simp[type_wh_cases, type_ok] >>
      CASE_TAC >> gvs[]
      >- (
        gvs[get_atoms_SOME_NONE_eq, EXISTS_MEM, LIST_REL_EL_EQN, EL_MAP, MEM_EL,
            PULL_EXISTS] >>
        first_x_assum drule >> strip_tac >>
        last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
        disch_then drule_all >> strip_tac >>
        qmatch_asmsub_abbrev_tac `type_wh _ _ _ _ atom` >>
        imp_res_tac type_atom_op_no_Bool >>
        drule type_wh_PrimTy_eq_wh_Atom >> gvs[MEM_EL] >>
        impl_tac >- (CCONTR_TAC >> gvs[]) >> rw[] >>
        pop_assum kall_tac >> first_x_assum $ qspec_then `n` assume_tac >> gvs[]
        ) >>
      gvs[get_atoms_SOME_SOME_eq] >> rename1 `MAP wh_Atom atoms` >>
      gvs[MAP_EQ_EVERY2] >>
      `LIST_REL type_lit atoms pts` by (
        gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
        ntac 2 (first_x_assum drule >> strip_tac) >>
        last_x_assum $ qspec_then `k - 1` assume_tac >> gvs[] >>
        pop_assum drule_all >> gvs[] >> simp[Once type_wh_cases] >>
        simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases]) >>
      qspecl_then [`pts`,`pt`,`a`,`atoms`]
        assume_tac $ GEN_ALL eval_op_type_safe >> gvs[] >>
      Cases_on `pt = Bool` >> gvs[]
      >- (IF_CASES_TAC >> simp[type_wh_cases, Once type_tcexp_cases]) >>
      simp[type_wh_cases] >>
      simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_def]
      )
    >- (
      pop_assum mp_tac >> simp[Once type_tcexp_cases] >> rw[] >>
      simp[eval_wh_to_def] >> reverse $ IF_CASES_TAC >> gvs[]
      >- (FULL_CASE_TAC >> gvs[])
      >- (
        simp[type_wh_cases] >>
        irule type_tcexp_type_ok >> simp[] >>
        rpt $ goal_assum $ drule_at Any >> simp[]
        ) >>
      FULL_CASE_TAC >> gvs[] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      ntac 2 $ disch_then drule >>
      disch_then $ qspecl_then [`e1`,`t1`] mp_tac >> gvs[] >>
      simp[type_wh_cases]
      )
    )
  >- ( (* Let *)
    rgs[eval_wh_to_def] >> rw[]
    >- (
      simp[type_wh_cases] >> irule type_tcexp_type_ok >> simp[] >>
      rpt $ goal_assum $ drule_at Any >> simp[]
      ) >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >> rw[Once type_tcexp_cases] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    ntac 2 $ disch_then drule >>
    disch_then $ qspecl_then [`subst_tc1 v x y`,`t`] mp_tac >>
    simp[subst_exp_of, FMAP_MAP2_FUPDATE] >> impl_tac
    >- (irule type_tcexp_closing_subst1 >> simp[] >> goal_assum drule >> simp[]) >>
    simp[bind1_def, FMAP_MAP2_FEMPTY] >> IF_CASES_TAC >> gvs[] >>
    imp_res_tac type_tcexp_freevars_tcexp >> gvs[closed_def, freevars_exp_of]
    )
  >- ( (* Apps *)
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >> rw[Once type_tcexp_cases] >>
    rename1 `Functions _ rt` >>
    qpat_x_assum `∀a. MEM a _ ⇒ _` kall_tac >> qpat_x_assum `_ ≠ _` kall_tac >>
    first_x_assum drule_all >> strip_tac >>
    pop_assum mp_tac >> qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    map_every qid_spec_tac [`f`,`t`,`rt`,`ts`] >>
    pop_assum mp_tac >> map_every qid_spec_tac [`arg_tys`,`xs`] >>
    ho_match_mp_tac LIST_REL_strongind >> rw[] >> gvs[Apps_def, Functions_def] >>
    first_x_assum $ qspecl_then [`rt`,`App f [h1]`] mp_tac >>
    simp[exp_of_def, Apps_def] >> disch_then irule >> rw[]
    >- (simp[Once type_tcexp_cases] >> qexists_tac `[h2]` >> simp[Functions_def]) >>
    simp[eval_wh_to_def] >>
    drule_at (Pos last) type_tcexp_type_ok >> simp[type_ok] >> strip_tac >>
    imp_res_tac type_wh_Function_eq_wh_Closure >> gvs[] >- simp[type_wh_cases] >>
    IF_CASES_TAC >- simp[type_wh_cases] >>
    imp_res_tac type_tcexp_freevars_tcexp >> gvs[] >>
    rw[bind1_def, closed_def, freevars_exp_of] >>
    qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >>
    simp[Once type_wh_cases] >> strip_tac >> gvs[] >>
    pop_assum mp_tac >> simp[Once type_tcexp_cases] >> strip_tac >> gvs[] >>
    rename1 `ats ≠ []` >> Cases_on `ats` >> gvs[Functions_def] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    disch_then $ qspec_then `subst_tc1 x h1 ce` mp_tac >>
    simp[subst_exp_of, FMAP_MAP2_FUPDATE, FMAP_MAP2_FEMPTY] >>
    disch_then irule >> simp[] >>
    irule type_tcexp_closing_subst1 >> simp[] >>
    goal_assum drule >> simp[]
    )
  >- ( (* Lams *)
    imp_res_tac type_tcexp_tcexp_wf >> gvs[tcexp_wf_def] >>
    Cases_on `vs` >> gvs[Lams_def] >> simp[eval_wh_to_def] >>
    simp[Once type_wh_cases] >> rename1 `Lams hs` >> Cases_on `hs` >> gvs[]
    >- (gvs[Lams_def] >> irule_at Any EQ_REFL >> simp[]) >>
    rename1 `v1::v2::vs` >>
    qexists_tac `Lam (v2::vs) x` >> simp[exp_of_def] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    simp[Once type_tcexp_cases] >> strip_tac >> gvs[] >>
    ntac 2 $ simp[Once type_tcexp_cases, PULL_EXISTS] >>
    qexistsl_tac [`[HD arg_tys]`,`TL arg_tys`,`ret_ty`] >>
    simp[Functions_def] >> simp[GSYM Functions_def] >>
    Cases_on `arg_tys` >> gvs[] >> Cases_on `t` >> gvs[]
    )
  >- ( (* Letrec *)
    simp[eval_wh_to_def] >> rw[]
    >- (
      simp[type_wh_cases] >> irule type_tcexp_type_ok >> simp[] >>
      rpt $ goal_assum $ drule_at Any >> simp[]
      ) >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >> rw[Once type_tcexp_cases] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    ntac 2 $ disch_then drule >>
    disch_then $ qspecl_then
      [`subst_tc (FEMPTY |++ MAP (λ(g,x). (g, Letrec rs x)) rs) x`,`t`] mp_tac >>
    simp[subst_exp_of, FMAP_MAP2_FUPDATE_LIST, FMAP_MAP2_FEMPTY] >> impl_tac
    >- (
      irule type_tcexp_closing_subst >> simp[] >> goal_assum $ drule_at Any >>
      imp_res_tac LIST_REL_LENGTH >> simp[MAP_REVERSE, MAP_ZIP] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >> rw[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      simp[Once type_tcexp_cases] >>
      qexists_tac `MAP (tshift_scheme vars) schemes` >>
      gvs[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      first_assum drule >>
      pop_assum (fn th => pop_assum (fn th' => rewrite_tac[th,th'])) >>
      simp[] >> strip_tac >> reverse $ rw[]
      >- (
        gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rw[] >>
        first_x_assum drule >> rw[] >> drule type_ok_shift_db >> simp[]
        ) >>
      rw[LIST_REL_EL_EQN, EL_MAP] >> rename1 `EL m _` >>
      qmatch_goalsub_abbrev_tac `_ a (_ b)` >>
      PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
      first_x_assum drule >> rw[] >> drule type_tcexp_shift_db >> simp[] >>
      disch_then $ qspecl_then [`b0`,`vars`] mp_tac >>
      simp[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF] >>
      simp[GSYM shift_db_shift_db] >> rw[] >>
      irule quotientTheory.EQ_IMPLIES >> goal_assum drule >>
      rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> simp[LAMBDA_PROD]
      ) >>
    simp[bind_def, subst_funs_def] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, exp_of_def] >>
    IF_CASES_TAC >> gvs[] >> rename1 `false` >>
    gvs[flookup_fupdate_list] >> every_case_tac >> gvs[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> pairarg_tac >> gvs[] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, freevars_exp_of]
    >- (
      gvs[MEM_EL, LIST_REL_EL_EQN] >>
      qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
      first_x_assum drule >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      imp_res_tac type_tcexp_freevars_tcexp >>
      gvs[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[pred_setTheory.SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD, MEM_ZIP] >>
      metis_tac[MEM_EL]
      )
    >- (
      pop_assum kall_tac >>
      gvs[EXISTS_MAP, EXISTS_MEM] >> pairarg_tac >> gvs[freevars_exp_of] >>
      gvs[MEM_EL, LIST_REL_EL_EQN] >>
      qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
      first_x_assum drule >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      imp_res_tac type_tcexp_freevars_tcexp >>
      gvs[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[pred_setTheory.SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD, MEM_ZIP] >>
      metis_tac[MEM_EL]
      )
    )
  >- ( (* Case *)
    drule type_tcexp_freevars_tcexp >> rw[] >>
    drule_at (Pos last) type_tcexp_type_ok >> rw[] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    rw[Once type_tcexp_cases] >> gvs[]
    >- ( (* BoolCase *)
      Cases_on `eval_wh_to k (exp_of x) = wh_Diverge`
      >- (
        drule_at Any eval_wh_to_Case_wh_Diverge >>
        gvs[closed_def, freevars_exp_of] >>
        disch_then $ qspecl_then [`v`,`rs`] mp_tac >>
        impl_tac >- (Cases_on `rs` >> gvs[]) >>
        rw[exp_of_def, type_wh_cases]
        ) >>
      first_x_assum $ drule_all >> strip_tac >>
      `∃cn. eval_wh_to k (exp_of x) = wh_Constructor cn []` by (
        drule type_wh_PrimTy_Bool_eq_wh_Constructor >> rw[] >> gvs[]) >>
      drule eval_wh_to_Case >> simp[closed_def, freevars_exp_of, FUPDATE_LIST_THM] >>
      disch_then $ qspec_then `rs` mp_tac >>
      `∃ce. ALOOKUP rs cn = SOME ([],ce)` by (
        gvs[pred_setTheory.EXTENSION] >>
        first_x_assum $ qspec_then `cn` assume_tac >>
        Cases_on `ALOOKUP rs cn` >> gvs[ALOOKUP_NONE] >>
        drule type_wh_PrimTy_Bool_eq_wh_Constructor >> strip_tac >> gvs[] >>
        Cases_on `x'` >> gvs[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
      simp[exp_of_def] >> disch_then $ qspec_then `v` mp_tac >> gvs[] >>
      impl_tac >> rw[] >> gvs[]
      >- (
        qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >>
        rw[type_wh_cases, Once type_tcexp_cases, monad_cns_def]
        )
      >- simp[type_wh_cases] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      ntac 2 $ disch_then drule >>
      imp_res_tac ALOOKUP_MEM >> gvs[FORALL_PROD, EVERY_MEM] >>
      first_x_assum drule >> strip_tac >>
      drule type_tcexp_closing_subst1 >> simp[] >>
      disch_then drule >> strip_tac >>
      disch_then drule >> simp[subst_exp_of, FMAP_MAP2_FUPDATE, FMAP_MAP2_FEMPTY]
      )
    >- ( (* TupleCase *)
      Cases_on `eval_wh_to k (exp_of x) = wh_Diverge`
      >- (
        drule_at Any eval_wh_to_Case_wh_Diverge >>
        gvs[closed_def, freevars_exp_of] >>
        disch_then $ qspecl_then [`v`,`["",pvars,cexp]`] mp_tac >>
        rw[exp_of_def, type_wh_cases]
        ) >>
      last_x_assum assume_tac >>
      last_x_assum $ drule_at $ Pos last >> simp[] >> strip_tac >>
      drule type_wh_Tuple_eq_wh_Constructor >> rw[] >> gvs[] >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
      rw[] >> gvs[] >> pop_assum mp_tac >> rw[Once type_tcexp_cases, type_cons_def] >>
      drule eval_wh_to_Case >> simp[closed_def, freevars_exp_of] >>
      disch_then $ qspec_then `["",pvars,cexp]` mp_tac >> simp[] >>
      disch_then drule >> imp_res_tac LIST_REL_LENGTH >> gvs[exp_of_def] >>
      impl_tac >> rw[] >> gvs[]
      >- simp[monad_cns_def]
      >- simp[type_wh_cases] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then drule >> simp[] >>
      DEP_REWRITE_TAC[GSYM subst_subst1_UPDATE] >> simp[closed_def, freevars_exp_of] >>
      DEP_ONCE_REWRITE_TAC[GSYM FUPDATE_FUPDATE_LIST_COMMUTES] >>
      simp[combinTheory.o_DEF, GSYM FUPDATE_LIST_THM] >>
      disch_then $ qspec_then
        `subst_tc (FEMPTY |++ ((v,x)::
          (MAPi (λi v. (v, SafeProj "" (LENGTH tyargs) i x)) pvars))) cexp` mp_tac >>
      simp[subst_exp_of, FMAP_MAP2_FUPDATE_LIST, MAP_SNOC, FMAP_MAP2_FEMPTY] >>
      simp[exp_of_def, combinTheory.o_DEF] >>
      disch_then irule >> simp[] >>
      irule type_tcexp_closing_subst >>
      rpt $ goal_assum $ drule_at Any >>
      simp[MAP_REVERSE, MAP_ZIP, combinTheory.o_DEF, MAP_MAP_o] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      first_x_assum drule >> strip_tac >>
      simp[Once type_tcexp_cases] >>
      disj1_tac >> rpt $ goal_assum $ drule_at Any >> simp[oEL_THM]
      )
    >- ( (* ExceptionCase *)
      Cases_on `eval_wh_to k (exp_of x) = wh_Diverge`
      >- (
        drule_at Any eval_wh_to_Case_wh_Diverge >>
        gvs[closed_def, freevars_exp_of] >>
        disch_then $ qspecl_then [`v`,`rs`] mp_tac >>
        impl_tac >- (CCONTR_TAC >> gvs[]) >>
        rw[exp_of_def, type_wh_cases]
        ) >>
      first_x_assum drule >> simp[] >> disch_then drule_all >> rw[] >>
      drule type_wh_Exception_eq_wh_Constructor >> rw[] >> gvs[] >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
      rw[] >> gvs[] >>
      pop_assum mp_tac >> rw[Once type_tcexp_cases, type_exception_def] >> gvs[]
      >- (
        `cn ≠ "Subscript" ∧ cn ∉ monad_cns` by (
          imp_res_tac ALOOKUP_MEM >>
          gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
          qpat_x_assum `∀e. _ ∈ _ ⇒ ¬ _` $ qspec_then `cn` mp_tac >>
          rw[reserved_cns_def, MEM_MAP, FORALL_PROD, monad_cns_def] >> metis_tac[]
          ) >>
        drule eval_wh_to_Case >> simp[closed_def, freevars_exp_of] >>
        disch_then $ qspec_then `rs` mp_tac >>
        Cases_on `ALOOKUP rs cn` >> gvs[]
        >- (
          gvs[ALOOKUP_NONE, pred_setTheory.EXTENSION] >>
          imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, FORALL_PROD, EXISTS_PROD] >>
          metis_tac[]
          ) >>
        rename1 `SOME y` >> namedCases_on `y` ["vs ce"] >> simp[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
        first_x_assum drule >> simp[] >> strip_tac >>
        disch_then drule >>
        imp_res_tac LIST_REL_LENGTH >> simp[exp_of_def] >> rw[] >> simp[]
        >- rw[type_wh_cases] >>
        last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
        disch_then drule >> simp[] >>
        DEP_REWRITE_TAC[GSYM subst_subst1_UPDATE] >> simp[closed_def, freevars_exp_of] >>
        DEP_ONCE_REWRITE_TAC[GSYM FUPDATE_FUPDATE_LIST_COMMUTES] >>
        simp[combinTheory.o_DEF, GSYM FUPDATE_LIST_THM] >>
        disch_then $ qspec_then
          `subst_tc (FEMPTY |++ ((v,x)::
            (MAPi (λi v. (v, SafeProj cn (LENGTH vs) i x)) vs))) ce` mp_tac >>
        simp[subst_exp_of, FMAP_MAP2_FUPDATE_LIST, MAP_SNOC, FMAP_MAP2_FEMPTY] >>
        simp[exp_of_def, combinTheory.o_DEF] >>
        disch_then irule >> simp[] >>
        irule type_tcexp_closing_subst >>
        rpt $ goal_assum $ drule_at Any >>
        simp[MAP_REVERSE, MAP_ZIP, combinTheory.o_DEF, MAP_MAP_o] >>
        gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
        first_x_assum drule >> strip_tac >>
        simp[Once type_tcexp_cases, oEL_THM]
        )
      >- (
        drule eval_wh_to_Case >> simp[closed_def, freevars_exp_of] >>
        disch_then $ qspec_then `rs` mp_tac >>
        Cases_on `ALOOKUP rs "Subscript"` >> gvs[]
        >- (gvs[ALOOKUP_NONE, pred_setTheory.EXTENSION] >> metis_tac[]) >>
        rename1 `SOME y` >> namedCases_on `y` ["vs ce"] >> simp[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
        `ALOOKUP exndef "Subscript" = NONE` by (
          simp[ALOOKUP_NONE] >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
          first_x_assum irule >> simp[reserved_cns_def]) >>
        first_x_assum drule >> simp[] >> strip_tac >> gvs[] >> simp[monad_cns_def] >>
        disch_then $ qspec_then `v` mp_tac >> simp[exp_of_def] >> rw[] >> gvs[]
        >- rw[type_wh_cases] >>
        last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
        disch_then drule >> simp[] >>
        DEP_REWRITE_TAC[GSYM subst_subst1_UPDATE] >> simp[closed_def, freevars_exp_of] >>
        DEP_ONCE_REWRITE_TAC[GSYM FUPDATE_FUPDATE_LIST_COMMUTES] >> simp[] >>
        simp[combinTheory.o_DEF, GSYM FUPDATE_LIST_THM] >>
        disch_then $ qspec_then `subst_tc (FEMPTY |++ [(v,x)]) ce` mp_tac >>
        simp[subst_exp_of, FMAP_MAP2_FUPDATE_LIST, MAP_SNOC, FMAP_MAP2_FEMPTY] >>
        simp[exp_of_def, combinTheory.o_DEF] >>
        disch_then irule >> simp[] >>
        irule type_tcexp_closing_subst >> simp[PULL_EXISTS, EXISTS_PROD] >>
        qexists_tac `0` >> simp[] >> goal_assum drule >> simp[]
        )
      )
    >- ( (* Case *)
      Cases_on `eval_wh_to k (exp_of x) = wh_Diverge`
      >- (
        drule_at Any eval_wh_to_Case_wh_Diverge >>
        gvs[closed_def, freevars_exp_of] >>
        disch_then $ qspecl_then [`v`,`rs`] mp_tac >> reverse $ impl_tac
        >- rw[exp_of_def, type_wh_cases] >>
        gvs[oEL_THM, namespace_ok_def, EVERY_EL] >>
        last_x_assum drule >> simp[] >> Cases_on `rs` >> gvs[]
        ) >>
      first_x_assum drule >> simp[] >> disch_then drule_all >> rw[] >>
      drule type_wh_TypeCons_eq_wh_Constructor >> rw[] >> gvs[] >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
      rw[] >> gvs[] >> pop_assum mp_tac >> rw[Once type_tcexp_cases, type_cons_def] >>
      drule eval_wh_to_Case >> simp[closed_def, freevars_exp_of] >>
      disch_then $ qspec_then `rs` mp_tac >>
      Cases_on `ALOOKUP rs cname` >> gvs[]
      >- (
        gvs[ALOOKUP_NONE, pred_setTheory.EXTENSION] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, FORALL_PROD, EXISTS_PROD] >>
        metis_tac[]
        ) >>
      rename1 `SOME y` >> namedCases_on `y` ["vs ce"] >> simp[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
      first_x_assum drule >> simp[] >> strip_tac >>
      disch_then drule >>
      imp_res_tac LIST_REL_LENGTH >> simp[exp_of_def] >> impl_tac >> rw[] >> simp[]
      >- (
        CCONTR_TAC >> gvs[] >>
        gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        qpat_x_assum `∀e. _ ⇒ ¬ _` $ qspec_then `cname` mp_tac >>
        simp[MEM_MAP, MEM_FLAT, EXISTS_PROD, SF DNF_ss] >>
        disj1_tac >> goal_assum $ drule_at Any >> simp[MEM_EL, SF DNF_ss] >>
        gvs[oEL_THM] >> rpt $ goal_assum $ drule_at Any >> simp[] >>
        pop_assum mp_tac >> rw[monad_cns_def, reserved_cns_def]
        )
      >- rw[type_wh_cases] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then drule >> simp[] >>
      DEP_REWRITE_TAC[GSYM subst_subst1_UPDATE] >> simp[closed_def, freevars_exp_of] >>
      DEP_ONCE_REWRITE_TAC[GSYM FUPDATE_FUPDATE_LIST_COMMUTES] >>
      simp[combinTheory.o_DEF, GSYM FUPDATE_LIST_THM] >>
      disch_then $ qspec_then
        `subst_tc (FEMPTY |++ ((v,x)::
          (MAPi (λi v. (v, SafeProj cname (LENGTH schemes) i x)) vs))) ce` mp_tac >>
      simp[subst_exp_of, FMAP_MAP2_FUPDATE_LIST, MAP_SNOC, FMAP_MAP2_FEMPTY] >>
      simp[exp_of_def, combinTheory.o_DEF] >>
      disch_then irule >> simp[] >>
      irule type_tcexp_closing_subst >>
      rpt $ goal_assum $ drule_at Any >>
      simp[MAP_REVERSE, MAP_ZIP, combinTheory.o_DEF, MAP_MAP_o] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      first_x_assum drule >> strip_tac >>
      simp[Once type_tcexp_cases] >>
      disj2_tac >> disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[oEL_THM]
      )
    )
  >- ( (* SafeProj *)
    drule type_tcexp_freevars_tcexp >> rw[] >>
    drule_at (Pos last) type_tcexp_type_ok >> rw[] >>
    gvs[eval_wh_to_def] >> rw[] >- simp[type_wh_cases] >>
    simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[] >- simp[type_wh_cases] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >> rw[Once type_tcexp_cases]
    >- ( (* TupleSafeProj *)
      first_x_assum $ drule_all >> strip_tac >>
      drule type_wh_Tuple_eq_wh_Constructor >> rw[] >> gvs[]
      >- (
        qsuff_tac `eval_wh_to (k - 2) (exp_of e) = wh_Diverge` >> reverse $ rw[]
        >- simp[type_wh_cases] >>
        CCONTR_TAC >> drule eval_wh_inc >> simp[] >> qexists_tac `k` >> simp[]
        ) >>
      Cases_on `eval_wh_to (k - 2) (exp_of e) = wh_Diverge` >> gvs[]
      >- simp[type_wh_cases] >>
      drule eval_wh_inc >> disch_then $ qspec_then `k` $ assume_tac o GSYM >>
      gvs[] >> simp[monad_cns_def] >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >>
      simp[Once type_wh_cases] >> simp[Once type_tcexp_cases] >> strip_tac >>
      gvs[LIST_REL_EL_EQN, oEL_THM, EL_MAP]
      )
    >- ( (* ExceptionSafeProj *)
      first_x_assum $ drule_all >> strip_tac >>
      drule type_wh_Exception_eq_wh_Constructor >> rw[] >> gvs[]
      >- (
        qsuff_tac `eval_wh_to (k - 2) (exp_of e) = wh_Diverge` >> reverse $ rw[]
        >- simp[type_wh_cases] >>
        CCONTR_TAC >> drule eval_wh_inc >> simp[] >> qexists_tac `k` >> simp[]
        ) >>
      Cases_on `eval_wh_to (k - 2) (exp_of e) = wh_Diverge` >> gvs[]
      >- simp[type_wh_cases] >>
      drule eval_wh_inc >> disch_then $ qspec_then `k` $ assume_tac o GSYM >>
      gvs[] >>
      `cn' ∉ monad_cns` by (
        qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >>
        simp[Once type_wh_cases, Once type_tcexp_cases] >>
        reverse $ rw[] >> gvs[type_exception_def] >- simp[monad_cns_def] >>
        drule ALOOKUP_MEM >> rw[] >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        qpat_x_assum `∀e. _ ∈ _ ⇒ ¬_` $ qspec_then `cn'` mp_tac >>
        simp[MEM_MAP, FORALL_PROD] >> disch_then $ drule_at Concl >>
        rw[reserved_cns_def, monad_cns_def]) >>
      simp[] >> qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >>
      simp[Once type_wh_cases] >> simp[Once type_tcexp_cases] >> reverse strip_tac
      >- (
        gvs[] >>
        `cn ≠ "Subscript"` by (
          imp_res_tac ALOOKUP_MEM >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
          last_x_assum $ qspec_then `"Subscript"` mp_tac >>
          rw[reserved_cns_def, MEM_MAP, FORALL_PROD] >> metis_tac[]) >>
        gvs[] >> mp_tac eval_wh_Bottom >> simp[eval_wh_def] >>
        DEEP_INTRO_TAC some_intro >> rw[type_wh_cases]
        ) >>
      gvs[type_exception_def] >> IF_CASES_TAC >> gvs[]
      >- (
        assume_tac eval_wh_Bottom >> gvs[eval_wh_eq_Diverge] >>
        simp[type_wh_cases]
        ) >>
      gvs[LIST_REL_EL_EQN, oEL_THM, EL_MAP]
      )
    >- ( (* SafeProj *)
      first_x_assum $ drule_all >> strip_tac >>
      drule type_wh_TypeCons_eq_wh_Constructor >> rw[] >> gvs[]
      >- (
        qsuff_tac `eval_wh_to (k - 2) (exp_of e) = wh_Diverge` >> reverse $ rw[]
        >- simp[type_wh_cases] >>
        CCONTR_TAC >> drule eval_wh_inc >> simp[] >> qexists_tac `k` >> simp[]
        ) >>
      Cases_on `eval_wh_to (k - 2) (exp_of e) = wh_Diverge` >> gvs[]
      >- simp[type_wh_cases] >>
      drule eval_wh_inc >> disch_then $ qspec_then `k` $ assume_tac o GSYM >>
      gvs[] >>
      `cname ∉ monad_cns` by (
        qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >>
        rw[Once type_wh_cases, Once type_tcexp_cases] >> gvs[type_cons_def] >>
        drule ALOOKUP_MEM >> rw[] >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        gvs[SF DNF_ss] >>
        qpat_x_assum `∀e. _ ∈ reserved_cns ⇒ _` $ qspec_then `cname` mp_tac >>
        simp[MEM_MAP, MEM_FLAT, FORALL_PROD, DISJ_EQ_IMP, PULL_EXISTS] >>
        disch_then $ drule_at Concl >> simp[MEM_EL, DISJ_EQ_IMP] >> gvs[oEL_THM] >>
        disch_then $ drule_at Concl >> rw[reserved_cns_def, monad_cns_def]) >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >>
      simp[Once type_wh_cases] >> simp[Once type_tcexp_cases] >> strip_tac >> gvs[] >>
      IF_CASES_TAC >> gvs[]
      >- (
        assume_tac eval_wh_Bottom >> gvs[eval_wh_eq_Diverge] >>
        simp[type_wh_cases]
        ) >>
      gvs[type_cons_def] >> imp_res_tac LIST_REL_LENGTH >> gvs[oEL_THM, EL_MAP] >>
      last_x_assum irule >> simp[] >>
      gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[EL_MAP]
      )
    )
QED

Theorem type_soundness_eval_wh:
  namespace_ok ns ∧
  EVERY (type_ok (SND ns) db) st ∧
  type_tcexp ns db st [] ce t ⇒
  type_wh ns db st [] (eval_wh $ exp_of ce) t
Proof
  rw[] >> drule_all type_soundness_up_to >> strip_tac >>
  rw[eval_wh_def] >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[]
QED


(********************)


Theorem type_wh_monad:
  type_wh ns db st env wh (M t) ⇒
  wh = wh_Diverge ∨
  ∃cn es. wh = wh_Constructor cn es ∧ cn ∈ monad_cns
Proof
  rw[type_wh_cases] >> gvs[Once type_tcexp_cases, monad_cns_def] >>
  Cases_on `arg_tys` >> gvs[Functions_def]
QED

Definition type_exp_def:
  type_exp ns db st e t ⇔
    ∃tce. type_tcexp ns db st [] tce t ∧ exp_of tce = e
End

Datatype:
  cont_type = DoneT
            | BCT type type cont_type (* arg type, return type *)
            | HCT type cont_type      (* return type *)
End

Definition unwind_stack_def:
  unwind_stack DoneT = NONE ∧
  unwind_stack (BCT t1 t2 stack) = unwind_stack stack ∧
  unwind_stack (HCT t stack) = SOME (t, stack)
End

Inductive type_cont:
  type_cont ns db st Done DoneT ∧

  (type_exp ns db st cont (Function t1 (M t2)) ∧
   type_cont ns db st stack t ⇒
    type_cont ns db st (BC cont stack) (BCT t1 t2 t)) ∧

  (type_exp ns db st cont (Function Exception (M t1)) ∧
   type_cont ns db st stack t ⇒
    type_cont ns db st (HC cont stack) (HCT t1 t))
End

Inductive config_type_ok:
  config_type_ok (t, DoneT) t ∧

  (config_type_ok (t2, stack) t ∧
   (∀t3 stack'.
    unwind_stack stack = SOME (t3, stack') ⇒ config_type_ok (t3, stack') t) ⇒
      config_type_ok (t1, BCT t1 t2 stack) t) ∧

   (config_type_ok (t2, stack) t ∧
    config_type_ok (t1, stack) t ⇒
      config_type_ok (t1, HCT t2 stack) t)
End

Definition type_config_def:
  type_config ns db st (wh, stack, state) t ⇔
    ∃wh_ty stack_ty.
      LIST_REL (λes t. EVERY (λe. type_exp ns db st e t) es) state st ∧
      type_wh ns db st [] wh (M wh_ty) ∧
      type_cont ns db st stack stack_ty ∧
      config_type_ok (wh_ty, stack_ty) t
End

Inductive type_next_res:
  type_next_res ns db st Ret t ∧
  type_next_res ns db st Div t ∧
  ((∀y. type_config ns db st (wh_Constructor "Ret" [Lit $ Str y], stack, state) t) ⇒
    type_next_res ns db st (pure_semantics$Act a stack state) t)
End

Theorem config_type_ok_unwind_stack:
  ∀stack_ty wh_ty t.
    config_type_ok (wh_ty, stack_ty) t ⇒
  ∀t' s'. unwind_stack stack_ty = SOME (t',s') ⇒ config_type_ok (t',s') t
Proof
  Induct >> rw[unwind_stack_def]
  >- (
    first_x_assum irule >> simp[] >>
    qpat_x_assum `config_type_ok _ _` mp_tac >>
    once_rewrite_tac[config_type_ok_cases] >>
    strip_tac >> once_rewrite_tac[GSYM config_type_ok_cases] >> gvs[] >>
    goal_assum drule
    )
  >- (
    pop_assum mp_tac >>
    once_rewrite_tac[config_type_ok_cases] >>
    strip_tac >> once_rewrite_tac[GSYM config_type_ok_cases] >> gvs[]
    )
QED

Theorem type_cont_weaken_state:
  type_cont ns db st stack stack_ty ⇒
  type_cont ns db (st ++ st') stack stack_ty
Proof
  Induct_on `type_cont` >> rw[] >> simp[Once type_cont_cases] >>
  gvs[type_exp_def] >> irule_at Any EQ_REFL >>
  drule type_tcexp_weaken >>
  disch_then $ qspecl_then [`0`,`st'`,`[]`] mp_tac >> simp[]
QED

Theorem type_soundness_next:
  ∀k st wh stack state t.
    namespace_ok ns ∧ EVERY (type_ok (SND ns) db) st ∧
    type_config ns db st (wh, stack, state) t
  ⇒ ∃st'.
    type_next_res ns db (st ++ st') (next k wh stack state) t ∧
    EVERY (type_ok (SND ns) db) st'
Proof
  strip_tac >> completeInduct_on `k` >> rw[] >>
  last_x_assum $ qspec_then `k - 1` assume_tac >> gvs[] >>
  qpat_x_assum `type_config _ _ _ _ _` mp_tac >> rw[Once type_config_def] >>
  imp_res_tac type_wh_monad >> rgs[]
  >- (simp[next_def, type_next_res_cases] >> goal_assum drule) >>
  qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[type_wh_cases] >>
  simp[Once type_tcexp_cases] >> strip_tac >> rgs[monad_cns_def] >>
  once_rewrite_tac[next_def] >> simp[]
  >- (
    TOP_CASE_TAC >> rgs [] \\ gvs []
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (
      gvs[Once type_cont_cases, apply_closure_def, type_exp_def] >>
      IF_CASES_TAC >- (simp[type_next_res_cases] >> goal_assum drule) >>
      drule_all type_soundness_eval_wh >> strip_tac >>
      drule type_wh_Function_eq_wh_Closure >> rw[] >> simp[] >>
      IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
      last_x_assum drule >> disch_then irule >>
      simp[type_config_def, type_exp_def] >> goal_assum $ drule_at Any >>
      qpat_x_assum `config_type_ok _ _` mp_tac >>
      simp[Once config_type_ok_cases] >> strip_tac >> gvs[] >>
      goal_assum $ drule_at Any >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
      strip_tac >> gvs[] >> pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      Cases_on `arg_tys` >> gvs[Functions_def] >>
      `closed (exp_of e)` by (
        imp_res_tac type_tcexp_freevars_tcexp >>
        gvs[closed_def, freevars_exp_of]) >>
      simp[bind1_def] >>
      drule type_tcexp_closing_subst1 >> simp[] >>
      disch_then drule >> strip_tac >>
      drule_at (Pos last) type_soundness_eval_wh >>
      simp[subst_exp_of, FMAP_MAP2_FUPDATE, FMAP_MAP2_FEMPTY]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
      first_x_assum irule >> simp[type_config_def] >>
      qpat_x_assum `type_cont _ _ _ _ _` mp_tac >> rw[Once type_cont_cases] >>
      goal_assum $ drule_at Any >>
      qpat_x_assum `config_type_ok _ _` mp_tac >> rw[Once config_type_ok_cases] >>
      goal_assum $ drule_at Any >>
      simp[type_wh_cases, PULL_EXISTS] >> irule_at Any EQ_REFL >>
      simp[Once type_tcexp_cases]
      )
    )
  >- (
    IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
    first_x_assum irule >> simp[type_config_def] >>
    qexistsl_tac [`t1`,`BCT t1 wh_ty stack_ty`] >>
    simp[Once type_cont_cases, type_exp_def, PULL_EXISTS, GSYM CONJ_ASSOC] >>
    goal_assum $ drule_at Any >> simp[] >>
    irule_at Any type_soundness_eval_wh >> simp[] >>
    simp[Once config_type_ok_cases] >>
    ho_match_mp_tac config_type_ok_unwind_stack >> goal_assum drule
    )
  >- (
    TOP_CASE_TAC >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (
      IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
      first_x_assum irule >> simp[type_config_def] >>
      qpat_x_assum `type_cont _ _ _ _ _` mp_tac >> rw[Once type_cont_cases] >>
      goal_assum $ drule_at Any >>
      qpat_x_assum `config_type_ok _ _` mp_tac >>
      simp[Once config_type_ok_cases] >> strip_tac >> gvs[] >>
      goal_assum $ drule_at Any >>
      simp[type_wh_cases, PULL_EXISTS] >> irule_at Any EQ_REFL >>
      simp[Once type_tcexp_cases] >> gvs[type_exp_def] >>
      drule_at Any type_tcexp_type_ok >> gvs[type_ok]
      )
    >- (
      gvs[Once type_cont_cases, apply_closure_def, type_exp_def] >>
      IF_CASES_TAC >- (simp[type_next_res_cases] >> goal_assum drule) >>
      drule_all type_soundness_eval_wh >> strip_tac >>
      drule type_wh_Function_eq_wh_Closure >> rw[] >> simp[] >>
      IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
      last_x_assum drule >> disch_then irule >>
      simp[type_config_def, type_exp_def] >> goal_assum $ drule_at Any >>
      qpat_x_assum `config_type_ok _ _` mp_tac >>
      simp[Once config_type_ok_cases] >> strip_tac >> gvs[] >>
      qexists_tac `t1` >> simp[] >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
      strip_tac >> gvs[] >> pop_assum mp_tac >> rw[Once type_tcexp_cases] >>
      Cases_on `arg_tys` >> gvs[Functions_def] >>
      `closed (exp_of e)` by (
        imp_res_tac type_tcexp_freevars_tcexp >>
        gvs[closed_def, freevars_exp_of]) >>
      simp[bind1_def] >>
      drule type_tcexp_closing_subst1 >> simp[] >>
      disch_then drule >> strip_tac >>
      drule_at (Pos last) type_soundness_eval_wh >>
      simp[subst_exp_of, FMAP_MAP2_FUPDATE, FMAP_MAP2_FEMPTY]
      )
    )
  >- (
    IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
    first_x_assum irule >> simp[type_config_def] >>
    qexistsl_tac [`wh_ty`,`HCT wh_ty stack_ty`] >>
    simp[Once type_cont_cases, Once config_type_ok_cases] >>
    simp[type_exp_def, PULL_EXISTS] >> goal_assum $ drule_at Any >> simp[] >>
    irule type_soundness_eval_wh >> simp[]
    )
  >- (
    drule_at (Pos last) type_soundness_eval_wh >> rw[] >>
    drule type_wh_PrimTy_eq_wh_Atom >> simp[] >>
    simp[with_atom_def, with_atoms_def] >> strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases, type_lit_cases] >>
    strip_tac >> gvs[] >> qexists_tac `[]` >> simp[] >>
    rw[type_next_res_cases] >> simp[type_config_def] >>
    goal_assum $ drule_at Any >> simp[type_wh_cases, PULL_EXISTS] >>
    qexists_tac `Prim (AtomOp $ Lit $ Str y) []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    ntac 2 $ simp[Once type_tcexp_cases] >>
    simp[get_PrimTys_def, type_atom_op_cases, type_lit_cases]
    )
  >- (
    qpat_x_assum `_ (PrimTy _)` assume_tac >>
    drule_at (Pos last) type_soundness_eval_wh >> rw[] >>
    drule type_wh_PrimTy_eq_wh_Atom >> simp[] >>
    simp[with_atom_def, with_atoms_def] >> strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases, type_lit_cases] >>
    strip_tac >> gvs[] >> IF_CASES_TAC >> gvs[]
    >- (qexists_tac `[]` >> simp[type_next_res_cases]) >>
    Q.REFINE_EXISTS_TAC `[t'] ++ rest` >> simp[] >>
    `type_ok (SND ns) db t'` by (
      irule type_tcexp_type_ok >> simp[] >>
      goal_assum $ drule_at $ Pos last >> simp[]) >>
    simp[] >> first_x_assum irule >> simp[type_config_def, GSYM CONJ_ASSOC] >>
    irule_at Any type_cont_weaken_state >> goal_assum drule >>
    goal_assum $ drule_at Any >> conj_tac
    >- (
      gvs[LIST_REL_EL_EQN, EVERY_MEM] >> rw[] >>
      last_x_assum drule_all >> strip_tac >> gvs[type_exp_def] >>
      irule_at Any EQ_REFL >> drule type_tcexp_weaken >>
      disch_then $ qspecl_then [`0`,`[t']`,`[]`] mp_tac >> simp[]
      ) >>
    simp[type_wh_cases, Once type_tcexp_cases, PULL_EXISTS] >>
    qexists_tac `Prim (AtomOp $ Lit $ Loc $ LENGTH state) []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    simp[Once type_tcexp_cases, oEL_THM, EL_APPEND_EQN] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    IF_CASES_TAC >> gvs[] >> rw[DISJ_EQ_IMP] >>
    simp[type_exp_def] >> irule_at Any EQ_REFL >>
    qpat_x_assum `_ e2 t'` assume_tac >> drule type_tcexp_weaken >>
    disch_then $ qspecl_then [`0`,`[t']`,`[]`] mp_tac >> simp[]
    )
  >- (
    drule_at (Pos last) type_soundness_eval_wh >> rw[] >>
    drule type_wh_Array_eq_Loc >> simp[] >>
    simp[with_atom_def, with_atoms_def] >> strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases, oEL_THM] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    IF_CASES_TAC >> gvs[] >- (simp[type_next_res_cases] >> goal_assum drule) >>
    first_x_assum irule >> simp[type_config_def] >>
    simp[type_wh_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
    goal_assum $ drule_at Any >> simp[] >>
    qmatch_goalsub_abbrev_tac `Lit a` >>
    qexists_tac `Prim (AtomOp $ Lit a) []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    ntac 2 $ simp[Once type_tcexp_cases] >>
    simp[get_PrimTys_def, type_atom_op_cases] >>
    unabbrev_all_tac >> simp[type_lit_def]
    )
  >- (
    drule_at (Pos last) type_soundness_eval_wh >> simp[] >> strip_tac >>
    drule type_wh_PrimTy_eq_wh_Atom >> simp[] >>
    qpat_x_assum `type_tcexp _ _ _ _ e1 _` assume_tac >>
    drule_at (Pos last) type_soundness_eval_wh >> simp[] >> strip_tac >>
    drule type_wh_Array_eq_Loc >> simp[] >>
    simp[with_atom2_def, with_atoms_def] >> ntac 2 strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases, oEL_THM] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ (PrimTy _)` mp_tac >>
    simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases, type_lit_cases] >>
    strip_tac >> gvs[] >>
    Cases_on `k = 0` >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    IF_CASES_TAC >> gvs[]
    >- (
      first_x_assum irule >> simp[type_config_def] >>
      goal_assum $ drule_at Any >> simp[] >>
      simp[type_wh_cases, PULL_EXISTS] >>
      gvs[LIST_REL_EL_EQN] >>
      last_x_assum drule >> simp[EVERY_EL, type_exp_def] >>
      disch_then $ qspec_then `Num i` mp_tac >> simp[] >> impl_tac
      >- (Cases_on `i` >> gvs[]) >>
      strip_tac >> gvs[] >>
      goal_assum $ drule o GSYM >> simp[Once type_tcexp_cases]
      ) >>
    first_x_assum irule >> simp[type_config_def] >>
    goal_assum $ drule_at Any >> simp[] >>
    simp[type_wh_cases, PULL_EXISTS] >>
    qexists_tac `Prim (Cons "Subscript") []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    ntac 2 $ simp[Once type_tcexp_cases] >> gvs[EVERY_EL]
    )
  >- (
    qpat_x_assum `type_tcexp _ _ _ _ e2 _` assume_tac >>
    drule_at (Pos last) type_soundness_eval_wh >> simp[] >> strip_tac >>
    drule type_wh_PrimTy_eq_wh_Atom >> simp[] >>
    qpat_x_assum `type_tcexp _ _ _ _ e1 _` assume_tac >>
    drule_at (Pos last) type_soundness_eval_wh >> simp[] >> strip_tac >>
    drule type_wh_Array_eq_Loc >> simp[] >>
    simp[with_atom2_def, with_atoms_def] >> ntac 2 strip_tac >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (simp[type_next_res_cases] >> goal_assum drule)
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    simp[pure_semanticsTheory.get_atoms_def] >> gvs[type_wh_cases, oEL_THM] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ (PrimTy _)` mp_tac >>
    simp[Once type_tcexp_cases, get_PrimTys_def, type_atom_op_cases, type_lit_cases] >>
    strip_tac >> gvs[] >>
    Cases_on `k = 0` >> gvs[]
    >- (simp[type_next_res_cases] >> goal_assum drule) >>
    IF_CASES_TAC >> gvs[]
    >- (
      first_x_assum irule >> simp[type_config_def] >>
      goal_assum $ drule_at Any >> simp[] >>
      simp[type_wh_cases, PULL_EXISTS] >>
      qexists_tac `Prim (Cons "") []` >>
      simp[exp_of_def, pure_cexpTheory.op_of_def] >>
      ntac 2 $ simp[Once type_tcexp_cases] >>
      gvs[LIST_REL_EL_EQN, EVERY_EL] >> rw[EL_LUPDATE] >>
      IF_CASES_TAC >> gvs[EL_LUPDATE] >>
      simp[type_exp_def] >> goal_assum drule >> simp[]
      ) >>
    first_x_assum irule >> simp[type_config_def] >>
    goal_assum $ drule_at Any >> simp[] >>
    simp[type_wh_cases, PULL_EXISTS] >>
    qexists_tac `Prim (Cons "Subscript") []` >>
    simp[exp_of_def, pure_cexpTheory.op_of_def] >>
    ntac 2 $ simp[Once type_tcexp_cases, type_ok]
    )
QED

Theorem type_soundness_next_action:
  ∀ns db st wh stack state t.
    namespace_ok ns ∧ EVERY (type_ok (SND ns) db) st ∧
    type_config ns db st (wh, stack, state) t
  ⇒ ∃st'.
      type_next_res ns db (st ++ st') (next_action wh stack state) t ∧
      EVERY (type_ok (SND ns) db) st'
Proof
  rw[next_action_def] >>
  DEEP_INTRO_TAC some_intro >> reverse $ rw[]
  >- (simp[type_next_res_cases] >> goal_assum drule) >>
  drule_all type_soundness_next >> simp[]
QED

Theorem type_soundness_interp:
  ∀ns db st wh stack state t.
    namespace_ok ns ∧ EVERY (type_ok (SND ns) db) st ∧
    type_config ns db st (wh, stack, state) t
  ⇒ safe_itree (interp wh stack state)
Proof
  qsuff_tac
    `∀tree.
      (∃ns db st wh stack state t.
      (namespace_ok ns ∧ EVERY (type_ok (SND ns) db) st ∧
      type_config ns db st (wh, stack, state) t ∧
      tree = interp wh stack state)) ∨ (∃e f. tree = Ret (FinalFFI e f))
    ⇒ safe_itree tree`
  >- (
    rw[] >> first_x_assum irule >> disj1_tac >>
    rpt $ goal_assum drule >> simp[]
    ) >>
  ho_match_mp_tac safe_itree_coind >> rw[] >>
  drule_all type_soundness_next_action >>
  simp[Once type_next_res_cases] >> strip_tac >> gvs[]
  >- (once_rewrite_tac[interp_def] >> simp[])
  >- (once_rewrite_tac[interp_def] >> simp[]) >>
  ntac 3 disj2_tac >> rw[Once interp_def] >>
  CASE_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >> disj1_tac >>
  goal_assum drule >> irule_at Any $ EQ_REFL >>
  first_x_assum $ qspec_then `y` assume_tac >>
  goal_assum $ drule_at $ Pos last >> simp[]
QED

Theorem type_soundness_tcexp:
  namespace_ok ns ∧ type_tcexp ns db [] [] tce (M t) ⇒
  safe_itree (itree_of (exp_of tce))
Proof
  rw[itree_of_def, semantics_def] >>
  irule type_soundness_interp >>
  simp[type_config_def, PULL_EXISTS] >>
  simp[Once type_cont_cases, Once config_type_ok_cases] >>
  goal_assum drule >>
  irule_at Any type_soundness_eval_wh >> simp[] >>
  goal_assum drule
QED

Theorem type_soundness_cexp:
  namespace_ok ns ∧ type_tcexp ns db [] [] (tcexp_of ce) (M t) ⇒
  safe_itree (itree_of (exp_of ce))
Proof
  rw[] >>
  `itree_of (exp_of ce) = itree_of (exp_of $ tcexp_of ce)` by (
    rw[itree_of_def] >>
    irule pure_obs_sem_equalTheory.bisimilarity_IMP_semantics_eq >>
    simp[pure_exp_relTheory.app_bisimilarity_eq] >>
    irule_at Any $ iffLR pure_congruenceTheory.exp_eq_sym >>
    irule_at Any exp_of_tcexp_of_exp_eq >>
    drule type_tcexp_freevars_tcexp >> strip_tac >>
    drule_at (Pos last) type_tcexp_tcexp_wf >> strip_tac >> gvs[] >>
    simp[cexp_wf_tcexp_wf, closed_def, freevars_exp_of] >>
    gvs[freevars_tcexp_of, pure_cexp_lemmasTheory.freevars_exp_of]) >>
  rw[itree_of_def, semantics_def] >>
  irule type_soundness_interp >>
  simp[type_config_def, PULL_EXISTS] >>
  simp[Once type_cont_cases, Once config_type_ok_cases] >>
  goal_assum drule >>
  irule_at Any type_soundness_eval_wh >> simp[] >>
  goal_assum drule
QED


(********************)

val _ = export_theory();
