open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory rich_listTheory alistTheory finite_mapTheory;
open pure_miscTheory pure_configTheory pure_expTheory pure_exp_lemmasTheory
     pure_evalTheory pure_cexpTheory pure_cexp_lemmasTheory
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

(* TODO: can't have α in α cexp free, so we use unit here.
   We should prove a basic theorem about types not caring about the α. *)
Inductive type_wh:
  (type_cexp ns db st env (Prim () (Cons s) ces) t ∧
   MAP exp_of ces = es ⇒
    type_wh ns db st env (wh_Constructor s es) t) ∧

  (type_cexp ns db st env (ce : unit cexp) t ∧
   exp_of ce = Lam s e ⇒
    type_wh ns db st env (wh_Closure s e) t) ∧

  (type_cexp ns db st env (Prim () (AtomOp $ Lit l) []) t ⇒
    type_wh ns db st env (wh_Atom l) t) ∧

  (type_ok (SND ns) db t ⇒ type_wh ns db st env wh_Diverge t)
End

Triviality type_wh_PrimTy_eq_wh_Atom:
  type_wh ns db st env wh (PrimTy pt) ∧ pt ≠ Bool ⇒
    wh = wh_Diverge ∨ ∃a. wh = wh_Atom a
Proof
  rw[type_wh_cases]
  >- gvs[Once type_cexp_cases] >>
  reverse $ Cases_on `ce` >> gvs[exp_of_def] >>
  gvs[Once type_cexp_cases] >>
  Cases_on `l` using SNOC_CASES >> gvs[MAP_SNOC, Apps_SNOC]
QED

Triviality type_wh_Function_eq_wh_Closure:
  type_wh ns db st env wh (Function ft rt) ⇒
    wh = wh_Diverge ∨ ∃x body. wh = wh_Closure x body
Proof
  rw[type_wh_cases] >> gvs[Once type_cexp_cases]
QED

Triviality type_wh_TypeCons_eq_wh_Constructor:
  type_wh ns db st env wh (TypeCons id ts) ⇒
    wh = wh_Diverge ∨ ∃cname es. wh = wh_Constructor cname es
Proof
  rw[type_wh_cases] >> gvs[Once type_cexp_cases, exp_of_def] >>
  Cases_on `es` using SNOC_CASES >> gvs[MAP_SNOC, Apps_SNOC]
QED

Triviality type_cexp_type_ok_unit =
  type_cexp_type_ok |> INST_TYPE [alpha |-> ``:unit``];

Theorem eval_wh_to_Case_wh_Diverge:
  closed (exp_of e) ∧ eval_wh_to k (exp_of e) = wh_Diverge ∧ es ≠ [] ⇒
  eval_wh_to k (exp_of (Case c e v es)) = wh_Diverge
Proof
  rw[exp_of_def, eval_wh_to_def, bind1_def] >>
  Cases_on `es` >> gvs[rows_of_def] >>
  PairCases_on `h` >> gvs[rows_of_def, subst1_def] >>
  rw[eval_wh_to_def] >>
  IF_CASES_TAC >> gvs[] >>
  qsuff_tac `eval_wh_to (k - 3) (exp_of e) = wh_Diverge` >> gvs[] >>
  CCONTR_TAC >> drule eval_wh_inc >> simp[] >> qexists_tac `k` >> simp[]
QED

Theorem lets_for_APPEND:
  ∀ws1 ws2 cn v n w b.
    lets_for cn v (ws1 ++ ws2) b =
      lets_for cn v ws1 (lets_for cn v ws2 b)
Proof
  Induct >> rw[lets_for_def] >>
  PairCases_on `h` >> simp[lets_for_def]
QED

Theorem eval_wh_to_lets_for:
  ∀vs e k cn v b.
  closed e ∧ vs ≠ [] ∧ ¬ MEM v vs ⇒
  ∃res.
    eval_wh_to k (subst1 v e (lets_for cn v (MAPi (λi v. (i,v)) vs) b)) = res ∧
    (res = wh_Diverge ∨
     k ≠ 0 ∧
     res =
      eval_wh_to (k - 1)
      (subst (FEMPTY |++ MAPi (λi v. (v, Proj cn i e)) vs) (subst1 v e b)))
Proof
  Induct using SNOC_INDUCT >> rw[SNOC_APPEND, lets_for_def, lets_for_APPEND] >>
  Cases_on `vs = []` >> gvs[]
  >- (
    simp[lets_for_def, bind1_def, subst1_def, eval_wh_to_def] >>
    IF_CASES_TAC >> gvs[] >> simp[FUPDATE_LIST_THM]
    ) >>
  last_x_assum drule >> disch_then drule >>
  strip_tac >> gvs[] >>
  simp[lets_for_APPEND, indexedListsTheory.MAPi_APPEND, lets_for_def] >>
  pop_assum $ qspecl_then
    [`k`,`cn`,`Let x (Proj cn (LENGTH vs) (Var v)) b`] assume_tac >>
  gvs[] >>
  simp[subst_def, FLOOKUP_UPDATE, DOMSUB_FUPDATE_NEQ] >>
  simp[FUPDATE_LIST_APPEND, GSYM FUPDATE_EQ_FUPDATE_LIST] >>
  qmatch_goalsub_abbrev_tac `FEMPTY |++ m` >>
  simp[eval_wh_to_def] >> IF_CASES_TAC >> gvs[] >> simp[bind1_def] >>
  rw[DISJ_EQ_IMP] >> drule eval_wh_inc >>
  disch_then $ qspec_then `k - 1` $ mp_tac o GSYM >> rw[] >>
  AP_TERM_TAC >> DEP_REWRITE_TAC[subst_subst_FUNION] >> simp[] >> conj_tac
  >- (
    simp[DOMSUB_FUPDATE_LIST] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
    simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, MEM_FILTER] >>
    unabbrev_all_tac >> simp[indexedListsTheory.MEM_MAPi, PULL_EXISTS]
    ) >>
  AP_THM_TAC >> AP_TERM_TAC >>
  rw[fmap_eq_flookup, FLOOKUP_FUNION, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM] >>
  every_case_tac >> gvs[]
QED

Theorem eval_wh_to_Case:
  ∀css c ce v k e es cname vs.
  eval_wh_to k (exp_of e) = wh_Constructor cname es ∧
  closed (exp_of e) ∧
  ALOOKUP css cname = SOME (vs, ce) ∧
  ¬ MEM v vs ∧
  LENGTH vs = LENGTH es
  ⇒ ∃res.
      eval_wh_to k (exp_of (Case c e v css)) = res ∧
      (res = wh_Diverge ∨
       k ≠ 0 ∧
       res =
        eval_wh_to (k - 1)
          (subst (FEMPTY |++ MAPi (λi v. (v, Proj cname i (exp_of e))) vs)
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
    disch_then $ qspecl_then [`k - 2`,`cname`,`exp_of ce`] mp_tac >> gvs[] >>
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

Theorem type_soundness:
  ∀k (ce : unit cexp) ns db st t.
    namespace_ok ns ∧
    EVERY (type_ok (SND ns) db) st ∧
    type_cexp ns db st [] ce t
  ⇒ ∃wh. eval_wh_to k (exp_of ce) = wh ∧ type_wh ns db st [] wh t
Proof
  strip_tac >> completeInduct_on `k` >>
  recInduct exp_of_ind >> rw[exp_of_def]
  >- gvs[Once type_cexp_cases]
  >- ( (* Prim *)
    Cases_on `p` >> gvs[op_of_def]
    >- (
      simp[eval_wh_to_def, type_wh_cases, SF ETA_ss] >>
      goal_assum $ drule_at Any >> simp[]
      )
    >- (
      gvs[Once type_cexp_cases]
      >- (
        simp[eval_wh_to_def, get_atoms_def] >>
        simp[Once type_wh_cases] >> simp[Once type_cexp_cases]
        ) >>
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
        >- (IF_CASES_TAC >> simp[type_wh_cases] >> simp[Once type_cexp_cases]) >>
        simp[type_wh_cases] >> simp[Once type_cexp_cases, get_PrimTys_def] >>
        simp[type_atom_op_cases]
        ) >>
      CASE_TAC >> gvs[] >- simp[type_wh_cases, type_ok] >>
      CASE_TAC >> gvs[]
      >- (
        gvs[get_atoms_SOME_NONE_eq, LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS] >>
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
        simp[Once type_cexp_cases, get_PrimTys_def, type_atom_op_cases]) >>
      qspecl_then [`pts`,`pt`,`a`,`atoms`]
        assume_tac $ GEN_ALL eval_op_type_safe >> gvs[] >>
      Cases_on `pt = Bool` >> gvs[]
      >- (IF_CASES_TAC >> simp[type_wh_cases, Once type_cexp_cases]) >>
      simp[type_wh_cases] >>
      simp[Once type_cexp_cases, get_PrimTys_def, type_atom_op_def]
      )
    >- (
      pop_assum mp_tac >> simp[Once type_cexp_cases] >> rw[] >>
      simp[eval_wh_to_def] >> reverse $ IF_CASES_TAC >> gvs[]
      >- (FULL_CASE_TAC >> gvs[])
      >- (
        simp[type_wh_cases] >>
        irule type_cexp_type_ok_unit >> simp[] >>
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
    gvs[eval_wh_to_def] >> rw[]
    >- (
      simp[type_wh_cases] >> irule type_cexp_type_ok_unit >> simp[] >>
      rpt $ goal_assum $ drule_at Any >> simp[]
      ) >>
    qpat_x_assum `type_cexp _ _ _ _ _ _` mp_tac >> rw[Once type_cexp_cases] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    ntac 2 $ disch_then drule >>
    disch_then $ qspecl_then [`substc1 v x y`,`t`] mp_tac >>
    simp[subst_exp_of, FMAP_MAP2_FUPDATE] >> impl_tac
    >- (irule type_cexp_closing_subst1 >> simp[] >> goal_assum drule >> simp[]) >>
    simp[bind1_def] >> IF_CASES_TAC >> gvs[] >>
    imp_res_tac type_cexp_freevars_cexp >> gvs[closed_def, freevars_exp_of]
    )
  >- ( (* Apps *)
    qpat_x_assum `type_cexp _ _ _ _ _ _` mp_tac >> rw[Once type_cexp_cases] >>
    rename1 `Function _ rt` >>
    qpat_x_assum `∀a. MEM a _ ⇒ _` kall_tac >> qpat_x_assum `_ ≠ _` kall_tac >>
    first_x_assum drule_all >> strip_tac >>
    ntac 2 $ pop_assum mp_tac >> qpat_x_assum `type_cexp _ _ _ _ _ _` mp_tac >>
    map_every qid_spec_tac [`f`,`t`,`rt`,`ts`] >>
    pop_assum mp_tac >> map_every qid_spec_tac [`arg_tys`,`xs`] >>
    ho_match_mp_tac LIST_REL_strongind >> rw[]
    >- (
      simp[Apps_def] >>
      Cases_on `ts` >> gvs[type_application_def] >>
      imp_res_tac type_cexp_type_ok >> gvs[type_ok]
      ) >>
    Cases_on `ts` >> gvs[type_application_def]
    >- (imp_res_tac type_cexp_type_ok >> gvs[type_ok]) >>
    rename1 `Function (ft::fts)` >> rename1 `exp_of arg :: _ args` >>
    simp[Apps_def] >> Cases_on `arg_tys` >> gvs[]
    >- (
      simp[Apps_def, eval_wh_to_def] >>
      `type_ok (SND ns) db t` by (
        irule type_ok_type_application >> goal_assum drule >> simp[] >>
        imp_res_tac type_cexp_type_ok >> gvs[type_ok, SF ETA_ss]) >>
      IF_CASES_TAC >> gvs[] >- simp[type_wh_cases] >>
      imp_res_tac type_wh_Function_eq_wh_Closure >> gvs[] >>
      IF_CASES_TAC >> gvs[] >- simp[type_wh_cases] >>
      imp_res_tac type_cexp_freevars_cexp >> gvs[] >>
      simp[bind1_def, closed_def, freevars_exp_of] >>
      rename1 `subst1 var _ _` >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      ntac 2 $ disch_then drule >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
      strip_tac >> gvs[] >>
      drule_at Any type_cexp_cexp_wf >> simp[] >> strip_tac >>
      Cases_on `ce` >> gvs[exp_of_def]
      >- (Cases_on `l` using SNOC_CASES >> gvs[MAP_SNOC, Apps_SNOC, cexp_wf_def]) >>
      Cases_on `l` >> gvs[cexp_wf_def, Lams_def] >> rename1 `v::vs` >>
      Cases_on `vs = []`
      >- (
        qpat_x_assum `type_cexp _ _ _ _ _ _` mp_tac >>
        rw[Once type_cexp_cases] >> gvs[Lams_def] >>
        pop_assum $ qspec_then `substc1 v arg c` mp_tac >>
        simp[subst_exp_of, FMAP_MAP2_FUPDATE, exp_of_def] >> disch_then irule >>
        irule type_cexp_closing_subst1 >> simp[] >>
        gvs[type_application_def] >> goal_assum drule >> simp[]
        ) >>
      disch_then $ qspec_then `substc1 v arg (Lam () vs c)` mp_tac >>
      simp[subst_exp_of, FMAP_MAP2_FUPDATE, exp_of_def] >> disch_then irule >>
      drule $ iffRL type_cexp_Lam_single >> impl_keep_tac
      >- (
        qpat_x_assum `type_cexp _ _ _ _ _ _` mp_tac >>
        rw[Once type_cexp_cases] >> gvs[] >> Cases_on `fts` >> gvs[]
        ) >>
      rw[] >> Cases_on `fts` >> gvs[type_application_def] >>
      irule type_cexp_closing_subst1 >> simp[] >> goal_assum drule >> simp[]
      ) >>
    rename1 `type_application _ _ $ at::ats` >> Cases_on `fts` >> gvs[]
    >- (
      Cases_on `rt` >> gvs[type_application_def] >>
      rename1 `Function _ $ Function fts rt` >>
      first_x_assum $ qspecl_then [`fts`,`rt`] mp_tac >> simp[Apps_def] >>
      disch_then $ qspec_then `App () f [arg]` mp_tac >>
      simp[exp_of_def, Apps_def] >>
      disch_then irule >> rw[]
      >- (
        simp[Once type_cexp_cases, PULL_EXISTS] >>
        rpt $ goal_assum drule >> simp[type_application_def]
        ) >>
      simp[eval_wh_to_def] >>
      `type_ok (SND ns) db (Function fts rt)` by (
        imp_res_tac type_cexp_type_ok >> gvs[type_ok]) >>
      IF_CASES_TAC >> gvs[] >- simp[type_wh_cases] >>
      imp_res_tac type_wh_Function_eq_wh_Closure >> gvs[] >>
      IF_CASES_TAC >> gvs[] >- simp[type_wh_cases] >>
      imp_res_tac type_cexp_freevars_cexp >> gvs[] >>
      simp[bind1_def, closed_def, freevars_exp_of] >>
      rename1 `subst1 var _ _` >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      ntac 2 $ disch_then drule >>
      qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
      strip_tac >> gvs[] >>
      drule_at Any type_cexp_cexp_wf >> simp[] >> strip_tac >>
      Cases_on `ce` >> gvs[exp_of_def]
      >- (Cases_on `l` using SNOC_CASES >> gvs[MAP_SNOC, Apps_SNOC, cexp_wf_def]) >>
      Cases_on `l` >> gvs[cexp_wf_def, Lams_def] >> rename1 `v::vs` >>
      reverse $ Cases_on `vs = []`
      >- (
        qpat_x_assum `type_cexp _ _ _ _ _ _` mp_tac >>
        simp[Once type_cexp_cases]
        ) >>
      qpat_x_assum `type_cexp _ _ _ _ _ _` mp_tac >>
      rw[Once type_cexp_cases] >> gvs[Lams_def] >>
      pop_assum $ qspec_then `substc1 v arg c` mp_tac >>
      simp[subst_exp_of, FMAP_MAP2_FUPDATE, exp_of_def] >>
      disch_then irule >>
      irule type_cexp_closing_subst1 >> simp[] >>
      gvs[type_application_def] >> goal_assum drule >> simp[]
      ) >>
    rename1 `ft1::ft2::fts` >>
    gvs[type_application_def] >>
    first_x_assum $ qspecl_then [`at::fts`,`rt`] mp_tac >> simp[] >>
    simp[Apps_def, type_application_def] >>
    disch_then $ qspec_then `App () f [arg]` mp_tac >>
    simp[exp_of_def, Apps_def] >>
    disch_then irule >> rw[]
    >- (
      simp[Once type_cexp_cases, PULL_EXISTS] >>
      rpt $ goal_assum drule >> simp[type_application_def]
      ) >>
    simp[eval_wh_to_def] >>
    `type_ok (SND ns) db (Function (at::fts) rt)` by (
      imp_res_tac type_cexp_type_ok >> gvs[type_ok]) >>
    IF_CASES_TAC >> gvs[] >- simp[type_wh_cases] >>
    imp_res_tac type_wh_Function_eq_wh_Closure >> gvs[] >>
    IF_CASES_TAC >> gvs[] >- simp[type_wh_cases] >>
    imp_res_tac type_cexp_freevars_cexp >> gvs[] >>
    simp[bind1_def, closed_def, freevars_exp_of] >>
    rename1 `subst1 var _ _` >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    ntac 2 $ disch_then drule >>
    qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
    strip_tac >> gvs[] >>
    drule_at Any type_cexp_cexp_wf >> simp[] >> strip_tac >>
    Cases_on `ce` >> gvs[exp_of_def]
    >- (Cases_on `l` using SNOC_CASES >> gvs[MAP_SNOC, Apps_SNOC, cexp_wf_def]) >>
    Cases_on `l` >> gvs[cexp_wf_def, Lams_def] >> rename1 `Lam _ $ v::vs` >>
    drule $ iffRL type_cexp_Lam_single >> simp[] >> strip_tac >>
    disch_then $ qspec_then `substc1 v arg (Lam () vs c)` mp_tac >>
    simp[subst_exp_of, FMAP_MAP2_FUPDATE, exp_of_def] >>
    disch_then irule >>
    irule type_cexp_closing_subst1 >> simp[] >>
    goal_assum drule >> simp[]
    )
  >- ( (* Lams *)
    imp_res_tac type_cexp_cexp_wf >> gvs[cexp_wf_def] >>
    Cases_on `vs` >> gvs[Lams_def] >> simp[eval_wh_to_def] >>
    simp[Once type_wh_cases] >>
    goal_assum drule >> simp[exp_of_def, Lams_def]
    )
  >- ( (* Letrec *)
    simp[eval_wh_to_def] >> rw[]
    >- (
      simp[type_wh_cases] >> irule type_cexp_type_ok_unit >> simp[] >>
      rpt $ goal_assum $ drule_at Any >> simp[]
      ) >>
    qpat_x_assum `type_cexp _ _ _ _ _ _` mp_tac >> rw[Once type_cexp_cases] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    ntac 2 $ disch_then drule >>
    disch_then $ qspecl_then
      [`substc (FEMPTY |++ MAP (λ(g,x). (g, Letrec () rs x)) rs) x`,`t`] mp_tac >>
    simp[subst_exp_of, FMAP_MAP2_FUPDATE_LIST] >> impl_tac
    >- (
      irule type_cexp_closing_subst >> simp[] >> goal_assum $ drule_at Any >>
      imp_res_tac LIST_REL_LENGTH >> simp[MAP_REVERSE, MAP_ZIP] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >> rw[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      simp[Once type_cexp_cases] >>
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
      first_x_assum drule >> rw[] >> drule type_cexp_shift_db >> simp[] >>
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
      imp_res_tac type_cexp_freevars_cexp >>
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
      imp_res_tac type_cexp_freevars_cexp >>
      gvs[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[pred_setTheory.SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD, MEM_ZIP] >>
      metis_tac[MEM_EL]
      )
    )
  >- ( (* Case *)
    drule type_cexp_freevars_cexp >> rw[] >>
    drule_at (Pos last) type_cexp_type_ok >> rw[] >>
    qpat_x_assum `type_cexp _ _ _ _ _ _` mp_tac >> rw[Once type_cexp_cases] >>
    Cases_on `eval_wh_to k (exp_of x) = wh_Diverge`
    >- (
      drule_at Any eval_wh_to_Case_wh_Diverge >>
      gvs[closed_def, freevars_exp_of] >>
      disch_then $ qspecl_then [`v`,`rs`] mp_tac >> reverse $ impl_tac
      >- rw[exp_of_def, type_wh_cases] >>
      gvs[oEL_THM, namespace_ok_def, EVERY_EL] >>
      qpat_x_assum `∀n. n < LENGTH typedefs ⇒ _` drule >> simp[] >>
      Cases_on `rs` >> gvs[]
      ) >>
    first_x_assum drule_all >> rw[] >>
    drule type_wh_TypeCons_eq_wh_Constructor >> rw[] >> gvs[] >>
    qpat_x_assum `type_wh _ _ _ _ _ _` mp_tac >> simp[Once type_wh_cases] >>
    rw[] >> gvs[] >> pop_assum mp_tac >> rw[Once type_cexp_cases, type_cons_def] >>
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
    imp_res_tac LIST_REL_LENGTH >> simp[exp_of_def] >> rw[] >> simp[]
    >- rw[type_wh_cases] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    disch_then drule >> simp[] >>
    cheat (* TODO - issue with CBN here*)
    )
QED

(********************)

val _ = export_theory();
