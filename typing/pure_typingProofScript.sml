open HolKernel Parse boolLib bossLib BasicProvers;
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

Triviality type_cexp_type_ok_unit =
  type_cexp_type_ok |> INST_TYPE [alpha |-> ``:unit``];

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
  >- (
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
  >- (
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
  >- (
    cheat (* TODO Apps case *)
    )
  >- (
    imp_res_tac type_cexp_cexp_wf >> gvs[cexp_wf_def] >>
    Cases_on `vs` >> gvs[Lams_def] >> simp[eval_wh_to_def] >>
    simp[Once type_wh_cases] >>
    goal_assum drule >> simp[exp_of_def, Lams_def]
    )
  >- (
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
  >- (
    cheat (* TODO Case case *)
    )
QED

(********************)

val _ = export_theory();
