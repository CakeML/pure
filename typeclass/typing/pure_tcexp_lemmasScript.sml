
Theory pure_tcexp_lemmas
Ancestors
  arithmetic list rich_list alist string option pair pred_set
  finite_map pure_misc pure_cexp pure_cexp_lemmas pure_tcexp
  pure_exp pure_exp_lemmas pure_eval pure_exp_rel pure_congruence
Libs
  BasicProvers dep_rewrite

Theorem freevars_lets_for:
  ∀c a v l b. freevars (lets_for c a v l b) =
    case l of
      [] => freevars b DIFF set (MAP SND l)
    | _ => v INSERT (freevars b DIFF set (MAP SND l))
Proof
  recInduct lets_for_ind >> rw[lets_for_def] >>
  CASE_TAC >> gvs[] >> simp[EXTENSION] >> gvs[Bottom_def] >>
  metis_tac[]
QED

Theorem MAPi_ID[local,simp]:
  ∀l. MAPi (λn v. v) l = l
Proof
  Induct >> rw[combinTheory.o_DEF]
QED

Theorem freevars_rows_of:
  ∀v l k.
    freevars (rows_of v l k) =
    case l of
      [] => freevars k
    | _ => v INSERT freevars k ∪
           BIGUNION (set (MAP (λ(cn,vs,b). freevars b DIFF set vs) l))
Proof
  recInduct rows_of_ind >> rw[rows_of_def] >>
  simp[freevars_lets_for, combinTheory.o_ABS_R] >>
  Cases_on `rest` >> gvs[combinTheory.o_DEF] >>
  CASE_TAC >> gvs[EXTENSION] >> metis_tac[]
QED

Theorem IMAGE_DIFFDELETE[local]:
  (∀x y. f x = f y ⇔ x = y) ⇒
  IMAGE f (A DIFF B) = IMAGE f A DIFF IMAGE f B ∧
  IMAGE f (A DELETE e) = IMAGE f A DELETE f e
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem MEM_adjustlemma[local]:
  ((∀x y. MEM (x,y) l ⇒ P x y) ⇔ (∀p. MEM p l ⇒ P (FST p) (SND p))) ∧
  ((∀x y z. MEM (x,y,z) l2 ⇒ Q x y z) ⇔
     (∀p. MEM p l2 ⇒ Q (FST p) (FST (SND p)) (SND (SND p))))
Proof
  simp[FORALL_PROD]
QED

Theorem app3_eq:
  f1 = f2 ∧ x1 = x2 ∧ y1 = y2 ⇒ f1 x1 y1 = f2 x2 y2
Proof
  simp[]
QED

Theorem freevars_exp_of:
  ∀ce. freevars (exp_of ce) = IMAGE explode $ freevars_tcexp ce
Proof
  recInduct freevars_tcexp_ind >>
  rpt strip_tac
  >~ [`NestedCase`]
  >- (
    PURE_REWRITE_TAC[exp_of_def,freevars_tcexp_def] >>
    `∀pes.
      (∀p' e'. MEM (p',e') pes ⇒
        freevars (exp_of e') = IMAGE explode (freevars_tcexp e')) ⇒
      freevars
       (nested_rows (Var (explode v))
          (MAP (λx. (FST x,exp_of (SND x))) pes)) DELETE explode v =
      BIGUNION
        (set (MAP (λx.
          IMAGE explode (freevars_tcexp (SND x)) DIFF
          IMAGE explode (cepat_vars (FST x))) pes))
        DELETE explode v` suffices_by (
      disch_then $ qspec_then `(p,e)::pes` strip_assume_tac >>
      gvs[exp_of_def,freevars_tcexp_def] >>
      pop_assum $ strip_assume_tac o
        SRULE[DISJ_IMP_THM,FORALL_AND_THM] >>
      pop_assum $ drule_then drule >>
      simp[AC UNION_COMM UNION_ASSOC,LAMBDA_PROD,IMAGE_DIFFDELETE,
          IMAGE_BIGUNION,GSYM LIST_TO_SET_MAP,MAP_MAP_o,
          combinTheory.o_DEF]
    ) >>
    rpt $ pop_assum kall_tac >>
    rpt strip_tac >>
    irule SUBSET_ANTISYM >>
    conj_tac
    >- (
      irule SUBSET_TRANS >>
      qrefine `_ DELETE explode v` >>
      irule_at (Pos hd) SUBSET_DELETE_BOTH >>
      irule_at (Pos hd) freevars_nested_rows_UB >>
      IF_CASES_TAC >- simp[] >>
      simp[LAMBDA_PROD,UNION_DELETE,MAP_MAP_o,combinTheory.o_DEF] >>
      irule $ cj 1 EQ_SUBSET_SUBSET >>
      irule app3_eq >> simp[] >>
      ntac 2 AP_TERM_TAC >>
      irule MAP_CONG >> rw[] >>
      pairarg_tac >> gvs[] >>
      metis_tac[]
    ) >>
    irule SUBSET_TRANS >>
    qrefine `_ DELETE explode v` >>
    irule_at (Pos last) SUBSET_DELETE_BOTH >>
    irule_at (Pos hd) freevars_nested_rows_LB >>
    simp[LAMBDA_PROD,MAP_MAP_o,combinTheory.o_DEF] >>
    irule $ cj 2 EQ_SUBSET_SUBSET >>
    irule combeq3 >> simp[] >>
    ntac 2 AP_TERM_TAC >>
    irule MAP_CONG >> rw[] >>
    pairarg_tac >> gvs[] >>
    metis_tac[]
  ) >>
  simp[optionTheory.FORALL_OPTION] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, Bottom_def, IMAGE_BIGUNION,
      GSYM LIST_TO_SET_MAP, IMAGE_DIFFDELETE, Cong MAP_CONG,
      freevars_rows_of, AC UNION_COMM UNION_ASSOC, ELIM_UNCURRY,
      exp_of_def]
  >- gvs[MEM_adjustlemma, ELIM_UNCURRY, Cong MAP_CONG] >>
  Cases_on `css` >> gvs[] >>
  every_case_tac >> gvs[freevars_IfDisj] >> every_case_tac >> gvs[] >>
  gvs[quantHeuristicsTheory.PAIR_EQ_EXPAND] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, IMAGE_DIFFDELETE,
      GSYM LIST_TO_SET_MAP, MEM_adjustlemma] >>
  simp[LAMBDA_PROD, IMAGE_DIFFDELETE] >>
  simp[ELIM_UNCURRY, Cong MAP_CONG, GSYM LIST_TO_SET_MAP,
       AC UNION_ASSOC UNION_COMM] >>
  rw[EXTENSION, PULL_EXISTS] >>
  simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
QED

Theorem subst_lets_for:
  ∀cn ar v l e f.  v ∉ FDOM f ⇒
    subst f (lets_for cn ar v l e) =
    lets_for cn ar v l (subst (FDIFF f (set (MAP SND l))) e)
Proof
  recInduct lets_for_ind >> rw[lets_for_def, subst_def] >>
  simp[FLOOKUP_DEF, FDIFF_FDOMSUB_INSERT, Bottom_def]
QED

Theorem subst_rows_of:
  ∀v l k f.
    v ∉ FDOM f ⇒
    subst f (rows_of v l k) =
    rows_of v (MAP (λ(a,b,c). (a,b, subst (FDIFF f (set b)) c)) l)
            (subst (f \\ v) k)
Proof
  recInduct rows_of_ind >> rw[rows_of_def, subst_def, DOMSUB_NOT_IN_DOM]
  >- simp[FLOOKUP_DEF] >>
  simp[subst_lets_for, combinTheory.o_DEF]
QED

Theorem patguards_subst_FST[local]:
  patguards eps = (gd,binds) ⇒
  FST (patguards (MAP (subst f ## I) eps)) = subst f gd
Proof
  metis_tac[patguards_subst,FST]
QED

Theorem patguards_subst_SND[local]:
  patguards eps = (gd,binds) ⇒
  SND (patguards (MAP (subst f ## I) eps)) =
    MAP (I ## subst f) binds
Proof
  metis_tac[patguards_subst,SND]
QED

Theorem subst_exp_of:
  ∀f ce.
    exp_of (subst_tc f ce) =
    subst (FUN_FMAP (λs. exp_of (f ' (implode s))) (IMAGE explode $ FDOM f))
          (exp_of ce)
Proof
  recInduct subst_tc_ind >> rw[subst_def, subst_tc_def, exp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, Bottom_def,
      Cong MAP_CONG, subst_Apps, subst_Lams, IMAGE_DIFFDELETE, FDOM_FDIFF_alt,
      GSYM LIST_TO_SET_MAP, FDIFF_FUN_FMAP, subst_rows_of]
  >- simp[AllCaseEqs(), FLOOKUP_DEF, SF CONJ_ss, exp_of_def, FUN_FMAP_DEF]
  >- (irule app3_eq >>
      simp[fmap_EXT, PULL_EXISTS, MEM_MAP, FUN_FMAP_DEF, FDIFF_def,
           DRESTRICT_DEF])
  >- (irule app3_eq >>
      simp[fmap_EXT, PULL_EXISTS, FUN_FMAP_DEF, DOMSUB_FAPPLY_THM])
  >- (gvs[MEM_adjustlemma] >> simp[LAMBDA_PROD] >>
      simp[ELIM_UNCURRY, Cong MAP_CONG] >> rw[MAP_EQ_f] >>
      irule app3_eq >>
      simp[FUN_FMAP_DEF, fmap_EXT, PULL_EXISTS, MEM_MAP, FORALL_PROD,
           FDIFF_def, DRESTRICT_DEF])
  >- (gvs[MEM_adjustlemma] >> simp[LAMBDA_PROD] >>
      irule app3_eq >>
      simp[FUN_FMAP_DEF, fmap_EXT, PULL_EXISTS, MEM_MAP, FORALL_PROD,
           FDIFF_def, DRESTRICT_DEF])
  >- (simp[LAMBDA_PROD] >> simp[ELIM_UNCURRY] >>
      gvs[MEM_adjustlemma, Cong MAP_CONG, FDIFF_FUN_FMAP,
          FDIFF_FDOMSUB_INSERT] >>
      rename [‘eopt = SOME _ ⇒ _’] >> Cases_on ‘eopt’ >> gvs[] >>
      irule app3_eq >> rw[MAP_EQ_f] >>
      gvs[subst_IfDisj, quantHeuristicsTheory.PAIR_EQ_EXPAND] >>
      irule app3_eq >>
      simp[fmap_EXT, FUN_FMAP_DEF, PULL_EXISTS, MEM_MAP, FDIFF_def,
           DRESTRICT_DEF, DOMSUB_FAPPLY_THM] >>
      AP_THM_TAC >> AP_TERM_TAC >>
      rw[fmap_eq_flookup, FLOOKUP_FUN_FMAP, DOMSUB_FLOOKUP_THM] >> rw[] >> gvs[])
  >- (
    pairarg_tac >>
    simp[subst_def] >>
    rw[]
    >- (
      irule EQ_TRANS >>
      drule_then (irule_at $ Pos last) patguards_subst_FST >>
      fs[pureLangTheory.patguards_def,subst_def])
    >- (
      DEP_REWRITE_TAC[subst_FOLDR_Let] >>
      simp[FDIFF_FUN_FMAP,FDIFF_FDOMSUB_INSERT] >>
      drule patguards_binds_pvars >>
      disch_then SUBST_ALL_TAC >>
      simp[] >>
      drule patguards_onebound_preserved >>
      rw[]
      >- (
        qexists_tac `{explode v}` >>
        simp[DELETE_INTER] >>
        conj_tac
        >- simp[INTER_DEF,DELETE_DEF,DIFF_DEF,EXTENSION] >>
        metis_tac[EQ_SUBSET_SUBSET]
      ) >>
      irule FOLDR_CONG >> simp[] >>
      irule app3_eq >> simp[] >>
      irule FUN_FMAP_CONG >>
      rw[PULL_EXISTS] >>
      fs[TO_FLOOKUP] >>
      DEP_REWRITE_TAC[TO_FLOOKUP] >>
      simp[FLOOKUP_FDIFF]) >>
    DEP_REWRITE_TAC[subst_nested_rows] >>
    simp[freevars_def,DELETE_INTER,MAP_MAP_o,
      combinTheory.o_DEF,FDIFF_FUN_FMAP,FUN_FMAP_DOMSUB] >>
    conj_tac
    >- simp[INTER_DEF,DELETE_DEF,DIFF_DEF,EXTENSION] >>
    AP_TERM_TAC >>
    irule MAP_CONG >>
    rw[] >>
    rename1`MEM pp pes` >>
    Cases_on `pp` >>
    gvs[DIFF_INSERT] >>
    irule app3_eq >> simp[] >>
    irule FUN_FMAP_CONG >>
    rw[PULL_EXISTS] >>
    fs[TO_FLOOKUP] >>
    DEP_REWRITE_TAC[TO_FLOOKUP] >>
    simp[FLOOKUP_FDIFF])
QED

Theorem lets_for_APPEND:
  ∀ws1 ws2 cn ar v n w b.
    lets_for cn ar v (ws1 ++ ws2) b =
      lets_for cn ar v ws1 (lets_for cn ar v ws2 b)
Proof
  Induct >> rw[lets_for_def] >>
  PairCases_on `h` >> simp[lets_for_def]
QED

Theorem cexp_wf_tcexp_wf:
  ∀e. (cexp_wf e ⇔ tcexp_wf (tcexp_of e) ∧ cexp_Lits_wf e)
Proof
  recInduct cexp_wf_ind >>
  rw[cexp_wf_def, tcexp_of_def, tcexp_wf_def, cexp_Lits_wf_def] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD, MEM_MAP,
      EXISTS_PROD, PULL_EXISTS, MEM_FLAT] >>
  eq_tac >> rw[] >> res_tac
  >- (Cases_on ‘eopt’ >> gvs[] >> rpt (pairarg_tac >> gvs[]) >> metis_tac[])
  >- (
    qmatch_goalsub_abbrev_tac `ALL_DISTINCT foo` >>
    qmatch_asmsub_abbrev_tac `ALL_DISTINCT bar` >>
    qsuff_tac `foo = bar` >> rw[] >> unabbrev_all_tac >> gvs[] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> Cases_on `eopt` >> rw[] >>
    rpt (pairarg_tac >> gvs[]) >> rw[MAP_EQ_f] >> pairarg_tac >> gvs[]
    )
  >- (Cases_on ‘eopt’ >> gvs[] >> rpt (pairarg_tac >> gvs[]) >> metis_tac[])
  >- (Cases_on ‘eopt’ >> gvs[] >> rpt (pairarg_tac >> gvs[]) >> metis_tac[])
  >- (
    qmatch_goalsub_abbrev_tac `ALL_DISTINCT foo` >>
    qmatch_asmsub_abbrev_tac `ALL_DISTINCT bar` >>
    qsuff_tac `foo = bar` >> rw[] >> unabbrev_all_tac >> gvs[] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> Cases_on `eopt` >> rw[] >>
    rpt (pairarg_tac >> gvs[]) >> rw[MAP_EQ_f] >> pairarg_tac >> gvs[]
    )
QED

Theorem freevars_tcexp_of:
  ∀ce. freevars_tcexp (tcexp_of ce) = freevars_cexp ce
Proof
  recInduct freevars_cexp_ind >>
  rw[freevars_cexp_def, tcexp_of_def, freevars_tcexp_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, EVERY_MEM, Cong MAP_CONG] >>
  simp[SF ETA_ss]
  >- (
    simp[LAMBDA_PROD, GSYM FST_THM] >>
    AP_THM_TAC >> ntac 4 AP_TERM_TAC >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    first_x_assum irule >> gvs[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
    goal_assum $ drule_at Any >> res_tac
    )
  >- (
    rename [‘eopt = SOME _ ⇒ _’] >> Cases_on ‘eopt’ >> gvs[] >>
    rpt (pairarg_tac >> gvs[]) >>
    simp[LAMBDA_PROD, GSYM FST_THM] >>
    gs[ELIM_UNCURRY, MEM_adjustlemma, MEM_MAP, PULL_EXISTS] >>
    simp[Cong MAP_CONG] >>
    simp[Once EXTENSION, MEM_MAP, PULL_EXISTS] >> metis_tac[]
    )
  >- (
    ntac 3 (irule app3_eq >> simp[]) >>
    ntac 2 AP_TERM_TAC >>
    irule MAP_CONG >>
    simp[LAMBDA_PROD,GSYM PFORALL_THM] >>
    metis_tac[]
    )
QED

Theorem tcexp_of_invert:
  (∀x. tcexp_of ce = Var x ⇔ ∃d. ce = Var d x) ∧
  (∀op tces. tcexp_of ce = Prim op tces ⇔
    ∃d ces. ce = Prim d op ces ∧ MAP tcexp_of ces = tces) ∧
  (∀x tce1 tce2. tcexp_of ce = Let x tce1 tce2 ⇔
    ∃d ce1 ce2. ce = Let d x ce1 ce2 ∧ tcexp_of ce1 = tce1 ∧ tcexp_of ce2 = tce2) ∧
  (∀tce tces. tcexp_of ce = App tce tces ⇔
    ∃d ce' ces. ce = App d ce' ces ∧ tcexp_of ce' = tce ∧ MAP tcexp_of ces = tces) ∧
  (∀xs tce. tcexp_of ce = Lam xs tce ⇔
    ∃d ce'. ce = Lam d xs ce' ∧ tcexp_of ce' = tce) ∧
  (∀tfns tce. tcexp_of ce = Letrec tfns tce ⇔
    ∃d fns ce'. ce = Letrec d fns ce' ∧
      tcexp_of ce' = tce ∧ MAP (λ(f,ce). (f,tcexp_of ce)) fns = tfns) ∧
  (∀tce x tcss tusopt. tcexp_of ce = pure_tcexp$Case tce x tcss tusopt ⇔
    ∃d ce' css usopt. ce = pure_cexp$Case d ce' x css usopt ∧
      tcexp_of ce' = tce ∧ MAP (λ(cn,pvs,ce). (cn,pvs,tcexp_of ce)) css = tcss ∧
      OPTION_MAP (λ(cn_ars,ce). (cn_ars, tcexp_of ce)) usopt = tusopt) ∧
  (∀tce x v p e pes. tcexp_of ce = pure_tcexp$NestedCase x v p e pes ⇔
    ∃d x' e' pes'. ce = pure_cexp$NestedCase d x' v p e' pes' ∧
      tcexp_of x' = x ∧ tcexp_of e' = e ∧
      MAP (λ(c,x'). (c,tcexp_of x')) pes' = pes)
Proof
  Induct_on `ce` using freevars_cexp_ind >> rw[] >> gvs[tcexp_of_def, SF ETA_ss] >>
  eq_tac >> rw[]
QED


(********************)


Theorem exp_eq_lets_for_cong:
  ∀vs cn i v a b. a ≅ b ⇒
  lets_for cn i v vs a ≅ lets_for cn i v vs b
Proof
  Induct >> rw[lets_for_def] >>
  PairCases_on `h` >> rw[lets_for_def] >>
  irule exp_eq_App_cong >> simp[exp_eq_refl] >>
  irule exp_eq_Lam_cong >> first_x_assum irule >> simp[]
QED

Theorem subst1_lets_for_closed[local]:
  ¬ MEM var (MAP SND vs) ∧ closed x
  ⇒ subst1 var x (lets_for cn ar v vs e) =
    subst1 var x (lets_for cn ar v vs (subst1 var x e))
Proof
  Induct_on `vs` >> rw[lets_for_def] >- simp[subst1_subst1_eq] >>
  PairCases_on `h` >> gvs[lets_for_def, subst1_def]
QED

Theorem subst1_lets_for_cexp_closed[local]:
  ¬ MEM var (MAP SND vs) ∧ closed x
  ⇒ subst1 var x (lets_for cn v vs e) =
    subst1 var x (lets_for cn v vs (subst1 var x e))
Proof
  Induct_on `vs` >> rw[pureLangTheory.lets_for_def]
  >- simp[subst1_subst1_eq] >>
  PairCases_on `h` >> gvs[pureLangTheory.lets_for_def, subst1_def]
QED

Theorem lets_for_exp_eq_lemma:
  ∀vs e.
    closed x ∧ eval_wh x = wh_Constructor cn es ∧
    ¬ MEM v vs ∧ cn ∉ monad_cns ⇒
  subst1 v x (lets_for cn (LENGTH es) v (MAPi (λi v. (i,v)) vs) e) ≅
  subst1 v x (lets_for cn v (MAPi (λi v. (i,v)) vs) e)
Proof
  Induct using SNOC_INDUCT
  >- rw[lets_for_def, pureLangTheory.lets_for_def, exp_eq_refl] >>
  rw[SNOC_APPEND, lets_for_APPEND, pure_cexp_lemmasTheory.lets_for_APPEND,
     indexedListsTheory.MAPi_APPEND] >>
  simp[lets_for_def, pureLangTheory.lets_for_def] >>
  DEP_ONCE_REWRITE_TAC[subst1_lets_for_closed, subst1_lets_for_cexp_closed] >>
  simp[combinTheory.o_DEF, subst1_def] >>
  qmatch_goalsub_abbrev_tac `_ (lets_for _ _ _ _ a) ≅ _ (lets_for _ _ _ b)` >>
  qsuff_tac `a ≅ b`
  >- (
    rw[] >> irule exp_eq_trans >> last_x_assum $ irule_at $ Pos last >> simp[] >>
    irule $ iffLR exp_eq_forall_subst >> simp[] >>
    irule exp_eq_lets_for_cong >> simp[]
    ) >>
  unabbrev_all_tac >> `closed Bottom` by gvs[Bottom_def] >> simp[] >>
  irule exp_eq_App_cong >> simp[exp_eq_refl] >>
  irule eval_wh_IMP_exp_eq >> rw[subst_def, eval_wh_thm]
QED

Theorem lets_for_exp_eq:
  ¬ MEM v vs ⇒
  If (IsEq cn (LENGTH vs) T (Var v))
    (lets_for cn (LENGTH vs) v (MAPi (λi v. (i,v)) vs) e) rest ≅
  If (IsEq cn (LENGTH vs) T (Var v))
    (lets_for cn v (MAPi (λi v. (i,v)) vs) e) rest
Proof
  rw[exp_eq_def, bind_def] >> IF_CASES_TAC >> simp[subst_def] >>
  simp[Once app_bisimilarity_iff] >>
  rpt $ irule_at Any IMP_closed_subst >> simp[] >>
  conj_tac >- simp[IN_FRANGE_FLOOKUP] >>
  TOP_CASE_TAC >> gvs[] >- gvs[FLOOKUP_DEF] >>
  conj_tac >- res_tac >>
  simp[eval_wh_thm] >>
  Cases_on `eval_wh x` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  Cases_on `s ∈ monad_cns` >> gvs[] >>
  Cases_on `s ≠ cn` >> gvs[]
  >- (
    qsuff_tac `(subst f rest ≃ subst f rest) T`
    >- simp[Once app_bisimilarity_iff] >>
    irule reflexive_app_bisimilarity >> irule IMP_closed_subst >>
    simp[IN_FRANGE_FLOOKUP]
    ) >>
  Cases_on `LENGTH vs ≠ LENGTH l` >> gvs[] >>
  `∃g. f = g |+ (v,x) ∧ v ∉ FDOM g` by (
    qexists_tac `f \\ v` >> simp[] >>
    irule $ GSYM FUPDATE_ELIM >> gvs[FLOOKUP_DEF]) >>
  gvs[] >>
  `subst (g |+ (v,x)) (lets_for cn (LENGTH l) v (MAPi (λi v. (i,v)) vs) e) =
   subst1 v x (lets_for cn (LENGTH l) v (MAPi (λi v. (i,v)) vs)
      (subst (FDIFF g (set vs)) e))` by (
        once_rewrite_tac[FUPDATE_EQ_FUNION] >>
        DEP_ONCE_REWRITE_TAC[FUNION_COMM] >>
        DEP_ONCE_REWRITE_TAC[GSYM subst_subst_FUNION] >> gvs[FLOOKUP_UPDATE] >>
        drule subst_lets_for >> simp[combinTheory.o_DEF] >> strip_tac >>
        rw[] >> first_x_assum irule >> gvs[IN_FRANGE_FLOOKUP] >>
        qexists_tac `k` >> simp[] >> rw[] >> gvs[FLOOKUP_DEF]) >>
  gvs[] >>
  `subst (g |+ (v,x)) (lets_for cn v (MAPi (λi v. (i,v)) vs) e) =
   subst1 v x (lets_for cn v (MAPi (λi v. (i,v)) vs)
      (subst (FDIFF g (set vs)) e))` by (
        once_rewrite_tac[FUPDATE_EQ_FUNION] >>
        DEP_ONCE_REWRITE_TAC[FUNION_COMM] >>
        DEP_ONCE_REWRITE_TAC[GSYM subst_subst_FUNION] >> gvs[FLOOKUP_UPDATE] >>
        drule pure_cexp_lemmasTheory.subst_lets_for >> rw[combinTheory.o_DEF] >>
        first_x_assum irule >> gvs[IN_FRANGE_FLOOKUP] >>
        qexists_tac `k` >> simp[] >> rw[] >> gvs[FLOOKUP_DEF]) >>
  gvs[] >> ntac 2 $ pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `lets_for _ _ _ _ e'` >>
  qsuff_tac
    `(subst1 v x (lets_for cn v (MAPi (λi v. (i,v)) vs) e') ≃
     subst1 v x (lets_for cn (LENGTH l) v (MAPi (λi v. (i,v)) vs) e')) T`
  >- (
    simp[Once app_bisimilarity_iff] >> strip_tac >> gvs[] >> rw[] >>
    first_x_assum drule >> strip_tac >> goal_assum drule
    >- metis_tac[symmetric_app_bisimilarity |>
                  SIMP_RULE (srw_ss()) [relationTheory.symmetric_def]]
    >- (
      gvs[LIST_REL_EL_EQN, opp_def, IN_DEF] >>
      metis_tac[symmetric_app_bisimilarity |>
                  SIMP_RULE (srw_ss()) [relationTheory.symmetric_def]]
      )
    >- metis_tac[symmetric_app_bisimilarity |>
                  SIMP_RULE (srw_ss()) [relationTheory.symmetric_def]]
    >- (
      gvs[LIST_REL_EL_EQN, opp_def, IN_DEF] >>
      metis_tac[symmetric_app_bisimilarity |>
                  SIMP_RULE (srw_ss()) [relationTheory.symmetric_def]]
      )
    ) >>
  `closed x` by (
    gvs[FLOOKUP_UPDATE] >> first_x_assum irule >> qexists_tac `v` >> simp[]) >>
  `freevars e' ⊆ v INSERT set vs` by (
    unabbrev_all_tac >> DEP_REWRITE_TAC[freevars_subst] >>
    gvs[SUBSET_DEF, freevars_lets_for, IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF,
        combinTheory.o_DEF, FLOOKUP_UPDATE] >> rw[]
    >- (first_x_assum irule >> qexists_tac `k` >> rw[] >> gvs[FLOOKUP_DEF])
    >- (Cases_on `vs` >> gvs[] >> metis_tac[])
    >- (Cases_on `vs` >> gvs[] >> metis_tac[])
    ) >>
  reverse $ rw[app_bisimilarity_eq]
  >- (
    irule IMP_closed_subst >> simp[freevars_lets_for, combinTheory.o_DEF] >>
    Cases_on `vs` >> gvs[SUBSET_DEF] >> metis_tac[]
    )
  >- (
    irule IMP_closed_subst >>
    simp[pure_cexp_lemmasTheory.freevars_lets_for, combinTheory.o_DEF] >>
    Cases_on `vs` >> gvs[SUBSET_DEF] >> metis_tac[]
    ) >>
  once_rewrite_tac[exp_eq_sym] >> irule lets_for_exp_eq_lemma >> simp[]
QED

Theorem exp_eq_FOLDR_cong_base_case[local]:
  e ≅ e' ∧ (∀x y y'. y ≅ y' ⇒  f x y ≅ f x y') ⇒
  FOLDR f e l ≅ FOLDR f e' l
Proof
  Induct_on `l` >>
  rw[]
QED

Theorem exp_of_tcexp_of_exp_eq:
  ∀e. tcexp_wf (tcexp_of e)
    ⇒ pure_tcexp$exp_of (tcexp_of e) ≅ pureLang$exp_of e
Proof
  recInduct tcexp_of_ind >>
  rw[tcexp_wf_def, tcexp_of_def, exp_of_def, pureLangTheory.exp_of_def]
  >- simp[exp_eq_Var_cong]
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
    irule exp_eq_Prim_cong >> rw[LIST_REL_EL_EQN] >> gvs[EL_MAP] >>
    first_x_assum irule >> simp[EL_MEM] >> gvs[EVERY_EL, EL_MAP]
    )
  >- (
    irule exp_eq_App_cong >> simp[] >>
    irule exp_eq_Lam_cong >> simp[]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF] >> gvs[] >>
    qpat_x_assum `_ ≠ []` kall_tac >> gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    Induct_on `xs` using SNOC_INDUCT >> rw[MAP_SNOC, Apps_SNOC] >>
    irule exp_eq_App_cong >> simp[]
    )
  >- (
    qpat_x_assum `_ ≠ _` kall_tac >> gvs[] >>
    Induct_on `vs` >> rw[Lams_def] >>
    irule exp_eq_Lam_cong >> simp[]
    )
  >- (
    irule exp_eq_Letrec_cong >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[LIST_REL_EL_EQN, EL_MAP] >> pairarg_tac >> gvs[] >>
    gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    first_x_assum irule >> gvs[MEM_EL, PULL_EXISTS, FORALL_PROD] >>
    goal_assum $ drule_at Any >> gvs[] >>
    metis_tac[]
    )
  >- (irule FALSITY >> gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rename [‘eopt = SOME _ ⇒ _’] >> reverse $ Cases_on ‘eopt’ >> gvs[] >>
    irule exp_eq_App_cong >> simp[] >>
    irule exp_eq_Lam_cong >> simp[] >>
    TRY (qpat_x_assum `rs ≠ _` kall_tac) >>
    rpt (pairarg_tac >> gvs[]) >>
    Induct_on `rs` >> rw[rows_of_def, pureLangTheory.rows_of_def, exp_eq_refl]
    >- (rw[pureLangTheory.IfDisj_def] >> irule exp_eq_Prim_cong >> simp[exp_eq_refl]) >>
    pairarg_tac >> gvs[rows_of_def, pureLangTheory.rows_of_def] >>
    qmatch_goalsub_abbrev_tac `_ ≅ If _ _ rows` >>
    irule exp_eq_trans >> irule_at Any exp_eq_Prim_cong >>
    qmatch_goalsub_abbrev_tac `[a;b c;_]` >>
    qexists_tac `[a;b (exp_of p2);rows]` >> unabbrev_all_tac >> simp[exp_eq_refl] >>
    last_x_assum $ irule_at Any >>
    (rw[]
     >- metis_tac[]
     >- (irule exp_eq_lets_for_cong >> simp[]) >>
     rename [‘MAP explode vv’] >>
     simp[lets_for_exp_eq
            |> Q.INST [‘vs’ |-> ‘MAP explode vv’]
            |> SRULE[PULL_EXISTS, MEM_MAP]])
    )
  >- (
    fs[EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY] >>
    irule exp_eq_App_cong >> simp[] >>
    irule exp_eq_Lam_cong >> simp[] >>
    irule exp_eq_Prim_cong >> simp[exp_eq_refl] >>
    conj_tac
    >- (
      rename1 `FOLDR _ _ l ≅ _` >>
      Induct_on `l` >>
      rw[] >>
      irule exp_eq_App_cong >> simp[exp_eq_refl] >>
      irule exp_eq_Lam_cong >> simp[exp_eq_refl])>>
    Induct_on `pes` >>
    rw[exp_eq_refl] >>
    pairarg_tac >>
    simp[] >>
    irule exp_eq_Prim_cong >> simp[exp_eq_refl] >>
    conj_tac
    >- (
      irule exp_eq_FOLDR_cong_base_case >>
      rw[ELIM_UNCURRY]
      >- (
        irule exp_eq_App_cong >> simp[exp_eq_refl] >>
        irule exp_eq_Lam_cong >> simp[exp_eq_refl]
      ) >>
      Cases_on `h` >>
      gvs[]) >>
    last_x_assum irule >>
    rw[] >>
    metis_tac[]
  )
QED


