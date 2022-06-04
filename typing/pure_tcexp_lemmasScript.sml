
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory rich_listTheory alistTheory stringTheory
     optionTheory pairTheory pred_setTheory finite_mapTheory;
open pure_miscTheory pure_cexpTheory pure_cexp_lemmasTheory
     pure_tcexpTheory pure_expTheory pure_exp_lemmasTheory
     pure_evalTheory pure_exp_relTheory pure_congruenceTheory;

val _ = new_theory "pure_tcexp_lemmas";

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

Triviality MAPi_ID[simp]:
  ∀l. MAPi (λn v. v) l = l
Proof
  Induct >> rw[combinTheory.o_DEF]
QED

Theorem freevars_rows_of:
  ∀v l. freevars (rows_of v l) =
    case l of
      [] => {}
    | _ => v INSERT BIGUNION (set (MAP (λ(cn,vs,b). freevars b DIFF set vs) l))
Proof
  recInduct rows_of_ind >> rw[rows_of_def] >> simp[freevars_lets_for] >>
  Cases_on `rest` >> gvs[combinTheory.o_DEF] >>
  CASE_TAC >> gvs[EXTENSION] >> metis_tac[]
QED

Theorem freevars_exp_of:
  ∀ce. freevars (exp_of ce) = freevars_tcexp ce
Proof
  recInduct freevars_tcexp_ind >> rw[exp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, Bottom_def]
  >- (ntac 2 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- (ntac 3 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- simp[UNION_COMM]
  >- (
    simp[LAMBDA_PROD, GSYM FST_THM] >>
    AP_THM_TAC >> ntac 4 AP_TERM_TAC >> rw[MAP_EQ_f] >>
    pairarg_tac >> gvs[] >> res_tac
    )
  >- (
    simp[Once UNION_COMM] >> AP_TERM_TAC >>
    simp[freevars_rows_of] >> Cases_on `css` >> gvs[] >>
    PairCases_on `h` >> gvs[] >> rw[EXTENSION, PULL_EXISTS] >>
    simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
    )
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
  ∀v l f.  v ∉ FDOM f ⇒
    subst f (rows_of v l) =
    rows_of v (MAP (λ(a,b,c). (a,b, subst (FDIFF f (set b)) c)) l)
Proof
  recInduct rows_of_ind >> rw[rows_of_def, subst_def]
  >- simp[FLOOKUP_DEF] >>
  simp[subst_lets_for, combinTheory.o_DEF]
QED

Theorem subst_exp_of:
  ∀f ce.
    exp_of (subst_tc f ce) =
    subst (FMAP_MAP2 (λ(k,v). exp_of v) f) (exp_of ce)
Proof
  recInduct subst_tc_ind >> rw[subst_def, subst_tc_def, exp_of_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, Bottom_def]
  >- (simp[FLOOKUP_FMAP_MAP2] >> CASE_TAC >> gvs[exp_of_def])
  >- rw[MAP_EQ_f]
  >- (
    simp[subst_Apps] >> AP_TERM_TAC >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >> rw[MAP_EQ_f]
    )
  >- (simp[subst_Lams] >> AP_TERM_TAC >> simp[FDIFF_FMAP_MAP2])
  >- simp[DOMSUB_FMAP_MAP2]
  >- (
    rw[MAP_EQ_f] >> pairarg_tac >> rw[] >>
    first_x_assum drule >> rw[FDIFF_FMAP_MAP2]
    )
  >- simp[FDIFF_FMAP_MAP2]
  >- (
    simp[subst_rows_of, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    AP_TERM_TAC >> rw[MAP_EQ_f] >> pairarg_tac >> rw[] >>
    first_x_assum drule >> rw[] >>
    simp[FDIFF_FDOMSUB_INSERT, FDIFF_FMAP_MAP2]
    )
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
  ∀e. NestedCase_free e ⇒ (cexp_wf e ⇔ tcexp_wf (tcexp_of e))
Proof
  recInduct cexp_wf_ind >> rw[cexp_wf_def, tcexp_of_def, tcexp_wf_def] >>
  gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD, MEM_MAP,
      EXISTS_PROD, PULL_EXISTS, MEM_FLAT] >>
  eq_tac >> rw[] >> metis_tac[]
QED

Theorem freevars_tcexp_of:
  ∀ce. NestedCase_free ce ⇒ (freevars_tcexp (tcexp_of ce) = freevars_cexp ce)
Proof
  recInduct freevars_cexp_ind >>
  rw[freevars_cexp_def, tcexp_of_def, freevars_tcexp_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, EVERY_MEM]
  >- (ntac 2 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- (ntac 3 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- (
    simp[LAMBDA_PROD, GSYM FST_THM] >>
    AP_THM_TAC >> ntac 4 AP_TERM_TAC >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    first_x_assum irule >> gvs[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
    goal_assum $ drule_at Any >> res_tac
    )
  >- (
    simp[LAMBDA_PROD, GSYM FST_THM] >>
    AP_TERM_TAC >> AP_THM_TAC >> ntac 3 AP_TERM_TAC >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    first_x_assum irule >> gvs[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
    goal_assum $ drule_at Any >> res_tac
    )
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

Triviality subst1_lets_for_closed:
  ¬ MEM var (MAP SND vs) ∧ closed x
  ⇒ subst1 var x (lets_for cn ar v vs e) =
    subst1 var x (lets_for cn ar v vs (subst1 var x e))
Proof
  Induct_on `vs` >> rw[lets_for_def] >- simp[subst1_subst1_eq] >>
  PairCases_on `h` >> gvs[lets_for_def, subst1_def]
QED

Triviality subst1_lets_for_cexp_closed:
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

Theorem exp_of_tcexp_of_exp_eq:
  ∀e. cexp_wf e ∧ NestedCase_free e
    ⇒ pure_tcexp$exp_of (tcexp_of e) ≅ pureLang$exp_of e
Proof
  recInduct tcexp_of_ind >>
  rw[cexp_wf_def, tcexp_of_def, exp_of_def, pureLangTheory.exp_of_def]
  >- simp[exp_eq_Var_cong]
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
    irule exp_eq_Prim_cong >> rw[LIST_REL_EL_EQN, EL_MAP] >>
    first_x_assum irule >> simp[EL_MEM] >> gvs[EVERY_EL]
    )
  >- (
    irule exp_eq_App_cong >> simp[] >>
    irule exp_eq_Lam_cong >> simp[]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF] >> gvs[] >>
    qpat_x_assum `_ ≠ []` kall_tac >> gvs[EVERY_MEM] >>
    ntac 4 $ pop_assum kall_tac >>
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
    ntac 2 (first_x_assum $ irule_at Any >> goal_assum drule) >> gvs[]
    ) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  irule exp_eq_App_cong >> simp[] >>
  irule exp_eq_Lam_cong >> simp[] >>
  qpat_x_assum `_ ≠ _` kall_tac >>
  Induct_on `rs` >> rw[rows_of_def, pureLangTheory.rows_of_def]
  >- simp[exp_eq_refl] >>
  pairarg_tac >> gvs[rows_of_def, pureLangTheory.rows_of_def] >>
  qmatch_goalsub_abbrev_tac `_ ≅ If _ _ rows` >>
  irule exp_eq_trans >> irule_at Any exp_eq_Prim_cong >>
  qmatch_goalsub_abbrev_tac `[a;b c;_]` >>
  qexists_tac `[a;b (exp_of p2);rows]` >> unabbrev_all_tac >> simp[exp_eq_refl] >>
  last_x_assum $ irule_at Any >> rw[]
  >- (
    first_x_assum irule >> simp[] >> qexistsl_tac [`c`,`vs`] >> simp[]
    )
  >- (irule exp_eq_lets_for_cong >> simp[]) >>
  rename [`If _ (_ e) rest`,`IsEq cn (_ vs) _`] >>
  simp[lets_for_exp_eq]
QED


val _ = export_theory();
