(*
   Correctness for freshening of bound variables.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory listTheory alistTheory rich_listTheory pred_setTheory
     finite_mapTheory;
open pure_miscTheory pure_expTheory pure_cexpTheory pureLangTheory
     pure_alpha_equivTheory pure_congruenceTheory pure_beta_equivTheory
     pure_barendregtTheory pure_exp_lemmasTheory pure_cexp_lemmasTheory
     pure_varsTheory var_setTheory pure_freshenTheory pure_letrecProofTheory
     pure_typingTheory pure_typingPropsTheory pure_tcexpTheory;

val _ = new_theory "pure_freshenProof";

val exp_of_def = pureLangTheory.exp_of_def;
val rows_of_def = pureLangTheory.rows_of_def;
val lets_for_def = pureLangTheory.lets_for_def;


(****************************** TODO move ******************************)

Theorem boundvars_subst_SUBSET:
  ∀m e.  boundvars (subst m e) ⊆ boundvars e ∪ BIGUNION (IMAGE boundvars $ FRANGE m)
Proof
  recInduct subst_ind >> rw[subst_def]
  >- (
    CASE_TAC >> rw[SUBSET_DEF, PULL_EXISTS, IN_FRANGE_FLOOKUP] >>
    rpt $ goal_assum drule
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF] >> rw[BIGUNION_SUBSET, MEM_MAP] >>
    first_x_assum drule >> strip_tac >>
    irule SUBSET_TRANS >> goal_assum drule >> rw[SUBSET_DEF] >> disj1_tac >>
    simp[MEM_MAP, PULL_EXISTS, SF SFY_ss]
    )
  >- (irule SUBSET_TRANS >> goal_assum drule >> simp[SUBSET_DEF])
  >- (irule SUBSET_TRANS >> goal_assum drule >> simp[SUBSET_DEF])
  >- (
    irule SUBSET_TRANS >> goal_assum drule >>
    rw[SUBSET_DEF, PULL_EXISTS, IN_FRANGE_FLOOKUP] >>
    gvs[DOMSUB_FLOOKUP_THM, SF SFY_ss]
    )
  >- (
    irule SUBSET_TRANS >> goal_assum drule >> rw[] >- simp[SUBSET_DEF] >>
    rw[BIGUNION_SUBSET, SUBSET_DEF, PULL_EXISTS] >> rpt disj2_tac >>
    gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_SIMP, SF SFY_ss]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >> rw[SUBSET_DEF]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
    rw[BIGUNION_SUBSET, MEM_MAP] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >> rw[] >> irule SUBSET_TRANS >> goal_assum drule >> rw[]
    >- rw[SUBSET_DEF, PULL_EXISTS, MEM_MAP, EXISTS_PROD, SF SFY_ss] >>
    rw[BIGUNION_SUBSET, SUBSET_DEF, PULL_EXISTS] >> rpt disj2_tac >>
    gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_SIMP, SF SFY_ss]
    )
QED

Theorem set_MAP_SND_fmap_to_alist:
  set (MAP SND (fmap_to_alist m)) = FRANGE m
Proof
  rw[fmap_to_alist_def, EXTENSION, MEM_MAP, EXISTS_PROD, IN_FRANGE_FLOOKUP]
QED

Theorem allvars_subst_SUBSET:
  allvars (subst m e) ⊆ allvars e ∪ BIGUNION (IMAGE allvars (FRANGE m))
Proof
  rw[SUBSET_DEF, allvars_thm] >>
  imp_res_tac $ SRULE [SUBSET_DEF] freevars_subst_SUBSET >>
  imp_res_tac $ SRULE [SUBSET_DEF] boundvars_subst_SUBSET >>
  gvs[PULL_EXISTS] >> metis_tac[]
QED

Theorem ALOOKUP_REVERSE_fmap_to_alist[simp]:
  ALOOKUP (REVERSE (fmap_to_alist m)) = ALOOKUP (fmap_to_alist m)
Proof
  rw[FUN_EQ_THM] >>
  Cases_on `ALOOKUP (REVERSE (fmap_to_alist m)) x`
  >- gvs[ALOOKUP_NONE, MAP_REVERSE, FLOOKUP_DEF]
  >- (imp_res_tac ALOOKUP_MEM >> gvs[])
QED

Theorem EL_split:
  ∀l n. n < LENGTH l ⇒ l = TAKE n l ++ [EL n l] ++ DROP (n + 1) l
Proof
  rw[] >> qspecl_then [`1`,`n`,`l`] assume_tac TAKE_SEG_DROP >> gvs[SEG1]
QED

Theorem FRANGE_FUPDATE_LIST_ALL_DISTINCT:
  ∀l m.
    ALL_DISTINCT (MAP FST l) ⇒
    set (MAP SND l) ⊆ FRANGE (m |++ l)
Proof
  Induct_on `l` using SNOC_INDUCT >> rw[] >>
  gvs[SNOC_APPEND, FUPDATE_LIST_APPEND, ALL_DISTINCT_APPEND] >>
  PairCases_on `x` >> gvs[FUPDATE_LIST_THM] >>
  gvs[DOMSUB_FUPDATE_LIST] >>
  qmatch_goalsub_abbrev_tac `FILTER f l`  >>
  qsuff_tac `FILTER f l = l` >- gvs[SUBSET_DEF] >>
  simp[FILTER_EQ_ID] >> unabbrev_all_tac >>
  gvs[EVERY_MEM, MEM_MAP, combinTheory.o_DEF, FORALL_PROD]
QED

Theorem letrecs_distinct_Disj[simp]:
  letrecs_distinct (Disj x cnars) = T
Proof
  Induct_on `cnars` >> rw[Disj_def, letrecs_distinct_def] >>
  PairCases_on `h` >> rw[Disj_def, letrecs_distinct_def]
QED

Theorem letrecs_distinct_IfDisj[simp]:
  letrecs_distinct (IfDisj x cnars e) ⇔
  letrecs_distinct e
Proof
  Induct_on `cnars` >> rw[IfDisj_def, letrecs_distinct_def]
QED

Triviality ALOOKUP_MAP_3':
  ALOOKUP (MAP (λ(k,v1,v2). (k,v1,f v1 v2)) l) =
  OPTION_MAP (λ(v1,v2). (v1, f v1 v2)) o ALOOKUP l
Proof
  Induct_on `l` >> rw[FUN_EQ_THM] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[]
QED


(****************************** Relations ******************************)

Overload subst_vars = ``λm. subst (Var o_f m)``;
Overload subst1_var = ``λx y. subst_vars (FEMPTY |+ (x,y))``;


(********** substitution **********)

Inductive freshen_subst:
  freshen_subst avoid (Var x) (Var x) ∧

  (LIST_REL (freshen_subst avoid) es es'
    ⇒ freshen_subst avoid (Prim op es) (Prim op es')) ∧

  (y ∉ avoid ∧
   freshen_subst (y INSERT avoid) (subst1_var x y e) e'
    ⇒ freshen_subst avoid (Lam x e) (Lam y e')) ∧

  (freshen_subst avoid e1 e1' ∧ freshen_subst avoid e2 e2'
    ⇒ freshen_subst avoid (App e1 e2) (App e1' e2')) ∧

  (FDOM m = set (MAP FST fns) ∧
   DISJOINT (FRANGE m) avoid ∧
   (∀k k' v. FLOOKUP m k = SOME v ∧ FLOOKUP m k' = SOME v ⇒ k = k') ∧
   LIST_REL (λ(f,body) (f',body').
      FLOOKUP m f = SOME f' ∧
      freshen_subst (avoid ∪ FRANGE m)
        (subst_vars m body) body') fns fns' ∧
   freshen_subst (avoid ∪ FRANGE m) (subst_vars m e) e'
    ⇒ freshen_subst avoid (Letrec fns e) (Letrec fns' e'))
End

Theorem perm_exp_alpha_subst:
  y ∉ allvars e ⇒
    exp_alpha (perm_exp x y e) (subst1 x (Var y) e)
Proof
  simp[allvars_thm] >>
  Induct_on `e` using freevars_ind >> rw[perm_exp_def, subst1_def, perm1_simps] >>
  gvs[exp_alpha_refl]
  >- rw[perm1_def, exp_alpha_refl]
  >- (
    irule exp_alpha_Prim >>
    gvs[LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS] >> rw[] >>
    last_x_assum drule >> disch_then irule >> metis_tac[EL_MAP]
    )
  >- (irule exp_alpha_App >> simp[])
  >- (
    simp[Once exp_alpha_cases] >>
    simp[Once perm_exp_compose, perm1_simps] >> disj2_tac >>
    simp[freevars_eqvt, perm1_def, AllCaseEqs()] >> metis_tac[]
    )
  >- (simp[perm1_def] >> irule exp_alpha_Lam >> simp[])
  >- (
    irule exp_alpha_sym >>
    drule exp_alpha_Letrec_Alpha_MEM >> simp[PAIR_MAP_ALT]
    )
  >- (
    irule exp_alpha_Letrec >> rw[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
    >- (
      rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
      gvs[MEM_MAP, FORALL_PROD] >> rw[perm1_def] >> gvs[]
      )
    >- (
      last_x_assum mp_tac >>
      rw[LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> disch_then irule >>
      gvs[MEM_MAP, FORALL_PROD] >> metis_tac[EL_MEM]
      )
    )
QED

Theorem perm_exp_list_alpha_subst:
  ∀binds m e.
  DISJOINT (FRANGE m) (allvars e) ∧
  binds_ok binds ∧
  ALL_DISTINCT (MAP FST binds) ∧
  set (MAP FST binds) = FDOM m ∧
  (∀k v. FLOOKUP m k = SOME v ⇒ ALOOKUP binds k = SOME v)
  ⇒ exp_alpha (perm_exp_list binds e) (subst_vars m e)
Proof
  Induct >> rw[] >> gvs[perm_exp_list_def]
  >- (Cases_on `m` >> gvs[exp_alpha_refl]) >>
  PairCases_on `h` >> rename1 `x,y` >> gvs[perm_exp_list_def] >>
  gvs[ALOOKUP_APPEND, AllCaseEqs(), ALOOKUP_NONE, MAP_REVERSE] >>
  `FLOOKUP m x = SOME y` by (
    Cases_on `FLOOKUP m x` >> gvs[]
    >- (gvs[FLOOKUP_DEF, EXTENSION] >> metis_tac[]) >>
    first_x_assum drule >> rw[] >> gvs[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP]) >>
  `m = m |+ (x,y)` by (irule $ GSYM FUPDATE_ELIM >> gvs[FLOOKUP_DEF]) >>
  pop_assum SUBST1_TAC >>
  rewrite_tac[Once FUPDATE_PURGE] >>
  simp[Once FUPDATE_EQ_FUNION] >> simp[Once FUNION_COMM] >>
  DEP_REWRITE_TAC[GSYM subst_subst_DISJOINT_FUNION] >> conj_tac
  >- (
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
    rw[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] >>
    first_x_assum drule >> rw[] >> gvs[binds_ok_def] >>
    first_x_assum $ qspec_then `[]` assume_tac >> gvs[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP]
    ) >>
  irule exp_alpha_Trans >>
  irule_at Any exp_alpha_perm_closed >>
  irule_at Any perm_exp_alpha_subst >> rw[]
  >- (
    gvs[DISJOINT_ALT, IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
    CCONTR_TAC >> gvs[] >>
    drule $ SRULE [SUBSET_DEF] allvars_subst_SUBSET >>
    strip_tac >> gvs[] >- res_tac >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_o_f, AllCaseEqs(), DOMSUB_FLOOKUP_THM] >>
    first_assum drule >> strip_tac >> imp_res_tac ALOOKUP_MEM >>
    gvs[binds_ok_def] >>
    qpat_x_assum `∀l x y r. _` $ qspec_then `[]` assume_tac >> gvs[MEM_MAP]
    ) >>
  last_x_assum irule >> rw[]
  >- (gvs[DOMSUB_FLOOKUP_THM] >> first_x_assum drule >> rw[])
  >- gvs[binds_ok_def]
  >- (gvs[EXTENSION] >> metis_tac[])
  >- (
    gvs[DISJOINT_ALT, IN_FRANGE_FLOOKUP, PULL_EXISTS, DOMSUB_FLOOKUP_THM] >>
    metis_tac[]
    )
QED

Theorem fmap_to_alist_binds_ok:
  (∀k k' v. FLOOKUP m k = SOME v ∧ FLOOKUP m k' = SOME v ⇒ k = k') ∧
  DISJOINT (FDOM m) (FRANGE m)
  ⇒ binds_ok (fmap_to_alist m)
Proof
  rw[binds_ok_def]
  >- (
    CCONTR_TAC >> gvs[MEM_MAP, EXISTS_PROD] >>
    `x ∈ FDOM m` by (
      rewrite_tac[GSYM set_MAP_FST_fmap_to_alist] >>
      simp[Excl "set_MAP_FST_fmap_to_alist"]) >>
    `x ∈ FRANGE m` by (
      simp[GSYM set_MAP_SND_fmap_to_alist, MEM_MAP, EXISTS_PROD, SF SFY_ss]) >>
    gvs[DISJOINT_ALT]
    )
  >- (
    CCONTR_TAC >> gvs[MEM_MAP, EXISTS_PROD] >>
    `MEM (x,y) (fmap_to_alist m) ∧ MEM (p_1,y) (fmap_to_alist m)` by (
      qpat_x_assum `fmap_to_alist _ = _` SUBST_ALL_TAC >> simp[]) >>
    gvs[] >> first_x_assum dxrule_all >> rw[] >>
    qspec_then `m` assume_tac ALL_DISTINCT_fmap_to_alist_keys >>
    qpat_x_assum `fmap_to_alist _ = _` SUBST_ALL_TAC >> simp[] >>
    gvs[ALL_DISTINCT_APPEND, MEM_MAP, EXISTS_PROD] >> metis_tac[]
    )
QED

Theorem freshen_subst_exp_alpha:
  ∀avoid e1 e2.
    freshen_subst avoid e1 e2 ∧ allvars e1 ⊆ avoid
  ⇒ exp_alpha e1 e2
Proof
  Induct_on `freshen_subst` >> rw[exp_alpha_refl]
  >- ( (* Prim *)
    irule exp_alpha_Prim >> gvs[LIST_REL_EL_EQN] >> rw[] >>
    first_x_assum drule >> strip_tac >>
    first_x_assum irule >> gvs[BIGUNION_SUBSET, MEM_MAP, MEM_EL, PULL_EXISTS]
    )
  >- ( (* Lam *)
    `x ≠ y` by (CCONTR_TAC >> gvs[]) >>
    irule exp_alpha_Trans >> qexists `Lam y (subst1 x (Var y) e)` >>
    irule_at Any exp_alpha_Trans >> qexists `Lam y (perm_exp x y e)` >>
    irule_at Any exp_alpha_Lam >> irule_at Any perm_exp_alpha_subst >>
    irule_at Any exp_alpha_Alpha >>
    irule_at Any exp_alpha_Lam >> gvs[] >>
    first_x_assum $ irule_at Any >>
    irule_at Any SUBSET_TRANS >> irule_at Any allvars_subst_SUBSET >>
    simp[IN_FRANGE_FLOOKUP, FLOOKUP_SIMP] >>
    gvs[SUBSET_DEF, allvars_thm] >> metis_tac[]
    )
  >- (irule exp_alpha_App >> gvs[]) (* App *) >>
  (* Letrec *)
  qpat_x_assum `_ ⇒ exp_alpha _ _` mp_tac >> impl_keep_tac
  >- (
    irule SUBSET_TRANS >> irule_at Any allvars_subst_SUBSET >>
    gvs[SUBSET_DEF, PULL_EXISTS, IN_FRANGE_FLOOKUP, FLOOKUP_o_f, AllCaseEqs()]
    ) >>
  strip_tac >> irule exp_alpha_Trans >>
  irule_at Any exp_alpha_perm_exp_list >>
  simp[perm_exp_list_Letrec] >>
  irule_at Any exp_alpha_Letrec >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  qexists `fmap_to_alist m` >> rw[]
  >- (
    irule exp_alpha_Trans >> goal_assum $ drule_at Any >>
    irule perm_exp_list_alpha_subst >> simp[] >>
    irule_at Any fmap_to_alist_binds_ok >> simp[] >>
    gvs[DISJOINT_ALT, SUBSET_DEF, allvars_thm] >> metis_tac[]
    )
  >- (
    rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >>
    `binds_ok (fmap_to_alist m)` by (
      irule_at Any fmap_to_alist_binds_ok >> simp[] >>
      gvs[DISJOINT_ALT, SUBSET_DEF, allvars_thm] >> metis_tac[]) >>
    drule_at Any perm1_list_apply >> simp[] >>
    disch_then $ qspec_then `f` mp_tac >>
    simp[MEM_EL, PULL_EXISTS] >> disch_then drule >> simp[EL_MAP]
    )
  >- (
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >>
    irule exp_alpha_Trans >> first_x_assum $ irule_at Any >>
    irule_at Any perm_exp_list_alpha_subst >> simp[] >>
    irule_at Any fmap_to_alist_binds_ok >> simp[] >>
    irule_at Any SUBSET_TRANS >> irule_at Any allvars_subst_SUBSET >>
    gvs[DISJOINT_ALT, SUBSET_DEF, allvars_thm,
        MEM_MAP, MEM_EL, EXISTS_PROD, GSYM IMAGE_FRANGE, PULL_EXISTS] >>
    metis_tac[]
    )
  >- simp[DISJOINT_ALT]
  >- (
    simp[set_MAP_SND_fmap_to_alist] >>
    irule DISJOINT_SUBSET >> goal_assum drule >>
    gvs[allvars_thm, SUBSET_DEF, MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
    metis_tac[]
    )
QED


(********** stacked substitution **********)

Inductive freshen_stack:
  (FLOOKUP m x = NONE
    ⇒ freshen_stack avoid m (Var x) (Var x)) ∧

  (FLOOKUP m x = SOME y
    ⇒ freshen_stack avoid m (Var x) (Var y)) ∧

  (LIST_REL (freshen_stack avoid m) es es'
    ⇒ freshen_stack avoid m (Prim op es) (Prim op es')) ∧

  (y ∉ avoid ∧ freshen_stack (y INSERT avoid) (m |+ (x,y)) e e'
    ⇒ freshen_stack avoid m (Lam x e) (Lam y e')) ∧

  (freshen_stack avoid m e1 e1' ∧ freshen_stack avoid m e2 e2'
    ⇒ freshen_stack avoid m (App e1 e2) (App e1' e2')) ∧

  (FDOM new = set (MAP FST fns) ∧
   DISJOINT (FRANGE new) avoid ∧
   (∀k k' v. FLOOKUP new k = SOME v ∧ FLOOKUP new k' = SOME v ⇒ k = k') ∧
   LIST_REL (λ(f,body) (f',body').
      FLOOKUP new f = SOME f' ∧
      freshen_stack (avoid ∪ FRANGE new) (FUNION new m) body body') fns fns' ∧
   freshen_stack (avoid ∪ FRANGE new) (FUNION new m) e e'
   ⇒ freshen_stack avoid m (Letrec fns e) (Letrec fns' e'))
End

Theorem freshen_stack_freshen_subst:
  ∀m e1 e2 avoid.
    freshen_stack avoid m e1 e2 ∧
    boundvars e1 ⊆ avoid ∧
    FRANGE m ⊆ avoid ∧
    DISJOINT (FRANGE m) (boundvars e1)
  ⇒ freshen_subst avoid (subst_vars m e1) e2
Proof
  Induct_on `freshen_stack` >> rw[] >>
  simp[Once freshen_subst_cases] >> gvs[subst_def, FLOOKUP_o_f]
  >- (
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> pop_assum irule >>
    gvs[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, MEM_EL]
    )
  >- (
    qpat_x_assum `_ ⇒ _` mp_tac >> impl_tac
    >-  (
      gvs[SUBSET_DEF, DISJOINT_ALT, IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] >>
      metis_tac[]
      ) >>
    strip_tac >>
    qsuff_tac `subst (Var o_f m |+ (x,Var y)) e1 =
               subst1 x (Var y) (subst_vars (m \\ x) e1)` >>
    rw[] >> gvs[] >>
    rewrite_tac[Once FUPDATE_PURGE, Once FUPDATE_EQ_FUNION] >>
    DEP_ONCE_REWRITE_TAC[FUNION_COMM] >> simp[] >>
    DEP_REWRITE_TAC[GSYM subst_subst_DISJOINT_FUNION] >> simp[] >>
    gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_o_f,
        DOMSUB_FLOOKUP_THM, AllCaseEqs()]
    )
  >- (
    rpt $ first_x_assum $ irule_at Any >> gvs[DISJOINT_ALT] >> metis_tac[]
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
    goal_assum drule >> reverse $ rw[]
    >- (
      `subst_vars new (subst (FDIFF (Var o_f m) (set (MAP FST fns))) e1) =
       subst_vars (FUNION new m) e1` by (
        simp[o_f_FUNION] >> once_rewrite_tac[FUNION_FDIFF] >>
        DEP_ONCE_REWRITE_TAC[FUNION_COMM] >>
        DEP_REWRITE_TAC[GSYM subst_subst_DISJOINT_FUNION] >>
        gvs[FDOM_FDIFF_alt, PULL_EXISTS, IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF,
            FLOOKUP_o_f, AllCaseEqs(), DISJOINT_ALT] >> metis_tac[]) >>
      simp[] >> first_x_assum irule >> rw[]
      >- (
        irule $ iffLR DISJOINT_SYM >> irule DISJOINT_SUBSET >>
        irule_at Any FRANGE_FUNION_SUBSET >> simp[] >>
        gvs[DISJOINT_ALT, SUBSET_DEF] >> metis_tac[]
        )
      >- (
        irule SUBSET_TRANS >> irule_at Any FRANGE_FUNION_SUBSET >> simp[] >>
        gvs[SUBSET_DEF]
        )
      >- gvs[SUBSET_DEF]
      ) >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >>
    strip_tac >> gvs[] >>
    `subst_vars new (subst (FDIFF (Var o_f m) (set (MAP FST fns))) e1') =
     subst_vars (FUNION new m) e1'` by (
      simp[o_f_FUNION] >> once_rewrite_tac[FUNION_FDIFF] >>
      DEP_ONCE_REWRITE_TAC[FUNION_COMM] >>
      DEP_REWRITE_TAC[GSYM subst_subst_DISJOINT_FUNION] >>
      gvs[FDOM_FDIFF_alt, PULL_EXISTS, IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF,
          FLOOKUP_o_f, AllCaseEqs(), DISJOINT_ALT] >> metis_tac[]) >>
    simp[] >> qpat_x_assum `_ ⇒ _` mp_tac >> impl_tac >> rw[]
    >- (
      qpat_x_assum `BIGUNION _ ⊆ _` mp_tac >>
      simp[BIGUNION_SUBSET, MEM_MAP, MEM_EL, PULL_EXISTS] >>
      disch_then drule >> rw[SUBSET_DEF]
      )
    >- (
      irule SUBSET_TRANS >> irule_at Any FRANGE_FUNION_SUBSET >> simp[] >>
      gvs[SUBSET_DEF]
      )
    >- (
      irule $ iffLR DISJOINT_SYM >> irule DISJOINT_SUBSET >>
      irule_at Any FRANGE_FUNION_SUBSET >> simp[] >>
      gvs[BIGUNION_SUBSET, MEM_MAP, MEM_EL, PULL_EXISTS] >>
      rpt $ first_x_assum drule >> simp[] >>
      gvs[DISJOINT_ALT, SUBSET_DEF] >> metis_tac[]
      )
    )
QED

Theorem freshen_stack_mono:
  ∀avoid m e1 e2 avoid'.
    freshen_stack avoid m e1 e2 ∧
    avoid' ⊆ avoid
  ⇒ freshen_stack avoid' m e1 e2
Proof
  Induct_on `freshen_stack` >> rw[] >>
  simp[Once freshen_stack_cases]
  >- gvs[LIST_REL_EL_EQN]
  >- (first_x_assum $ irule_at Any >> gvs[SUBSET_DEF] >> metis_tac[])
  >- (
    goal_assum drule >> gvs[] >>
    irule_at Any DISJOINT_SUBSET >> goal_assum drule >> simp[] >>
    first_x_assum $ irule_at Any >> rw[] >- gvs[SUBSET_DEF] >>
    gvs[LIST_REL_EL_EQN] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
    pop_assum irule >> gvs[SUBSET_DEF]
    )
QED

Theorem freshen_stack_boundvars:
  ∀avoid m e1 e2.
    freshen_stack avoid m e1 e2 ⇒ DISJOINT (boundvars e2) avoid
Proof
  Induct_on `freshen_stack` >> rw[]
  >- (
    pop_assum mp_tac >> simp[MEM_MAP, MEM_EL] >> rw[] >> gvs[] >>
    gvs[LIST_REL_EL_EQN]
    )
  >- simp[Once DISJOINT_SYM]
  >- (
    rw[DISJOINT_ALT, MEM_MAP, MEM_EL, EXISTS_PROD] >>
    pop_assum $ assume_tac o GSYM >> gvs[LIST_REL_EL_EQN] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >>
    `MEM f (MAP FST fns)` by (
      simp[MEM_MAP, MEM_EL, EXISTS_PROD] >> goal_assum drule >> simp[]) >>
    qpat_x_assum `FLOOKUP _ _ = _` mp_tac >>
    simp[FLOOKUP_SIMP, Once FLOOKUP_DEF] >>
    gvs[FRANGE_DEF, DISJOINT_ALT] >> metis_tac[]
    )
  >- (
    gvs[MEM_MAP, MEM_EL, LIST_REL_EL_EQN] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >>
    simp[Once DISJOINT_SYM]
    )
QED


(********** global stacked substitution **********)

Inductive freshen_global:
  (FLOOKUP m x = NONE
    ⇒ freshen_global avoid m (Var x) (Var x)) ∧

  (FLOOKUP m x = SOME y
    ⇒ freshen_global avoid m (Var x) (Var y)) ∧

  (LENGTH es' = LENGTH es ∧
   (∀l e r. es = l ++ [e] ++ r ⇒
      ∃l' e' r'. es' = l' ++ [e'] ++ r' ∧ LENGTH l' = LENGTH l ∧
        freshen_global (avoid ∪ BIGUNION (set (MAP boundvars l'))) m e e')
    ⇒ freshen_global avoid m (Prim op es) (Prim op es')) ∧

  (y ∉ avoid ∧ freshen_global (y INSERT avoid) (m |+ (x,y)) e e'
    ⇒ freshen_global avoid m (Lam x e) (Lam y e')) ∧

  (freshen_global avoid m e1 e1' ∧
   freshen_global (avoid ∪ boundvars e1') m e2 e2'
    ⇒ freshen_global avoid m (App e1 e2) (App e1' e2')) ∧

  (freshen_global avoid m e1 e1' ∧
   y ∉ avoid ∪ boundvars e1' ∧
   freshen_global (y INSERT avoid ∪ boundvars e1') (m |+ (x,y)) e2 e2'
    ⇒ freshen_global avoid m (Let x e1 e2) (Let y e1' e2')) ∧

  (FDOM new = set (MAP FST fns) ∧
   DISJOINT (FRANGE new) avoid ∧
   (∀k k' v. FLOOKUP new k = SOME v ∧ FLOOKUP new k' = SOME v ⇒ k = k') ∧
   LENGTH fns' = LENGTH fns ∧
   (∀l f e r. fns = l ++ [f,e] ++ r ⇒
      ∃l' f' e' r'. fns' = l' ++ [f',e'] ++ r' ∧ LENGTH l' = LENGTH l ∧
        FLOOKUP new f = SOME f' ∧
        freshen_global
          (avoid ∪ FRANGE new ∪ BIGUNION (set $ MAP (λ(f,e). boundvars e) l'))
          (FUNION new m) e e') ∧
    freshen_global
      (avoid ∪ FRANGE new ∪ BIGUNION (set $ MAP (λ(f,e). boundvars e) fns'))
      (FUNION new m) e e'
   ⇒ freshen_global avoid m (Letrec fns e) (Letrec fns' e'))
End

Theorem freshen_global_freshen_stack:
  ∀m avoid e1 e2.
    freshen_global avoid m e1 e2 ⇒ freshen_stack avoid m e1 e2
Proof
  Induct_on `freshen_global` >> rw[] >>
  simp[Once freshen_stack_cases]
  >- (
    rw[LIST_REL_EL_EQN] >>
    drule EL_split >> strip_tac >>
    first_x_assum drule >> rw[] >> gvs[EL_APPEND_EQN] >>
    irule freshen_stack_mono >> goal_assum $ drule_at Any >> simp[]
    )
  >- (irule freshen_stack_mono >> goal_assum $ drule_at Any >> simp[])
  >- (
    simp[Once freshen_stack_cases] >>
    irule freshen_stack_mono >> goal_assum $ drule_at Any >> simp[]
    )
  >- (
    goal_assum drule >> simp[] >>
    irule_at Any freshen_stack_mono >> goal_assum $ drule_at Any >>
    conj_tac >- gvs[SUBSET_DEF] >>
    rw[LIST_REL_EL_EQN] >> rpt (pairarg_tac >> gvs[]) >>
    drule EL_split >> strip_tac >> gvs[] >>
    last_x_assum drule >> strip_tac >> gvs[EL_APPEND_EQN] >>
    irule freshen_stack_mono >> goal_assum $ drule_at Any >> simp[SUBSET_DEF]
    )
QED

Theorem freshen_global_boundvars:
  ∀m avoid e1 e2.
    freshen_global avoid m e1 e2 ⇒ DISJOINT (boundvars e2) avoid
Proof
  rw[] >> dxrule freshen_global_freshen_stack >> rw[] >>
  dxrule freshen_stack_boundvars >> simp[]
QED

Theorem freshen_global_mono:
  ∀m avoid e1 e2 avoid'.
    freshen_global avoid m e1 e2 ∧ avoid' ⊆ avoid
  ⇒ freshen_global avoid' m e1 e2
Proof
  Induct_on `freshen_global` >> rw[] >> simp[Once freshen_global_cases] >>
  rw[] >> gvs[]
  >- (
    last_x_assum $ qspec_then `l` mp_tac >> rw[] >> gvs[] >>
    irule_at Any EQ_REFL >> simp[] >>
    first_x_assum irule >> gvs[SUBSET_DEF]
    )
  >- (gvs[SUBSET_DEF] >> CCONTR_TAC >> gvs[])
  >- ( first_x_assum irule >> gvs[SUBSET_DEF])
  >- (disj1_tac >> first_x_assum irule >> gvs[SUBSET_DEF])
  >- (
    disj2_tac >> first_x_assum $ irule_at Any >> gvs[SUBSET_DEF] >>
    CCONTR_TAC >> gvs[]
    )
  >- (
    goal_assum drule >> gvs[] >> rw[]
    >- (irule DISJOINT_SUBSET >> goal_assum drule >> simp[])
    >- (
      last_x_assum $ qspec_then `l` mp_tac >> rw[] >>
      irule_at Any EQ_REFL >> gvs[] >>
      first_x_assum irule >> gvs[SUBSET_DEF]
      )
    >- (first_x_assum irule >> gvs[SUBSET_DEF])
    )
QED

(*
  TODO:
    letrec_distinct should not be necessary here,
    if the freshening relations are strengthened
*)
Theorem freshen_global_unique_boundvars:
  ∀m avoid e1 e2.
    freshen_global avoid m e1 e2 ∧ letrecs_distinct e1
  ⇒ unique_boundvars e2
Proof
  Induct_on `freshen_global` >>
  rw[unique_boundvars_def, letrecs_distinct_def, list_disjoint_cons] >>
  gvs[]
  >- (
    gvs[EVERY_EL] >> rw[] >> drule EL_split >> strip_tac >>
    last_x_assum drule >> rw[] >> gvs[EL_APPEND_EQN]
    )
  >- (
    simp[list_disjoint_def, MAP_EQ_APPEND] >> rw[] >> gvs[]
    >- (
      rename1 `l' ++ [e'] ++ r'` >> gvs[MEM_MAP, MEM_EL] >>
      qspecl_then [`es`,`LENGTH l'`] mp_tac EL_split >>
      simp[] >> strip_tac >>
      first_x_assum drule >> rw[] >> gvs[EVERY_EL, APPEND_11_LENGTH] >>
      dxrule freshen_global_boundvars >> rw[DISJOINT_ALT] >>
      gvs[MEM_MAP, MEM_EL, PULL_EXISTS] >> metis_tac[]
      )
    >- (
      rename1 `l' ++ [e'] ++ r'` >> gvs[MEM_MAP, MEM_EL] >>
      qspecl_then [`es`,`LENGTH l' + n + 1`] mp_tac EL_split >>
      simp[] >> strip_tac >>
      first_x_assum drule >> rw[] >>
      gvs[APPEND_EQ_APPEND_MID, EL_APPEND_EQN, EVERY_EL] >>
      rename1 `LENGTH _ + (LENGTH ll + _)` >>
      `n = LENGTH ll` by DECIDE_TAC >> pop_assum SUBST_ALL_TAC >> gvs[] >>
      dxrule freshen_global_boundvars >> rw[DISJOINT_ALT]
      )
    )
  >- (dxrule freshen_global_boundvars >> rw[DISJOINT_ALT])
  >- (dxrule freshen_global_boundvars >> rw[DISJOINT_ALT])
  >- (dxrule freshen_global_boundvars >> rw[DISJOINT_ALT])
  >- (dxrule freshen_global_boundvars >> rw[DISJOINT_ALT] >> metis_tac[])
  >- (
    `MAP FST fns' = MAP (λx. THE (FLOOKUP new x)) (MAP FST fns)` by (
      rw[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_MAP] >>
      drule EL_split >> strip_tac >> Cases_on `EL n fns` >>
      first_x_assum drule >> rw[] >> gvs[EL_APPEND_EQN]) >>
    simp[] >> irule ALL_DISTINCT_MAP_INJ >> rw[] >>
    last_x_assum $ qspecl_then [`x`,`y`] mp_tac >> gvs[FLOOKUP_DEF]
    )
  >- (
    simp[list_disjoint_def, MAP_EQ_APPEND] >> rw[] >> gvs[MAP_EQ_APPEND]
    >- (
      rename1 `l' ++ [e'] ++ r'` >> gvs[MEM_MAP, MEM_EL] >>
      qspecl_then [`fns`,`LENGTH l'`] mp_tac EL_split >>
      simp[] >> strip_tac >> Cases_on `EL (LENGTH l') fns` >>
      first_x_assum drule >> rw[] >> gvs[EVERY_EL, APPEND_11_LENGTH] >>
      dxrule freshen_global_boundvars >> rw[DISJOINT_ALT] >>
      gvs[MEM_MAP, MEM_EL, PULL_EXISTS] >>
      first_x_assum drule >> pairarg_tac >> gvs[] >> metis_tac[]
      )
    >- (
      rename1 `l' ++ [e'] ++ r'` >> gvs[MEM_MAP, MEM_EL] >>
      qspecl_then [`fns`,`LENGTH l' + n + 1`] mp_tac EL_split >>
      simp[] >> strip_tac >>
      Cases_on `EL (n + (LENGTH l' + 1)) fns` >>
      first_x_assum drule >> rw[] >>
      gvs[APPEND_EQ_APPEND_MID, EL_APPEND_EQN, EVERY_EL] >>
      rename1 `LENGTH _ + (LENGTH ll + _)` >>
      `n = LENGTH ll` by DECIDE_TAC >> pop_assum SUBST_ALL_TAC >> gvs[] >>
      dxrule freshen_global_boundvars >> rw[DISJOINT_ALT] >>
      gvs[MEM_MAP, MEM_EL, PULL_EXISTS] >> PairCases_on `e'` >> gvs[]
      )
    )
  >- (
    dxrule freshen_global_boundvars >> rw[EVERY_MEM, DISJOINT_ALT] >>
    gvs[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> metis_tac[]
    )
  >- (
    simp[Once DISJOINT_SYM] >>
    irule DISJOINT_SUBSET >> qexists `FRANGE new` >>
    dxrule freshen_global_boundvars >> rw[EVERY_MEM, DISJOINT_ALT]
    >- metis_tac[] >>
    rw[SUBSET_DEF] >> gvs[MEM_MAP, MEM_EL] >>
    drule EL_split >> strip_tac >> Cases_on `EL n fns` >>
    first_x_assum drule >> rw[] >> gvs[EL_APPEND_EQN] >>
    gvs[IN_FRANGE_FLOOKUP, SF SFY_ss]
    )
  >- (
    gvs[EVERY_EL, EL_MAP] >> rw[] >>
    simp[Once DISJOINT_SYM] >> irule DISJOINT_SUBSET >>
    qexists `FRANGE new` >> rw[]
    >- (
      drule EL_split >> strip_tac >> Cases_on `EL n fns` >>
      rpt $ first_x_assum drule >> rw[] >> gvs[EL_APPEND_EQN] >>
      dxrule freshen_global_boundvars >> rw[DISJOINT_ALT] >> metis_tac[]
      )
    >- (
      rw[SUBSET_DEF] >> gvs[MEM_MAP, MEM_EL] >>
      drule EL_split >> strip_tac >> Cases_on `EL n' fns` >>
      last_x_assum drule >> rw[] >> gvs[EL_APPEND_EQN] >>
      gvs[IN_FRANGE_FLOOKUP, SF SFY_ss]
      )
    )
  >- (
    gvs[EVERY_EL] >> rw[] >> drule EL_split >> strip_tac >>
    first_x_assum drule >> rw[] >> Cases_on `EL n fns` >>
    last_x_assum drule >> rw[] >> gvs[EL_APPEND_EQN, EL_MAP]
    )
QED

Theorem unique_boundvars_letrecs_distinct:
  ∀e. unique_boundvars e ⇒ letrecs_distinct e
Proof
  Induct using unique_boundvars_ind >>
  rw[unique_boundvars_def, letrecs_distinct_def] >> gvs[EVERY_MEM]
QED

Theorem freshen_global_Lams:
  ∀xs ex ys ey avoid m.
    LENGTH xs = LENGTH ys ∧
    DISJOINT (set ys) avoid ∧
    ALL_DISTINCT ys ∧
    freshen_global (avoid ∪ set ys) (m |++ ZIP (xs,ys)) ex ey
  ⇒ freshen_global avoid m (Lams xs ex) (Lams ys ey)
Proof
  Induct >> rw[Lams_def] >> gvs[FUPDATE_LIST_THM] >>
  rename1 `x::xs` >> namedCases_on `ys` ["","y ys"] >> gvs[Lams_def] >>
  simp[Once freshen_global_cases] >> last_x_assum irule >> simp[] >>
  gvs[FUPDATE_LIST_THM] >>
  qmatch_goalsub_abbrev_tac `freshen_global A` >>
  qmatch_asmsub_abbrev_tac `freshen_global B` >>
  qsuff_tac `A = B` >> gvs[] >>
  unabbrev_all_tac >> rw[EXTENSION] >> gvs[] >> metis_tac[]
QED

Theorem freshen_global_Disj:
  FLOOKUP m x = SOME y ⇒
  freshen_global avoid m (Disj x cnars) (Disj y cnars)
Proof
  Induct_on `cnars` >> rw[Disj_def]
  >- simp[Once freshen_global_cases] >>
  PairCases_on `h` >> rw[Disj_def] >>
  rw[Once freshen_global_cases] >> Cases_on `l` >> gvs[]
  >- (
    rw[Once freshen_global_cases] >> Cases_on `l` >> gvs[] >>
    simp[Once freshen_global_cases]
    ) >>
  Cases_on `t` >> gvs[LENGTH_EQ_NUM_compute, PULL_EXISTS]
  >- simp[Once freshen_global_cases] >>
  Cases_on `t'` >> gvs[LENGTH_EQ_NUM_compute, PULL_EXISTS]
QED

Theorem freshen_global_IfDisj:
  FLOOKUP m (explode x) = SOME (explode y) ∧ freshen_global avoid m e1 e2 ⇒
  freshen_global avoid m (IfDisj x cnars e1) (IfDisj y cnars e2)
Proof
  rw[IfDisj_def] >>
  rw[Once freshen_global_cases] >> Cases_on `l` >> gvs[]
  >- (irule freshen_global_Disj >> simp[]) >>
  Cases_on `t` >> gvs[LENGTH_EQ_NUM_compute, PULL_EXISTS] >>
  Cases_on `t'` >> gvs[LENGTH_EQ_NUM_compute, PULL_EXISTS] >>
  simp[Once freshen_global_cases]
QED

Theorem freshen_global_lets_for:
  ∀projs1 projs2 x y avoid m e1 e2.
    ¬MEM x (MAP SND projs1) ∧
    FLOOKUP m x = SOME y ∧
    freshen_global (avoid ∪ set (MAP SND projs2))
      (m |++ ZIP (MAP SND projs1, MAP SND projs2)) e1 e2 ∧
    MAP FST projs2 = MAP FST projs1 ∧
    ALL_DISTINCT (MAP SND projs2) ∧
    DISJOINT (set (MAP SND projs2)) avoid
  ⇒ freshen_global avoid m (lets_for cn x projs1 e1) (lets_for cn y projs2 e2)
Proof
  Induct >> rw[lets_for_def] >> gvs[FUPDATE_LIST_THM] >>
  PairCases_on `h` >> gvs[] >>
  Cases_on `projs2` >> gvs[] >> PairCases_on `h` >> gvs[lets_for_def] >>
  simp[Once freshen_global_cases] >> disj2_tac >> rw[]
  >- (
    rw[Once freshen_global_cases] >> Cases_on `l` >> gvs[] >>
    simp[Once freshen_global_cases]
    ) >>
  last_x_assum irule >> simp[] >> gvs[FLOOKUP_SIMP, FUPDATE_LIST_THM] >>
  qmatch_goalsub_abbrev_tac `freshen_global A` >>
  qmatch_asmsub_abbrev_tac `freshen_global B` >>
  qsuff_tac `A = B` >> gvs[] >>
  unabbrev_all_tac >> rw[EXTENSION] >> metis_tac[]
QED

Theorem freshen_global_rows_of:
  ∀css1 css2 x y avoid m k1 k2.
    FLOOKUP m x = SOME y ∧
    freshen_global
      (avoid ∪ BIGUNION (set $ MAP (λ(cn,pvs,ce). set pvs ∪ boundvars ce) css2))
      m k1 k2 ∧
    LENGTH css1 = LENGTH css2 ∧
    (∀l1 cn pvs1 ce1 r1. css1 = l1 ++ [cn,pvs1,ce1] ++ r1 ⇒
      ¬ MEM x pvs1 ∧
      ∃l2 pvs2 ce2 r2. css2 = l2 ++ [cn,pvs2,ce2] ++ r2 ∧
        LENGTH l2 = LENGTH l1 ∧ LENGTH pvs2 = LENGTH pvs1 ∧
        ALL_DISTINCT pvs2 ∧
        DISJOINT (set pvs2) avoid ∧
        EVERY (λ(cn,pvs,ce). DISJOINT (set pvs2) (set pvs ∪ boundvars ce)) l2 ∧
        freshen_global
          (avoid ∪ set pvs2 ∪
           BIGUNION (set $ MAP (λ(cn,pvs,ce). set pvs ∪ boundvars ce) l2))
          (m |++ ZIP(pvs1,pvs2)) ce1 ce2)
  ⇒ freshen_global avoid m (rows_of x k1 css1) (rows_of y k2 css2)
Proof
  Induct >> rw[rows_of_def] >> gvs[] >>
  PairCases_on `h` >> Cases_on `css2` >> gvs[] >>
  PairCases_on `h` >> gvs[rows_of_def] >>
  first_assum $ qspec_then `[]` mp_tac >>
  first_x_assum $ qspec_then `(h0,h1,h2)::l1` $ mp_tac o GEN_ALL >> rw[] >>
  rw[Once freshen_global_cases] >> Cases_on `l` >> gvs[]
  >- (
    rw[Once freshen_global_cases] >> Cases_on `l` >> gvs[] >>
    simp[Once freshen_global_cases]
    ) >>
  Cases_on `t'` >> gvs[LENGTH_EQ_NUM_compute, PULL_EXISTS]
  >- (
    irule freshen_global_lets_for >>
    simp[indexedListsTheory.MAP_MAPi, combinTheory.o_DEF, GSYM MAPi_EQ_l]
    ) >>
  Cases_on `t''` >> gvs[LENGTH_EQ_NUM_compute, PULL_EXISTS] >>
  simp[boundvars_lets_for, combinTheory.o_DEF] >>
  last_x_assum irule >> simp[] >> reverse conj_tac
  >- (
    qmatch_goalsub_abbrev_tac `freshen_global A _ k1` >>
    qmatch_asmsub_abbrev_tac `freshen_global B _ k1` >>
    qsuff_tac `A = B` >> gvs[] >>
    unabbrev_all_tac >> rw[EXTENSION] >> metis_tac[]
    ) >>
  rw[] >> first_x_assum $ qspec_then `l1` mp_tac >> rw[] >>
  Cases_on `l2` >> gvs[] >> irule_at Any EQ_REFL >> rw[]
  >- simp[Once DISJOINT_SYM] >>
  qmatch_goalsub_abbrev_tac `freshen_global A` >>
  qmatch_asmsub_abbrev_tac `freshen_global B` >>
  qsuff_tac `A = B` >> gvs[] >>
  unabbrev_all_tac >> rw[EXTENSION] >> metis_tac[]
QED



(****************************** Implementation ******************************)

(********** simple lemmas **********)

Theorem freshen_return[simp] = freshen_return_def;
Theorem freshen_bind[simp]:
  freshen_bind g f = λs. let (r,s') = g s in f r s'
Proof
  simp[freshen_bind_def, combinTheory.o_DEF, UNCURRY]
QED

Triviality freshen_aux_list_LENGTH:
  ∀l m avoid l' avoid'.
    freshen_aux_list m l avoid = (l', avoid')
  ⇒ LENGTH l' = LENGTH l
Proof
  Induct >> rw[freshen_aux_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum drule >> simp[]
QED

Theorem freshen_aux_list_append:
  freshen_aux_list varmap (l1 ++ l2) = do
    l1' <- freshen_aux_list varmap l1;
    l2' <- freshen_aux_list varmap l2;
    return (l1' ++ l2')
  od
Proof
  Induct_on `l1` >> rw[FUN_EQ_THM] >>
  rpt (pairarg_tac >> gvs[freshen_aux_def])
QED

Theorem freshen_mapM_LENGTH:
  ∀l f avoid l' avoid'.
    freshen_mapM f l avoid = (l', avoid')
  ⇒ LENGTH l' = LENGTH l
Proof
  Induct >> rw[freshen_mapM_def] >>
  rpt (pairarg_tac >> gvs[]) >> res_tac
QED

Theorem freshen_mapM_append:
  freshen_mapM f (l1 ++ l2) = do
    l1' <- freshen_mapM f l1;
    l2' <- freshen_mapM f l2;
    return (l1' ++ l2')
  od
Proof
  Induct_on `l1` >> rw[FUN_EQ_THM, freshen_mapM_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem fresh_boundvars_LENGTH:
  ∀xs varmap avoid ys varmap' avoid'.
    fresh_boundvars xs varmap avoid = ((ys,varmap'), avoid')
  ⇒ LENGTH ys = LENGTH xs
Proof
  Induct >> rw[fresh_boundvars_def] >>
  rpt (pairarg_tac >> gvs[]) >> res_tac
QED

Theorem fresh_boundvars_append:
  ∀l1 l2 varmap.
    fresh_boundvars (l1 ++ l2) varmap = do
      (l1',varmap') <- fresh_boundvars l1 varmap;
      (l2',varmap'') <- fresh_boundvars l2 varmap';
      return (l1' ++ l2', varmap'')
    od
Proof
  Induct >> rw[FUN_EQ_THM, fresh_boundvars_def] >>
  rpt (pairarg_tac >> gvs[])
QED


(********** structural properties / lemmas **********)

Theorem fresh_boundvar_vars:
  fresh_boundvar x varmap avoid = ((y,varmap'), avoid') ∧
  vars_ok avoid
  ⇒ vars_ok avoid' ∧ set_of avoid' = explode y INSERT set_of avoid ∧
    explode y ∉ set_of avoid
Proof
  strip_tac >> gvs[fresh_boundvar_def] >> rpt (pairarg_tac >> gvs[]) >>
  drule_all invent_var_thm >> strip_tac >> gvs[]
QED

Theorem fresh_boundvars_vars:
  ∀xs varmap avoid ys varmap' avoid'.
    fresh_boundvars xs varmap avoid = ((ys,varmap'), avoid') ∧
    vars_ok avoid
  ⇒ vars_ok avoid' ∧
    set_of avoid' = set (MAP explode ys) ∪ set_of avoid ∧
    DISJOINT (set (MAP explode ys)) (set_of avoid) ∧
    ALL_DISTINCT ys
Proof
  Induct >> rpt gen_tac >> strip_tac >> gvs[fresh_boundvars_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  dxrule_all fresh_boundvar_vars >> strip_tac >>
  last_x_assum drule_all >> simp[] >> strip_tac >>
  gvs[MEM_MAP] >> rw[EXTENSION] >> metis_tac[]
QED

Theorem fresh_boundvar_varmap:
  fresh_boundvar x varmap avoid = ((y, varmap'), avoid') ∧ map_ok varmap
  ⇒ map_ok varmap' ∧
    (∀k. lookup varmap' k = if k = x then SOME y else lookup varmap k)
Proof
  strip_tac >> gvs[fresh_boundvar_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[mlmapTheory.insert_thm, mlmapTheory.lookup_insert] >> rw[] >> gvs[]
QED

Theorem fresh_boundvars_varmap:
  ∀xs varmap avoid ys varmap' avoid'.
    fresh_boundvars xs varmap avoid = ((ys, varmap'), avoid') ∧ map_ok varmap
  ⇒ map_ok varmap' ∧
    (∀k. lookup varmap' k =
          case ALOOKUP (REVERSE (ZIP (xs,ys))) k of
          | SOME y => SOME y
          | NONE => lookup varmap k)
Proof
  Induct >> simp[fresh_boundvars_def] >>
  rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  dxrule_all fresh_boundvar_varmap >> strip_tac >>
  last_x_assum $ dxrule_all >> strip_tac >> simp[] >> gen_tac >>
  simp[ALOOKUP_APPEND] >> TOP_CASE_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
QED

Theorem freshen_aux_mono:
  (∀varmap (ce1:'a cexp) avoid1 ce2 avoid2.
    freshen_aux varmap ce1 avoid1 = (ce2,avoid2) ∧ vars_ok avoid1
    ⇒ vars_ok avoid2 ∧ set_of avoid1 ⊆ set_of avoid2) ∧
  (∀varmap (ces1:'a cexp list) avoid1 ces2 avoid2.
    freshen_aux_list varmap ces1 avoid1 = (ces2,avoid2) ∧ vars_ok avoid1
    ⇒ vars_ok avoid2 ∧ set_of avoid1 ⊆ set_of avoid2)
Proof
  ho_match_mp_tac freshen_aux_ind >> simp[freshen_aux_def] >>
  rpt conj_tac >> rpt gen_tac
  >- simp[SUBSET_DEF] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (first_x_assum dxrule_all >> strip_tac) >> gvs[]
  >- gvs[SUBSET_DEF]
  >- (
    dxrule_all fresh_boundvars_vars >> strip_tac >>
    first_x_assum dxrule_all >> rw[] >> gvs[SUBSET_DEF]
    )
  >- (
    dxrule_all fresh_boundvar_vars >> strip_tac >>
    first_x_assum dxrule_all >> rw[] >> gvs[SUBSET_DEF]
    )
  >- (
    dxrule_all fresh_boundvars_vars >> strip_tac >>
    rename1 `freshen_mapM _ _ s1 = (fns',s2)` >>
    `vars_ok s2 ∧ set_of s1 ⊆ set_of s2` by (
      map_every (fn p => qpat_x_assum p mp_tac)
        [`vars_ok _`,`freshen_mapM _ _ _ = _`,`∀f c m. _ ⇒ _`] >>
      rpt $ pop_assum kall_tac >> map_every qid_spec_tac [`s1`, `fns'`] >>
      Induct_on `fns` >> rw[freshen_mapM_def] >> gvs[] >>
      rpt (pairarg_tac >> gvs[]) >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      rpt (first_x_assum dxrule_all >> strip_tac) >> gvs[SUBSET_DEF]) >>
    last_x_assum dxrule_all >> rw[] >> gvs[SUBSET_DEF]
    )
  >- (
    dxrule_all fresh_boundvar_vars >> strip_tac >>
    rename1 `freshen_mapM _ _ s1 = (css',s2)` >>
    `vars_ok s2 ∧ set_of s1 ⊆ set_of s2` by (
      map_every (fn p => qpat_x_assum p mp_tac)
        [`vars_ok _`,`freshen_mapM _ _ _ = _`,`∀cn pvs ce vm. _ ⇒ _`] >>
      rpt $ pop_assum kall_tac >> map_every qid_spec_tac [`s1`, `css'`] >>
      Induct_on `css` >> rw[freshen_mapM_def] >> gvs[] >>
      rpt (pairarg_tac >> gvs[]) >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      dxrule_all fresh_boundvars_vars >> strip_tac >>
      rpt (first_x_assum dxrule_all >> strip_tac) >> gvs[SUBSET_DEF]) >>
    `vars_ok avoid2 ∧ set_of s2 ⊆ set_of avoid2` by (
      Cases_on `usopt` >> gvs[] >> PairCases_on `x` >> gvs[] >>
      rpt (pairarg_tac >> gvs[]) >> first_x_assum drule_all >> simp[]) >>
    gvs[SUBSET_DEF]
    )
  >- gvs[SUBSET_DEF]
QED

Definition avoid_ok_def:
  avoid_ok avoid (ce : 'a cexp) ⇔
    vars_ok avoid ∧
    allvars (exp_of ce) ⊆ set_of avoid
End

Theorem avoid_ok_simps[simp]:
  (avoid_ok avoid (Prim c op ces) ⇔ EVERY (avoid_ok avoid) ces ∧ vars_ok avoid) ∧
  (avoid_ok avoid (Let c x ce1 ce2) ⇔
    avoid_ok avoid ce1 ∧ avoid_ok avoid ce2 ∧ explode x ∈ set_of avoid) ∧
  (avoid_ok avoid (Lam c xs ce) ⇔
    avoid_ok avoid ce ∧ set (MAP explode xs) ⊆ set_of avoid) ∧
  (avoid_ok avoid (App c ce ces) ⇔ avoid_ok avoid ce ∧ EVERY (avoid_ok avoid) ces) ∧
  (avoid_ok avoid (Letrec c fns ce) ⇔
    avoid_ok avoid ce ∧
    EVERY ( λ(f,ce). avoid_ok avoid ce) fns ∧
    set (MAP (explode o FST) fns) ⊆ set_of avoid) ∧
  (avoid_ok avoid (pure_cexp$Case c ce x css usopt) ⇔
    avoid_ok avoid ce ∧
    explode x ∈ set_of avoid ∧
    EVERY (λ(cn,pvs,ce). set (MAP explode pvs) ⊆ set_of avoid ∧ avoid_ok avoid ce) css ∧
    (∀cnars ce. usopt = SOME (cnars,ce) ⇒ avoid_ok avoid ce)) ∧
  (avoid_ok avoid (Annot c annot ce) ⇔ avoid_ok avoid ce)
Proof
  rw[avoid_ok_def, exp_of_def, EVERY_MEM, allvars_Apps, allvars_Lams, allvars_rows_of]
  >- (simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> metis_tac[])
  >- (simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> metis_tac[])
  >- (simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> metis_tac[])
  >- (simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> metis_tac[])
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY, FORALL_PROD] >>
    simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
    ) >>
  (
    pop_assum kall_tac >>
    simp[COND_RAND, COND_RATOR, SF CONJ_ss] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY, FORALL_PROD] >>
    simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    eq_tac >> rw[] >> gvs[]
    >- metis_tac[]
    >- metis_tac[]
    >- gvs[allvars_IfDisj, COND_RAND, COND_RATOR]
    >- (CASE_TAC >> gvs[] >> CASE_TAC >> gvs[allvars_IfDisj] >> rw[])
    >- metis_tac[]
    >- metis_tac[]
    >- (CASE_TAC >> gvs[])
  )
QED

(* Helper for mlmap theorems *)
fun cjs th =
  let fun generate_list f seed =
          if not (can f seed) then []
          else let val (e, seed') = f seed
               in e :: (generate_list f seed') end
  in generate_list (fn i => (cj i th, i + 1)) 1 end;

Theorem freshen_aux_avoid_ok:
  (∀varmap (ce1:'a cexp) avoid1 ce2 avoid2.
    freshen_aux varmap ce1 avoid1 = (ce2,avoid2) ∧
    avoid_ok avoid1 ce1
   ⇒ avoid_ok avoid2 ce2) ∧
  (∀varmap (ces1:'a cexp list) avoid1 ces2 avoid2.
    freshen_aux_list varmap ces1 avoid1 = (ces2,avoid2) ∧
    EVERY (avoid_ok avoid1) ces1
   ⇒ EVERY (avoid_ok avoid2) ces2)
Proof
  ho_match_mp_tac freshen_aux_ind >> rw[freshen_aux_def] >> gvs[]
  >- ( (* Var *)
    gvs[avoid_ok_def, exp_of_def] >> CASE_TAC >> gvs[] >> res_tac
    )
  >- ( (* Prim *)
    rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    Cases_on `ces1` >> gvs[freshen_aux_def] >> rpt (pairarg_tac >> gvs[]) >>
    gvs[avoid_ok_def]
    )
  >- ( (* App *)
    rpt (pairarg_tac >> gvs[]) >>
    last_x_assum drule >> simp[] >> strip_tac >>
    last_x_assum drule >> impl_tac
    >- (
      gvs[avoid_ok_def, EVERY_MEM] >>
      drule_all $ cj 1 freshen_aux_mono >> metis_tac[SUBSET_DEF]
      ) >>
    gvs[avoid_ok_def] >>
    drule_all $ cj 2 freshen_aux_mono >> strip_tac >> metis_tac[SUBSET_DEF]
    )
  >- ( (* Lam *)
    rpt (pairarg_tac >> gvs[]) >> gvs[avoid_ok_def] >>
    dxrule_all fresh_boundvars_vars >> strip_tac >>
    last_x_assum drule >> simp[] >> impl_tac >> simp[]
    >- (gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> metis_tac[])
    >- (drule_all $ cj 1 freshen_aux_mono >> strip_tac >> gvs[SUBSET_DEF])
    )
  >- ( (* Let *)
    rpt (pairarg_tac >> gvs[]) >> gvs[avoid_ok_def, exp_of_def] >>
    first_x_assum drule_all >> strip_tac >>
    drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    drule_all fresh_boundvar_vars >> strip_tac >>
    drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    last_x_assum drule >> simp[] >> impl_tac >> simp[]
    >- (gvs[SUBSET_DEF] >> metis_tac[]) >>
    strip_tac >> gvs[SUBSET_DEF]
    )
  >- ( (* Letrec *)
    rpt (pairarg_tac >> gvs[]) >> gvs[avoid_ok_def] >>
    DEP_REWRITE_TAC $ cjs MAP_ZIP >>
    imp_res_tac freshen_mapM_LENGTH >> simp[] >>
    imp_res_tac fresh_boundvars_LENGTH >> simp[] >>
    rename1 `freshen_aux _ ce1 avoid3 = (ce2,avoid4)` >>
    rename1 `freshen_mapM _ fns avoid2 = (fns',_)` >>
    rename1 `fresh_boundvars _ _ _ = ((freshes,_),_)` >>
    drule_all fresh_boundvars_vars >> strip_tac >>
    DEP_REWRITE_TAC $ cjs $ SRULE [LAMBDA_PROD] every_zip_snd >>
    qsuff_tac
      `vars_ok avoid3 ∧ set_of avoid2 ⊆ set_of avoid3 ∧
       EVERY (λce. allvars (exp_of ce) ⊆ set_of avoid3) fns'`
     >- (
      strip_tac >> last_x_assum drule >> simp[] >> impl_tac
      >- (gvs[SUBSET_DEF, EXTENSION, MEM_MAP] >> metis_tac[]) >>
      strip_tac >> simp[] >>
      drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
      gvs[SUBSET_DEF, EXTENSION, EVERY_MEM] >> metis_tac[]
      ) >>
    `EVERY (λ(f,ce). allvars (exp_of ce) ⊆ set_of avoid2) fns` by (
      gvs[EVERY_MEM, FORALL_PROD, SUBSET_DEF] >> metis_tac[]) >>
    qpat_x_assum `set_of avoid2 = _` kall_tac >>
    map_every (fn p => qpat_x_assum p mp_tac)
      [`freshen_mapM _ _ _ = _`,`vars_ok avoid2`,`EVERY _ fns`,
       `∀f ce vm. _`] >>
    rpt $ pop_assum kall_tac >> strip_tac >>
    map_every qid_spec_tac [`avoid2`,`fns'`] >>
    Induct_on `fns` >- rw[freshen_mapM_def] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >>
    PairCases_on `h` >> simp[freshen_mapM_def] >> simp[AND_IMP_INTRO] >> strip_tac >>
    qpat_x_assum `∀f ce vm. _` mp_tac >>
    simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
    last_x_assum dxrule >> strip_tac >>
    pairarg_tac >> last_x_assum drule_all >> strip_tac >>
    rpt (pairarg_tac >> gvs[]) >>
    first_x_assum $ drule_at $ Pat `freshen_mapM` >> impl_tac
    >- (
      drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
      gvs[EVERY_MEM, SUBSET_DEF, FORALL_PROD] >> metis_tac[]
      ) >>
    strip_tac >> simp[] >>
    drule_all $ cj 1 freshen_aux_mono >> strip_tac >> metis_tac[SUBSET_DEF]
    )
  >- ( (* Case *)
    rpt (pairarg_tac >> gvs[]) >>
    rename1 `avoid_ok avoid5 _ ∧ _` >>
    rename1 `freshen_mapM _ css1 avoid3 = (css2,avoid4)` >>
    rename1 `fresh_boundvar x _ avoid2 = ((y,varmap'), _)` >>
    rename1 `freshen_aux _ _ _ = (ce2,avoid2)` >>
    first_x_assum $ drule_all >> strip_tac >>
    drule fresh_boundvar_vars >> impl_tac >- fs[avoid_ok_def] >> strip_tac >>
    drule $ cj 1 freshen_aux_mono >> impl_tac >- gvs[avoid_ok_def] >> strip_tac >>
    `EVERY (λ(cn,pvs,ce).
      set (MAP explode pvs) ⊆ set_of avoid3 ∧ avoid_ok avoid3 ce) css1` by (
        gvs[EVERY_MEM, EVERY_MAP, FORALL_PROD] >>
        gvs[SUBSET_DEF, EXTENSION, avoid_ok_def] >> metis_tac[]) >>
    qsuff_tac
      `set_of avoid3 ⊆ set_of avoid4 ∧ vars_ok avoid4 ∧
       EVERY (λ(cn,pvs,ce).
        set (MAP explode pvs) ⊆ set_of avoid4 ∧ avoid_ok avoid4 ce) css2`
    >- (
      strip_tac >> namedCases_on `usopt` ["","us"] >> gvs[]
      >- (gvs[SUBSET_DEF, avoid_ok_def]) >>
      PairCases_on `us` >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
      last_x_assum drule >> impl_tac >- gvs[avoid_ok_def, SUBSET_DEF] >>
      strip_tac >> simp[] >>
      drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
      gvs[EVERY_MEM, FORALL_PROD, SUBSET_DEF, avoid_ok_def] >> metis_tac[]
      ) >>
    pop_assum mp_tac >>
    map_every (fn p => qpat_x_assum p mp_tac)
      [`freshen_mapM _ _ _ = _`,`vars_ok avoid3`,`∀cn pvs ce vm. _`] >>
    rpt $ pop_assum kall_tac >> strip_tac >>
    map_every qid_spec_tac [`avoid3`,`css2`] >>
    Induct_on `css1` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
    simp[DISJ_IMP_THM, FORALL_AND_THM] >>
    gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    last_x_assum dxrule >> strip_tac >>
    rpt (pairarg_tac >> gvs[]) >>
    rename1 `fresh_boundvars _ _ avoid1 = (_,avoid2)` >>
    rename1 `freshen_aux _ _ _ = (_,avoid3)` >>
    drule_all fresh_boundvars_vars >> strip_tac >>
    last_x_assum drule >> impl_tac >- (gvs[avoid_ok_def, SUBSET_DEF]) >> strip_tac >>
    drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    last_x_assum $ drule_at $ Pat `freshen_mapM` >> reverse impl_tac >> simp[]
    >- (strip_tac >> gvs[SUBSET_DEF, avoid_ok_def]) >>
    gvs[EVERY_MEM, FORALL_PROD, avoid_ok_def, SUBSET_DEF, EXTENSION] >> metis_tac[]
    )
  >- (
    rpt (pairarg_tac >> gvs[]) >> res_tac
    )
  >- ( (* list case *)
    rpt (pairarg_tac >> gvs[]) >>
    last_x_assum drule_all >> strip_tac >> drule $ cj 1 freshen_aux_mono >>
    impl_tac >- gvs[avoid_ok_def] >> strip_tac >> gvs[] >>
    last_x_assum drule >> impl_tac
    >- (gvs[EVERY_MEM, avoid_ok_def] >> metis_tac[SUBSET_DEF]) >>
    strip_tac >> simp[] >>
    drule $ cj 2 freshen_aux_mono >> gvs[avoid_ok_def, SUBSET_DEF]
    )
QED

Theorem freshen_aux_cns_arities:
  (∀m (ce1:'a cexp) avoid1 ce2 avoid2.
    freshen_aux m ce1 avoid1 = (ce2, avoid2)
  ⇒ cns_arities ce2 = cns_arities ce1) ∧
  (∀m (ces1:'a cexp list) avoid1 ces2 avoid2.
    freshen_aux_list m ces1 avoid1 = (ces2, avoid2)
  ⇒ LIST_REL (λce1 ce2. cns_arities ce2 = cns_arities ce1) ces1 ces2)
Proof
  ho_match_mp_tac freshen_aux_ind >>
  rw[freshen_return_def, freshen_bind_def, freshen_aux_def, cns_arities_def] >>
  gvs[combinTheory.o_DEF] >> rpt (pairarg_tac >> gvs[]) >> gvs[cns_arities_def] >>
  rpt $ first_x_assum drule >> rw[]
  >- (
    gvs[LIST_REL_EL_EQN] >>
    ntac 3 AP_TERM_TAC >> rw[MAP_EQ_EVERY2, LIST_REL_EL_EQN]
    )
  >- (
    ntac 3 AP_TERM_TAC >> gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN]
    )
  >- (
    imp_res_tac fresh_boundvars_LENGTH >> gvs[] >>
    imp_res_tac freshen_mapM_LENGTH >> gvs[] >>
    AP_THM_TAC >> ntac 3 AP_TERM_TAC >>
    simp[SRULE [combinTheory.o_DEF, LAMBDA_PROD] MAP_ZIP] >>
    qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
    last_x_assum mp_tac >> rpt $ pop_assum kall_tac >> strip_tac >>
    rename1 `freshen_mapM _ _ avoid = (fns',avoid2)` >>
    map_every qid_spec_tac [`fns'`,`avoid`]  >>
    Induct_on `fns` >> rw[freshen_mapM_def] >>
    rpt (pairarg_tac >> gvs[]) >> gvs[SF DNF_ss] >>
    first_x_assum drule >> rw[] >>
    last_x_assum drule_all >> rw[]
    )
  >- (
    rename1 `freshen_mapM _ css avoid = (css',avoid')` >>
    `LIST_REL (λ(cn,vs,e) (cn',vs',e').
        cn = cn' ∧ LENGTH vs = LENGTH vs' ∧ cns_arities e = cns_arities e') css css'`
      by (
        qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
        last_x_assum mp_tac >> rpt $ pop_assum kall_tac >> strip_tac >>
        map_every qid_spec_tac [`css'`,`avoid`] >>
        Induct_on `css` >> rw[freshen_mapM_def] >>
        rpt (pairarg_tac >> gvs[]) >> gvs[SF DNF_ss] >>
        imp_res_tac fresh_boundvars_LENGTH >> simp[] >>
        first_x_assum drule >> rw[] >> last_x_assum drule_all >> simp[]) >>
    `MAP (λ(cn,vs,e). (cn,LENGTH vs)) css' =
     MAP (λ(cn,vs,e). (cn,LENGTH vs)) css` by (
      rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN] >> rw[] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
    `MAP (λ(cn,vs,e). cns_arities e) css' =
     MAP (λ(cn,vs,e). cns_arities e) css` by (
      rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN] >> rw[] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
     simp[] >> AP_THM_TAC >> AP_TERM_TAC >>
     namedCases_on `usopt` ["","us"] >> gvs[] >>
     PairCases_on `us` >> gvs[] >> pairarg_tac >> gvs[] >>
     last_x_assum drule >> simp[]
    )
QED

Theorem freshen_aux_cexp_wf:
  (∀m (ce1:'a cexp) avoid1 ce2 avoid2.
    freshen_aux m ce1 avoid1 = (ce2, avoid2) ∧ vars_ok avoid1 ∧ cexp_wf ce1
    ⇒ cexp_wf ce2) ∧
  (∀m (ces1:'a cexp list) avoid1 ces2 avoid2.
    freshen_aux_list m ces1 avoid1 = (ces2, avoid2) ∧ vars_ok avoid1 ∧
    EVERY cexp_wf ces1
  ⇒ EVERY cexp_wf ces2)
Proof
  ho_match_mp_tac freshen_aux_ind >>
  rw[freshen_return_def, freshen_bind_def, freshen_aux_def, cexp_wf_def] >>
  gvs[combinTheory.o_DEF] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[cexp_wf_def, SF ETA_ss] >>
  rpt $ (first_x_assum drule_all >> strip_tac) >> gvs[]
  >- (imp_res_tac freshen_aux_list_LENGTH >> gvs[])
  >- (
    last_x_assum $ irule_at Any >> goal_assum drule >>
    imp_res_tac freshen_aux_list_LENGTH >> Cases_on `ces'` >> gvs[] >>
    dxrule_all $ cj 1 freshen_aux_mono >> rw[]
    )
  >- (
    last_x_assum $ irule_at Any >> goal_assum drule >>
    imp_res_tac fresh_boundvars_LENGTH >> Cases_on `vs'` >> gvs[] >>
    drule_all fresh_boundvars_vars >> strip_tac
    )
  >- (
    last_x_assum irule >> goal_assum $ drule_at Any >>
    drule_all $ cj 1 freshen_aux_mono >> rw[] >>
    drule_all fresh_boundvar_vars >> simp[]
    )
  >- (
    rename1 `freshen_aux _ ce1 avoid3 = (ce2,avoid4)` >>
    rename1 `freshen_mapM _ _ avoid2 = (fns',_)` >>
    rename1 `fresh_boundvars _ _ _ = ((freshes,_),_)` >>
    imp_res_tac fresh_boundvars_LENGTH >>
    imp_res_tac freshen_mapM_LENGTH >>
    last_x_assum $ irule_at Any >> goal_assum drule >>
    dxrule_all fresh_boundvars_vars >> strip_tac >> simp[MAP_ZIP] >>
    once_rewrite_tac[CONJ_ASSOC] >> reverse conj_tac
    >- (
      Cases_on `fns` >> gvs[] >>
      Cases_on `freshes` >> gvs[] >> Cases_on `fns'` >> gvs[]
      ) >>
    qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
    qpat_x_assum `EVERY cexp_wf _` mp_tac >>
    qpat_x_assum `vars_ok avoid2` mp_tac >>
    last_x_assum mp_tac >> rpt $ pop_assum kall_tac >> strip_tac >>
    map_every qid_spec_tac [`avoid2`,`fns'`] >>
    Induct_on `fns` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
    gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    last_x_assum drule >> strip_tac >>
    rpt (pairarg_tac >> gvs[]) >> PairCases_on `h` >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> simp[] >>
    first_x_assum irule >> goal_assum $ drule_at $ Pat `freshen_mapM` >>
    drule_all $ cj 1 freshen_aux_mono >> rw[]
    )
  >- (
    rename1 `freshen_mapM _ css avoid = (css',avoid')` >>
    `LIST_REL (λ(cn,vs,e) (cn',vs',e').
        cn = cn' ∧ LENGTH vs = LENGTH vs' ∧ cexp_wf e' ∧
        ALL_DISTINCT vs' ∧ ¬MEM v' vs') css css' ∧ vars_ok avoid'`
      by (
        qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
        qpat_x_assum `EVERY cexp_wf _` mp_tac >>
        `vars_ok avoid ∧ explode v' ∈ set_of avoid` by (
          drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
          drule_all $ fresh_boundvar_vars >> rw[]) >>
        ntac 2 $ pop_assum mp_tac >>
        last_x_assum mp_tac >> rpt $ pop_assum kall_tac >> strip_tac >>
        map_every qid_spec_tac [`css'`,`avoid`] >>
        Induct_on `css` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
        gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
        gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
        last_x_assum drule >> strip_tac >>
        rpt (pairarg_tac >> gvs[]) >>
        last_x_assum $ dxrule_at $ Pat `freshen_mapM` >> strip_tac >>
        gvs[UNCURRY] >> simp[FST_THM] >> pairarg_tac >> gvs[] >>
        drule_all fresh_boundvars_vars >> strip_tac >>
        last_x_assum drule_all >> strip_tac >> simp[] >>
        imp_res_tac fresh_boundvars_LENGTH >> simp[] >>
        simp[GSYM CONJ_ASSOC] >> conj_tac
        >- (gvs[DISJOINT_ALT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
        first_x_assum irule >> drule_all $ cj 1 freshen_aux_mono >> gvs[SUBSET_DEF]) >>
    `MAP FST css' = MAP FST css` by (
      rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN] >> rw[] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
    `css' ≠ []` by (Cases_on `css` >> gvs[]) >> simp[] >> conj_tac
    >- (
      gvs[EVERY_MAP, EVERY_EL, LIST_REL_EL_EQN] >>
      rw[] >> first_x_assum drule >> rpt (pairarg_tac >> gvs[])
      ) >>
    qsuff_tac `EVERY ALL_DISTINCT (MAP (FST o SND) css') ∧
              ¬MEM v' (FLAT (MAP (FST o SND) css'))`
    >- (
      simp[] >> strip_tac >> namedCases_on `usopt` ["","us"] >> gvs[] >>
      PairCases_on `us` >> gvs[UNCURRY] >> simp[FST_THM] >> pairarg_tac >> gvs[] >>
      first_x_assum drule >> simp[]
      ) >>
    simp[EVERY_MAP, EVERY_EL, MEM_FLAT, DISJ_EQ_IMP] >>
    simp[Once MEM_EL, PULL_EXISTS, EL_MAP] >>
    rw[] >> gvs[LIST_REL_EL_EQN] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[])
    )
  >- gvs[combinTheory.o_DEF]
  >- (
    first_x_assum irule >> goal_assum $ drule_at Any >>
    drule_all $ cj 1 freshen_aux_mono >> rw[]
    )
QED

Theorem freshen_aux_NestedCase_free:
  (∀m (ce1:'a cexp) avoid1 ce2 avoid2.
    freshen_aux m ce1 avoid1 = (ce2, avoid2) ∧ NestedCase_free ce1
  ⇒ NestedCase_free ce2) ∧
  (∀m (ces1:'a cexp list) avoid1 ces2 avoid2.
    freshen_aux_list m ces1 avoid1 = (ces2, avoid2) ∧
    EVERY NestedCase_free ces1
  ⇒ EVERY NestedCase_free ces2)
Proof
  ho_match_mp_tac freshen_aux_ind >>
  rw[freshen_return_def, freshen_bind_def, freshen_aux_def, NestedCase_free_def] >>
  gvs[combinTheory.o_DEF] >> rpt (pairarg_tac >> gvs[]) >> gvs[NestedCase_free_def] >>
  rpt $ first_x_assum drule >> rw[] >> gvs[SF ETA_ss]
  >- (
    imp_res_tac fresh_boundvars_LENGTH >>
    imp_res_tac freshen_mapM_LENGTH >> simp[MAP_ZIP] >>
    qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
    qpat_x_assum `EVERY _ _` mp_tac >>
    last_x_assum mp_tac >> rpt $ pop_assum kall_tac >> strip_tac >>
    map_every qid_spec_tac [`x`,`fces'`] >>
    Induct_on `fns` >> rw[freshen_mapM_def] >>
    rpt (pairarg_tac >> gvs[]) >> gvs[SF DNF_ss] >> PairCases_on `h` >> gvs[] >>
    first_x_assum drule >> rw[] >> last_x_assum drule_all >> simp[]
    )
  >- (
    qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
    qpat_x_assum `EVERY _ _` mp_tac >>
    last_x_assum mp_tac >> rpt $ pop_assum kall_tac >> strip_tac >>
    map_every qid_spec_tac [`x'`,`css'`] >>
    Induct_on `css` >> rw[freshen_mapM_def] >>
    rpt (pairarg_tac >> gvs[]) >> gvs[SF DNF_ss] >>
    last_x_assum drule_all >> rw[] >>
    gvs[UNCURRY] >> simp[FST_THM] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >> simp[]
    )
  >- (
    namedCases_on `usopt` ["","us"] >> gvs[] >>
    PairCases_on `us` >> gvs[] >>
    gvs[UNCURRY] >> simp[FST_THM] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >> rw[]
    )
QED

Theorem freshen_aux_letrecs_distinct:
  (∀m (ce1:'a cexp) avoid1 ce2 avoid2.
    freshen_aux m ce1 avoid1 = (ce2, avoid2) ∧ vars_ok avoid1 ∧
    letrecs_distinct (exp_of ce1)
    ⇒ letrecs_distinct (exp_of ce2)) ∧
  (∀m (ces1:'a cexp list) avoid1 ces2 avoid2.
    freshen_aux_list m ces1 avoid1 = (ces2, avoid2) ∧ vars_ok avoid1 ∧
    EVERY (letrecs_distinct o exp_of) ces1
  ⇒ EVERY (letrecs_distinct o exp_of) ces2)
Proof
  ho_match_mp_tac freshen_aux_ind >> rw[freshen_aux_def] >>
  gvs[combinTheory.o_DEF] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[letrecs_distinct_def, exp_of_def, SF ETA_ss, EVERY_MAP] >>
  rpt $ (first_x_assum drule_all >> strip_tac >> gvs[])
  >- (
    gvs[letrecs_distinct_Apps, EVERY_MAP] >>
    last_x_assum drule_all >> strip_tac >> simp[] >>
    last_x_assum drule >> disch_then irule >> imp_res_tac freshen_aux_mono
    )
  >- (
    gvs[letrecs_distinct_Lams] >>
    last_x_assum drule >> disch_then irule >> imp_res_tac fresh_boundvars_vars
    )
  >- (
    last_x_assum drule >> disch_then irule >>
    imp_res_tac fresh_boundvar_vars >> imp_res_tac freshen_aux_mono >> gvs[]
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    imp_res_tac fresh_boundvars_LENGTH >> imp_res_tac freshen_mapM_LENGTH >>
    gvs $ map (SRULE [combinTheory.o_DEF]) [MAP_ZIP, every_zip_snd] >>
    dxrule_all fresh_boundvars_vars >> strip_tac >> gvs[] >>
    last_x_assum drule >> disch_then $ irule_at Any >>
    qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
    qpat_x_assum `vars_ok _` mp_tac >>
    qpat_x_assum `EVERY _ fns` mp_tac >>
    last_x_assum mp_tac >> rpt $ pop_assum kall_tac >> strip_tac >>
    map_every qid_spec_tac [`s'`,`fces'`] >>
    Induct_on `fns` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    rpt (pairarg_tac >> gvs[]) >> PairCases_on `h` >> gvs[] >>
    drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    first_x_assum dxrule_all >> strip_tac >>
    last_x_assum dxrule_all >> simp[]
    )
  >- (
    gvs[COND_RAND, letrecs_distinct_def, letrecs_distinct_rows_of] >>
    gvs[EVERY_MAP, UNCURRY] >> last_x_assum drule_all >> strip_tac >> simp[] >>
    rename1 `freshen_mapM _ css avoid = (css',avoid')` >>
    qsuff_tac
      `EVERY (λx. letrecs_distinct (exp_of (SND (SND x)))) css' ∧ vars_ok avoid'`
    >- (
      strip_tac >>
      namedCases_on `usopt` ["","us"] >> gvs[letrecs_distinct_def] >>
      PairCases_on `us` >> gvs[] >> simp[FST_THM] >> pairarg_tac >> gvs[] >>
      first_x_assum drule >> simp[]
      ) >>
    dxrule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    dxrule_all fresh_boundvar_vars >> strip_tac >>
    qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
    qpat_x_assum `vars_ok _` mp_tac >>
    qpat_x_assum `EVERY _ css` mp_tac >>
    last_x_assum mp_tac >> rpt $ pop_assum kall_tac >> strip_tac >>
    map_every qid_spec_tac [`avoid`,`css'`] >>
    Induct_on `css` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    rpt (pairarg_tac >> gvs[]) >> simp[FST_THM] >> rpt (pairarg_tac >> gvs[]) >>
    rename1 `fresh_boundvars _ _ _ = (pvs',_)` >> PairCases_on `pvs'` >>
    dxrule_all fresh_boundvars_vars >> strip_tac >>
    drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    first_x_assum dxrule_all >> strip_tac >> gvs[] >>
    last_x_assum drule_all >> rw[]
    )
  >- (
    first_x_assum irule >> goal_assum $ drule_at Any >>
    drule_all $ cj 1 freshen_aux_mono >> rw[]
    )
QED


(********** relating freshen_aux and freshen_global **********)

Definition varmap_rel_def:
  varmap_rel varmap fmap ⇔
    map_ok varmap ∧
    (∀k v. lookup varmap k = SOME v ⇔
      FLOOKUP fmap (explode k) = SOME (explode v))
End

Triviality fresh_boundvar_rel:
  varmap_rel varmap m ∧
  vars_ok avoid ∧
  fresh_boundvar x varmap avoid = ((y,varmap'), avoid')
  ⇒ varmap_rel varmap' (m |+ (explode x,explode y)) ∧
    explode y ∉ set_of avoid ∧
    set_of avoid' = explode y INSERT set_of avoid ∧
    vars_ok avoid'
Proof
  strip_tac >> gvs[varmap_rel_def] >>
  drule_all fresh_boundvar_vars >> strip_tac >>
  drule_all fresh_boundvar_varmap >> strip_tac >> simp[FLOOKUP_SIMP] >> rw[]
QED

Triviality ALOOKUP_MAP_explode_FST:
  ALOOKUP (MAP (λ(a,b). (explode a,b)) l) (explode k) = ALOOKUP l k
Proof
  Induct_on `l` >> rw[] >>
  pairarg_tac >> gvs[]
QED

Triviality fresh_boundvars_rel:
  ∀xs varmap avoid ys varmap' avoid' m.
  varmap_rel varmap m ∧
  vars_ok avoid ∧
  fresh_boundvars xs varmap avoid = ((ys,varmap'), avoid')
  ⇒ LENGTH xs = LENGTH ys ∧
    varmap_rel varmap' (m |++ ZIP (MAP explode xs, MAP explode ys)) ∧
    set_of avoid' = set (MAP explode ys) ∪ set_of avoid ∧
    ALL_DISTINCT ys ∧
    DISJOINT (set (MAP explode ys)) (set_of avoid) ∧
    vars_ok avoid'
Proof
  rpt gen_tac >> strip_tac >> gvs[varmap_rel_def] >>
  drule_all fresh_boundvars_vars >> strip_tac >>
  drule_all fresh_boundvars_varmap >> strip_tac >>
  imp_res_tac fresh_boundvars_LENGTH >>
  simp[FLOOKUP_FUPDATE_LIST, GSYM MAP_ZIP_ALT, GSYM MAP_REVERSE] >>
  simp[ALOOKUP_MAP_explode_FST, ALOOKUP_MAP] >>
  rw[] >> CASE_TAC >> gvs[]
QED

Theorem freshen_aux_freshen_global:
  (∀varmap (ce1:'a cexp) avoid1 ce2 avoid2 m.
    freshen_aux varmap ce1 avoid1 = (ce2,avoid2) ∧
    varmap_rel varmap m ∧ avoid_ok avoid1 ce1 ∧
    NestedCase_free ce1 ∧ letrecs_distinct (exp_of ce1) ∧ cexp_wf ce1
   ⇒ freshen_global (set_of avoid1) m (exp_of ce1) (exp_of ce2)) ∧

  (∀varmap (ces1:'a cexp list) avoid1 ces2 avoid4 m.
    freshen_aux_list varmap ces1 avoid1 = (ces2,avoid4) ⇒
    ∀l1 ce1 r1 l2 avoid2 ce2 avoid3.
      ces1 = l1 ++ [ce1] ++ r1 ∧
      freshen_aux_list varmap l1 avoid1 = (l2,avoid2) ∧
      freshen_aux varmap ce1 avoid2 = (ce2,avoid3) ∧
      varmap_rel varmap m ∧ EVERY (avoid_ok avoid1) (l1 ++ [ce1]) ∧
      EVERY NestedCase_free (l1 ++ [ce1]) ∧
      EVERY letrecs_distinct (MAP exp_of l1 ++ [exp_of ce1]) ∧
      EVERY cexp_wf (l1 ++ [ce1])
    ⇒ ∃r2. ces2 = l2 ++ [ce2] ++ r2 ∧
        freshen_global (set_of avoid2) m (exp_of ce1) (exp_of ce2))
Proof
  ho_match_mp_tac freshen_aux_ind >>
  rw[freshen_aux_def] >> gvs[exp_of_def]
  >- ( (* Var *)
    simp[Once freshen_global_cases] >>
    CASE_TAC >> gvs[varmap_rel_def] >>
    Cases_on `FLOOKUP m (explode v)` >> gvs[] >>
    `∃x'. x = explode x'` by (qexists `implode x` >> simp[]) >> gvs[] >>
    first_x_assum $ drule o iffRL >> simp[]
    )
  >- ( (* Prim *)
    simp[Once freshen_global_cases] >>
    pairarg_tac >> gvs[exp_of_def, cexp_wf_def, letrecs_distinct_def, SF ETA_ss] >>
    imp_res_tac freshen_aux_list_LENGTH >> rw[] >>
    gvs[MAP_EQ_APPEND, PULL_EXISTS] >> rename1 `l ++ [ce] ++ r` >>
    last_x_assum drule >>
    disch_then $ qspecl_then [`m`,`l`] mp_tac >> simp[] >>
    gvs[freshen_aux_list_append, freshen_aux_def] >>
    rpt (pairarg_tac >> gvs[]) >> strip_tac >>
    irule_at Any EQ_REFL >> imp_res_tac freshen_aux_list_LENGTH >> simp[] >>
    irule freshen_global_mono >> goal_assum $ drule_at Any >>
    rev_drule_all $ cj 2 freshen_aux_avoid_ok >> strip_tac >> rw[]
    >- (rev_drule $ cj 2 freshen_aux_mono >> gvs[]) >>
    simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
    gvs[EVERY_MEM, avoid_ok_def, allvars_thm]
    )
  >- ( (* App *)
    rpt (pairarg_tac >> gvs[]) >>
    gvs[exp_of_def, cexp_wf_def, letrecs_distinct_Apps, SF ETA_ss] >>
    rename1 `freshen_aux_list _ ces1 _ = (ces2, avoid3)` >>
    rename1 `freshen_aux _ ce1 _ = (ce2, avoid2)` >>
    last_x_assum drule_all >> strip_tac >>
    last_x_assum drule >> strip_tac >>
    `EVERY (avoid_ok avoid2) ces1` by (
      drule $ cj 1 freshen_aux_mono >>
      gvs[avoid_ok_def, EVERY_MEM, SUBSET_DEF] >> metis_tac[]) >>
    `set_of avoid1 ⊆ set_of avoid2 ∧ avoid_ok avoid2 ce2` by (
      drule $ cj 1 freshen_aux_mono >> gvs[avoid_ok_def] >>
      drule $ cj 1 freshen_aux_avoid_ok >> gvs[avoid_ok_def]) >>
    map_every (fn p => qpat_x_assum p kall_tac)
      [`freshen_aux _ _ _ = _`, `EVERY (avoid_ok avoid1) _`, `_ ≠ []`,
       `NestedCase_free ce1`,`letrecs_distinct (exp_of ce1)`,`cexp_wf ce1`] >>
    rpt $ pop_assum mp_tac >>
    map_every qid_spec_tac [`ces2`,`avoid3`] >>
    Induct_on `ces1` using SNOC_INDUCT >> rw[] >> gvs[SNOC_APPEND]
    >- gvs[freshen_aux_def, Apps_def] >>
    gvs[Apps_append, freshen_aux_list_append, freshen_aux_def] >>
    rpt (pairarg_tac >> gvs[]) >> gvs[Apps_append, Apps_def] >>
    simp[Once freshen_global_cases] >> disj1_tac >> reverse $ rw[]
    >- (
      first_x_assum $ qspecl_then [`m`,`ces1`] mp_tac >> simp[] >>
      strip_tac >> irule freshen_global_mono >> goal_assum $ drule_at Any >>
      rev_drule $ cj 2 freshen_aux_mono >> strip_tac >>
      rev_drule_all $ cj 2 freshen_aux_avoid_ok >> strip_tac >>
      gvs[avoid_ok_def, boundvars_Apps, allvars_thm,
          SUBSET_DEF, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
      rw[] >> gvs[] >> metis_tac[]
      )
    >- (
      last_x_assum irule >> rw[] >> gvs[] >>
      last_x_assum $ qspecl_then [`m'`,`l1`] mp_tac >> rw[] >>
      gvs[freshen_aux_list_append, freshen_aux_def] >> rpt (pairarg_tac >> gvs[])
      )
    )
  >- ( (* Lams *)
    rpt (pairarg_tac >> gvs[]) >>
    gvs[exp_of_def, letrecs_distinct_Lams, cexp_wf_def] >>
    last_x_assum drule >> strip_tac >>
    irule freshen_global_Lams >>
    drule fresh_boundvars_rel >> rpt $ disch_then $ drule_at Any >>
    gvs[avoid_ok_def] >> strip_tac >>
    irule_at Any freshen_global_mono >> first_x_assum $ irule_at Any >> simp[] >>
    gvs[SUBSET_DEF]
    )
  >- ( (* Let *)
    rpt (pairarg_tac >> gvs[]) >> gvs[exp_of_def, letrecs_distinct_def, cexp_wf_def] >>
    rename1 `freshen_aux varmap1 ce2 avoid3 = (ce2',avoid4)` >>
    rename1 `freshen_aux varmap ce1 _ = (ce1',avoid2)` >>
    first_x_assum drule_all >> strip_tac >>
    simp[Once freshen_global_cases] >> disj2_tac >>
    drule_all $ cj 1 freshen_aux_avoid_ok >> strip_tac >>
    rev_drule $ cj 1 freshen_aux_mono >> strip_tac >>
    drule fresh_boundvar_rel >> rpt $ disch_then $ drule_at Any >>
    impl_tac >- gvs[avoid_ok_def] >> strip_tac >> rw[]
    >- (gvs[avoid_ok_def, SUBSET_DEF] >> CCONTR_TAC >> gvs[allvars_thm])
    >- (gvs[avoid_ok_def, SUBSET_DEF] >> CCONTR_TAC >> gvs[allvars_thm]) >>
    irule freshen_global_mono >> first_x_assum $ irule_at Any >>
    rpt $ goal_assum $ drule_at Any >>
    gvs[avoid_ok_def, SUBSET_DEF] >> gvs[allvars_thm]
    )
  >- ( (* Letrec *)
    rpt (pairarg_tac >> gvs[]) >> gvs[exp_of_def, letrecs_distinct_def, cexp_wf_def] >>
    rename1 `freshen_aux _ ce1 avoid3 = (ce2,avoid4)` >>
    rename1 `fresh_boundvars _ _ _ = ((freshes,_),avoid2)` >>
    rename1 `freshen_mapM _ _ _ = (fns',_)` >>
    simp[Once freshen_global_cases] >>
    drule fresh_boundvars_rel >> rpt $ disch_then $ drule_at Any >>
    impl_tac >- gvs[avoid_ok_def] >> strip_tac >> gvs[] >>
    qexists `FEMPTY |++ ZIP (MAP (explode o FST) fns, MAP explode freshes)` >>
    rw[]
    >- simp[FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_ZIP]
    >- (
      simp[Once DISJOINT_SYM] >> irule DISJOINT_SUBSET >>
      irule_at Any FRANGE_FUPDATE_LIST_SUBSET >> simp[MAP_ZIP]
      )
    >- (
      gvs[FLOOKUP_FUPDATE_LIST, AllCaseEqs()] >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      rpt $ dxrule_then assume_tac ALOOKUP_MEM >> gvs[MEM_ZIP, EL_MAP] >>
      gvs[EL_ALL_DISTINCT_EL_EQ, EL_MAP]
      )
    >- (imp_res_tac freshen_mapM_LENGTH >> gvs[])
    >- (
      last_x_assum kall_tac >> qpat_x_assum `freshen_aux _ _ _ = _` kall_tac >>
      gvs[MAP_EQ_APPEND, PULL_EXISTS] >> pairarg_tac >> gvs[] >>
      rename1 `l ++ [f1,fce1] ++ r` >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      qpat_x_assum `∀f ce vm. MEM _ r ⇒ _` kall_tac >>
      gvs[freshen_mapM_append, freshen_mapM_def,
          fresh_boundvars_append, fresh_boundvars_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac fresh_boundvars_LENGTH >> imp_res_tac freshen_mapM_LENGTH >>
      gvs[] >>
      rename1 `ZIP (fresh_l ++ [y] ++ fresh_r, fns'_l ++ [fn'] ++ fns'_r)` >>
      simp[GSYM ZIP_APPEND] >> irule_at Any EQ_REFL >> rw[]
      >- (
        simp[FLOOKUP_FUPDATE_LIST, REVERSE_APPEND, ALOOKUP_APPEND, AllCaseEqs()] >>
        disj1_tac >> qpat_x_assum `ALL_DISTINCT (_ ++ [explode _] ++ _)` mp_tac >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, ALL_DISTINCT_APPEND] >>
        simp[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP] >> simp[MEM_MAP, FORALL_PROD]
        ) >>
      first_x_assum drule >> disch_then drule >> rename1 `avoid_ok avoid2'` >>
      `EVERY (avoid_ok avoid2) (MAP SND l)` by (
        gvs[EVERY_MEM, avoid_ok_def, MEM_MAP, PULL_EXISTS, FORALL_PROD, SUBSET_DEF] >>
        metis_tac[]) >>
      `vars_ok avoid2' ∧ set_of avoid2 ⊆ set_of avoid2' ∧
       EVERY (avoid_ok avoid2') fns'_l` by (
        pop_assum mp_tac >>
        qpat_x_assum `freshen_mapM _ _ avoid2 = _` mp_tac >>
        qpat_x_assum `vars_ok avoid2` mp_tac >> rpt $ pop_assum kall_tac >>
        map_every qid_spec_tac [`avoid2`,`fns'_l`] >>
        Induct_on `l` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
        rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
        drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
        drule_all $ cj 1 freshen_aux_avoid_ok >> strip_tac >>
        last_x_assum drule >> rpt $ disch_then drule >>
        impl_tac >> rw[] >>
        gvs[avoid_ok_def, EVERY_MEM, SUBSET_DEF, MEM_MAP, PULL_EXISTS] >>
        metis_tac[]
        ) >>
      impl_tac >- (rw[] >> gvs[avoid_ok_def] >> gvs[SUBSET_DEF]) >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FORALL_PROD, GSYM ZIP_APPEND] >>
      qmatch_goalsub_abbrev_tac `FRANGE (FEMPTY |++ new)` >> strip_tac >>
      simp[SRULE [combinTheory.o_DEF, LAMBDA_PROD] MAP_ZIP] >>
      qpat_x_assum `varmap_rel _ _` mp_tac >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM ZIP_APPEND] >> strip_tac >>
      simp[GSYM fupdate_list_funion] >>
      irule freshen_global_mono >> goal_assum $ drule_at Any >> rw[]
      >- gvs[SUBSET_DEF]
      >- (
        qabbrev_tac `fresh_set =
          set (MAP explode fresh_l) ∪ {explode y} ∪ set (MAP explode fresh_r)` >>
        qsuff_tac `FRANGE (FEMPTY |++ new) = fresh_set` >- (strip_tac >> gvs[]) >>
        irule SUBSET_ANTISYM >> rw[]
        >- (
          irule SUBSET_TRANS >> irule_at Any FRANGE_FUPDATE_LIST_SUBSET >> simp[] >>
          unabbrev_all_tac >> gvs[MAP_ZIP, SUBSET_DEF]
          )
        >- (
          irule SUBSET_TRANS >> irule_at Any FRANGE_FUPDATE_LIST_ALL_DISTINCT >>
          unabbrev_all_tac >> simp[SUBSET_DEF] >>
          gvs[MAP_ZIP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
          )
        )
      >- (
        simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
        gvs[EVERY_MEM, avoid_ok_def, allvars_thm]
        )
      )
    >- (
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM fupdate_list_funion] >>
      qmatch_goalsub_abbrev_tac `FRANGE (FEMPTY |++ new)` >>
      drule freshen_mapM_LENGTH >> strip_tac >> gvs[] >>
      simp[SRULE [combinTheory.o_DEF, LAMBDA_PROD] MAP_ZIP] >>
      last_x_assum drule >> disch_then drule >>
      `EVERY (avoid_ok avoid2) (MAP SND fns)` by (
        gvs[EVERY_MEM, avoid_ok_def, MEM_MAP, PULL_EXISTS, FORALL_PROD, SUBSET_DEF] >>
        metis_tac[]) >>
      `vars_ok avoid3 ∧ set_of avoid2 ⊆ set_of avoid3 ∧
       EVERY (avoid_ok avoid3) fns'` by (
        pop_assum mp_tac >>
        qpat_x_assum `freshen_mapM _ _ avoid2 = _` mp_tac >>
        qpat_x_assum `vars_ok avoid2` mp_tac >> rpt $ pop_assum kall_tac >>
        map_every qid_spec_tac [`avoid2`,`fns'`] >>
        Induct_on `fns` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
        rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
        drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
        drule_all $ cj 1 freshen_aux_avoid_ok >> strip_tac >>
        last_x_assum drule >> rpt $ disch_then drule >>
        impl_tac >> rw[] >>
        gvs[avoid_ok_def, EVERY_MEM, SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
        metis_tac[]
        ) >>
      impl_tac >- (rw[] >> gvs[avoid_ok_def] >> gvs[SUBSET_DEF]) >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> strip_tac >>
      irule freshen_global_mono >> goal_assum $ drule_at Any >> rw[]
      >- gvs[SUBSET_DEF]
      >- (
        qsuff_tac `FRANGE (FEMPTY |++ new) = set (MAP explode freshes)`
        >- (strip_tac >> gvs[]) >>
        irule SUBSET_ANTISYM >> rw[]
        >- (
          irule SUBSET_TRANS >> irule_at Any FRANGE_FUPDATE_LIST_SUBSET >> simp[] >>
          unabbrev_all_tac >> gvs[MAP_ZIP]
          )
        >- (
          irule SUBSET_TRANS >> irule_at Any FRANGE_FUPDATE_LIST_ALL_DISTINCT >>
          unabbrev_all_tac >> simp[SUBSET_DEF] >>
          gvs[MAP_ZIP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
          )
        )
      >- (
        simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
        gvs[EVERY_MEM, avoid_ok_def, allvars_thm]
        )
      )
    )
  >- ( (* Case *)
    `¬MEM v (FLAT (MAP (FST o SND) css)) ∧ cexp_wf ce1 ∧
     EVERY (λ(cn,pvs,ce). cexp_wf ce) css ∧ css ≠ [] ∧
     (∀cnars us. usopt = SOME (cnars,us) ⇒ cexp_wf us)` by (
      gvs[cexp_wf_def, combinTheory.o_DEF, LAMBDA_PROD, EVERY_MAP] >> rw[] >> gvs[]) >>
    qpat_x_assum `cexp_wf (Case _ _ _ _ _)` kall_tac >> simp[] >>
    rpt (pairarg_tac >> gvs[]) >>
    gvs[exp_of_def, letrecs_distinct_rows_of, letrecs_distinct_def, cexp_wf_def] >>
    rename1 `freshen_mapM _ css1 avoid3 = (css2,avoid4)` >>
    rename1 `(usopt2,avoid5)` >>
    rename1 `fresh_boundvar x _ avoid2 = ((y,_),_)` >>
    rename1 `freshen_aux _ _ _ = (ce2,_)` >>
    `¬ MEM y (FLAT (MAP (FST o SND) css2))` by (
      `explode y ∈ set_of avoid3 ∧ vars_ok avoid3` by (
        drule $ cj 1 freshen_aux_mono >> impl_tac >- gvs[avoid_ok_def] >> strip_tac >>
        drule fresh_boundvar_vars >> simp[]) >>
      qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
      ntac 2 $ pop_assum mp_tac >> rpt $ pop_assum kall_tac >>
      map_every qid_spec_tac [`avoid3`,`css2`] >>
      Induct_on `css1` >> rw[freshen_mapM_def] >> rpt (pairarg_tac >> gvs[]) >>
      drule_all fresh_boundvars_vars >> strip_tac >>
      gvs[DISJOINT_ALT, MEM_MAP, PULL_EXISTS] >> rw[] >- metis_tac[] >>
      first_x_assum irule >> goal_assum $ drule_at $ Pat `freshen_mapM` >>
      drule_all $ cj 1 freshen_aux_mono >> gvs[SUBSET_DEF]) >>
    simp[Once freshen_global_cases] >> disj2_tac >>
    first_x_assum drule_all >> strip_tac >>
    drule_all $ cj 1 freshen_aux_avoid_ok >> strip_tac >>
    drule $ cj 1 freshen_aux_mono >>
    impl_tac >- gvs[avoid_ok_def] >> strip_tac >>
    drule_all fresh_boundvar_rel >> strip_tac >> rw[]
    >- (CCONTR_TAC >> gvs[SUBSET_DEF])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF, avoid_ok_def, allvars_thm]) >>
    irule freshen_global_rows_of >> simp[FLOOKUP_SIMP] >>
    imp_res_tac freshen_mapM_LENGTH >> simp[] >> reverse conj_tac >> rw[]
    >- (
      namedCases_on `usopt` ["","us"] >> gvs[] >- simp[Once freshen_global_cases] >>
      PairCases_on `us` >> gvs[] >> pairarg_tac >> gvs[] >>
      irule freshen_global_IfDisj >> simp[FLOOKUP_SIMP] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      irule freshen_global_mono >> first_x_assum $ irule_at Any >>
      goal_assum drule >> simp[] >>
      qsuff_tac
        `vars_ok avoid4 ∧ set_of avoid3 ⊆ set_of avoid4 ∧
         EVERY (λ(cn,pvs,ce).
            set (MAP explode pvs) ∪ boundvars (exp_of ce) ⊆ set_of avoid4) css2`
      >- (
        strip_tac >> gvs[avoid_ok_def, SUBSET_DEF] >>
        conj_tac >- gvs[allvars_thm] >>
        gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]
        ) >>
      `EVERY (λ(cn,pvs,ce).
        set (MAP explode pvs) ⊆ set_of avoid3 ∧ avoid_ok avoid3 ce) css1` by (
          gvs[EVERY_MEM, FORALL_PROD, SUBSET_DEF, avoid_ok_def] >>
          metis_tac[]) >>
      pop_assum mp_tac >>
      map_every (fn p => qpat_x_assum p mp_tac)
        [`freshen_mapM _ _ _ = _`,`vars_ok avoid3`] >>
      rpt $ pop_assum kall_tac >>
      map_every qid_spec_tac [`avoid3`,`css2`] >>
      Induct_on `css1` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
      rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
      drule_all fresh_boundvars_vars >> strip_tac >>
      drule_all $ cj 1 freshen_aux_mono >> strip_tac >> gvs[] >>
      last_x_assum $ drule_at $ Pat `freshen_mapM` >> simp[] >> impl_tac
      >- (gvs[EVERY_MEM, FORALL_PROD, SUBSET_DEF, avoid_ok_def] >> metis_tac[]) >>
      drule $ cj 1 freshen_aux_avoid_ok >> impl_tac >- gvs[avoid_ok_def, SUBSET_DEF] >>
      strip_tac >> simp[] >> gvs[SUBSET_DEF, avoid_ok_def, allvars_thm]
      )
    >- (
      CCONTR_TAC >> qpat_x_assum `¬MEM x _` mp_tac >> gvs[MAP_EQ_APPEND] >>
      pairarg_tac >> gvs[MEM_MAP]
      ) >>
    gvs[MAP_EQ_APPEND, PULL_EXISTS] >> pairarg_tac >> gvs[EXISTS_PROD] >>
    rename1 `l1 ++ [(cn,pvs1,ce)] ++ r1` >>
    last_x_assum mp_tac >> simp[SF DNF_ss] >> strip_tac >> pop_assum kall_tac >>
    gvs[freshen_mapM_append, freshen_mapM_def] >> rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> strip_tac >>
    rename1 `l2 ++ [(cn,pvs2,ce')] ++ r2` >> irule_at Any EQ_REFL >>
    imp_res_tac fresh_boundvars_LENGTH >> imp_res_tac freshen_mapM_LENGTH >> gvs[] >>
    simp[MEM_MAP] >>
    rename1 `freshen_mapM _ _ avoid3 = (_,avoidL)` >>
    rename1 `fresh_boundvars _ _ _ = (_,avoidB)` >>
    rename1 `freshen_aux _ _ avoidB = (_,avoidE)` >>
    qpat_x_assum `freshen_mapM _ _ avoidE = _` kall_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    irule_at Any freshen_global_mono >> first_x_assum $ irule_at Any >>
    `EVERY (λ(cn,pvs,ce).
      set (MAP explode pvs) ⊆ set_of avoid3 ∧ avoid_ok avoid3 ce) l1` by (
        gvs[EVERY_MEM, FORALL_PROD, SUBSET_DEF, avoid_ok_def] >>
        metis_tac[]) >>
    `vars_ok avoidL ∧ set_of avoid3 ⊆ set_of avoidL ∧
     EVERY (λ(cn,pvs,ce).
      set (MAP explode pvs) ∪ boundvars (exp_of ce) ⊆ set_of avoidL) l2` by (
      pop_assum mp_tac >>
      map_every (fn p => qpat_x_assum p mp_tac)
        [`freshen_mapM _ _ _ = _`,`vars_ok avoid3`] >>
      rpt $ pop_assum kall_tac >>
      map_every qid_spec_tac [`avoid3`,`l2`] >>
      Induct_on `l1` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
      rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
      drule_all fresh_boundvars_vars >> strip_tac >>
      drule_all $ cj 1 freshen_aux_mono >> strip_tac >> gvs[] >>
      last_x_assum $ drule_at $ Pat `freshen_mapM` >> simp[] >> impl_tac
      >- (gvs[EVERY_MEM, FORALL_PROD, SUBSET_DEF, avoid_ok_def] >> metis_tac[]) >>
      drule $ cj 1 freshen_aux_avoid_ok >> impl_tac >- gvs[avoid_ok_def, SUBSET_DEF] >>
      strip_tac >> simp[] >> gvs[SUBSET_DEF, avoid_ok_def, allvars_thm]) >>
    drule_all fresh_boundvars_rel >> strip_tac >> gvs[] >>
    rw[]
    >- gvs[avoid_ok_def, SUBSET_DEF]
    >- gvs[SUBSET_DEF]
    >- gvs[avoid_ok_def, SUBSET_DEF, allvars_thm]
    >- (
      gvs[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, FORALL_PROD, EVERY_MEM] >>
      gvs[SUBSET_DEF] >> metis_tac[]
      )
    >- (gvs[DISJOINT_ALT, SUBSET_DEF] >> metis_tac[])
    >- (
      gvs[DISJOINT_ALT, SUBSET_DEF, avoid_ok_def, allvars_thm] >>
      metis_tac[]
      )
    >- (
      gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD, DISJOINT_ALT,
          SUBSET_DEF, avoid_ok_def, allvars_thm] >>
      metis_tac[]
      )
    )
  >- (
    rpt (pairarg_tac >> gvs[]) >> gvs[exp_of_def, cexp_wf_def]
    )
  >- ( (* list case *)
    rpt (pairarg_tac >> gvs[]) >>
    rename1 `freshen_aux_list _ ces1 avoid1' = (ces2,_)` >>
    rename1 `freshen_aux _ ce1' _ = (ce2',_)` >>
    rename1 `freshen_aux _ ce1 _ = (ce2,_)` >>
    Cases_on `l1` >> gvs[freshen_aux_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    last_x_assum drule_all >> strip_tac >>
    last_x_assum drule >> strip_tac >>
    gvs[freshen_aux_list_append, freshen_aux_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    first_x_assum $ qspecl_then [`m`,`t`] mp_tac >>
    simp[] >> impl_tac
    >- (
      gvs[EVERY_MEM, avoid_ok_def] >>
      drule $ cj 1 freshen_aux_mono >> strip_tac >> gvs[] >>
      gvs[SUBSET_DEF, allvars_thm, contains_var_in_set_of] >> metis_tac[]
      ) >>
    strip_tac >> simp[] >> gvs[AC UNION_ASSOC UNION_COMM]
    )
QED

Theorem freshen_cexp_freshen_global:
  ∀ce1 avoid1 ce2 avoid2.
    freshen_cexp ce1 avoid1 = (ce2,avoid2) ∧
    avoid_ok avoid1 ce1 ∧
    NestedCase_free ce1 ∧ letrecs_distinct (exp_of ce1) ∧ cexp_wf ce1
  ⇒ freshen_global (set_of avoid1) FEMPTY (exp_of ce1) (exp_of ce2)
Proof
  rw[freshen_cexp_def] >>
  irule $ cj 1 freshen_aux_freshen_global >> simp[] >>
  goal_assum drule >> simp[varmap_rel_def]
QED


(********** typing **********)

Definition ctxt_rel_def:
  ctxt_rel m s ctxt1 ctxt2 ⇔
    ∀x t. x ∈ s ∧ ALOOKUP ctxt1 x = SOME t ⇒
      case lookup m x of
      | NONE => ALOOKUP ctxt2 x = SOME t
      | SOME y => ALOOKUP ctxt2 y = SOME t
End

Theorem ctxt_rel_extend:
  ∀xs ys ts env1 env2 m s.
    ctxt_rel m (s DIFF set xs) env1 env2 ∧
    ALL_DISTINCT ys ∧
    DISJOINT (set ys) s ∧
    LENGTH xs = LENGTH ts ∧ LENGTH ys = LENGTH ts ∧
    (∀k v. lookup m k = SOME v ⇒ ¬ MEM v ys) ∧
    (∀k. lookup m' k =
          case ALOOKUP (ZIP (xs,ys)) k of
          | NONE => lookup m k
          | SOME v => SOME v)
  ⇒ ctxt_rel m' s (ZIP (xs,ts) ++ env1) (ZIP (ys,ts) ++ env2)
Proof
  rw[ctxt_rel_def] >> gvs[ALOOKUP_APPEND] >>
  pop_assum mp_tac >> CASE_TAC >> gvs[ALOOKUP_NONE] >> strip_tac
  >- (
    gvs[MAP_ZIP] >>
    `ALOOKUP (ZIP (xs,ys)) x = NONE` by simp[ALOOKUP_NONE, MAP_ZIP] >>
    simp[] >> last_x_assum drule_all >> rw[] >>
    `¬ MEM x ys` by (gvs[DISJOINT_ALT] >> metis_tac[]) >>
    `ALOOKUP (ZIP (ys,ts)) x = NONE` by simp[ALOOKUP_NONE, MAP_ZIP] >> simp[] >>
    TOP_CASE_TAC >> gvs[] >>
    qsuff_tac `ALOOKUP (ZIP (ys,ts)) x' = NONE` >> rw[] >>
    simp[ALOOKUP_NONE, MAP_ZIP] >> CCONTR_TAC >> gvs[DISJOINT_ALT] >> metis_tac[]
    )
  >- (
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, EL_MAP] >>
    CASE_TAC >- gvs[ALOOKUP_NONE, MAP_ZIP, EL_MEM] >>
    rename1 `ALOOKUP _ (EL _ _) = SOME y` >>
    qsuff_tac `ALOOKUP (ZIP (ys,ts)) y = SOME $ EL n ts` >> rw[] >>
    qspecl_then [`ZIP (xs,ys)`,`ZIP (xs,ts)`] mp_tac ALOOKUP_SOME_EL_2 >>
    disch_then drule >> simp[MAP_ZIP] >> strip_tac >> gvs[EL_ZIP] >>
    qspec_then `ZIP (ys,ts)` mp_tac ALOOKUP_ALL_DISTINCT_EL >> simp[MAP_ZIP] >>
    disch_then drule >> simp[EL_ZIP]
    )
QED

Theorem freshen_aux_preserves_typing:
  (∀m (ce1:α cexp) avoid1 ce2 avoid2 ce2 ns db st env1 t env2.
    freshen_aux m ce1 avoid1 = (ce2, avoid2) ∧
    type_tcexp ns db st env1 (tcexp_of ce1) t ∧
    ctxt_rel m (freevars_cexp ce1) env1 env2 ∧
    map_ok m ∧ (∀k v. lookup m k = SOME v ⇒ explode v ∈ set_of avoid1) ∧
    avoid_ok avoid1 ce1
  ⇒ type_tcexp ns db st env2 (tcexp_of ce2) t) ∧
  (∀m (ces1:α cexp list) avoid1 ces2 avoid2 ns db st env1 t env2.
    freshen_aux_list m ces1 avoid1 = (ces2, avoid2) ∧
    ctxt_rel m (BIGUNION $ set $ MAP freevars_cexp ces1) env1 env2 ∧
    map_ok m ∧ (∀k v. lookup m k = SOME v ⇒ explode v ∈ set_of avoid1) ∧
    EVERY (avoid_ok avoid1) ces1
  ⇒ LIST_REL (λce1 ce2. ∀t.
      type_tcexp ns db st env1 (tcexp_of ce1) t
      ⇒ type_tcexp ns db st env2 (tcexp_of ce2) t) ces1 ces2)
Proof
  ho_match_mp_tac freshen_aux_ind >> rw[freshen_aux_def] >> gvs[tcexp_of_def]
  >- ( (* Var *)
    gvs[Once type_tcexp_cases] >> simp[Once type_tcexp_cases] >>
    gvs[ctxt_rel_def] >> CASE_TAC >> gvs[]
    )
  >- ( (* Prim *)
    rpt (pairarg_tac >> gvs[]) >> gvs[tcexp_of_def, SF ETA_ss] >>
    last_x_assum drule_all >> disch_then $ qspecl_then [`ns`,`db`,`st`] mp_tac >>
    rw[LIST_REL_EL_EQN] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    once_rewrite_tac[type_tcexp_cases] >> rw[] >>
    gvs[LENGTH_EQ_NUM_compute, MAP_EQ_CONS, numeral_less_thm, SF DNF_ss] >>
    rpt $ first_x_assum drule >> simp[SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]
    )
  >- ( (* App *)
    rpt (pairarg_tac >> gvs[]) >> gvs[tcexp_of_def, SF ETA_ss] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    once_rewrite_tac[type_tcexp_cases] >> rw[] >> goal_assum $ drule_at Any >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    conj_tac >- gvs[ctxt_rel_def] >>
    last_x_assum drule >>
    disch_then $ qspecl_then [`ns`,`db`,`st`,`env1`,`env2`] mp_tac >>
    impl_tac >> rw[]
    >- gvs[ctxt_rel_def]
    >- (
      gvs[avoid_ok_def] >> drule_all $ cj 1 freshen_aux_mono >>
      gvs[SUBSET_DEF] >> metis_tac[]
      )
    >- (
      gvs[EVERY_MEM, avoid_ok_def] >>
      drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
      drule_all $ cj 2 freshen_aux_mono >> gvs[SUBSET_DEF] >> metis_tac[]
      )
    >- (imp_res_tac freshen_aux_list_LENGTH >> gvs[LIST_REL_EL_EQN, EL_MAP])
    )
  >- ( (* Lam *)
    rpt (pairarg_tac >> gvs[]) >> gvs[tcexp_of_def] >>
    rename1 `fresh_boundvars xs m avoid1 = ((ys,m'), avoid1')` >>
    rename1 `freshen_aux m' ce avoid1' = (ce',avoid2)` >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    once_rewrite_tac[type_tcexp_cases] >> rw[] >> gvs[] >>
    irule_at Any EQ_REFL >> simp[] >>
    imp_res_tac fresh_boundvars_LENGTH >> gvs[] >>
    first_x_assum irule >> rpt $ goal_assum $ drule_at Any >>
    gvs[avoid_ok_def] >>
    drule_all fresh_boundvars_varmap >> strip_tac >> simp[] >>
    drule_all fresh_boundvars_vars >> strip_tac >> simp[] >>
    rev_drule_all $ cj 1 freshen_aux_mono >> strip_tac >> rw[]
    >- (
      rw[] >> FULL_CASE_TAC >> gvs[] >- (res_tac >> simp[]) >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP] >> simp[MEM_MAP, EL_MEM]
      )
    >- gvs[SUBSET_DEF] >>
    gvs[REVERSE_ZIP] >> irule ctxt_rel_extend >> simp[PULL_EXISTS] >>
    goal_assum $ drule_at Any >> simp[] >>
    gvs[allvars_thm, freevars_exp_of] >>
    gvs[DISJOINT_ALT, SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> metis_tac[]
    )
  >- ( (* Let *)
    rpt (pairarg_tac >> gvs[]) >> gvs[tcexp_of_def] >>
    rename1 `freshen_aux m' ce2 avoid3 = (ce2',avoid4)` >>
    rename1 `fresh_boundvar x m avoid2 = ((y,_),_)` >>
    rename1 `freshen_aux m ce1 avoid1 = (ce1',_)` >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    once_rewrite_tac[type_tcexp_cases] >> rw[] >> gvs[] >>
    first_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    first_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[avoid_ok_def] >>
    rev_drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    drule_all fresh_boundvar_varmap >> strip_tac >> simp[] >>
    drule_all fresh_boundvar_vars >> strip_tac >> simp[] >>
    reverse $ rw[]
    >- (
      gvs[ctxt_rel_def] >> rw[] >> gvs[ALOOKUP_MAP] >>
      last_x_assum $ drule_at Any >> simp[] >> TOP_CASE_TAC >> gvs[]
      )
    >- gvs[SUBSET_DEF]
    >- metis_tac[SUBSET_DEF] >>
    qspecl_then [`[x]`,`[y]`,`[new,t1]`] mp_tac ctxt_rel_extend >> simp[] >>
    disch_then irule >> simp[PULL_EXISTS] >> qexists `m` >> rw[]
    >- (gvs[allvars_thm, freevars_exp_of] >> gvs[SUBSET_DEF] >> metis_tac[])
    >- (gvs[SUBSET_DEF] >> metis_tac[])
    >- gvs[ctxt_rel_def]
    )
  >- ( (* Letrec *)
    rpt (pairarg_tac >> gvs[]) >> gvs[tcexp_of_def] >>
    rename1 `freshen_aux m' ce avoid3 = (ce',avoid4)` >>
    rename1 `freshen_mapM _ fns avoid2 = (fns',_)` >>
    rename1 `fresh_boundvars _ _ _ = ((ys,_),_)` >>
    imp_res_tac fresh_boundvars_LENGTH >>
    imp_res_tac freshen_mapM_LENGTH >> gvs[MAP_ZIP_ALT] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    once_rewrite_tac[type_tcexp_cases] >> rw[] >> gvs[] >>
    goal_assum $ drule_at Any >> gvs[MAP_ZIP] >>
    pop_assum mp_tac >> simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM FST_THM] >> strip_tac >>
    drule_all fresh_boundvars_varmap >> strip_tac >> simp[] >>
    drule fresh_boundvars_vars >> impl_tac >- gvs[avoid_ok_def] >> strip_tac >>
    `vars_ok avoid3 ∧ set_of avoid2 ⊆ set_of avoid3` by (
      qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
      qpat_x_assum `vars_ok avoid2` mp_tac >>
      rpt $ pop_assum kall_tac >> map_every qid_spec_tac [`fns'`,`avoid2`] >>
      Induct_on `fns` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
      rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
      drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
      last_x_assum drule_all >> rw[] >> gvs[SUBSET_DEF]) >>
    qmatch_asmsub_abbrev_tac `freevars_cexp _ ∪ bigunion` >>
    `ctxt_rel m' (freevars_cexp ce ∪ bigunion)
      (REVERSE (ZIP (MAP FST fns,schemes)) ++ env1)
      (REVERSE (ZIP (ys,schemes)) ++ env2)` by (
      imp_res_tac LIST_REL_LENGTH >> gvs[REVERSE_ZIP] >>
      irule ctxt_rel_extend >> simp[PULL_EXISTS] >>
      goal_assum $ drule_at Any >> simp[] >> unabbrev_all_tac >>
      gvs[EVERY_MEM, FORALL_PROD, avoid_ok_def, allvars_thm, freevars_exp_of] >>
      gvs[DISJOINT_ALT, MEM_MAP, PULL_EXISTS, FORALL_PROD, SUBSET_DEF] >>
      metis_tac[]) >>
    reverse $ rw[]
    >- (
      last_x_assum drule >> disch_then drule >> disch_then irule >> rw[]
      >- (
        pop_assum mp_tac >> CASE_TAC >> strip_tac >> gvs[]
        >- (gvs[SUBSET_DEF] >> metis_tac[]) >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, SUBSET_DEF, MEM_MAP] >>
        metis_tac[EL_MEM]
        )
      >- gvs[avoid_ok_def, SUBSET_DEF]
      >- gvs[ctxt_rel_def]
      )
    >- (
      Cases_on `fns` >> Cases_on `ys` >> Cases_on `fns'` >> gvs[]
      ) >>
    qpat_x_assum `LIST_REL _ _ _` mp_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
    `ctxt_rel m' bigunion
      (REVERSE (ZIP (MAP FST fns,schemes)) ++ env1)
      (REVERSE (ZIP (ys,schemes)) ++ env2)` by gvs[ctxt_rel_def] >>
    rewrite_tac[GSYM MAP_APPEND] >>
    qmatch_asmsub_abbrev_tac `ctxt_rel _ _ env1' env2'` >>
    qpat_x_assum `ctxt_rel _ _ _ _` mp_tac >> simp[Abbr `bigunion`] >>
    `∀k v. lookup m' k = SOME v ⇒ explode v ∈ set_of avoid2` by (
      simp[] >> rpt gen_tac >> CASE_TAC >> strip_tac >> gvs[]
      >- (gvs[SUBSET_DEF] >> metis_tac[]) >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, SUBSET_DEF, MEM_MAP] >>
      metis_tac[EL_MEM]) >>
    pop_assum mp_tac >> qpat_x_assum `map_ok m'` mp_tac >>
    `EVERY (λ(f,ce). avoid_ok avoid2 ce) fns` by (
      gvs[EVERY_MEM, FORALL_PROD, avoid_ok_def, SUBSET_DEF] >> metis_tac[]) >>
    pop_assum mp_tac >> qpat_x_assum `LENGTH ys = _` mp_tac >>
    qpat_x_assum `∀f ce1 m. MEM _ _ ⇒ _` mp_tac >>
    rpt $ pop_assum kall_tac >> strip_tac >>
    map_every qid_spec_tac [`fns'`,`ys`,`schemes`,`avoid2`] >>
    Induct_on `fns` >> rw[freshen_mapM_def] >>
    rpt (pairarg_tac >> gvs[]) >> Cases_on `ys` >> gvs[SF DNF_ss] >>
    last_x_assum dxrule >> disch_then $ irule_at Any >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[EVERY_MEM, avoid_ok_def] >>
    drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    reverse $ rw[]
    >- gvs[ctxt_rel_def]
    >- (gvs[SUBSET_DEF] >> res_tac >> res_tac)
    >- (pairarg_tac >> gvs[FORALL_PROD, SUBSET_DEF] >> metis_tac[])
    >- (
      gvs[ctxt_rel_def, ALOOKUP_MAP_3'] >> rw[] >>
      first_x_assum $ qspec_then `x` mp_tac >> simp[] >>
      CASE_TAC >> gvs[]
      )
    )
  >- ( (* Case *)
    rpt (pairarg_tac >> gvs[]) >> gvs[tcexp_of_def] >>
    rename1 `_ avoid4 = (usopt',avoid5)` >>
    rename1 `freshen_mapM _ css avoid3 = (css',_)` >>
    rename1 `fresh_boundvar x m avoid2 = ((y,m'),_)` >>
    rename1 `freshen_aux m ce avoid1 = (ce',_)` >>
    imp_res_tac fresh_boundvars_LENGTH >>
    imp_res_tac freshen_mapM_LENGTH >> gvs[MAP_ZIP_ALT] >>
    gvs[avoid_ok_def] >> drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    drule_all fresh_boundvar_varmap >> strip_tac >>
    drule_all fresh_boundvar_vars >> strip_tac >>
    qmatch_asmsub_abbrev_tac `ctxt_rel m fvs env1 env2` >>
    `IMAGE explode fvs ⊆ set_of avoid1` by (
      gvs[Abbr `fvs`, allvars_thm, freevars_exp_of] >>
      simp[UNION_DELETE] >> gvs[SUBSET_DEF, PULL_EXISTS] >> rw[]
      >- (gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD, FORALL_PROD] >> metis_tac[])
      >- (namedCases_on `usopt` ["","us"] >> gvs[] >> PairCases_on `us` >> gvs[])) >>
    `∀s t. s ⊆ x INSERT fvs ⇒ ctxt_rel m' s ((x,t)::env1) ((y,t)::env2)` by (
      rw[] >> qspecl_then [`[x]`,`[y]`,`[t']`] mp_tac ctxt_rel_extend >> simp[] >>
      disch_then irule >> simp[PULL_EXISTS] >> qexists `m` >>
      rw[] >> gvs[SUBSET_DEF, ctxt_rel_def] >> metis_tac[]) >>
    first_x_assum drule >> rpt $ disch_then $ drule_at Any >> strip_tac >>
    `LIST_REL (λ(cn,pvs,ce) (cn',pvs',ce').
      cn' = cn ∧ LENGTH pvs' = LENGTH pvs ∧ ¬MEM y pvs' ∧ ALL_DISTINCT pvs' ∧
      (∀ts tx t. LENGTH ts = LENGTH pvs ∧
        type_tcexp ns db st
          (REVERSE (ZIP (pvs,ts)) ++ (x,tx)::env1) (tcexp_of ce) t
        ⇒ type_tcexp ns db st
            (REVERSE (ZIP (pvs',ts)) ++ (y,tx)::env2) (tcexp_of ce') t)) css css' ∧
     vars_ok avoid4 ∧ set_of avoid3 ⊆ set_of avoid4` by (
      qpat_x_assum `freshen_mapM _ _ _ = _` mp_tac >>
      `explode y ∈ set_of avoid3` by simp[] >> pop_assum mp_tac >>
      `∀s t. s ⊆ x INSERT
        BIGUNION (set $ MAP ( λ(cn,pvs,e). freevars_cexp e DIFF set pvs) css)
          ⇒ ctxt_rel m' s ((x,t)::env1) ((y,t)::env2)` by (
            unabbrev_all_tac >> rw[] >>
            first_x_assum irule >> gvs[SUBSET_DEF] >> metis_tac[]) >>
      pop_assum mp_tac >>
      qpat_x_assum `map_ok m'` mp_tac >>
      `∀k v. lookup m' k = SOME v ⇒ explode v ∈ set_of avoid3` by (
        rw[DISJ_EQ_IMP] >> gvs[SUBSET_DEF] >> metis_tac[]) >>
      pop_assum mp_tac >>
      qpat_x_assum `vars_ok avoid3` mp_tac >>
      `EVERY (λ(cn,pvs,ce). set (MAP explode pvs) ⊆ set_of avoid3 ∧
                            allvars (exp_of ce) ⊆ set_of avoid3) css` by (
        gvs[EVERY_MEM, FORALL_PROD, SUBSET_DEF] >> metis_tac[]) >>
      pop_assum mp_tac >>
      qpat_x_assum `∀cn pvs c m. MEM _ _ ⇒ _` mp_tac >>
      rpt $ pop_assum kall_tac >> strip_tac >>
      map_every qid_spec_tac [`css'`,`avoid3`] >>
      Induct_on `css` >> simp[freshen_mapM_def, AND_IMP_INTRO] >>
      gen_tac >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      strip_tac >> rpt gen_tac >> strip_tac >>
      last_x_assum dxrule >> strip_tac >>
      rpt (pairarg_tac >> gvs[]) >>
      first_x_assum $ dxrule_at $ Pat `freshen_mapM` >> strip_tac >>
      rename1 `fresh_boundvars _ _ _ = ((_,m''),avoid3A)` >>
      rename1 `freshen_aux _ _ _ = (_,avoid3B)` >>
      drule_all fresh_boundvars_varmap >> strip_tac >>
      gvs[avoid_ok_def] >> drule_all fresh_boundvars_vars >> strip_tac >>
      imp_res_tac fresh_boundvars_LENGTH >> simp[] >>
      drule_all $ cj 1 freshen_aux_mono >> strip_tac >> gvs[] >>
      simp[GSYM CONJ_ASSOC] >> conj_tac
      >- (gvs[DISJOINT_ALT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
      reverse conj_tac
      >- (
        qpat_x_assum `_ ⇒ LIST_REL _ _ _ ∧ _` mp_tac >> impl_tac
        >- (gvs[SUBSET_DEF, EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
        simp[] >> strip_tac >> gvs[SUBSET_DEF]
        ) >>
      rw[] >> last_x_assum irule >>
      goal_assum $ drule_at $ Pat `freshen_aux` >> simp[] >>
      goal_assum $ drule_at Any >> rw[]
      >- (
        gvs[MEM_MAP] >> pop_assum mp_tac >> TOP_CASE_TAC >> strip_tac >> gvs[]
        >- metis_tac[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, EL_MEM]
        )
      >- gvs[SUBSET_DEF] >>
      qpat_abbrev_tac `env1' = _::env1` >>
      qpat_abbrev_tac `env2' = _::env2` >>
      last_x_assum $ qspecl_then [`freevars_cexp ce DIFF set pvs`,`tx`] mp_tac >>
      simp[SUBSET_DEF] >> strip_tac >> gvs[REVERSE_ZIP] >>
      irule ctxt_rel_extend >> simp[PULL_EXISTS] >>
      goal_assum $ drule_at Any >> simp[] >>
      gvs[EVERY_MEM, FORALL_PROD, allvars_thm, freevars_exp_of] >>
      gvs[SUBSET_DEF, DISJOINT_ALT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
      ) >>
    qpat_x_assum `freshen_mapM _ _ _ = _` kall_tac >>
    qpat_x_assum `∀cn pvs e m. MEM _ _ ⇒ _` kall_tac >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    rw[Once type_tcexp_cases] >> gvs[]
    >- ( (* BoolCase *)
      irule type_tcexp_BoolCase >> gvs[] >> rw[]
      >- (
        qsuff_tac `MAP FST css = MAP FST css'` >> rw[]
        >- gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM] >>
        gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2] >> rw[] >>
        last_x_assum drule >> first_x_assum drule >> rpt (pairarg_tac >> gvs[])
        )
      >- (
        gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> rw[] >>
        ntac 2 $ (first_x_assum drule >> strip_tac) >>
        rpt (pairarg_tac >> gvs[])
        )
      >- (
        first_x_assum irule >> goal_assum $ drule_at Any >>
        unabbrev_all_tac >> gvs[ctxt_rel_def]
        )
      )
    >- ( (* TupleCase *)
      irule type_tcexp_TupleCase >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
      irule_at Any EQ_REFL >> first_x_assum $ irule_at Any >> simp[] >>
      first_x_assum $ irule_at Any >> simp[] >> goal_assum $ drule_at Any >>
      unabbrev_all_tac >> gvs[ctxt_rel_def]
      )
    >- ( (* ExceptionCase *)
      irule type_tcexp_ExceptionCase >> gvs[] >> rw[]
      >- (
        qsuff_tac `MAP FST css = MAP FST css'` >> rw[]
        >- gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM] >>
        gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2] >> rw[] >>
        last_x_assum drule >> first_x_assum drule >> rpt (pairarg_tac >> gvs[])
        )
      >- (
        gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> rw[] >>
        ntac 2 $ (first_x_assum drule >> strip_tac) >>
        rpt (pairarg_tac >> gvs[])
        )
      >- (
        first_x_assum irule >> goal_assum $ drule_at Any >>
        unabbrev_all_tac >> gvs[ctxt_rel_def]
        )
      )
    >- ( (* DataCase *)
      irule type_tcexp_Case >> gvs[] >> rpt $ goal_assum $ drule_at Any >>
      gvs[EXISTS_PROD] >> gvs[PULL_EXISTS] >>
      `MAP FST css = MAP FST css'` by (
        gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2] >> rw[] >>
        first_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
      first_x_assum $ irule_at Any >> goal_assum $ drule_at Any >> rpt conj_tac
      >- (unabbrev_all_tac >> gvs[ctxt_rel_def])
      >- (
        namedCases_on `usopt` ["","us"] >> gvs[] >>
        PairCases_on `us` >> gvs[] >> pairarg_tac >> gvs[] >>
        last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >> rw[]
        >- (last_x_assum irule >> unabbrev_all_tac >> gvs[SUBSET_DEF])
        >- gvs[SUBSET_DEF]
        >- (gvs[SUBSET_DEF] >> metis_tac[])
        >- gvs[SUBSET_DEF]
        >- gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
        >- gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
        >- (Cases_on `css` >> gvs[])
        )
      >- (
        reverse $ namedCases_on `usopt` ["","us"] >> gvs[]
        >- (PairCases_on `us` >> gvs[] >> pairarg_tac >> gvs[]) >>
        gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
        )
      >- (
        gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> rw[] >>
        ntac 2 $ (first_x_assum drule >> strip_tac) >>
        rpt (pairarg_tac >> gvs[])
        )
      )
    )
  >- ( (* Annot *)
    rpt (pairarg_tac >> gvs[]) >> gvs[tcexp_of_def] >>
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    once_rewrite_tac[type_tcexp_cases] >> rw[] >>
    first_x_assum irule >> simp[PULL_EXISTS] >> rpt $ goal_assum $ drule_at Any
    )
  >- ( (* NestedCase *)
    qpat_x_assum `type_tcexp _ _ _ _ _ _` mp_tac >>
    simp[Once type_tcexp_cases]
    )
  >- ( (* list case *)
    rpt (pairarg_tac >> gvs[]) >> rw[]
    >- (
      last_x_assum irule >> simp[PULL_EXISTS] >>
      rpt $ goal_assum $ drule_at Any >> gvs[ctxt_rel_def]
      ) >>
    last_x_assum irule >> simp[PULL_EXISTS] >>
    rpt $ goal_assum $ drule_at Any >> gvs[ctxt_rel_def] >>
    gvs[EVERY_MEM, avoid_ok_def] >>
    drule_all $ cj 1 freshen_aux_mono >> strip_tac >>
    drule_all $ cj 2 freshen_aux_mono >> strip_tac >>
    gvs[SUBSET_DEF] >> metis_tac[]
    )
QED


(********** boundvars_of **********)

Theorem boundvars_of_NestedCase_free:
  NestedCase_free ce ⇒
  vars_ok (boundvars_of ce) ∧
  set_of (boundvars_of ce) = boundvars (exp_of ce)
Proof
  Induct_on `ce` using boundvars_of_ind >>
  simp[boundvars_of_def, exp_of_def, boundvars_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >> strip_tac
  >- ( (* Prim *)
    qmatch_goalsub_abbrev_tac `FOLDR f acc` >>
    qmatch_goalsub_abbrev_tac `BIGUNION s` >>
    qsuff_tac
      `∀acc. EVERY NestedCase_free ces ∧ vars_ok acc ⇒ vars_ok (FOLDR f acc ces) ∧
        set_of (FOLDR f acc ces) = BIGUNION s ∪ set_of acc`
    >- (unabbrev_all_tac >> gvs[SF ETA_ss]) >>
    qpat_x_assum `Abbrev (acc = _)` kall_tac >> gvs[Abbr `s`] >>
    Induct_on `ces` >> rw[] >> unabbrev_all_tac >> gvs[] >>
    simp[AC UNION_ASSOC UNION_COMM]
    )
  >- ( (* App *)
    simp[boundvars_Apps] >>
    qmatch_goalsub_abbrev_tac `FOLDR f acc` >>
    qmatch_goalsub_abbrev_tac `BIGUNION s` >>
    qsuff_tac
      `∀acc. EVERY NestedCase_free ces ∧ vars_ok acc ⇒ vars_ok (FOLDR f acc ces) ∧
        set_of (FOLDR f acc ces) = BIGUNION s ∪ set_of acc`
    >- (
      unabbrev_all_tac >> gvs[EVERY_MEM] >>
      disch_then $ qspec_then `boundvars_of ce` mp_tac >> rw[] >>
      simp[AC UNION_ASSOC UNION_COMM]
      ) >>
    qpat_x_assum `Abbrev (acc = _)` kall_tac >> gvs[Abbr `s`] >>
    Induct_on `ces` >> rw[] >> unabbrev_all_tac >> gvs[] >>
    simp[AC UNION_ASSOC UNION_COMM]
    )
  >- simp[boundvars_Lams] (* Lams *)
  >- (rw[EXTENSION] >> metis_tac[]) (* Let *)
  >- ( (* Letrec *)
    qmatch_goalsub_abbrev_tac `FOLDR f acc` >>
    qmatch_goalsub_abbrev_tac `BIGUNION s` >>
    qsuff_tac
      `∀acc. EVERY NestedCase_free (MAP SND fns) ∧ vars_ok acc ⇒
        vars_ok (FOLDR f acc fns) ∧
        set_of (FOLDR f acc fns) =
          set (MAP (λ(f,e). explode f) fns) ∪ BIGUNION s ∪ set_of acc`
    >- (
      unabbrev_all_tac >> gvs[SF ETA_ss] >>
      disch_then $ qspec_then `boundvars_of ce` mp_tac >> rw[] >>
      simp[AC UNION_ASSOC UNION_COMM, LAMBDA_PROD]
      ) >>
    qpat_x_assum `Abbrev (acc = _)` kall_tac >> gvs[Abbr `s`] >>
    Induct_on `fns` >> unabbrev_all_tac >> gvs[] >>
    PairCases >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
    ntac 4 $ strip_tac >>
    last_x_assum drule >> strip_tac >> gvs[] >>
    rw[EXTENSION] >> metis_tac[]
    )
  >- ( (* Case *)
    simp[COND_RAND] >>
    irule_at Any vars_ok_union >>
    DEP_REWRITE_TAC[set_of_var_union] >> csimp[] >>
    simp[boundvars_rows_of] >>
    simp[AC UNION_ASSOC UNION_COMM, AC CONJ_ASSOC CONJ_COMM] >>
    conj_tac >- (rpt CASE_TAC >> gvs[]) >>
    simp[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    qmatch_goalsub_abbrev_tac `FOLDR f acc` >>
    qmatch_goalsub_abbrev_tac `BIGUNION s` >>
    `∀acc. vars_ok acc ⇒ vars_ok (FOLDR f acc css) ∧
      set_of (FOLDR f acc css) = BIGUNION s ∪ set_of acc` by (
      qpat_x_assum `Abbrev (acc = _)` kall_tac >> gvs[Abbr `s`] >>
      last_x_assum assume_tac >> ntac 4 $ last_x_assum kall_tac >>
      qpat_x_assum `OPTION_ALL _ _` kall_tac >>
      Induct_on `css` >> unabbrev_all_tac >> gvs[SF ETA_ss] >>
      PairCases >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      ntac 2 strip_tac >> gen_tac >> strip_tac >>
      last_x_assum drule_all >> strip_tac >> gvs[] >>
      rw[EXTENSION] >> metis_tac[]
      ) >>
    unabbrev_all_tac >> simp[] >>
    namedCases_on `us` ["","us'"] >> gvs[]
    >- (rw[EXTENSION] >> metis_tac[]) >>
    PairCases_on `us'` >> simp[IfDisj_def] >> gvs[] >>
    rw[EXTENSION] >> metis_tac[]
    )
QED

Theorem boundvars_of_SUBSET:
  vars_ok (boundvars_of ce) ∧
  boundvars (exp_of ce) ⊆ set_of (boundvars_of ce)
Proof
  Induct_on `ce` using boundvars_of_ind >>
  simp[boundvars_of_def, exp_of_def, boundvars_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY]
  >- ( (* Prim *)
    qmatch_goalsub_abbrev_tac `FOLDR f acc` >>
    qmatch_goalsub_abbrev_tac `BIGUNION s` >>
    qsuff_tac
      `∀acc. vars_ok acc ⇒ vars_ok (FOLDR f acc ces) ∧
        BIGUNION s ∪ set_of acc ⊆ set_of (FOLDR f acc ces)`
    >- (unabbrev_all_tac >> gvs[SF ETA_ss]) >>
    qpat_x_assum `Abbrev (acc = _)` kall_tac >> gvs[Abbr `s`] >>
    Induct_on `ces` >> rw[] >> unabbrev_all_tac >> gvs[SUBSET_DEF]
    )
  >- ( (* App *)
    simp[boundvars_Apps] >>
    qmatch_goalsub_abbrev_tac `FOLDR f acc` >>
    qmatch_goalsub_abbrev_tac `BIGUNION s` >>
    qsuff_tac
      `∀acc. vars_ok acc ⇒ vars_ok (FOLDR f acc ces) ∧
        BIGUNION s ∪ set_of acc ⊆ set_of (FOLDR f acc ces)`
    >- (
      unabbrev_all_tac >> gvs[] >>
      disch_then $ qspec_then `boundvars_of ce` mp_tac >> rw[] >> gvs[SUBSET_DEF]
      ) >>
    qpat_x_assum `Abbrev (acc = _)` kall_tac >> gvs[Abbr `s`] >>
    Induct_on `ces` >> rw[] >> unabbrev_all_tac >> gvs[SUBSET_DEF]
    )
  >- ( (* Lams *)
    simp[boundvars_Lams] >> gvs[SUBSET_DEF]
    )
  >- gvs[SUBSET_DEF] (* Let *)
  >- ( (* Letrec *)
    qmatch_goalsub_abbrev_tac `FOLDR f acc` >>
    qmatch_goalsub_abbrev_tac `BIGUNION s` >>
    qsuff_tac
      `∀acc. vars_ok acc ⇒
        vars_ok (FOLDR f acc fns) ∧
        set (MAP (λ(f,e). explode f) fns) ∪ BIGUNION s ∪ set_of acc ⊆
          set_of (FOLDR f acc fns)`
    >- (
      unabbrev_all_tac >> gvs[SF ETA_ss] >>
      disch_then $ qspec_then `boundvars_of ce` mp_tac >> rw[] >>
      gvs[SUBSET_DEF, LAMBDA_PROD]
      ) >>
    qpat_x_assum `Abbrev (acc = _)` kall_tac >> gvs[Abbr `s`] >>
    Induct_on `fns` >> unabbrev_all_tac >> gvs[] >>
    PairCases >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
    ntac 4 $ strip_tac >>
    last_x_assum drule >> strip_tac >> gvs[SUBSET_DEF]
    )
  >- ( (* Case *)
    simp[COND_RAND] >>
    irule_at Any vars_ok_union >>
    DEP_REWRITE_TAC[set_of_var_union] >> csimp[] >>
    simp[boundvars_rows_of] >>
    simp[AC UNION_ASSOC UNION_COMM, AC CONJ_ASSOC CONJ_COMM] >>
    conj_tac >- (rpt CASE_TAC >> gvs[]) >>
    simp[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    qmatch_goalsub_abbrev_tac `FOLDR f acc` >>
    qmatch_goalsub_abbrev_tac `BIGUNION s` >>
    `∀acc. vars_ok acc ⇒ vars_ok (FOLDR f acc css) ∧
      BIGUNION s ∪ set_of acc ⊆ set_of (FOLDR f acc css)` by (
      qpat_x_assum `Abbrev (acc = _)` kall_tac >> gvs[Abbr `s`] >>
      last_x_assum assume_tac >> ntac 3 $ last_x_assum kall_tac >>
      Induct_on `css` >> unabbrev_all_tac >> gvs[SF ETA_ss] >>
      PairCases >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      strip_tac >> gen_tac >> strip_tac >>
      last_x_assum drule_all >> strip_tac >> gvs[] >> gvs[SUBSET_DEF]) >>
    unabbrev_all_tac >> simp[] >>
    namedCases_on `us` ["","us'"] >> gvs[]
    >- gvs[SUBSET_DEF] >>
    PairCases_on `us'` >> simp[IfDisj_def] >> gvs[SUBSET_DEF]
    )
  >- ( (* NestedCase *)
    irule_at Any vars_ok_union >>
    DEP_REWRITE_TAC[set_of_var_union] >> csimp[] >>
    qmatch_goalsub_abbrev_tac `FOLDR f acc` >>
    simp[LIST_TO_SET_MAP, cepat_vars_l_correct] >>
    `∀acc. vars_ok acc ⇒ vars_ok (FOLDR f acc pces) ∧
      BIGUNION $ set $ MAP
        (λ(p,e). boundvars (exp_of e) ∪ IMAGE explode (cepat_vars p)) pces ⊆
      set_of (FOLDR f acc pces)` by (
      qpat_x_assum `Abbrev (acc = _)` kall_tac >>
      last_x_assum assume_tac >> ntac 4 $ last_x_assum kall_tac >>
      Induct_on `pces` >> unabbrev_all_tac >> gvs[SF ETA_ss] >>
      PairCases >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      strip_tac >> gen_tac >> strip_tac >>
      last_x_assum drule_all >> strip_tac >> gvs[SUBSET_DEF] >>
      gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> simp[cepat_vars_l_correct]) >>
    pop_assum $ qspec_then `acc` assume_tac >> gvs[Abbr `acc`] >> rw[]
    >- (
      irule SUBSET_TRANS >> irule_at Any boundvars_FST_patguards_SUBSET >>
      simp[SUBSET_DEF]
      )
    >- (
      irule SUBSET_TRANS >> irule_at Any boundvars_FOLDR_Let_SUBSET >>
      simp[AC CONJ_ASSOC CONJ_COMM] >> conj_tac >- gvs[SUBSET_DEF] >> rw[]
      >- (
        simp[SUBSET_DEF, PULL_EXISTS, MEM_MAP] >> gen_tac >> strip_tac >>
        PairCases_on `y` >> gvs[] >> Cases_on `patguards [Var (explode x),p]` >>
        drule patguards_binds_pvars >> gvs[MEM_MAP, EXTENSION, EXISTS_PROD] >>
        metis_tac[]
        )
      >- (
        irule SUBSET_TRANS >> irule_at Any boundvars_SND_patguards_SUBSET >>
        simp[]
        )
      )
    >- (
      irule SUBSET_TRANS >> irule_at Any boundvars_nested_rows_SUBSET >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[SUBSET_DEF]
      )
    >- gvs[SUBSET_DEF]
    )
QED


(****************************** Top-level theorems ******************************)

Definition avoid_set_ok_def:
  avoid_set_ok avoid (ce:'a cexp) ⇔
    vars_ok avoid ∧
    ∀x. x ∈ freevars (exp_of ce) ∪ boundvars (exp_of ce)
      ⇒ ∃v. lookup (FST avoid) (implode x) = SOME v
End

Theorem avoid_set_ok_avoid_ok:
  avoid_set_ok avoid ce ⇔ avoid_ok avoid ce
Proof
  rw[avoid_set_ok_def, avoid_ok_def] >>
  simp[allvars_thm, SUBSET_DEF] >> eq_tac >> strip_tac >> gvs[] >> gen_tac
  >- (
    `∃x'. x = explode x'` by (qexists `implode x` >> simp[]) >>
    strip_tac >> gvs[] >> res_tac >> simp[GSYM contains_var_in_set_of] >>
    PairCases_on `avoid` >> simp[contains_var_def] >> fs[]
    ) >>
  gvs[SF DNF_ss] >> rw[] >> first_x_assum drule >>
  `∃x'. x = explode x'` by (qexists `implode x` >> simp[]) >> gvs[] >>
  simp[GSYM contains_var_in_set_of] >>
  PairCases_on `avoid` >> gvs[contains_var_def] >> CASE_TAC >> gvs[]
QED

Theorem avoid_set_ok_boundvars_of:
  closed (exp_of x) ⇒ avoid_set_ok (boundvars_of x) x
Proof
  rw[closed_def, avoid_set_ok_def] >>
  qspec_then `x` assume_tac $ GEN_ALL boundvars_of_SUBSET >> gvs[] >>
  gvs[SUBSET_DEF] >> first_x_assum drule >> strip_tac >>
  `∃y. x' = explode y` by (qexists `implode x'` >> simp[]) >>
  gvs[GSYM contains_var_in_set_of] >>
  Cases_on `boundvars_of x` >> gvs[contains_var_def] >>
  FULL_CASE_TAC >> gvs[]
QED

Theorem freshen_cexp_letrecs_distinct:
  freshen_cexp e b = (e1,s) ∧ vars_ok b ∧
  letrecs_distinct (exp_of e)
  ⇒ letrecs_distinct (exp_of e1)
Proof
  rw[freshen_cexp_def] >>
  irule $ cj 1 freshen_aux_letrecs_distinct >> rpt $ goal_assum $ drule_at Any
QED

Theorem fresh_cexp_subset:
  freshen_cexp x ns = (e,ns1) ∧ vars_ok ns ⇒
  set_of ns ⊆ set_of ns1 ∧ vars_ok ns1
Proof
  simp[freshen_cexp_def] >> strip_tac >>
  drule_all $ cj 1 freshen_aux_mono >> simp[]
QED

Theorem freshen_cexp_correctness:
  ∀ce avoid ce' avoid'.
    freshen_cexp ce avoid = (ce',avoid') ∧ avoid_set_ok avoid ce ∧
    NestedCase_free ce ∧ letrecs_distinct (exp_of ce) ∧ cexp_wf ce
  ⇒ exp_of ce ≅ exp_of ce' ∧ avoid_set_ok avoid' ce' ∧ barendregt (exp_of ce') ∧
    (freevars $ exp_of ce' = freevars $ exp_of ce) ∧
    cns_arities ce' = cns_arities ce ∧ cexp_wf ce' ∧ NestedCase_free ce'
Proof
  rpt gen_tac >> strip_tac >> gvs[avoid_set_ok_avoid_ok] >>
  drule_all freshen_cexp_freshen_global >> strip_tac >>
  drule freshen_global_freshen_stack >> strip_tac >>
  dxrule freshen_stack_freshen_subst >> simp[] >>
  impl_tac >- gvs[avoid_ok_def, allvars_thm] >> strip_tac >>
  dxrule freshen_subst_exp_alpha >>
  impl_tac >- gvs[avoid_ok_def] >> strip_tac >>
  irule_at Any exp_alpha_exp_eq >> simp[] >>
  drule exp_alpha_freevars >> strip_tac >> simp[] >>
  gvs[freshen_cexp_def] >>
  drule_all $ cj 1 freshen_aux_avoid_ok >> strip_tac >> simp[] >>
  drule_all $ cj 1 freshen_aux_cns_arities >> strip_tac >> simp[] >>
  drule $ cj 1 freshen_aux_cexp_wf >> impl_tac >- gvs[avoid_ok_def] >> strip_tac >>
  drule $ cj 1 freshen_aux_NestedCase_free >> rw[] >>
  simp[barendregt_def] >>
  irule_at Any freshen_global_unique_boundvars >> goal_assum drule >> simp[] >>
  irule DISJOINT_SUBSET >> irule_at Any freshen_global_boundvars >>
  goal_assum drule >> gvs[avoid_ok_def, allvars_thm]
QED

Theorem freshen_cexp_preserves_typing:
  ∀ce avoid ce' avoid' ns db st env t.
    freshen_cexp ce avoid = (ce',avoid') ∧ avoid_set_ok avoid ce ∧
    type_tcexp ns db st env (tcexp_of ce) t
  ⇒ type_tcexp ns db st env (tcexp_of ce') t
Proof
  rw[freshen_cexp_def] >>
  irule $ cj 1 freshen_aux_preserves_typing >>
  rpt $ goal_assum $ drule_at Any >> gvs[avoid_set_ok_avoid_ok] >>
  rw[ctxt_rel_def]
QED

Theorem freshen_cexp_preserves_wf:
  ∀ce avoid ce' avoid'.
    freshen_cexp ce avoid = (ce',avoid') ∧ avoid_set_ok avoid ce
  ⇒ (NestedCase_free ce ⇒ NestedCase_free ce') ∧
    (letrecs_distinct (exp_of ce) ⇒ letrecs_distinct (exp_of ce')) ∧
    (cexp_wf ce ⇒ cexp_wf ce')
Proof
  rpt gen_tac >> strip_tac >> gvs[freshen_cexp_def] >>
  drule $ cj 1 freshen_aux_NestedCase_free >> strip_tac >> simp[] >>
  drule $ cj 1 freshen_aux_letrecs_distinct >> strip_tac >> simp[] >>
  drule $ cj 1 freshen_aux_cexp_wf >> strip_tac >> simp[] >>
  gvs[avoid_set_ok_def]
QED

(**********)

val _ = export_theory();
