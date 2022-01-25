open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory stringTheory optionTheory pred_setTheory
     listTheory rich_listTheory alistTheory finite_mapTheory sptreeTheory;
open mlmapTheory;
open pure_miscTheory pure_typingTheory pure_typingPropsTheory
     pure_tcexpTheory pure_inference_commonTheory pure_unificationTheory
     pure_inferenceTheory pure_inferencePropsTheory pure_inference_modelTheory;

val _ = new_theory "pure_inferenceProof";


(******************** Trivial results ********************)

Triviality isubst_pure_apply_subst_MAP_itype_of:
  ∀sub its it.
    isubst (MAP itype_of its) (pure_apply_subst sub it) =
    pure_apply_subst ((isubst (MAP itype_of its)) o_f sub) (isubst (MAP itype_of its) it)
Proof
  rw[] >> DEP_REWRITE_TAC[isubst_pure_apply_subst] >> simp[MEM_MAP, PULL_EXISTS]
QED

Triviality pure_apply_subst_isubst_MAP_lemma:
  ∀it ts sub. (∀v. v ∈ FRANGE sub ⇒ DISJOINT (pure_vars v) (FDOM sub)) ⇒
    pure_apply_subst sub (isubst (MAP (pure_apply_subst sub) ts) it) =
    pure_apply_subst sub (isubst ts it)
Proof
  recInduct itype_ind >> rw[isubst_def, pure_apply_subst, EL_MAP] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
  irule pure_apply_subst_unchanged >>
  qspecl_then [`EL n ts`,`sub`] mp_tac pure_vars_pure_apply_subst_SUBSET >>
  simp[SUBSET_DEF, PULL_EXISTS, DISJOINT_ALT] >> rw[] >>
  first_x_assum drule >> rw[] >> gvs[] >>
  first_x_assum drule >> simp[DISJOINT_ALT]
QED

Triviality pure_vars_pure_walkstar_SUBSET_lemma:
  ∀sub it s. pure_wfs sub ⇒
  ((∀n. n ∈ pure_vars it ⇒ pure_vars (pure_walkstar sub (CVar n)) ⊆ s) ⇔
   pure_vars (pure_walkstar sub it) ⊆ s)
Proof
  simp[GSYM PULL_FORALL] >> gen_tac >> strip_tac >>
  qspec_then `sub` mp_tac pure_walkstar_alt_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[pure_walkstar_alt, pure_vars] >>
  gvs[BIGUNION_SUBSET, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF,
      MEM_MAP, PULL_EXISTS, EQ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM] >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >> rw[] >> res_tac)
  >- (first_x_assum irule >> goal_assum drule >> simp[])
  >- (first_x_assum irule >> simp[] >> rw[] >> res_tac)
  >- (first_x_assum irule >> goal_assum drule >> simp[])
QED

Triviality pure_vars_pure_apply_subst_SUBSET_lemma:
  ∀sub it s.
  ((∀n. n ∈ pure_vars it ⇒ pure_vars (pure_apply_subst sub (CVar n)) ⊆ s) ⇔
   pure_vars (pure_apply_subst sub it) ⊆ s)
Proof
  gen_tac >> recInduct itype_ind >> rw[pure_apply_subst, pure_vars] >>
  gvs[BIGUNION_SUBSET, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF,
      MEM_MAP, PULL_EXISTS, EQ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM] >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >> rw[] >> res_tac)
  >- (first_x_assum irule >> goal_assum drule >> simp[])
  >- (first_x_assum irule >> simp[] >> rw[] >> res_tac)
  >- (first_x_assum irule >> goal_assum drule >> simp[])
QED


(******************** Lemmas ********************)

Theorem minfer_freedbvars:
  ∀ns mset cexp as cs it.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns
  ⇒ freedbvars it = {}
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[freedbvars_def] >>
  simp[LIST_TO_SET_EQ_SING, DISJ_EQ_IMP] >> rw[]
  >- (
    gvs[LIST_REL_EL_EQN, EVERY_MAP, EVERY_MEM] >> rw[MEM_EL] >>
    first_x_assum drule >> simp[EL_ZIP]
    )
  >- simp[EVERY_MAP, freedbvars_def]
  >- (
    simp[freedbvars_iFunctions, MAP_MAP_o, combinTheory.o_DEF, freedbvars_def] >>
    simp[LIST_TO_SET_EQ_SING, DISJ_EQ_IMP, EVERY_MAP]
    )
  >- (
    Cases_on `tys` >> gvs[] >> Cases_on `cases` >> gvs[] >>
    rpt (pairarg_tac >> gvs[])
    )
  >- (
    reverse $ Cases_on `tys` >> gvs[]
    >- (Cases_on `cases` >> gvs[] >> rpt (pairarg_tac >> gvs[])) >>
    PairCases_on `ns` >> gvs[namespace_ok_def, oEL_THM, EVERY_EL] >>
    last_x_assum drule >> simp[]
    )
QED

Theorem minfer_msets:
  ∀ns mset cexp as cs it tsub vars tsup.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns ∧
    mImplicit tsub vars tsup ∈ cs
  ⇒ mset ⊆ vars
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[LIST_REL_EL_EQN, EL_ZIP, MEM_EL, MAP2_MAP, EL_MAP]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (imp_res_tac infer_atom_op_LENGTH >> gvs[MAP2_MAP, EL_MAP, EL_ZIP])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    first_x_assum drule >> pairarg_tac >> gvs[] >> strip_tac >>
    pop_assum drule >> simp[]
    )
  >- (first_x_assum drule >> pairarg_tac >> gvs[])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    ntac 2 $ first_x_assum drule >> pairarg_tac >> gvs[] >>
    ntac 2 strip_tac >> reverse $ gvs[] >- metis_tac[] >>
    qpat_x_assum `MEM _ _` mp_tac >>
    DEP_REWRITE_TAC[MAP2_MAP] >> simp[MEM_MAP, MEM_ZIP, EXISTS_PROD] >>
    reverse conj_tac >- (strip_tac >> gvs[]) >>
    PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
    qsuff_tac `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) ns0)`
    >- (
      rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
      rev_drule ALOOKUP_ALL_DISTINCT_MEM >> disch_then drule >> simp[]
      ) >>
    drule $ iffRL sortingTheory.PERM_MEM_EQ >>
    simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
    simp[Once MEM_EL, PULL_EXISTS] >>
    disch_then drule >> simp[DISJ_IMP_THM] >> strip_tac >> gvs[] >>
    last_x_assum $ qspec_then `"Subscript"` mp_tac >>
    simp[pure_configTheory.reserved_cns_def] >>
    imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> goal_assum drule
    )
  >- metis_tac[]
  >- (
    last_x_assum drule >> pairarg_tac >> gvs[] >> strip_tac >>
    first_x_assum drule >> simp[] >>
    strip_tac >> reverse $ gvs[] >- metis_tac[] >>
    qpat_x_assum `MEM _ _` mp_tac >>
    DEP_REWRITE_TAC[MAP2_MAP] >> simp[MEM_MAP, MEM_ZIP, EXISTS_PROD] >>
    reverse conj_tac >- (strip_tac >> gvs[]) >>
    PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
    `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)` by (
      drule $ iffRL sortingTheory.PERM_MEM_EQ >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
      disch_then irule >> simp[MEM_EL] >> goal_assum drule >> simp[]) >>
    gvs[MEM_MAP, EXISTS_PROD] >>
    drule_at (Pos last) ALOOKUP_ALL_DISTINCT_MEM >> impl_tac >> simp[] >>
    gvs[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    irule ALL_DISTINCT_FLAT_IMP >> goal_assum drule >>
    simp[MEM_MAP, EXISTS_PROD] >> irule_at Any EQ_REFL >> simp[MEM_EL] >>
    gvs[oEL_THM] >> goal_assum drule >> simp[]
    )
QED

Theorem minfer_pure_vars:
  ∀ns mset cexp as cs it v.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns ∧
    v ∈ pure_vars it
  ⇒ v ∈ new_vars as cs Exception
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[pure_vars, new_vars_def, pure_vars_iFunctions] >>
  gvs[LIST_REL_EL_EQN, EL_ZIP, MEM_EL, MAP2_MAP, EL_MAP,
      PULL_EXISTS, SF CONJ_ss, pure_vars]
  >- (
    first_x_assum drule >> strip_tac >> pop_assum drule >> reverse $ rw[]
    >- (disj2_tac >> rpt $ goal_assum drule) >>
    disj1_tac >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, FLOOKUP_DEF,
        PULL_EXISTS, GSYM CONJ_ASSOC] >>
    rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
    )
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum drule) >>
    rpt disj1_tac >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, PULL_EXISTS] >>
    Cases_on `FLOOKUP as k` >> gvs[]
    >- (qexistsl_tac [`s`,`k`] >> simp[])
    >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
    )
  >- (disj2_tac >> rpt disj1_tac >> irule_at Any EQ_REFL >> simp[])
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum drule) >>
    rpt disj1_tac >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, PULL_EXISTS] >>
    Cases_on `FLOOKUP as k` >> gvs[]
    >- (qexistsl_tac [`s`,`k`] >> simp[])
    >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
    )
  >- (disj2_tac >> disj1_tac >> disj2_tac >> irule_at Any EQ_REFL >> simp[])
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (disj2_tac >> rpt disj1_tac >> rpt $ goal_assum drule) >>
    Cases_on `s ∈ FRANGE (FDIFF as (set xs))`
    >- (rpt disj1_tac >> goal_assum drule >> simp[]) >>
    rpt disj2_tac >> gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF] >>
    first_x_assum drule >> rw[MEM_EL] >>
    qexists_tac `n` >> simp[get_massumptions_def] >>
    goal_assum $ drule_at Any >> simp[]
    )
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum drule) >>
    Cases_on `s ∈ FRANGE (as' \\ x)`
    >- (
      rpt disj1_tac >> qpat_x_assum `_ ∈ FRANGE as'` kall_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, DOMSUB_FLOOKUP_THM, PULL_EXISTS] >>
      Cases_on `FLOOKUP as k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x' ∪ s`,`k`] >> simp[])
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] >>
      first_x_assum drule >> rw[] >>
      disj2_tac >> rpt disj1_tac >> simp[get_massumptions_def] >>
      goal_assum $ drule_at Any >> simp[]
      )
    )
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (disj2_tac >> rpt disj1_tac >> goal_assum drule >> simp[]) >>
    simp[FDIFF_maunion] >>
    Cases_on `s ∈ FRANGE (FDIFF as' (set (MAP FST fns)))`
    >- (
      rpt disj1_tac >> qpat_x_assum `_ ∈ FRANGE as'` kall_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FDIFF, PULL_EXISTS] >>
      Cases_on `FLOOKUP as k` >> gvs[] >>
      Cases_on `FLOOKUP (FOLDR maunion FEMPTY ass) k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x'`,`k`] >> simp[])
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF] >> first_x_assum drule >> rw[] >>
      rpt disj2_tac >> gvs[MEM_EL, EL_MAP] >> goal_assum $ drule_at Any >>
      pairarg_tac >> gvs[PULL_EXISTS, pure_vars] >>
      simp[get_massumptions_def, FLOOKUP_maunion] >>
      qexists_tac `v` >> simp[] >> CASE_TAC >> simp[]
      )
    )
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> goal_assum drule >> simp[]) >>
    Cases_on `s ∈ FRANGE (FDIFF as (v INSERT set pvars))`
    >- (
      rpt disj1_tac >> qpat_x_assum `_ ∈ FRANGE as` kall_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FDIFF, PULL_EXISTS] >>
      Cases_on `FLOOKUP as' k` >>  gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF] >> first_x_assum drule >> rw[] >>
      simp[get_massumptions_def, GSYM DISJ_ASSOC]
      >- (ntac 5 disj2_tac >> disj1_tac >> goal_assum $ drule_at Any >> simp[]) >>
      ntac 6 disj2_tac >> disj1_tac >> gvs[MEM_EL] >>
      ntac 2 (goal_assum $ drule_at Any >> simp[])
      )
    )
  >- (
    first_x_assum $ qspec_then `0` mp_tac >>
    impl_keep_tac >- (Cases_on `cases` >> gvs[]) >>
    last_x_assum assume_tac >> last_x_assum $ qspec_then `0` mp_tac >> simp[] >>
    pairarg_tac >> gvs[] >> ntac 2 strip_tac >>
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[]) >>
    Cases_on `s ∈ FRANGE (FDIFF (HD ass) (v INSERT set pvars))`
    >- (
      qpat_x_assum `_ ∈ FRANGE (HD _)` kall_tac >> rpt disj1_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      simp[PULL_EXISTS] >>
      qexists_tac `(case FLOOKUP as k of NONE => {} | SOME s => s) ∪
        BIGUNION ({ s | ∃m. MEM m final_as ∧ FLOOKUP m k = SOME s})` >>
      simp[PULL_EXISTS] >> irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS] >>
      qexists_tac `k` >> simp[GSYM CONJ_ASSOC] >>
      goal_assum drule >> qexists_tac `FDIFF (HD ass) (v INSERT set pvars)` >>
      simp[FLOOKUP_FDIFF] >> conj_asm1_tac >- (Cases_on `final_as` >> gvs[]) >>
      TOP_CASE_TAC >> gvs[]
      >- (goal_assum drule >> gvs[FDOM_FDIFF, FLOOKUP_DEF]) >>
      IF_CASES_TAC >> gvs[] >> irule FALSITY >>
      first_x_assum drule >> gvs[FDOM_FDIFF, FLOOKUP_DEF]
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF, PULL_EXISTS] >>
      first_x_assum drule >> rw[] >>
      rpt disj2_tac >> simp[Once SWAP_EXISTS_THM] >>
      qexists_tac `0` >> simp[]
      >- (
        rpt $ irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS] >>
        simp[get_massumptions_def, pure_vars] >> goal_assum drule >> simp[]
        )
      >- (
        irule_at Any OR_INTRO_THM1 >> irule_at Any OR_INTRO_THM2 >>
        simp[PULL_EXISTS] >> DEP_REWRITE_TAC[MAP2_MAP] >> reverse conj_asm1_tac
        >- (
          simp[MEM_MAP, PULL_EXISTS, MEM_ZIP, pure_vars] >> gvs[MEM_EL] >>
          qexists_tac `n` >> simp[get_massumptions_def] >>
          goal_assum drule >> simp[]
          ) >>
        simp[] >> PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        qsuff_tac `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) ns0)`
        >- (
          rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
          rev_drule ALOOKUP_ALL_DISTINCT_MEM >> disch_then drule >> simp[]
          ) >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
        simp[Once MEM_EL, PULL_EXISTS] >>
        disch_then drule >> simp[DISJ_IMP_THM] >> strip_tac >> gvs[] >>
        first_x_assum $ qspec_then `"Subscript"` mp_tac >>
        simp[pure_configTheory.reserved_cns_def] >>
        imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> goal_assum drule
        )
      )
    )
  >- (
    first_x_assum $ qspec_then `0` mp_tac >> impl_keep_tac
    >- (
      PairCases_on `ns` >> gvs[namespace_ok_def] >>
      gvs[EVERY_EL, oEL_THM] >> last_x_assum drule >> simp[] >> strip_tac >>
      imp_res_tac sortingTheory.PERM_LENGTH >> gvs[] >> Cases_on `cdefs` >> gvs[]
      ) >>
    last_x_assum assume_tac >> last_x_assum $ qspec_then `0` mp_tac >> simp[] >>
    pairarg_tac >> gvs[] >> ntac 2 strip_tac >>
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[]) >>
    Cases_on `s ∈ FRANGE (FDIFF (HD ass) (v INSERT set pvars))`
    >- (
      qpat_x_assum `_ ∈ FRANGE (HD _)` kall_tac >> rpt disj1_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      simp[PULL_EXISTS] >>
      qexists_tac `(case FLOOKUP as k of NONE => {} | SOME s => s) ∪
        BIGUNION ({ s | ∃m. MEM m final_as ∧ FLOOKUP m k = SOME s})` >>
      simp[PULL_EXISTS] >> irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS] >>
      qexists_tac `k` >> simp[GSYM CONJ_ASSOC] >>
      goal_assum drule >> qexists_tac `FDIFF (HD ass) (v INSERT set pvars)` >>
      simp[FLOOKUP_FDIFF] >> conj_asm1_tac >- (Cases_on `final_as` >> gvs[]) >>
      TOP_CASE_TAC >> gvs[]
      >- (goal_assum drule >> gvs[FDOM_FDIFF, FLOOKUP_DEF]) >>
      IF_CASES_TAC >> gvs[] >> irule FALSITY >>
      first_x_assum drule >> gvs[FDOM_FDIFF, FLOOKUP_DEF]
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF, PULL_EXISTS] >>
      first_x_assum drule >> rw[] >>
      rpt disj2_tac >> simp[Once SWAP_EXISTS_THM] >>
      qexists_tac `0` >> simp[]
      >- (
        rpt $ irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS] >>
        simp[get_massumptions_def, pure_vars] >> goal_assum drule >> simp[]
        )
      >- (
        irule_at Any OR_INTRO_THM1 >> irule_at Any OR_INTRO_THM2 >>
        simp[PULL_EXISTS] >> DEP_REWRITE_TAC[MAP2_MAP] >> reverse conj_asm1_tac
        >- (
          simp[MEM_MAP, PULL_EXISTS, MEM_ZIP, pure_vars] >> gvs[MEM_EL] >>
          qexists_tac `n` >> simp[get_massumptions_def] >>
          goal_assum drule >> simp[]
          ) >>
        simp[] >> PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)` by (
          drule $ iffRL sortingTheory.PERM_MEM_EQ >>
          simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
          disch_then irule >> simp[MEM_EL] >> goal_assum drule >> simp[]) >>
        gvs[MEM_MAP, EXISTS_PROD] >>
        drule_at (Pos last) ALOOKUP_ALL_DISTINCT_MEM >> impl_tac >> simp[] >>
        gvs[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        irule ALL_DISTINCT_FLAT_IMP >> goal_assum drule >>
        simp[MEM_MAP, EXISTS_PROD] >> irule_at Any EQ_REFL >> simp[MEM_EL] >>
        gvs[oEL_THM] >> goal_assum drule >> simp[]
        )
      )
    )
QED

Theorem CARD_fmap_injection:
  ∀fm. CARD (FDOM fm) = CARD (FRANGE fm) ⇔
    (∀k1 k2 v. FLOOKUP fm k1 = SOME v ∧ FLOOKUP fm k2 = SOME v ⇒ k1 = k2)
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    qspecl_then [`$' fm`,`FDOM fm`]
      mp_tac $ GEN_ALL miscTheory.CARD_IMAGE_EQ_BIJ >>
    simp[FRANGE_ALT_DEF] >> gvs[BIJ_DEF, INJ_DEF, FLOOKUP_DEF]
    )
  >- (
    simp[FRANGE_ALT_DEF] >> irule $ GSYM INJ_CARD_IMAGE_EQ >> simp[] >>
    qexists_tac `FRANGE fm` >> simp[FRANGE_ALT_DEF] >>
    gvs[INJ_DEF, FLOOKUP_DEF]
    )
QED

Theorem CARD_has_fmap_linv:
  ∀f. (∃g. fmap_linv f g) ⇔ CARD (FDOM f) = CARD (FRANGE f)
Proof
  rw[miscTheory.has_fmap_linv_inj, CARD_fmap_injection] >>
  simp[INJ_DEF, FLOOKUP_DEF, FRANGE_DEF] >> eq_tac >> rw[] >>
  goal_assum drule >> gvs[]
QED

Theorem fmap_linv_sym:
  ∀f g. fmap_linv f g ⇔ fmap_linv g f
Proof
  rw[miscTheory.fmap_linv_def] >> eq_tac >> rw[] >>
  gvs[FLOOKUP_DEF, FRANGE_DEF, EXTENSION] >> metis_tac[]
QED

Theorem fmap_linv_alt_def:
  fmap_linv f g ⇔
    FDOM f = FRANGE g ∧
    FDOM g = FRANGE f ∧
    (∀x. x ∈ FDOM f ⇒ g ' (f ' x) = x) ∧
    (∀x. x ∈ FDOM g ⇒ f ' (g ' x) = x)
Proof
  eq_tac >> strip_tac
  >- (imp_res_tac fmap_linv_sym >> gvs[miscTheory.fmap_linv_def, FLOOKUP_DEF])
  >- (
    rw[miscTheory.fmap_linv_def, FLOOKUP_DEF] >>
    last_x_assum $ assume_tac o GSYM >> gvs[] >>
    simp[FRANGE_DEF] >> goal_assum drule >> simp[]
    )
QED

Theorem pure_apply_subst_split_isubst:
  ∀fm (sub : num |-> itype) it.
    CARD (FDOM fm) = CARD (FRANGE fm) ∧
    count (CARD (FDOM fm)) = FRANGE fm ∧
    FDOM sub ⊆ FDOM fm ∧
    freedbvars it = {}
  ⇒ ∃gm.
      fmap_linv fm gm ∧
      isubst
        (GENLIST (λn. if gm ' n ∈ FDOM sub then sub ' (gm ' n) else CVar (gm ' n))
          (CARD (FDOM fm)))
        (pure_apply_subst (DBVar o_f fm) it) =
      pure_apply_subst sub it
Proof
  rw[] >> drule $ iffRL CARD_has_fmap_linv >> rw[] >>
  goal_assum drule >> qpat_x_assum `_ = {}` mp_tac >>
  qid_spec_tac `it` >> recInduct itype_ind >>
  rw[pure_apply_subst, isubst_def] >> gvs[freedbvars_def] >>
  gvs[LIST_TO_SET_EQ_SING, EVERY_MAP, EVERY_MEM] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, FLOOKUP_o_f] >>
  gvs[miscTheory.fmap_linv_def, FLOOKUP_DEF] >>
  Cases_on `n ∈ FDOM sub` >> Cases_on `n ∈ FDOM fm` >> gvs[SUBSET_DEF, isubst_def] >>
  qsuff_tac `fm ' n < CARD (FRANGE fm)` >> rw[] >>
  gvs[FRANGE_DEF, EXTENSION]
QED


(******************** Definitions/apparatus ********************)

Definition satisfies_def:
  satisfies s (mUnify t1 t2) = (pure_walkstar s t1 = pure_walkstar s t2) ∧

  satisfies s (mInstantiate t (vars, scheme)) = (
    ∃subs.
      LENGTH subs = vars ∧
      pure_walkstar s t = isubst subs (pure_walkstar s scheme)) ∧

  satisfies s (mImplicit tsub vars tsup) = (
    ∃sub.
      DISJOINT (FDOM sub) (pure_vars (pure_walkstar s tsub)) ∧
      DISJOINT (FDOM sub) (BIGUNION (IMAGE (pure_vars o pure_walkstar s o CVar) vars)) ∧
      pure_walkstar s tsub = pure_apply_subst sub (pure_walkstar s tsup))
End

Definition ctxt_rel_def:
  ctxt_rel tdefs db closing sub as ctxt ⇔
    ∀k v. FLOOKUP as k = SOME v ⇒
      ∃vars scheme. ALOOKUP ctxt k = SOME (vars,scheme) ∧
        ∀n. n ∈ v ⇒
          ∃ts.
            LENGTH ts = vars ∧ EVERY (type_ok tdefs db) ts ∧
            itype_of (subst_db 0 ts scheme) =
            pure_apply_subst (itype_of o_f closing) (pure_walkstar sub (CVar n))
End


(******************** Main results ********************)

Theorem inference_constraints_sound:
  ∀ns mset cexp as cs it sub ctxt.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns ∧
    pure_wfs sub ∧
    FINITE mset ∧
    (∀it. it ∈ FRANGE sub ⇒ freedbvars it = ∅ ∧ itype_wf (SND ns) it) ∧
    (∀c. c ∈ cs ⇒ satisfies sub c)
    ⇒ ∀closing t db.
        ctxt_rel (SND ns) db closing sub as ctxt ∧
        (∀n. n ∈ new_vars as cs it ⇒
          pure_vars (pure_apply_subst (itype_of o_f closing)
                        (pure_walkstar sub (CVar n))) = ∅) ∧
        type_of (pure_apply_subst
          (itype_of o_f closing) (pure_walkstar sub it)) = SOME t ∧
        (∀ty. ty ∈ FRANGE closing ⇒ type_ok (SND ns) db ty) ⇒
        type_tcexp ns db [] ctxt (tcexp_of cexp) t
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[tcexp_of_def]
  >- ( (* Var *)
    simp[Once type_tcexp_cases] >>
    gvs[ctxt_rel_def, FLOOKUP_UPDATE] >>
    simp[specialises_def, PULL_EXISTS] >>
    qpat_x_assum `itype_of _ = _` $ assume_tac o GSYM >> gvs[type_of_itype_of] >>
    irule_at Any EQ_REFL >> simp[] >>
    gvs[EVERY_MEM] >> rw[] >>
    first_x_assum drule >> rw[] >>
    irule type_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )
  >- ( (* Tuple *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >>
    gvs[LIST_REL_EL_EQN, EL_ZIP, GSYM CONJ_ASSOC, EL_MAP] >>
    gvs[IMP_CONJ_THM, FORALL_AND_THM] >>
    qpat_x_assum `_ = SOME t` mp_tac >>
    DEP_REWRITE_TAC[cj 5 pure_walkstar_alt] >> rw[pure_apply_subst] >>
    imp_res_tac type_of_SOME_lemma >> gvs[MAP_MAP_o, combinTheory.o_DEF] >>
    drule $ iffLR MAP_EQ_EVERY2 >> rw[] >>
    first_x_assum irule >> simp[] >>
    rpt $ goal_assum $ drule_at Any >> simp[] >> rw[]
    >- (first_x_assum irule >> goal_assum drule >> simp[EL_MEM])
    >- (
      first_x_assum irule >> gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, pure_vars, MEM_MAP,
          FLOOKUP_DEF, PULL_EXISTS] >>
      metis_tac[EL_MEM]
      )
    >- gvs[LIST_REL_EL_EQN]
    >- (
      gvs[ctxt_rel_def] >> rw[] >>
      gvs[FLOOKUP_FOLDR_maunion, PULL_EXISTS, MEM_EL, FLOOKUP_DEF] >>
      first_x_assum drule_all >> strip_tac >> rw[] >>
      first_x_assum drule_all >> simp[]
      )
    )
  >- ( (* Ret *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >> gvs[] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    first_x_assum irule >> rpt $ goal_assum $ drule_at Any >> rw[] >>
    first_x_assum irule >> gvs[new_vars_def, pure_vars] >> metis_tac[]
    )
  >- ( (* Bind *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >> gvs[] >>
    rgs[Once pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >>
    rpt $ goal_assum $ drule_at Any >> simp[] >>
    simp[cj 6 pure_walkstar_alt, cj 8 pure_walkstar_alt,
         pure_apply_subst, type_of_def, SF CONJ_ss] >>
    first_assum $ qspec_then `f1` mp_tac >> impl_tac >- simp[new_vars_def, pure_vars] >>
    simp[Once pure_vars_empty_eq_type_of] >> strip_tac >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as' k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      )
    )
  >- ( (* Raise *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >> gvs[] >>
    rgs[Once pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    last_x_assum $ irule_at Any >>
    rpt $ goal_assum $ drule_at Any >>
    simp[cj 3 pure_walkstar_alt, pure_apply_subst, type_of_def] >> rw[]
    >- (first_x_assum irule >> gvs[new_vars_def, pure_vars] >> metis_tac[]) >>
    simp[type_ok_def, freetyvars_ok_freedbvars, type_wf_itype_wf] >>
    imp_res_tac type_of_SOME >> gvs[] >> reverse conj_tac
    >- (
      irule itype_wf_pure_apply_subst >>
      irule_at Any itype_wf_pure_walkstar >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, GSYM type_wf_itype_wf] >>
      gvs[type_ok_def, itype_wf_def]
      ) >>
    qspecl_then [`pure_walkstar sub (CVar f)`,`itype_of o_f closing`]
      mp_tac freedbvars_pure_apply_subst_SUBSET >>
    qspecl_then [`sub`,`CVar f`] mp_tac freedbvars_pure_walkstar_SUBSET >>
    simp[freedbvars_def] >> rw[SUBSET_DEF, PULL_EXISTS] >>
    first_x_assum drule >> simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
    rw[] >> gvs[] >>
    first_x_assum drule >> rw[] >> gvs[type_ok_def, freetyvars_ok_freedbvars]
    )
  >- ( (* Handle *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >> gvs[] >>
    rgs[Once pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >>
    rpt $ goal_assum $ drule_at Any >>
    simp[cj 3 pure_walkstar_alt, cj 6 pure_walkstar_alt, cj 8 pure_walkstar_alt] >>
    simp[pure_apply_subst, type_of_def] >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as' k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      )
    )
  >- ( (* Act *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >> gvs[] >>
    rgs[Ntimes pure_walkstar_alt 2, pure_apply_subst, type_of_def] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    last_x_assum irule >> rpt $ goal_assum $ drule_at Any >>
    simp[cj 2 pure_walkstar_alt, pure_apply_subst, type_of_def] >> rw[] >>
    first_x_assum irule >> gvs[new_vars_def, pure_vars] >> metis_tac[]
    )
  >- ( (* Alloc *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >> gvs[] >>
    rgs[Ntimes pure_walkstar_alt 2, pure_apply_subst, type_of_def] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    simp[cj 2 pure_walkstar_alt, pure_apply_subst, type_of_def] >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as' k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      )
    )
  >- ( (* Length *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >> gvs[] >>
    rgs[Ntimes pure_walkstar_alt 2, pure_apply_subst, type_of_def] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    simp[cj 7 pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    simp[GSYM PULL_EXISTS, GSYM pure_vars_empty_eq_type_of] >> rw[] >>
    first_x_assum irule >> reverse $ gvs[new_vars_def] >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
    >- metis_tac[] >>
    rpt disj1_tac >> Cases_on `FLOOKUP as k` >> gvs[] >> rpt $ goal_assum drule
    )
  >- ( (* Deref *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >> gvs[] >>
    rgs[Once pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    simp[cj 2 pure_walkstar_alt, cj 7 pure_walkstar_alt] >>
    simp[pure_apply_subst, type_of_def] >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as' k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      )
    )
  >- ( (* Update *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM1 >> gvs[] >>
    rgs[Ntimes pure_walkstar_alt 2, pure_apply_subst, type_of_def] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    ntac 3 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    simp[cj 2 pure_walkstar_alt, cj 7 pure_walkstar_alt] >>
    simp[pure_apply_subst, type_of_def] >>
    `∃t. type_of (pure_apply_subst (itype_of o_f closing)
                    (pure_walkstar sub (CVar f))) = SOME t` by (
      simp[GSYM pure_vars_empty_eq_type_of] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars]) >>
    goal_assum $ drule_at Any >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as k` >> Cases_on `FLOOKUP as' k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ (x' ∪ s)`,`k`] >> simp[])
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as k` >> Cases_on `FLOOKUP as' k` >>
      Cases_on `FLOOKUP as'' k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x'`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ (s ∪ x'')`,`k`] >> simp[])
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> CASE_TAC >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as k` >> Cases_on `FLOOKUP as' k` >>
      Cases_on `FLOOKUP as'' k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x'`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x'`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ (x' ∪ x'')`,`k`] >> simp[])
      )
    )
  >- ( (* True *)
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    simp[Once type_tcexp_cases]
    )
  >- ( (* False *)
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    simp[Once type_tcexp_cases]
    )
  >- ( (* Subscript *)
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    simp[Once type_tcexp_cases]
    )
  >- ( (* Exception *)
    gvs[cj 3 pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    rgs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, satisfies_def] >>
    simp[Once type_tcexp_cases] >> disj1_tac >>
    PairCases_on `ns` >> gvs[LIST_REL_EL_EQN, type_exception_def, EL_MAP, EL_ZIP] >>
    rw[] >> first_x_assum drule >> strip_tac >>
    pop_assum irule >> rpt $ goal_assum $ drule_at Any >> rw[]
    >- (last_x_assum irule >> goal_assum $ drule_at Any >> simp[EL_MEM])
    >- (
      first_x_assum irule >> gvs[new_vars_def, pure_vars]
      >- (
        disj1_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            FLOOKUP_DEF, GSYM CONJ_ASSOC] >>
        rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
        )
       >- (
        disj2_tac >> disj2_tac >> gvs[MAP2_MAP, PULL_EXISTS, MEM_MAP, MEM_ZIP] >>
        rpt $ goal_assum drule >> simp[EL_MEM]
        )
      >- (
        disj2_tac >> disj1_tac >> gvs[MAP2_MAP, PULL_EXISTS, MEM_MAP, MEM_ZIP] >>
        rpt $ goal_assum drule
        )
      )
    >- (
      gvs[MAP2_MAP, MEM_MAP, PULL_EXISTS, MEM_ZIP, satisfies_def] >>
      simp[type_of_itype_of]
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_FOLDR_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >> impl_tac
      >- (gvs[FLOOKUP_DEF] >> goal_assum $ drule_at Any >> simp[EL_MEM]) >>
      strip_tac >> gvs[PULL_EXISTS] >> rw[] >>
      first_x_assum irule >> goal_assum drule >> simp[EL_MEM]
      )
    )
  >- ( (* Cons *)
    rgs[Once pure_walkstar_alt, pure_apply_subst] >>
    rgs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
    rgs[MAP2_MAP, MEM_MAP, PULL_EXISTS, MEM_ZIP, satisfies_def] >>
    drule $ cj 2 type_of_SOME_lemma >> strip_tac >> gvs[] >>
    simp[Once type_tcexp_cases] >>
    PairCases_on `ns` >> gvs[LIST_REL_EL_EQN, EL_MAP, EL_ZIP] >>
    simp[type_cons_def, PULL_EXISTS, oEL_THM, EL_MAP] >>
    imp_res_tac LIST_EQ_REWRITE >> gvs[] >> reverse $ rw[]
    >- (
      rw[EVERY_EL] >> gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_MAP] >>
      first_x_assum drule >> strip_tac >>
      simp[type_ok_def, freetyvars_ok_freedbvars, type_wf_itype_wf] >>
      imp_res_tac type_of_SOME >> gvs[] >> reverse conj_tac
      >- (
        irule itype_wf_pure_apply_subst >> irule_at Any itype_wf_pure_walkstar >>
        simp[GSYM IMAGE_FRANGE, PULL_EXISTS, GSYM type_wf_itype_wf] >>
        gvs[type_ok_def, itype_wf_def]
        ) >>
      qspecl_then [`pure_walkstar sub (CVar $ EL n freshes)`,`itype_of o_f closing`]
        mp_tac freedbvars_pure_apply_subst_SUBSET >>
      qspecl_then [`sub`,`CVar $ EL n freshes`] mp_tac freedbvars_pure_walkstar_SUBSET >>
      simp[freedbvars_def] >> rw[SUBSET_DEF, PULL_EXISTS] >>
      first_x_assum drule >> simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
      rw[] >> gvs[] >>
      first_x_assum drule >> rw[] >> gvs[type_ok_def, freetyvars_ok_freedbvars]
      ) >>
    last_x_assum drule >> strip_tac >>
    pop_assum irule >> rpt $ goal_assum $ drule_at Any >> rw[]
    >- (last_x_assum irule >> goal_assum $ drule_at Any >> simp[EL_MEM])
    >- (
      first_x_assum irule >> gvs[new_vars_def, pure_vars, GSYM DISJ_ASSOC]
      >- (
        disj1_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            FLOOKUP_DEF, GSYM CONJ_ASSOC] >>
        rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
        )
       >- (
        ntac 3 disj2_tac >> disj1_tac >> simp[PULL_EXISTS] >>
        rpt $ goal_assum drule >> simp[EL_MEM]
        )
      >- (
        ntac 2 disj2_tac >> disj1_tac >>
        gvs[MAP2_MAP, PULL_EXISTS, MEM_MAP, MEM_ZIP] >>
        goal_assum $ drule_at Any >> simp[]
        )
      )
    >- (
      gvs[MAP2_MAP, MEM_MAP, PULL_EXISTS, MEM_ZIP, satisfies_def] >>
      DEP_REWRITE_TAC[pure_walkstar_isubst] >> simp[] >>
      simp[pure_apply_subst_isubst_itype_of] >>
      qsuff_tac `∃ts.
        MAP (pure_apply_subst (itype_of o_f closing))
          (MAP (pure_walkstar sub) (MAP CVar freshes)) = MAP itype_of ts`
      >- (
        rw[] >> gvs[] >>
        gvs[MAP_MAP_o, combinTheory.o_DEF, isubst_itype_of, type_of_itype_of] >>
        gvs[SF ETA_ss, miscTheory.map_some_eq]
        ) >>
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_MAP] >> irule_at Any EQ_REFL >> rw[] >>
      first_x_assum drule >> rw[] >> imp_res_tac type_of_SOME >> simp[]
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_FOLDR_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >> impl_tac
      >- (gvs[FLOOKUP_DEF] >> goal_assum $ drule_at Any >> simp[EL_MEM]) >>
      strip_tac >> gvs[PULL_EXISTS] >> rw[] >>
      first_x_assum irule >> goal_assum drule >> simp[EL_MEM]
      )
    )
  >- ( (* AtomOp *)
    simp[Once type_tcexp_cases] >> irule_at Any OR_INTRO_THM2 >>
    rgs[Once pure_walkstar, pure_walk, pure_apply_subst, type_of_def] >>
    rgs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    drule infer_atom_op_LENGTH >> disch_then $ assume_tac o GSYM >> gvs[] >>
    gvs[infer_atom_op, get_PrimTys_SOME] >> goal_assum $ drule_at Any >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> simp[EL_ZIP] >> strip_tac >>
    pop_assum irule >> rpt $ goal_assum $ drule_at Any >> rw[]
    >- (last_x_assum irule >> goal_assum $ drule_at Any >> simp[EL_MEM])
    >- (
      first_x_assum irule >> gvs[new_vars_def, pure_vars]
      >- (
        disj1_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            FLOOKUP_DEF, GSYM CONJ_ASSOC] >>
        rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
        )
       >- (
        disj2_tac >> disj2_tac >> gvs[MAP2_MAP, PULL_EXISTS, MEM_MAP, MEM_ZIP] >>
        rpt $ goal_assum drule >> simp[EL_MEM]
        )
      >- (
        disj2_tac >> disj1_tac >> gvs[MAP2_MAP, PULL_EXISTS, MEM_MAP, MEM_ZIP] >>
        irule_at Any OR_INTRO_THM1 >> goal_assum drule >> simp[]
        )
      )
    >- (
      gvs[MAP2_MAP, MEM_MAP, PULL_EXISTS, MEM_ZIP, satisfies_def] >>
      simp[pure_walkstar_alt, pure_apply_subst, type_of_def]
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_FOLDR_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >> impl_tac
      >- (gvs[FLOOKUP_DEF] >> goal_assum $ drule_at Any >> simp[EL_MEM]) >>
      strip_tac >> gvs[PULL_EXISTS] >> rw[] >>
      first_x_assum irule >> goal_assum drule >> simp[EL_MEM]
      )
    )
  >- ( (* Seq *)
    simp[Once type_tcexp_cases] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    simp[GSYM PULL_EXISTS] >> conj_tac
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> gvs[] >> strip_tac >> simp[]
      ) >>
    conj_tac
    >- (
      rw[] >> first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP as k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      ) >>
    conj_tac
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> gvs[] >> strip_tac >> simp[]
      ) >>
    conj_asm1_tac
    >- (
      rw[] >> first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- (
        drule_all minfer_pure_vars >> strip_tac >> reverse $ gvs[new_vars_def] >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
        >- (disj1_tac >> disj2_tac >> disj1_tac >> rpt $ goal_assum drule) >>
        rpt disj1_tac >> Cases_on `FLOOKUP as' k` >> simp[]
        >- (qexistsl_tac [`s`,`k`] >> simp[])
        >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
        )
      >- metis_tac[]
      >- (
        rpt disj1_tac >> Cases_on `FLOOKUP as' k` >> simp[]
        >- (qexistsl_tac [`s`,`k`] >> simp[])
        >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
        )
      )
    >- (
      simp[GSYM pure_vars_empty_eq_type_of] >>
      once_rewrite_tac[GSYM SUBSET_EMPTY] >>
      irule SUBSET_TRANS >> irule_at Any pure_vars_pure_apply_subst_SUBSET >>
      simp[IMAGE_FRANGE, combinTheory.o_DEF] >> simp[GSYM IMAGE_FRANGE, IMAGE_EQ_SING] >>
      simp[SUBSET_DIFF_EMPTY] >>
      irule $ iffLR pure_vars_pure_walkstar_SUBSET_lemma >> simp[] >>
      rw[] >> first_x_assum $ qspec_then `n` mp_tac >> impl_tac
      >- (drule_all minfer_pure_vars >> simp[new_vars_def]) >>
      rw[GSYM SUBSET_DIFF_EMPTY] >>
      qspecl_then [`pure_walkstar sub (CVar n)`,`itype_of o_f closing`]
        mp_tac pure_vars_pure_apply_subst_SUPERSET >> simp[]
      )
    )
  >- ( (* App *)
    rgs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    `∃t. type_of (pure_apply_subst (itype_of o_f closing)
          (pure_walkstar sub (iFunctions tys (CVar f)))) = SOME t` by (
      rw[GSYM pure_vars_empty_eq_type_of] >>
      simp[pure_walkstar_iFunctions, pure_apply_subst_iFunctions,
           pure_vars_iFunctions, DISJ_EQ_IMP] >>
      simp[MAP_MAP_o, combinTheory.o_DEF] >> reverse $ rw[]
      >- (first_x_assum irule >> simp[new_vars_def, pure_vars]) >>
      simp[LIST_TO_SET_MAP, IMAGE_EQ_SING] >> rw[] >>
      once_rewrite_tac[GSYM SUBSET_EMPTY] >>
      irule SUBSET_TRANS >> irule_at Any pure_vars_pure_apply_subst_SUBSET >>
      simp[IMAGE_FRANGE, combinTheory.o_DEF] >> simp[GSYM IMAGE_FRANGE, IMAGE_EQ_SING] >>
      simp[SUBSET_DIFF_EMPTY] >>
      irule $ iffLR pure_vars_pure_walkstar_SUBSET_lemma >> simp[] >>
      rw[] >> first_x_assum $ qspec_then `n` mp_tac >> impl_tac
      >- (simp[new_vars_def, pure_vars_iFunctions, MEM_MAP] >> metis_tac[]) >>
      rw[GSYM SUBSET_DIFF_EMPTY] >>
      qspecl_then [`pure_walkstar sub (CVar n)`,`itype_of o_f closing`]
        mp_tac pure_vars_pure_apply_subst_SUPERSET >> simp[]) >>
    gvs[pure_walkstar_iFunctions, pure_apply_subst_iFunctions] >>
    drule $ cj 3 type_of_SOME_lemma >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
    rw[] >> gvs[] >>
    simp[Once type_tcexp_cases] >> qexists_tac `ts` >>
    first_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    simp[pure_apply_subst_iFunctions] >> imp_res_tac $ cj 1 $ iffLR MAP_EQ_EVERY2 >>
    `ts ≠ []` by (Cases_on `ts` >> gvs[]) >> simp[] >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      CASE_TAC >> gvs[] >> strip_tac >> simp[]
      )
    >- (
      rw[] >> first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP (FOLDR maunion FEMPTY ass) k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      ) >>
    gvs[LIST_REL_EL_EQN] >> imp_res_tac $ cj 1 $ iffLR MAP_EQ_EVERY2 >> gvs[] >>
    rw[] >> first_x_assum drule >> simp[EL_ZIP, EL_MAP] >> strip_tac >>
    pop_assum irule >> rpt $ goal_assum $ drule_at Any >> rw[]
    >- (last_x_assum irule >> goal_assum drule >> simp[EL_MEM])
    >- (
      first_x_assum irule >> gvs[new_vars_def]
      >- (
        rpt disj1_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, PULL_EXISTS] >>
        Cases_on `FLOOKUP (FOLDR maunion FEMPTY ass) k`
        >- (
          gvs[FLOOKUP_FOLDR_maunion, FLOOKUP_DEF] >>
          irule FALSITY >> pop_assum mp_tac >> simp[] >>
          goal_assum $ drule_at Any >> simp[EL_MEM]
          ) >>
        `n' ∈ x` by (
          gvs[FLOOKUP_FOLDR_maunion, PULL_EXISTS] >>
          goal_assum $ drule_at $ Pos last >> simp[EL_MEM]) >>
        Cases_on `FLOOKUP as' k` >> gvs[]
        >- (qexistsl_tac [`x`,`k`] >> simp[])
        >- (qexistsl_tac [`x' ∪ x`,`k`] >> simp[])
        )
      >- (
        disj1_tac >> rpt disj2_tac >> simp[PULL_EXISTS] >>
        rpt $ goal_assum drule >> simp[EL_MEM]
        )
      >- (
        disj1_tac >> disj2_tac >> disj1_tac >> disj2_tac >>
        simp[pure_vars_iFunctions, MEM_MAP] >> disj1_tac >>
        goal_assum drule >> irule_at Any EQ_REFL >> simp[EL_MEM]
        )
      )
    >- gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN]
    >- (
      gvs[ctxt_rel_def] >> rw[] >>
      qsuff_tac `∃s. FLOOKUP (maunion as' (FOLDR maunion FEMPTY ass)) k = SOME s ∧ v ⊆ s`
      >- (rw[SUBSET_DEF] >> first_x_assum drule >> strip_tac >> gvs[]) >>
      simp[FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      every_case_tac >> gvs[FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[EL_MEM]
      )
    )
  >- ( (* Lam *)
    simp[Once type_tcexp_cases] >>
    gvs[pure_walkstar_iFunctions, pure_apply_subst_iFunctions] >>
    drule $ cj 3 type_of_SOME_lemma >> strip_tac >> simp[] >>
    irule_at Any EQ_REFL >> simp[] >> gvs[MAP_MAP_o, combinTheory.o_DEF] >>
    imp_res_tac $ cj 1 $ iffLR MAP_EQ_EVERY2 >> gvs[] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_FDIFF] >> rw[] >> first_x_assum $ drule_at Any >>
      Cases_on `¬MEM k xs` >> gvs[]
      >- (
        strip_tac >> simp[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, EL_MEM]
        ) >>
      simp[ALOOKUP_APPEND] >> CASE_TAC >> gvs[]
      >- gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP] >>
      PairCases_on `x` >> gvs[] >> rw[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, EL_MAP] >>
      qpat_x_assum `∀c. _ ⇒ satisfies _ _` mp_tac >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def,
           MAP2_MAP, MEM_MAP, MEM_ZIP, PULL_EXISTS] >>
      strip_tac >> gvs[MEM_EL] >>
      first_x_assum $ qspecl_then [`n'`,`n`] mp_tac >> simp[get_massumptions_def] >>
      disch_then $ assume_tac o GSYM >> gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      first_x_assum drule >> strip_tac >> drule type_of_SOME >> rw[]
      )
    >- (
      rw[] >> first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF,
          pure_vars, pure_vars_iFunctions, PULL_EXISTS]
      >- metis_tac[] >>
      Cases_on `¬MEM k xs` >> gvs[]
      >- (rpt disj1_tac >> rpt $ goal_assum drule) >>
      disj1_tac >> rpt disj2_tac >>
      simp[MAP2_MAP, MEM_MAP, MEM_ZIP, PULL_EXISTS, pure_vars, get_massumptions_def] >>
      gvs[MEM_EL] >> goal_assum $ drule_at Any >> simp[] >>
      goal_assum $ drule_at Any >> simp[]
      )
    >- (
      rw[EVERY_EL] >> gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_MAP] >>
      first_x_assum drule >> strip_tac >>
      simp[type_ok_def, freetyvars_ok_freedbvars, type_wf_itype_wf] >>
      imp_res_tac type_of_SOME >> gvs[] >> reverse conj_tac
      >- (
        irule itype_wf_pure_apply_subst >> irule_at Any itype_wf_pure_walkstar >>
        simp[GSYM IMAGE_FRANGE, PULL_EXISTS, GSYM type_wf_itype_wf] >>
        gvs[type_ok_def, itype_wf_def]
        ) >>
      qspecl_then [`pure_walkstar sub (CVar $ EL n freshes)`,`itype_of o_f closing`]
        mp_tac freedbvars_pure_apply_subst_SUBSET >>
      qspecl_then [`sub`,`CVar $ EL n freshes`] mp_tac freedbvars_pure_walkstar_SUBSET >>
      simp[freedbvars_def] >> rw[SUBSET_DEF, PULL_EXISTS] >>
      first_x_assum drule >> simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
      rw[] >> gvs[] >>
      first_x_assum drule >> rw[] >> gvs[type_ok_def, freetyvars_ok_freedbvars]
      )
    >- (Cases_on `ts` >> gvs[])
    )
  >- ( (* Let *)
    simp[Once type_tcexp_cases] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    rgs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, satisfies_def] >>
    qabbrev_tac `monos = BIGUNION (IMAGE (pure_vars o pure_walkstar sub o CVar) mset)` >>
    `∃smonos : num_set. domain smonos = monos ∧ wf smonos` by (
      qexists_tac `list_to_num_set (SET_TO_LIST monos)` >>
      simp[EXTENSION, domain_list_to_num_set, wf_list_to_num_set] >>
      DEP_REWRITE_TAC[MEM_SET_TO_LIST] >> unabbrev_all_tac >> gvs[] >>
      rw[] >> gvs[]) >>
    qabbrev_tac `gen = generalise 0 smonos FEMPTY (pure_walkstar sub it)` >>
    PairCases_on `gen` >> gvs[] >> rename1 `(new_dbvars,gen_sub,let_ity)` >>
    drule_all generalise_0_FEMPTY >> simp[] >> strip_tac >>
    `pure_vars let_ity ⊆ FDOM closing` by (
      gvs[] >> irule SUBSET_TRANS >> irule_at Any pure_vars_pure_apply_subst_SUBSET >>
      simp[FDOM_FDIFF_alt, IMAGE_FRANGE, combinTheory.o_DEF, pure_vars] >>
      simp[GSYM IMAGE_FRANGE, BIGUNION_SUBSET, PULL_EXISTS] >>
      irule SUBSET_TRANS >> irule_at Any pred_setTheory.DIFF_SUBSET >>
      simp[Once $ GSYM pure_vars_pure_walkstar_SUBSET_lemma] >> rw[] >>
      drule_all minfer_pure_vars >> strip_tac >>
      first_x_assum $ qspec_then `n` mp_tac >> reverse $ impl_tac
      >- (
        strip_tac >>
        qspecl_then [`pure_walkstar sub (CVar n)`,`itype_of o_f closing`]
          mp_tac pure_vars_pure_apply_subst_SUPERSET >>
        simp[SUBSET_DIFF_EMPTY]
        ) >>
      reverse $ gvs[new_vars_def, pure_vars, IN_FRANGE_FLOOKUP, PULL_EXISTS]
      >- metis_tac[] >>
      rpt disj1_tac >> simp[FLOOKUP_maunion] >>
      Cases_on `FLOOKUP (as' \\ x) k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x'`,`k`] >> simp[]) ) >>
    `∃let_ty.
      type_of (pure_apply_subst
        (ishift new_dbvars o_f itype_of o_f closing) let_ity) = SOME let_ty` by (
      simp[GSYM pure_vars_empty_eq_type_of, combinTheory.o_DEF] >>
      once_rewrite_tac[GSYM SUBSET_EMPTY] >>
      irule SUBSET_TRANS >> irule_at Any pure_vars_pure_apply_subst_SUBSET >>
      simp[IMAGE_FRANGE, combinTheory.o_DEF] >>
      simp[GSYM IMAGE_FRANGE, IMAGE_EQ_SING, SUBSET_DIFF_EMPTY]) >>
    gvs[] >> qmatch_asmsub_abbrev_tac `(new_dbvars,_,_)` >>
    `FDIFF gen_sub (domain smonos) = gen_sub` by (
      rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> simp[FLOOKUP_DEF] >>
      IF_CASES_TAC >> simp[]) >>
    gvs[] >> pop_assum kall_tac >>
    qexistsl_tac [`let_ty`,`new_dbvars`] >>
    qmatch_goalsub_abbrev_tac `pure_apply_subst _ wlkit` >>
    simp[GSYM PULL_EXISTS] >> rw[]
    >- (
      gvs[ctxt_rel_def, get_massumptions_def] >> reverse $ rw[] >> gvs[]
      >- (
        gvs[FLOOKUP_maunion, DOMSUB_FLOOKUP_THM] >>
        first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
        CASE_TAC >> gvs[] >> strip_tac >> gvs[]
        ) >>
      qpat_x_assum `∀k v. FLOOKUP _ _ = _ ⇒ _` kall_tac >>
      last_x_assum drule >> strip_tac >> gvs[] >>
      rename1 `pure_apply_subst _ (pure_apply_subst inst _)` >>
      `pure_vars (pure_walkstar sub (CVar n)) ⊆ FDOM closing` by (
        last_x_assum $ qspec_then `n` mp_tac >>
        simp[new_vars_def, PULL_EXISTS, pure_vars, GSYM DISJ_ASSOC] >> impl_tac
        >- (disj2_tac >> disj1_tac >> goal_assum $ drule_at Any >> simp[]) >>
        strip_tac >>
        qspecl_then [`pure_apply_subst inst wlkit`,`itype_of o_f closing`]
          mp_tac pure_vars_pure_apply_subst_SUPERSET >>
        simp[SUBSET_DIFF_EMPTY]) >>
      gvs[] >> simp[GSYM isubst_itype_of] >> drule type_of_SOME >> rw[] >>
      simp[Once isubst_pure_apply_subst_MAP_itype_of, combinTheory.o_DEF] >>
      simp[isubst_ishift_1, SF CONJ_ss, SF ETA_ss] >>
      `∃inst'. FDOM inst' ⊆ pure_vars wlkit DIFF domain smonos ∧
        pure_apply_subst inst wlkit = pure_apply_subst inst' wlkit` by (
          qpat_x_assum `_ = domain smonos` $ assume_tac o GSYM >> gvs[] >>
          simp[Once pure_apply_subst_min] >> irule_at Any EQ_REFL >>
          simp[FDOM_DRESTRICT] >> rw[EXTENSION] >> gvs[DISJOINT_ALT] >>
          rw[SUBSET_DEF, DISJ_EQ_IMP] >> CCONTR_TAC >> gvs[]) >>
      simp[] >>
      qspecl_then [`gen_sub`,`inst'`,`wlkit`] mp_tac pure_apply_subst_split_isubst >>
      impl_tac
      >- (
        simp[] >> unabbrev_all_tac >> gvs[] >>
        once_rewrite_tac[GSYM SUBSET_EMPTY] >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
        imp_res_tac minfer_freedbvars >> simp[] >>
        rw[DISJ_EQ_IMP, IMAGE_EQ_SING]
        ) >>
      disch_then $ assume_tac o GSYM >> gvs[] >>
      qmatch_goalsub_abbrev_tac `GENLIST genl` >>
      qabbrev_tac `sub_genl = MAP (pure_apply_subst (itype_of o_f closing)) $
                                GENLIST genl new_dbvars` >>
      `∃ts. MAP type_of sub_genl = MAP SOME ts` by (
        gvs[Abbr `sub_genl`, Abbr `genl`] >>
        simp[GSYM pure_vars_empty_eq_type_of_MAP] >>
        simp[EVERY_MEM, MEM_MAP, MEM_GENLIST, PULL_EXISTS] >> rw[]
        >- (
          once_rewrite_tac[GSYM SUBSET_EMPTY] >>
          irule SUBSET_TRANS >> irule_at Any pure_vars_pure_apply_subst_SUBSET >>
          simp[IMAGE_EQ_SING, DISJ_EQ_IMP, SUBSET_DIFF_EMPTY] >>
          simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
          qsuff_tac `∀v. v ∈ FRANGE inst' ⇒ pure_vars v ⊆ FDOM closing`
          >- (rw[FRANGE_DEF, PULL_EXISTS]) >>
          qpat_x_assum `pure_apply_subst inst _ = _` $ assume_tac o GSYM >>
          qpat_x_assum `pure_apply_subst inst' _ = _` $ assume_tac o GSYM >>
          rgs[] >> qpat_x_assum `pure_vars _ ⊆ _` mp_tac >>
          simp[Once $ GSYM pure_vars_pure_apply_subst_SUBSET_lemma] >>
          strip_tac >> simp[FRANGE_DEF, PULL_EXISTS] >>
          rw[] >> `x ∈ pure_vars wlkit` by gvs[SUBSET_DEF] >>
          first_x_assum drule >> simp[pure_apply_subst, FLOOKUP_DEF]
          )
        >- (
          qpat_x_assum `pure_apply_subst inst _ = _` $ assume_tac o GSYM >>
          qpat_x_assum `pure_apply_subst inst' _ = _` $ assume_tac o GSYM >>
          gvs[] >>
          `∃cv. cv ∈ FDOM gen_sub ∧ gen_sub ' cv = n'` by (
            `n' ∈ FRANGE gen_sub` by gvs[] >> pop_assum mp_tac >>
            rewrite_tac[FRANGE_DEF] >> simp[]) >>
          gvs[miscTheory.fmap_linv_def, FLOOKUP_DEF] >>
          once_rewrite_tac[GSYM SUBSET_EMPTY] >>
          irule SUBSET_TRANS >> irule_at Any pure_vars_pure_apply_subst_SUBSET >>
          simp[pure_vars, IMAGE_FRANGE, combinTheory.o_DEF] >>
          simp[GSYM IMAGE_FRANGE, IMAGE_EQ_SING] >>
          qsuff_tac `cv ∈ FDOM closing` >> rw[] >> gvs[Abbr `wlkit`] >>
          drule_all pure_vars_pure_walkstar >> strip_tac >>
          drule_all minfer_pure_vars >> strip_tac >>
          last_x_assum $ qspec_then `cv'` mp_tac >> impl_tac
          >- (
            reverse $ gvs[new_vars_def, IN_FRANGE_FLOOKUP, FLOOKUP_maunion] >>
            gvs[PULL_EXISTS, GSYM DISJ_ASSOC, pure_vars]
            >- metis_tac[] >>
            rpt disj1_tac >> Cases_on `FLOOKUP (as' \\ k) k'` >> gvs[]
            >- (qexistsl_tac [`s`,`k'`] >> simp[])
            >- (qexistsl_tac [`s ∪ x`,`k'`] >> simp[])
            ) >>
          strip_tac >>
          qspecl_then [`pure_walkstar sub (CVar cv')`,`itype_of o_f closing`]
            mp_tac pure_vars_pure_apply_subst_SUPERSET >>
          simp[SUBSET_DIFF_EMPTY] >> simp[SUBSET_DEF]
          )
        ) >>
      qexists_tac `ts` >>
      conj_asm1_tac >- (unabbrev_all_tac >> gvs[MAP_EQ_EVERY2]) >>
      `∀v. v ∈ FRANGE inst' ⇒ freedbvars v = {}` by (
        qpat_x_assum `pure_apply_subst inst _ = _` $ assume_tac o GSYM >>
        qpat_x_assum `pure_apply_subst inst' _ = _` $ assume_tac o GSYM >>
        rw[] >> gvs[] >> qpat_x_assum `pure_walkstar _ (CVar _) = _` assume_tac >>
        `freedbvars (pure_walkstar sub (CVar n)) = {}` by (
          once_rewrite_tac[GSYM SUBSET_EMPTY] >>
          irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
          simp[freedbvars_def, IMAGE_EQ_SING]) >>
        gvs[] >>
        qspecl_then [`wlkit`,`inst'`] mp_tac freedbvars_pure_apply_subst_SUPERSET >>
        simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >> strip_tac >> gvs[] >>
        gvs[FRANGE_DEF] >> `x ∈ pure_vars wlkit` by gvs[SUBSET_DEF] >>
        first_x_assum $ drule_at Any >> impl_tac >- (CCONTR_TAC >> rgs[]) >>
        simp[pure_apply_subst, FLOOKUP_DEF]) >>
      `∀v. v ∈ FRANGE inst' ⇒ itype_wf (SND ns) v` by (
        qpat_x_assum `pure_apply_subst inst _ = _` $ assume_tac o GSYM >>
        qpat_x_assum `pure_apply_subst inst' _ = _` $ assume_tac o GSYM >>
        rw[] >> rgs[] >> qpat_x_assum `pure_walkstar _ (CVar _) = _` assume_tac >>
        `itype_wf (SND ns) (pure_walkstar sub (CVar n))` by (
          irule itype_wf_pure_walkstar >> simp[itype_wf_def]) >>
        gvs[] >> drule pure_apply_subst_itype_wf >> gvs[FRANGE_DEF] >>
        `x ∈ pure_vars wlkit` by gvs[SUBSET_DEF] >>
        disch_then drule >> simp[FLOOKUP_DEF]) >>
      conj_tac
      >- (
        rw[EVERY_EL] >> gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
        first_x_assum drule >> strip_tac >>
        drule type_of_SOME >> strip_tac >>
        simp[type_ok_def, type_wf_itype_wf, freetyvars_ok_freedbvars] >>
        gvs[Abbr `sub_genl`, EL_MAP, Abbr `genl`] >> rw[]
        >- (
          qspecl_then [`inst' ' (gm ' n')`,`itype_of o_f closing`]
            mp_tac freedbvars_pure_apply_subst_SUBSET >>
          simp[SUBSET_DEF, PULL_EXISTS] >> disch_then drule >>
          strip_tac >> gvs[] >- gvs[FRANGE_DEF, PULL_EXISTS] >>
          gvs[GSYM IMAGE_FRANGE] >> last_x_assum drule >>
          simp[type_ok_def, freetyvars_ok_freedbvars]
          )
        >- (
          qspecl_then [`CVar (gm ' n')`,`itype_of o_f closing`]
            mp_tac freedbvars_pure_apply_subst_SUBSET >>
          simp[freedbvars_def, SUBSET_DEF, PULL_EXISTS] >> disch_then drule >>
          strip_tac >> gvs[GSYM IMAGE_FRANGE] >> last_x_assum drule >>
          simp[type_ok_def, freetyvars_ok_freedbvars]
          )
        >- (
          irule itype_wf_pure_apply_subst >> rw[GSYM IMAGE_FRANGE, PULL_EXISTS]
          >- (last_x_assum drule >> simp[type_ok_def, type_wf_itype_wf])
          >- gvs[FRANGE_DEF, PULL_EXISTS]
          )
        >- (
          irule itype_wf_pure_apply_subst >> rw[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
          simp[itype_wf_def] >>
          last_x_assum drule >> simp[type_ok_def, type_wf_itype_wf]
          )
        ) >>
      `sub_genl = MAP itype_of ts` by (
        gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[LIST_EQ_REWRITE] >>
        first_x_assum drule >> unabbrev_all_tac >> simp[EL_MAP, EL_GENLIST] >>
        strip_tac >> imp_res_tac type_of_SOME >> simp[]) >>
      pop_assum $ SUBST1_TAC o GSYM >> gvs[] >>
      irule EQ_SYM >>
      DEP_ONCE_REWRITE_TAC[GSYM pure_apply_subst_isubst_MAP_lemma] >> simp[] >>
      rw[GSYM IMAGE_FRANGE] >> simp[pure_vars_itype_of]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM, FLOOKUP_maunion,
          pure_vars, PULL_EXISTS]
      >- metis_tac[] >>
      Cases_on `k = x` >> gvs[]
      >- (
        simp[get_massumptions_def] >>
        disj1_tac >> disj2_tac >> rpt disj1_tac >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- (
        rpt disj1_tac >> Cases_on `FLOOKUP as k` >> gvs[]
        >- (qexistsl_tac [`s`,`k`] >> simp[])
        >- (qexistsl_tac [`x' ∪ s`,`k`] >> simp[])
        )
      ) >>
    qpat_x_assum `type_of _ = _` mp_tac >>
    DEP_REWRITE_TAC[pure_apply_subst_FUNION] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
    qmatch_goalsub_abbrev_tac `type_of (_ foo _)` >>
    `foo = itype_of o_f (TypeVar o_f gen_sub ⊌ tshift new_dbvars o_f closing)` by (
      unabbrev_all_tac >> simp[o_f_FUNION] >>
      simp[combinTheory.o_DEF, itype_of_def, GSYM ishift_itype_of, SF ETA_ss]) >>
    gvs[] >> disch_then $ irule_at Any >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      strip_tac >> simp[ALOOKUP_MAP] >> rw[] >>
      first_x_assum $ qspec_then `n` mp_tac >> impl_tac >- (CASE_TAC >> simp[]) >>
      strip_tac >> simp[] >>
      qexists_tac `MAP (tshift new_dbvars) ts` >> simp[] >>
      qspecl_then [`0`,`ts`,`scheme`,`0`,`new_dbvars`] mp_tac subst_db_shift_db_2 >>
      simp[] >> disch_then kall_tac >> rw[]
      >- (
        gvs[EVERY_MAP, EVERY_MEM] >> rw[] >>
        first_x_assum drule >> rw[] >> irule type_ok_shift_db >> simp[]
        ) >>
      qpat_x_assum `FUNION _ _ = _` $ assume_tac o GSYM >> simp[] >>
      DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
      cheat (* TODO *)
      )
    >- cheat
    >- cheat
    )
  >- ( (* Letrec *)
    cheat (* TODO *)
    )
  >- ( (* BoolCase *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, satisfies_def] >>
    gvs[cj 2 pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 3 $ last_x_assum $ irule_at Any >>
    rpt $ goal_assum $ drule_at Any >> simp[pure_apply_subst, type_of_def] >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >> strip_tac >> rw[] >>
      first_x_assum $ qspec_then `n` mp_tac >> impl_tac >> simp[] >>
      CASE_TAC >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, pure_vars, FLOOKUP_maunion]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP (maunion as as' \\ v) k` >> simp[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[]
      >- (
        simp[itype_of_def] >> last_x_assum $ qspec_then `n` mp_tac >>
        simp[get_massumptions_def, pure_apply_subst]
        ) >>
      last_x_assum $ qspec_then `k` mp_tac >>
      simp[DOMSUB_FLOOKUP_THM, FLOOKUP_maunion] >>
      rpt TOP_CASE_TAC >> simp[] >> strip_tac >> rw[] >>
      every_case_tac >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, pure_vars,
          DOMSUB_FLOOKUP_THM, FLOOKUP_maunion]
      >- metis_tac[] >>
      Cases_on `v = k` >> gvs[]
      >- (
        simp[GSYM DISJ_ASSOC] >> ntac 7 disj2_tac >> disj1_tac >>
        simp[get_massumptions_def] >> goal_assum $ drule_at Any >> simp[]
        ) >>
      rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
      every_case_tac >> simp[]
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion] >> rw[]
      >- (
        simp[itype_of_def] >> last_x_assum $ qspec_then `n` mp_tac >>
        simp[get_massumptions_def, pure_apply_subst]
        ) >>
      last_x_assum $ qspec_then `k` mp_tac >>
      simp[DOMSUB_FLOOKUP_THM, FLOOKUP_maunion] >>
      rpt TOP_CASE_TAC >> simp[] >> strip_tac >> rw[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, pure_vars,
          DOMSUB_FLOOKUP_THM, FLOOKUP_maunion]
      >- metis_tac[] >>
      Cases_on `v = k` >> gvs[]
      >- (
        simp[GSYM DISJ_ASSOC] >> ntac 6 disj2_tac >> disj1_tac >>
        simp[get_massumptions_def] >> goal_assum $ drule_at Any >> simp[]
        ) >>
      rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
      every_case_tac >> simp[]
      )
    )
  >- ( (* TupleCase *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, LEFT_AND_OVER_OR, satisfies_def] >>
    `∃t. type_of (pure_apply_subst (itype_of o_f closing)
          (pure_walkstar sub (Tuple (MAP CVar freshes)))) = SOME t` by (
      rw[GSYM pure_vars_empty_eq_type_of] >>
      simp[pure_walkstar_alt, pure_apply_subst, pure_vars] >>
      simp[LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF, IMAGE_EQ_SING] >>
      simp[DISJ_EQ_IMP] >> rw[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars, MEM_MAP, PULL_EXISTS]) >>
    gvs[cj 5 pure_walkstar_alt, pure_apply_subst] >>
    drule $ cj 1 type_of_SOME_lemma >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
    rw[] >> gvs[] >> qexists_tac `ts` >> ntac 2 $ last_x_assum $ irule_at Any >>
    rpt $ goal_assum $ drule_at Any >> simp[pure_apply_subst] >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion, FLOOKUP_FDIFF] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      strip_tac >> rw[] >> every_case_tac >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, pure_vars, FLOOKUP_maunion]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP (FDIFF as (v INSERT set pvars)) k` >> simp[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      )
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion, ALOOKUP_APPEND] >> rw[] >>
      CASE_TAC >> rw[]
      >- (
        drule type_of_SOME >> rw[] >>
        last_x_assum $ qspec_then `n` mp_tac >>
        rw[get_massumptions_def, itype_of_def, SF ETA_ss, pure_apply_subst]
        )
      >- (
        drule ALOOKUP_MEM >> simp[] >>
        DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >> conj_asm1_tac >- gvs[MAP_EQ_EVERY2] >>
        strip_tac >> gvs[EL_MAP] >> rw[] >> gvs[EL_MEM]
        )
      >- (
        qsuff_tac `¬MEM k pvars` >> rw[]
        >- (
          first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_FDIFF] >>
          CASE_TAC >> simp[] >> strip_tac >> simp[]
          ) >>
        gvs[ALOOKUP_NONE, MEM_MAP, EXISTS_PROD] >>
        simp[Once MEM_EL] >> CCONTR_TAC >> gvs[] >>
        first_x_assum $ qspecl_then [`0`,`EL n ts`] mp_tac >> simp[] >>
        DEP_REWRITE_TAC[MEM_ZIP] >> gvs[MAP_EQ_EVERY2, EL_MAP] >>
        gvs[MEM_EL] >> goal_assum drule >> simp[EL_MAP]
        )
      >- (
        drule ALOOKUP_MEM >> simp[] >>
        DEP_REWRITE_TAC[MEM_ZIP] >> conj_asm1_tac >- gvs[MAP_EQ_EVERY2] >>
        strip_tac >> gvs[EL_MAP] >> rw[] >>
        qpat_x_assum `∀c s. _ ∧ _ ⇒ _` mp_tac >>
        simp[MAP2_MAP, MEM_MAP, MEM_ZIP, PULL_EXISTS, EL_MAP,
             get_massumptions_def, satisfies_def] >>
        disch_then $ drule_at Any >> simp[] >> disch_then drule >> rw[] >>
        gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
        first_x_assum drule >> strip_tac >>
        drule type_of_SOME >> rw[]
        )
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, pure_vars,
          FLOOKUP_FDIFF, FLOOKUP_maunion]
      >- metis_tac[] >>
      Cases_on `v = k` >> gvs[]
      >- (
        simp[GSYM DISJ_ASSOC] >> ntac 5 disj2_tac >> disj1_tac >>
        simp[get_massumptions_def] >> goal_assum $ drule_at Any >> simp[]
        ) >>
      reverse $ Cases_on `MEM k pvars` >> gvs[]
      >- (
        rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
        every_case_tac >> simp[]
        ) >>
      simp[GSYM DISJ_ASSOC] >> ntac 6 disj2_tac >> disj1_tac >>
      simp[MAP2_MAP, MEM_MAP, PULL_EXISTS, MEM_ZIP, pure_vars] >>
      irule_at Any OR_INTRO_THM1 >> simp[] >> gvs[MEM_EL] >>
      goal_assum $ drule_at Any >> simp[get_massumptions_def]
      )
    >- gvs[MAP_EQ_EVERY2]
    )
  >- ( (* ExceptionCase *)
    simp[Once type_tcexp_cases] >> ntac 2 disj2_tac >> disj1_tac >>
    PairCases_on `ns` >> gvs[] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, satisfies_def] >>
    gvs[MEM_MAP, PULL_EXISTS, satisfies_def] >>
    qpat_x_assum `∀t. MEM _ _ ⇒ _` $ assume_tac o GSYM >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    simp[cj 3 pure_walkstar_alt, pure_apply_subst, type_of_def] >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion, FLOOKUP_FDIFF] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      strip_tac >> rw[] >> every_case_tac >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, pure_vars, FLOOKUP_maunion]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP (FOLDR maunion FEMPTY final_as) k` >> simp[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      )
    >- (
      drule sortingTheory.PERM_LIST_TO_SET >> rw[EXTENSION] >>
      gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD, FORALL_PROD, EQ_IMP_THM, FORALL_AND_THM] >>
      metis_tac[]
      )
    >- (drule sortingTheory.PERM_LENGTH >> simp[]) >>
    gvs[EVERY_EL, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rw[] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    first_assum drule >> first_assum $ rewrite_tac o single >>
    simp[] >> strip_tac >> simp[] >>
    last_x_assum drule >> simp[] >> strip_tac >> simp[] >>
    `c ≠ "Subscript"` by (
      qpat_x_assum `namespace_ok _` assume_tac >>
      gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
      last_x_assum $ qspec_then `"Subscript"` mp_tac >>
      impl_tac >- simp[pure_configTheory.reserved_cns_def] >> strip_tac >>
      CCONTR_TAC >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP]) >>
    gvs[] >> conj_asm1_tac
    >- (
      last_x_assum mp_tac >> simp[MEM_FLAT, MEM_MAP, DISJ_EQ_IMP, EXISTS_PROD] >>
      disch_then irule >> simp[MEM_EL] >> goal_assum drule >> simp[]
      ) >>
    conj_asm1_tac
    >- (
      gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
      qsuff_tac `MEM (c, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) ns0)`
      >- (
        rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
        rev_drule ALOOKUP_ALL_DISTINCT_MEM >> disch_then drule >> simp[]
        ) >>
      drule $ iffRL sortingTheory.PERM_MEM_EQ >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
      simp[Once MEM_EL, PULL_EXISTS] >> disch_then drule >> simp[]
      ) >>
    first_x_assum irule >> rpt $ goal_assum $ drule_at Any >> simp[] >> rw[]
    >- (
      first_x_assum irule >> simp[MEM_EL, PULL_EXISTS] >>
      goal_assum drule >> simp[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      simp[pure_vars, PULL_EXISTS, MEM_MAP, GSYM DISJ_ASSOC]
      >- (
        Cases_on `n` >> gvs[] >>
        ntac 4 disj2_tac >> disj1_tac >> irule_at Any OR_INTRO_THM2 >>
        goal_assum drule >> simp[EL] >> DEP_REWRITE_TAC[EL_MEM] >>
        gvs[namespace_ok_def] >> Cases_on `tys` >> gvs[]
        )
      >- (
        ntac 6 disj2_tac >> disj1_tac >>
        simp[MEM_EL, PULL_EXISTS] >> rpt $ goal_assum $ drule_at Any >> simp[]
        ) >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      Cases_on `k ∈ v INSERT set pvars` >> gvs[]
      >- (
        ntac 6 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[PULL_EXISTS] >>
        rpt $ irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS, pure_vars] >>
        simp[get_massumptions_def] >> goal_assum drule >> simp[]
        )
      >- (
        ntac 6 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[PULL_EXISTS] >>
        irule_at Any OR_INTRO_THM1 >> irule_at Any OR_INTRO_THM2 >>
        simp[PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP, EL_MAP, pure_vars] >>
        gvs[MEM_EL] >> qexists_tac `n''` >> simp[] >>
        simp[get_massumptions_def] >> goal_assum drule >> simp[]
        )
      >- (
        rpt disj1_tac >> simp[PULL_EXISTS, Once SWAP_EXISTS_THM] >>
        qexists_tac `k` >> CASE_TAC >> gvs[]
        >- (
          irule FALSITY >> pop_assum mp_tac >> simp[MEM_EL, PULL_EXISTS] >>
          goal_assum drule >> gvs[FLOOKUP_DEF]
          ) >>
        CASE_TAC >> simp[PULL_EXISTS, MEM_EL] >> gvs[]
        >- (rpt $ goal_assum $ drule_at Any >> simp[FLOOKUP_FDIFF])
        >- (disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[FLOOKUP_FDIFF])
        )
      )
    >- (
      Cases_on `n` >> gvs[EL] >>
      first_x_assum $ qspec_then `EL n' (TL tys)` mp_tac >> impl_tac >> simp[] >>
      irule EL_MEM >> Cases_on `tys` >> gvs[]
      ) >>
    gvs[ctxt_rel_def, FLOOKUP_maunion, ALOOKUP_APPEND] >> rw[] >>
    CASE_TAC >> rw[]
    >- (
      simp[itype_of_def] >> qpat_x_assum `∀c s. _ ∧ _ ⇒ _` mp_tac >>
      simp[Once SWAP_FORALL_THM] >>
      disch_then $ qspec_then `EL n final_cs` mp_tac >> simp[] >>
      disch_then $ qspec_then `mUnify (CVar n') (CVar f)` mp_tac >> simp[] >>
      simp[get_massumptions_def, MEM_EL, PULL_EXISTS] >>
      disch_then drule >> simp[get_massumptions_def, satisfies_def] >>
      simp[pure_walkstar_alt, pure_apply_subst]
      )
    >- (
      irule FALSITY >> qpat_x_assum `¬MEM _ _` mp_tac >> simp[] >>
      drule ALOOKUP_MEM >> simp[] >>
      DEP_REWRITE_TAC[MEM_ZIP] >> simp[MEM_EL] >>
      strip_tac >> gvs[EL_MAP] >> goal_assum drule >> simp[]
      )
    >- (
      `¬MEM k pvars` by (
        gvs[ALOOKUP_NONE, MEM_MAP, EXISTS_PROD] >>
        simp[MEM_EL] >> CCONTR_TAC >> gvs[] >>
        first_x_assum $ qspecl_then [`0`,`EL n' schemes`] mp_tac >> simp[] >>
        DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >>
        goal_assum drule >> simp[EL_MAP]) >>
      last_x_assum $ qspec_then `k` mp_tac >>
      `∃s. FLOOKUP (FOLDR maunion FEMPTY final_as) k = SOME s ∧ v' ⊆ s` by (
        simp[FLOOKUP_FOLDR_maunion] >> rw[MEM_EL, PULL_EXISTS]
        >- (goal_assum drule >> gvs[FLOOKUP_DEF]) >>
        simp[SUBSET_DEF, PULL_EXISTS] >> rw[] >>
        rpt $ goal_assum drule >> simp[FLOOKUP_FDIFF]) >>
      simp[] >> CASE_TAC >> rw[] >> gvs[SUBSET_DEF]
      )
    >- (
      drule ALOOKUP_MEM >> simp[] >>
      DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >> strip_tac >> gvs[EL_MAP] >> rw[] >>
      qpat_x_assum `∀c s. _ ∧ _ ⇒ _` mp_tac >> simp[MEM_EL, PULL_EXISTS] >>
      disch_then $ drule_at Any >> simp[] >>
      simp[MAP2_MAP, MEM_MAP, PULL_EXISTS, EXISTS_PROD, DISJ_IMP_THM, FORALL_AND_THM] >>
      strip_tac >> pop_assum kall_tac >>
      pop_assum $ qspec_then `EL n' pvars` mp_tac >> simp[get_massumptions_def] >>
      disch_then drule >> simp[MEM_ZIP, PULL_EXISTS, EL_MAP] >>
      disch_then drule >> simp[satisfies_def]
      )
    )
  >- ( (* Case *)
    simp[Once type_tcexp_cases] >> rpt disj2_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, satisfies_def] >>
    `∃t. type_of (pure_apply_subst (itype_of o_f closing)
          (pure_walkstar sub (TypeCons id (MAP CVar freshes)))) = SOME t` by (
      rw[GSYM pure_vars_empty_eq_type_of] >>
      simp[pure_walkstar_alt, pure_apply_subst, pure_vars] >>
      simp[LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF, IMAGE_EQ_SING] >>
      simp[DISJ_EQ_IMP] >> rw[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars, MEM_MAP, PULL_EXISTS]) >>
    gvs[cj 4 pure_walkstar_alt, pure_apply_subst] >>
    drule $ cj 2 type_of_SOME_lemma >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
    rw[] >> gvs[] >>
    PairCases_on `ns` >> gvs[] >>
    qpat_x_assum `∀t. MEM _ _ ⇒ _` $ assume_tac o GSYM >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    qexistsl_tac [`id`,`ts`] >> simp[] >>
    gvs[cj 4 pure_walkstar_alt, pure_apply_subst] >> rw[]
    >- (
      gvs[ctxt_rel_def, FLOOKUP_maunion, FLOOKUP_FDIFF] >> rw[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[] >>
      strip_tac >> rw[] >> every_case_tac >> gvs[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, pure_vars, FLOOKUP_maunion]
      >- metis_tac[] >>
      rpt disj1_tac >> Cases_on `FLOOKUP (FOLDR maunion FEMPTY final_as) k` >> simp[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      )
    >- gvs[MAP_EQ_EVERY2]
    >- (
      simp[LAMBDA_PROD] >>
      drule sortingTheory.PERM_LIST_TO_SET >> rw[EXTENSION] >>
      gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD, FORALL_PROD, EQ_IMP_THM, FORALL_AND_THM] >>
      metis_tac[]
      )
    >- (drule sortingTheory.PERM_LENGTH >> simp[]) >>
    gvs[EVERY_EL, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rw[] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    first_assum drule >> first_assum $ rewrite_tac o single >>
    simp[] >> strip_tac >> simp[] >>
    last_x_assum drule >> simp[] >> strip_tac >> simp[] >>
    gvs[] >> conj_asm1_tac
    >- (
      gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
      `MEM (c, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)` by (
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
        disch_then irule >> simp[MEM_EL] >> goal_assum drule >> simp[]) >>
      gvs[MEM_MAP, EXISTS_PROD] >>
      drule_at (Pos last) ALOOKUP_ALL_DISTINCT_MEM >> impl_tac >> simp[] >>
      gvs[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      irule ALL_DISTINCT_FLAT_IMP >> goal_assum drule >>
      simp[MEM_MAP, EXISTS_PROD] >> irule_at Any EQ_REFL >> simp[MEM_EL] >>
      gvs[oEL_THM] >> goal_assum drule >> simp[]
      ) >>
    conj_asm1_tac
    >- (
      last_x_assum mp_tac >> simp[MEM_FLAT, MEM_MAP, DISJ_EQ_IMP, EXISTS_PROD] >>
      disch_then irule >> simp[MEM_EL] >> goal_assum drule >> simp[]
      ) >>
    first_x_assum irule >> rpt $ goal_assum $ drule_at Any >> simp[] >> rw[]
    >- (
      qpat_x_assum `∀c s. _ ∧ _ ⇒ _` irule >> simp[MEM_EL, PULL_EXISTS] >>
      goal_assum $ drule_at Any >> simp[]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      simp[pure_vars, PULL_EXISTS, MEM_MAP, GSYM DISJ_ASSOC]
      >- (
        Cases_on `n` >> gvs[] >>
        ntac 5 disj2_tac >> disj1_tac >> irule_at Any OR_INTRO_THM2 >>
        goal_assum drule >> simp[EL] >> DEP_REWRITE_TAC[EL_MEM] >>
        gvs[namespace_ok_def] >> Cases_on `tys` >> gvs[]
        )
      >- (
        ntac 7 disj2_tac >> disj1_tac >>
        simp[MEM_EL, PULL_EXISTS] >> rpt $ goal_assum $ drule_at Any >> simp[]
        ) >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      Cases_on `k ∈ v INSERT set pvars` >> gvs[]
      >- (
        ntac 7 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[PULL_EXISTS] >>
        rpt $ irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS, pure_vars] >>
        simp[get_massumptions_def] >> goal_assum drule >> simp[]
        )
      >- (
        ntac 7 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[PULL_EXISTS] >>
        irule_at Any OR_INTRO_THM1 >> irule_at Any OR_INTRO_THM2 >>
        simp[PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP, EL_MAP, pure_vars] >>
        gvs[MEM_EL] >> qexists_tac `n''` >> simp[] >>
        simp[get_massumptions_def] >> goal_assum drule >> simp[]
        )
      >- (
        rpt disj1_tac >> simp[PULL_EXISTS, Once SWAP_EXISTS_THM] >>
        qexists_tac `k` >> CASE_TAC >> gvs[]
        >- (
          irule FALSITY >> pop_assum mp_tac >> simp[MEM_EL, PULL_EXISTS] >>
          goal_assum drule >> gvs[FLOOKUP_DEF]
          ) >>
        CASE_TAC >> simp[PULL_EXISTS, MEM_EL] >> gvs[]
        >- (rpt $ goal_assum $ drule_at Any >> simp[FLOOKUP_FDIFF])
        >- (disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[FLOOKUP_FDIFF])
        )
      )
    >- (
      Cases_on `n` >> gvs[EL, MEM_MAP, PULL_EXISTS] >>
      first_x_assum $ qspec_then `EL n' (TL tys)` mp_tac >>
      impl_tac >> simp[satisfies_def]
      >- (irule EL_MEM >> Cases_on `tys` >> gvs[])
      >- (disch_then $ assume_tac o GSYM >> simp[])
      ) >>
    gvs[ctxt_rel_def, FLOOKUP_maunion, ALOOKUP_APPEND] >> rw[] >>
    CASE_TAC >> rw[]
    >- (
      simp[itype_of_def] >> qpat_x_assum `∀c s. _ ∧ _ ⇒ _` mp_tac >>
      simp[Once SWAP_FORALL_THM] >>
      disch_then $ qspec_then `EL n final_cs` mp_tac >> simp[] >>
      disch_then $ qspec_then `mUnify (CVar n') (CVar f)` mp_tac >> simp[] >>
      simp[get_massumptions_def, MEM_EL, PULL_EXISTS] >>
      disch_then drule >> simp[get_massumptions_def, satisfies_def, SF ETA_ss] >>
      strip_tac >> drule type_of_SOME >> rw[itype_of_def, SF ETA_ss] >>
      simp[pure_apply_subst]
      )
    >- (
      irule FALSITY >> qpat_x_assum `¬MEM _ _` mp_tac >> simp[] >>
      drule ALOOKUP_MEM >> simp[] >>
      DEP_REWRITE_TAC[MEM_ZIP] >> simp[MEM_EL] >>
      strip_tac >> gvs[EL_MAP] >> goal_assum drule >> simp[]
      )
    >- (
      `¬MEM k pvars` by (
        gvs[ALOOKUP_NONE, MEM_MAP, EXISTS_PROD] >>
        simp[MEM_EL] >> CCONTR_TAC >> gvs[] >>
        first_x_assum $ qspecl_then [`0`,`tsubst ts (EL n' schemes)`] mp_tac >>
        simp[] >> DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >>
        goal_assum drule >> simp[EL_MAP]) >>
      last_x_assum $ qspec_then `k` mp_tac >>
      `∃s. FLOOKUP (FOLDR maunion FEMPTY final_as) k = SOME s ∧ v' ⊆ s` by (
        simp[FLOOKUP_FOLDR_maunion] >> rw[MEM_EL, PULL_EXISTS]
        >- (goal_assum drule >> gvs[FLOOKUP_DEF]) >>
        simp[SUBSET_DEF, PULL_EXISTS] >> rw[] >>
        rpt $ goal_assum drule >> simp[FLOOKUP_FDIFF]) >>
      simp[] >> CASE_TAC >> rw[] >> gvs[SUBSET_DEF]
      )
    >- (
      drule ALOOKUP_MEM >> simp[] >>
      DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >> strip_tac >> gvs[EL_MAP] >> rw[] >>
      qpat_x_assum `∀c s. _ ∧ _ ⇒ _` mp_tac >> simp[MEM_EL, PULL_EXISTS] >>
      disch_then $ drule_at Any >> simp[] >>
      simp[MAP2_MAP, MEM_MAP, PULL_EXISTS, EXISTS_PROD, DISJ_IMP_THM, FORALL_AND_THM] >>
      strip_tac >> pop_assum kall_tac >>
      pop_assum $ qspec_then `EL n' pvars` mp_tac >> simp[get_massumptions_def] >>
      disch_then drule >> simp[MEM_ZIP, PULL_EXISTS, EL_MAP] >>
      disch_then drule >> rw[satisfies_def] >>
      DEP_REWRITE_TAC[pure_walkstar_isubst] >> simp[] >>
      simp[pure_apply_subst_isubst_itype_of] >>
      qsuff_tac
        `MAP (pure_apply_subst (itype_of o_f closing))
          (MAP (pure_walkstar sub) (MAP CVar freshes)) = MAP itype_of ts`
      >- (
        rw[] >> gvs[] >>
        gvs[MAP_MAP_o, combinTheory.o_DEF, isubst_itype_of, type_of_itype_of] >>
        gvs[SF ETA_ss, miscTheory.map_some_eq]
        ) >>
      gvs[MAP_MAP_o, combinTheory.o_DEF] >>
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_MAP] >>
      rw[] >> first_x_assum drule >> strip_tac >>
      drule type_of_SOME >> simp[]
      )
    )
QED


(****************************************)

val _ = export_theory();

