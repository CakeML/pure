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


(******************** Main results ********************)


(****************************************)

val _ = export_theory();

