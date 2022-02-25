open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory stringTheory optionTheory pred_setTheory
     listTheory rich_listTheory alistTheory finite_mapTheory sptreeTheory;
open mlmapTheory;
open pure_miscTheory pure_typingTheory pure_typingPropsTheory pure_typingProofTheory
     pure_tcexpTheory pure_inference_commonTheory pure_unificationTheory
     pure_inferenceTheory pure_inferencePropsTheory pure_inference_modelTheory;

val _ = new_theory "pure_inferenceProof";

Overload csubst = ``pure_apply_subst``;

(******************** Lemmas ********************)

Theorem minfer_itype_ok:
  ∀ns mset cexp as cs it.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns
  ⇒ itype_ok (SND ns) 0 it
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[itype_ok_iFunctions, itype_ok] >>
  gvs[LIST_REL_EL_EQN, EVERY_MAP, EVERY_MEM, itype_ok]
  >- (rw[MEM_EL] >> first_x_assum drule >> simp[EL_ZIP])
  >- gvs[oEL_THM]
  >- (
    Cases_on `tys` >> gvs[] >> Cases_on `final_cs` >> gvs[] >>
    gvs[EL_ZIP] >> last_x_assum $ qspec_then `0` mp_tac >> simp[] >>
    rpt (pairarg_tac >> simp[])
    )
  >- (
    Cases_on `tys` >> gvs[]
    >- (
      PairCases_on `ns` >> gvs[namespace_ok_def, oEL_THM, EVERY_EL] >>
      last_x_assum drule >> simp[]
      ) >>
    Cases_on `final_cs` >> gvs[] >>
    gvs[EL_ZIP] >> last_x_assum $ qspec_then `0` mp_tac >> simp[] >>
    rpt (pairarg_tac >> simp[])
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

Theorem minfer_msets_disjoint:
  ∀ns mset cexp as cs it.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns
  ⇒ DISJOINT mset (new_vars as cs it)
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[new_vars_def, pure_vars, pure_vars_iFunctions, PULL_EXISTS, MEM_MAP,
      LIST_REL_EL_EQN, EL_ZIP, MEM_EL, MAP2_MAP, EL_MAP, EVERY_EL] >>
  gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion, FLOOKUP_FDIFF,
      DOMSUB_FLOOKUP_THM, MEM_EL, PULL_EXISTS, PULL_FORALL] >>
  gvs[FORALL_AND_THM, IMP_CONJ_THM]
  >- (rw[] >> gvs[DISJOINT_BIGUNION, PULL_EXISTS] >> rw[] >> res_tac)
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> gvs[DISJOINT_BIGUNION, PULL_EXISTS] >> rw[] >> res_tac)
  >- (
    rw[] >> gvs[DISJOINT_BIGUNION, PULL_EXISTS] >> rw[] >> res_tac >>
    irule SUBSET_DISJOINT >> irule_at Any pure_vars_isubst_SUBSET >>
    simp[MAP_MAP_o, combinTheory.o_DEF, pure_vars, MEM_MAP, PULL_EXISTS] >>
    irule_at Any SUBSET_REFL >> rw[MEM_EL] >> gvs[]
    )
  >- (
    rw[] >> gvs[DISJOINT_BIGUNION, PULL_EXISTS] >> rw[] >> res_tac >>
    imp_res_tac infer_atom_op_LENGTH >> simp[MAP2_MAP, EL_MAP, EL_ZIP, pure_vars]
    )
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (
    rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[] >>
    gvs[PULL_EXISTS] >> rw[MEM_EL] >> res_tac
    )
  >- (
    rw[] >> gvs[EL_ZIP, pure_vars] >- (res_tac >> simp[]) >>
    gvs[get_massumptions_def] >> every_case_tac >> gvs[] >> metis_tac[DISJOINT_ALT]
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[] >>
    gvs[get_massumptions_def] >> every_case_tac >> gvs[] >> metis_tac[DISJOINT_ALT]
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> rw[]
    >- res_tac
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (
      gvs[EL_ZIP] >> pairarg_tac >> gvs[pure_vars] >>
      gvs[get_massumptions_def, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      every_case_tac >> gvs[]
      >- (last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT])
      >- (
        reverse $ rw[] >- (last_x_assum drule >> simp[]) >>
        gvs[MEM_EL] >> last_x_assum drule >> pairarg_tac >> rw[] >>
        metis_tac[DISJOINT_ALT]
        )
      >- (last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT])
      >- (
        reverse $ rw[] >- (last_x_assum drule >> simp[]) >>
        gvs[MEM_EL] >> last_x_assum drule >> pairarg_tac >> rw[] >>
        metis_tac[DISJOINT_ALT]
        )
      )
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[] >>
    gvs[get_massumptions_def] >> every_case_tac >> gvs[] >> metis_tac[DISJOINT_ALT]
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[] >>
    gvs[EL_ZIP, EL_MAP, pure_vars] >>
    gvs[get_massumptions_def] >> every_case_tac >> gvs[] >> metis_tac[DISJOINT_ALT]
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> rw[]
    >- res_tac
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >>
      gvs[FLOOKUP_FDIFF] >> last_x_assum drule >> rw[] >> res_tac
      )
    >- res_tac
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >>
      gvs[FLOOKUP_FDIFF] >> last_x_assum drule >> rw[] >> res_tac
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `0` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[]
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `SUC n` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[] >>
      Cases_on `tys` >> gvs[]
      )
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >> gvs[pure_vars]
      >- (
        gvs[get_massumptions_def] >> every_case_tac >> gvs[] >>
        last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT]
        )
      >- (
        qpat_x_assum `MEM _ (MAP2 _ _ _)` mp_tac >>
        DEP_REWRITE_TAC[MAP2_MAP] >> simp[] >>
        reverse conj_asm1_tac
        >- (
          simp[MEM_MAP, MEM_ZIP] >> rw[] >> gvs[pure_vars, EL_MAP] >>
          qpat_x_assum `_ ∈ get_massumptions _ _` mp_tac >>
          gvs[get_massumptions_def] >> CASE_TAC >> rw[] >>
          last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT]
          ) >>
        simp[] >> PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        `cn ≠ "Subscript"` by (
          imp_res_tac ALOOKUP_MEM >> gvs[pure_configTheory.reserved_cns_def] >>
          gvs[MEM_MAP, FORALL_PROD] >> metis_tac[]) >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
        simp[Once MEM_EL, PULL_EXISTS] >>
        disch_then drule >> rw[] >> gvs[] >>
        drule_at (Pos last) ALOOKUP_ALL_DISTINCT_MEM >> simp[]
        )
      >- (last_x_assum drule >> simp[])
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `0` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[]
      )
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> rw[]
    >- res_tac
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >>
      gvs[FLOOKUP_FDIFF] >> last_x_assum drule >> rw[] >> res_tac
      )
    >- res_tac
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >>
      gvs[FLOOKUP_FDIFF] >> last_x_assum drule >> rw[] >> res_tac
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `0` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[]
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `SUC n` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[] >>
      Cases_on `tys` >> gvs[]
      )
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >> gvs[pure_vars]
      >- (
        gvs[get_massumptions_def] >> every_case_tac >> gvs[] >>
        last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT]
        )
      >- (
        qpat_x_assum `MEM _ (MAP2 _ _ _)` mp_tac >>
        DEP_REWRITE_TAC[MAP2_MAP] >> simp[] >>
        reverse conj_asm1_tac
        >- (
          simp[MEM_MAP, MEM_ZIP] >> rw[] >> gvs[pure_vars, EL_MAP] >>
          qpat_x_assum `_ ∈ get_massumptions _ _` mp_tac >>
          gvs[get_massumptions_def] >> CASE_TAC >> simp[] >> strip_tac >>
          last_x_assum drule >> simp[] >> strip_tac >>
          conj_tac >- metis_tac[DISJOINT_ALT] >>
          irule SUBSET_DISJOINT >> irule_at Any pure_vars_isubst_SUBSET >>
          simp[MAP_MAP_o, combinTheory.o_DEF, pure_vars, MEM_MAP, PULL_EXISTS] >>
          irule_at Any SUBSET_REFL >> rw[MEM_EL] >> gvs[]
          ) >>
        simp[] >> PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        `MEM (cn, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)` by (
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
      >- (last_x_assum drule >> simp[])
      )
    >- (
      last_x_assum assume_tac >> last_x_assum $ qspec_then `0` mp_tac >>
      reverse $ Cases_on `final_cs` >> gvs[]
      >- (pairarg_tac >> simp[]) >>
      PairCases_on `ns` >> gvs[namespace_ok_def] >>
      gvs[EVERY_EL, oEL_THM] >> last_x_assum drule >> simp[]
      )
    )
QED

Theorem minfer_pure_vars[local]:
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
    first_x_assum drule >> strip_tac >> gvs[SF SFY_ss] >>
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

Theorem minfer_pure_vars:
  ∀ns mset cexp as cs it v.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns
  ⇒ pure_vars it ⊆ new_vars as cs Exception
Proof
  rw[SUBSET_DEF] >> imp_res_tac minfer_pure_vars
QED

Theorem minfer_constraints_ok:
  ∀ns mset cexp as cs it.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns ∧
    FINITE mset
  ⇒ constraints_ok (SND ns) cs
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[constraints_ok_def, itype_ok, itype_ok_iFunctions] >>
  gvs[LIST_REL_EL_EQN, EL_ZIP, MEM_EL, MAP2_MAP, EL_MAP,
      PULL_EXISTS, SF CONJ_ss, pure_vars] >>
  rpt gen_tac >> imp_res_tac minfer_itype_ok
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (
    strip_tac >> gvs[itype_ok] >> res_tac >> simp[] >> res_tac >> simp[] >>
    simp[itype_ok_type_ok] >>
    PairCases_on `ns` >> gvs[namespace_ok_def, EVERY_MEM, FORALL_PROD] >>
    imp_res_tac ALOOKUP_MEM >> first_x_assum drule >> disch_then irule >> simp[EL_MEM]
    )
  >- (
    strip_tac >> gvs[itype_ok] >> res_tac >> simp[] >> res_tac >> simp[] >>
    irule itype_ok_isubst >> simp[EVERY_MAP, itype_ok] >>
    simp[itype_ok_type_ok] >>
    PairCases_on `ns` >> gvs[namespace_ok_def, EVERY_EL, FORALL_PROD] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL] >> pop_assum $ assume_tac o GSYM >>
    first_x_assum drule >> simp[] >> disch_then drule >> simp[]
    )
  >- (
    strip_tac >> gvs[itype_ok] >> res_tac >> simp[] >>
    imp_res_tac infer_atom_op_LENGTH >> gvs[MAP2_MAP, EL_MAP, EL_ZIP, itype_ok] >>
    res_tac >> simp[] >> res_tac >> simp[]
    )
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (
    strip_tac >> gvs[itype_ok, itype_ok_iFunctions] >> res_tac >> simp[] >>
    rw[EVERY_EL] >> last_x_assum drule >> strip_tac >> imp_res_tac minfer_itype_ok
    )
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (
    strip_tac >> gvs[itype_ok] >> res_tac >> simp[] >>
    rpt (pairarg_tac >> gvs[])
    >- (last_x_assum drule >> rw[] >> imp_res_tac minfer_itype_ok)
    >- (last_x_assum drule >> simp[] >> strip_tac >> res_tac >> simp[])
    >- (simp[itype_ok] >> last_x_assum drule >> rw[] >> imp_res_tac minfer_itype_ok)
    )
  >- (strip_tac >> gvs[itype_ok] >> res_tac >> simp[])
  >- (
    strip_tac >> gvs[itype_ok] >> res_tac >> simp[] >>
    gvs[EVERY_MAP, itype_ok]
    )
  >- (
    strip_tac >> gvs[itype_ok] >> res_tac >> simp[]
    >- (
      imp_res_tac sortingTheory.PERM_LENGTH >> gvs[] >>
      Cases_on `tys` >> gvs[] >> qpat_x_assum `∀n. _` kall_tac >>
      first_assum $ qspec_then `0` mp_tac >>
      first_x_assum $ qspec_then `SUC n` mp_tac >> gvs[] >>
      rpt $ (pairarg_tac >> gvs[]) >> ntac 2 strip_tac >>
      imp_res_tac minfer_itype_ok >> simp[]
      ) >>
    rpt $ (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> simp[] >> strip_tac >>
    first_x_assum drule >> simp[] >> strip_tac >> reverse $ gvs[itype_ok]
    >- (res_tac >> simp[]) >>
    Cases_on `cname = "Subscript"` >> gvs[] >>
    qpat_x_assum `MEM _ (MAP2 _ _ _)` mp_tac >>
    DEP_REWRITE_TAC[MAP2_MAP] >> reverse conj_asm1_tac >> gvs[] >>
    PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND]
    >- (
      simp[MEM_MAP, MEM_ZIP, EL_MAP, EXISTS_PROD, PULL_EXISTS] >>
      gen_tac >> strip_tac >> gvs[itype_ok, EL_MAP] >>
      simp[itype_ok_type_ok] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL, EVERY_EL] >>
      pop_assum $ assume_tac o GSYM >> first_x_assum drule >> simp[]
      ) >>
    `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) ns0)` by (
      drule $ iffRL sortingTheory.PERM_MEM_EQ >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
      simp[Once MEM_EL, PULL_EXISTS] >> disch_then drule >> simp[]) >>
    rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
    rev_drule ALOOKUP_ALL_DISTINCT_MEM >> disch_then drule >> simp[]
    )
  >- (
    strip_tac >> gvs[itype_ok] >> res_tac >> simp[]
    >- gvs[EVERY_MAP, itype_ok]
    >- (
      imp_res_tac sortingTheory.PERM_LENGTH >> gvs[] >>
      Cases_on `tys` >> gvs[] >> qpat_x_assum `∀n. _` kall_tac >>
      first_assum $ qspec_then `0` mp_tac >>
      first_x_assum $ qspec_then `SUC n` mp_tac >> gvs[] >>
      rpt $ (pairarg_tac >> gvs[]) >> ntac 2 strip_tac >>
      imp_res_tac minfer_itype_ok >> simp[]
      ) >>
    rpt $ (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> simp[] >> strip_tac >>
    first_x_assum drule >> simp[] >> strip_tac >> reverse $ gvs[itype_ok]
    >- (res_tac >> simp[]) >>
    qpat_x_assum `MEM _ (MAP2 _ _ _)` mp_tac >>
    DEP_REWRITE_TAC[MAP2_MAP] >> reverse conj_asm1_tac >> gvs[] >>
    PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND]
    >- (
      simp[MEM_MAP, MEM_ZIP, EL_MAP, EXISTS_PROD, PULL_EXISTS] >>
      gen_tac >> strip_tac >> gvs[itype_ok, EL_MAP] >>
      irule itype_ok_isubst >> simp[EVERY_MAP, itype_ok] >>
      simp[itype_ok_type_ok] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL, EVERY_EL] >>
      pop_assum $ assume_tac o GSYM >>
      gvs[oEL_THM] >> first_x_assum drule >> simp[] >> disch_then drule >> simp[]
      ) >>
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


(******************** Simple lemmas ********************)

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
        (GENLIST (λn. csubst sub (CVar $ gm ' n))
          (CARD (FDOM fm)))
        (csubst (DBVar o_f fm) it) = csubst sub it
Proof
  rw[pure_apply_subst, FLOOKUP_DEF] >> drule $ iffRL CARD_has_fmap_linv >> rw[] >>
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

Theorem pure_walkstar_pure_apply_subst_pure_walkstar[local]:
  ∀s. pure_wfs s ⇒
  ∀it sub. (∀v. v ∈ FRANGE sub ⇒ pure_vars v = {}) ⇒
  pure_walkstar s (pure_apply_subst sub (pure_walkstar s it)) =
  pure_apply_subst sub (pure_walkstar s it)
Proof
  gen_tac >> strip_tac >>
  qspec_then `s` mp_tac pure_walkstar_alt_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[pure_walkstar_alt, pure_apply_subst]
  >- simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
  >- simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
  CASE_TAC >> gvs[] >>
  simp[pure_apply_subst] >> CASE_TAC >> gvs[pure_walkstar_alt] >>
  irule pure_walkstar_unchanged >> simp[] >>
  gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
  first_x_assum drule >> simp[]
QED

Triviality new_vars_SUBSET:
  BIGUNION (FRANGE as) ⊆ BIGUNION (FRANGE as') ∧ cs ⊆ cs' ∧
  pure_vars it ⊆ pure_vars it' ∧
  v ∈ new_vars as cs it ⇒
  v ∈ new_vars as' cs' it'
Proof
  rw[new_vars_def] >> gvs[SUBSET_DEF] >> metis_tac[]
QED

Triviality new_vars_SUBSET_minfer:
  BIGUNION (FRANGE as) ⊆ BIGUNION (FRANGE as') ∧ cs ⊆ cs' ∧
  pure_vars it ⊆ new_vars as cs Exception ⇒
  ∀n. n ∈ new_vars as cs it ⇒ n ∈ new_vars as' cs' it'
Proof
  rw[new_vars_def] >> gvs[SUBSET_DEF, pure_vars] >> metis_tac[]
QED

Triviality pure_vars_csubst_EMPTY_suff:
  (∀it. it ∈ FRANGE s ⇒ pure_vars it = {}) ∧
  pure_vars t ⊆ FDOM s ⇒
  pure_vars (csubst s t) = {}
Proof
  rw[] >> once_rewrite_tac[GSYM SUBSET_EMPTY] >> irule SUBSET_TRANS >>
  irule_at Any pure_vars_pure_apply_subst_SUBSET >>
  simp[IMAGE_EQ_SING, SUBSET_DIFF_EMPTY]
QED

Triviality freedbvars_isubst_EMPTY_suff:
  ∀it its.
    freedbvars it ⊆ count (LENGTH its) ∧
    EVERY ( λit. freedbvars it = {}) its
  ⇒ freedbvars (isubst its it) = {}
Proof
  Induct using itype_ind >> rw[isubst_def, freedbvars_def] >>
  gvs[LIST_TO_SET_MAP, IMAGE_EQ_SING, PULL_EXISTS, DISJ_EQ_IMP, BIGUNION_SUBSET] >>
  gvs[EVERY_EL]
QED

Triviality shift_shift_let_lemma:
  ∀it t sub vs1 vs2.
    type_of (csubst (ishift vs1 o_f sub) it) = SOME t ∧
    freedbvars it ⊆ count vs1 ⇒
    type_of (csubst ((ishift vs1 ∘ ishift vs2) o_f sub) it) =
    SOME (shift_db vs1 vs2 t)
Proof
  Induct using itype_ind >> rw[] >>
  gvs[pure_apply_subst, freedbvars_def, type_of_def, shift_db_def]
  >- (
    ntac 2 $ pop_assum mp_tac >> qid_spec_tac `z` >>
    Induct_on `ts` >> rw[] >> gvs[]
    )
  >- (
    ntac 2 $ pop_assum mp_tac >> qid_spec_tac `z` >>
    Induct_on `ts` >> rw[] >> gvs[]
    ) >>
  gvs[FLOOKUP_o_f] >> CASE_TAC >> gvs[type_of_def] >>
  drule_then (assume_tac o GSYM) type_of_SOME >> simp[] >>
  simp[ishift_itype_of, type_of_itype_of] >> gvs[type_of_ishift] >>
  simp[tshift_tshift] >> simp[GSYM tshift_tshift] >> simp[GSYM shift_db_shift_db]
QED

Triviality subset_union:
  a ⊆ c ⇒ a ⊆ b ∪ c
Proof
  rw[SUBSET_DEF]
QED

Theorem minfer_constraint_vars_lemma[local]:
  ∀ns mset cexp as cs it tsub vars tsup.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns ∧
    mImplicit tsub vars tsup ∈ cs
  ⇒ vars ⊆ mset ∪ new_vars as cs it
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[LIST_REL_EL_EQN, EL_ZIP, MEM_EL, MAP2_MAP, EL_MAP] >> res_tac
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET >> goal_assum drule >>
    irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
    simp[pure_vars, SUBSET_DEF, MEM_MAP, MEM_EL, PULL_EXISTS, SF SFY_ss]
    )
  >- gvs[new_vars_def, pure_vars]
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
    simp[pure_vars, SUBSET_DEF, MEM_MAP, MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    first_x_assum drule >> strip_tac >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
    simp[pure_vars, SUBSET_DEF, MEM_MAP, MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    first_x_assum drule >> strip_tac >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (imp_res_tac infer_atom_op_LENGTH >> gvs[MAP2_MAP, EL_MAP, EL_ZIP])
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
    simp[pure_vars, SUBSET_DEF, MEM_MAP, MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    first_x_assum drule >> strip_tac >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion] >>
    once_rewrite_tac[INSERT_SING_UNION] >> rpt $ irule_at Any subset_union >>
    irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
    first_x_assum drule >> strip_tac >>
    imp_res_tac minfer_pure_vars >> simp[] >>
    rw[SUBSET_DEF, MEM_EL, SF SFY_ss, PULL_EXISTS]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac
    >- simp[new_vars_def, pure_vars_iFunctions, MEM_MAP, PULL_EXISTS, pure_vars] >>
    gvs[new_vars_def, PULL_EXISTS, MEM_MAP, SF SFY_ss, IN_FRANGE_FLOOKUP]
    >- (
      Cases_on `k ∈ set xs` >> gvs[FLOOKUP_FDIFF, SF SFY_ss, GSYM DISJ_ASSOC] >>
      ntac 3 disj2_tac >> disj1_tac >>
      simp[MEM_ZIP, get_massumptions_def, EXISTS_PROD, PULL_EXISTS, pure_vars] >>
      gvs[MEM_EL] >> goal_assum $ drule_at Any >> simp[SF DNF_ss]
      )
    >- simp[pure_vars_iFunctions]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    gvs[new_vars_def, PULL_EXISTS, MEM_MAP, SF SFY_ss, IN_FRANGE_FLOOKUP] >>
    Cases_on `k = x` >> gvs[FLOOKUP_maunion, DOMSUB_FLOOKUP_THM, GSYM DISJ_ASSOC]
    >- (disj2_tac >> disj1_tac >> simp[pure_vars, get_massumptions_def, SF DNF_ss])
    >- (
      rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >>
      qexists_tac `k` >> simp[] >> CASE_TAC >> simp[]
      )
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    gvs[new_vars_def, PULL_EXISTS, MEM_MAP, SF SFY_ss, IN_FRANGE_FLOOKUP] >>
    Cases_on `k ∈ set (MAP FST fns)` >>
    gvs[FLOOKUP_FDIFF, FLOOKUP_maunion, SF SFY_ss, GSYM DISJ_ASSOC]
    >- (
      ntac 4 disj2_tac >> disj1_tac >>
      simp[MEM_ZIP, EXISTS_PROD, PULL_EXISTS, pure_vars, SF DNF_ss] >>
      simp[get_massumptions_def, FLOOKUP_maunion] >> disj1_tac >>
      qexists_tac `k` >> simp[] >> gvs[MEM_EL] >>
      goal_assum $ drule_at Any >> gvs[EL_MAP] >> Cases_on `EL n fns` >> simp[] >>
      CASE_TAC >> simp[]
      )
    >- (
      rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >>
      qexists_tac `k` >> simp[] >> CASE_TAC >> simp[]
      )
    )
  >- (
    rpt (pairarg_tac >> gvs[]) >>
    last_x_assum drule >> simp[] >> strip_tac >> pop_assum drule >> rw[] >>
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    gvs[new_vars_def, PULL_EXISTS, MEM_MAP, SF SFY_ss, IN_FRANGE_FLOOKUP]
    >- (
      Cases_on `k ∈ set (MAP FST fns)` >>
      gvs[FLOOKUP_FDIFF, FLOOKUP_maunion, SF SFY_ss, GSYM DISJ_ASSOC]
      >- (
        ntac 4 disj2_tac >> disj1_tac >>
        simp[MEM_ZIP, EXISTS_PROD, PULL_EXISTS, pure_vars, SF DNF_ss] >>
        simp[get_massumptions_def, FLOOKUP_maunion] >> disj1_tac >>
        qexists_tac `k` >> simp[] >> gvs[MEM_EL, EL_MAP] >>
        Cases_on `EL n' fns` >> gvs[] >>
        qsuff_tac `∃v. FLOOKUP (FOLDR maunion FEMPTY ass) q = SOME v ∧ s ⊆ v` >>
        rw[] >> gvs[SUBSET_DEF]
        >- (CASE_TAC >> gvs[] >> goal_assum drule >> simp[]) >>
        simp[FLOOKUP_FOLDR_maunion, PULL_EXISTS, MEM_EL, SF SFY_ss] >>
        gvs[FLOOKUP_DEF, SF SFY_ss]
        )
      >- (
        rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >>
        qexists_tac `k` >> simp[] >>
        qsuff_tac `∃v. FLOOKUP (FOLDR maunion FEMPTY ass) k = SOME v ∧ s ⊆ v` >>
        rw[] >> gvs[SUBSET_DEF]
        >- (CASE_TAC >> gvs[] >> goal_assum drule >> simp[]) >>
        simp[FLOOKUP_FOLDR_maunion, PULL_EXISTS, MEM_EL, SF SFY_ss] >>
        gvs[FLOOKUP_DEF, SF SFY_ss]
        )
      )
    >- simp[MEM_EL, PULL_EXISTS, SF SFY_ss]
    >- simp[MEM_EL, PULL_EXISTS, SF SFY_ss]
    )
  >- (rpt (pairarg_tac >> gvs[]))
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    gvs[new_vars_def, PULL_EXISTS, pure_vars, SF SFY_ss, GSYM DISJ_ASSOC] >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, DOMSUB_FLOOKUP_THM, PULL_EXISTS] >>
    Cases_on `k = v` >> gvs[] >- gvs[get_massumptions_def, SF DNF_ss] >>
    rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
    CASE_TAC >> simp[] >> CASE_TAC >> simp[]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    gvs[new_vars_def, PULL_EXISTS, pure_vars, SF SFY_ss, GSYM DISJ_ASSOC] >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, DOMSUB_FLOOKUP_THM, PULL_EXISTS] >>
    Cases_on `k = v` >> gvs[] >- gvs[get_massumptions_def, SF DNF_ss] >>
    rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
    CASE_TAC >> simp[] >> CASE_TAC >> simp[]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[]
    >- simp[new_vars_def, pure_vars, MEM_MAP, PULL_EXISTS]
    >- simp[new_vars_def, pure_vars, MEM_MAP, PULL_EXISTS] >>
    disj2_tac >> gvs[new_vars_def, PULL_EXISTS, pure_vars, SF SFY_ss, GSYM DISJ_ASSOC] >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FDIFF, PULL_EXISTS] >>
    Cases_on `k = v` >> gvs[] >- gvs[get_massumptions_def, SF DNF_ss] >>
    Cases_on `MEM k pvars` >> gvs[]
    >- (
      ntac 6 disj2_tac >> disj1_tac >>
      simp[MEM_MAP, MEM_ZIP, PULL_EXISTS, pure_vars, get_massumptions_def] >>
      gvs[MEM_EL] >> goal_assum $ drule_at Any >>
      simp[EL_MAP, pure_vars, SF SFY_ss, SF DNF_ss]
      ) >>
    rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >>
    qexists_tac `k` >> simp[] >> CASE_TAC >> gvs[]
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> simp[] >> strip_tac >>
    first_x_assum drule >> simp[] >> strip_tac >> gvs[]
    >- (
      qpat_x_assum `MEM _ (MAP2 _ _ _)` mp_tac >>
      DEP_REWRITE_TAC[MAP2_MAP] >> conj_asm1_tac
      >- (
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
        ) >>
      simp[MEM_MAP, MEM_ZIP, EXISTS_PROD, PULL_EXISTS] >> rw[] >> gvs[]
      )
    >- (
      first_x_assum drule >> rw[SUBSET_DEF] >> gvs[] >>
      first_x_assum drule >> strip_tac >> gvs[]
      >- simp[new_vars_def, pure_vars] >>
      disj2_tac >>
      `LENGTH pvars = LENGTH schemes` by (
        PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        qsuff_tac `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH schemes)) ns0)`
        >- (rw[] >> gvs[MEM_MAP, EXISTS_PROD]) >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
        simp[Once MEM_EL, PULL_EXISTS] >>
        disch_then drule >> simp[DISJ_IMP_THM] >> strip_tac >> gvs[]
        >- (
          last_x_assum $ qspec_then `"Subscript"` mp_tac >>
          simp[pure_configTheory.reserved_cns_def] >>
          imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
          )
        >- (
          rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
          rev_drule ALOOKUP_ALL_DISTINCT_MEM >> disch_then drule >> simp[SF SFY_ss]
          )) >>
      gvs[new_vars_def, IN_FRANGE_FLOOKUP, pure_vars, PULL_EXISTS, GSYM DISJ_ASSOC]
      >- (
        Cases_on `k = v` >> gvs[]
        >- (
          ntac 6 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
          goal_assum $ drule_at Any >> simp[SF DNF_ss, pure_vars, get_massumptions_def]
          ) >>
        Cases_on `MEM k pvars` >> gvs[]
        >- (
          ntac 6 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
          goal_assum $ drule_at Any >>
          simp[pure_vars, get_massumptions_def, GSYM DISJ_ASSOC] >>
          simp[MAP2_MAP, MEM_MAP, MEM_ZIP, EL_MAP, PULL_EXISTS, SF DNF_ss, pure_vars] >>
          disj2_tac >> rpt disj1_tac >>
          gvs[MEM_EL] >> goal_assum $ drule_at Any >> simp[]
          )
        >- (
          rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >>
          simp[FLOOKUP_maunion] >>
          qsuff_tac `∃v. FLOOKUP (FOLDR maunion FEMPTY final_as) k = SOME v ∧ s ⊆ v` >>
          rw[] >> gvs[SUBSET_DEF]
          >- (CASE_TAC >> gvs[] >> goal_assum drule >> simp[]) >>
          simp[FLOOKUP_FOLDR_maunion, PULL_EXISTS, MEM_EL] >>
          goal_assum $ drule_at Any >> rw[] >- gvs[FLOOKUP_DEF] >>
          rpt $ goal_assum drule >> simp[FLOOKUP_FDIFF]
          )
        )
      >- (
        ntac 6 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        rpt $ goal_assum $ drule_at Any >> simp[]
        )
      >- (
        Cases_on `n` >> gvs[EL] >> ntac 4 disj2_tac >> disj1_tac >>
        simp[MEM_MAP, MEM_EL, PULL_EXISTS] >> qexists_tac `n'` >> simp[] >>
        Cases_on `tys` >> gvs[]
        )
      )
    )
  >- (
    gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> disj2_tac >>
    irule new_vars_SUBSET_minfer >> goal_assum drule >>
    simp[BIGUNION_FRANGE_maunion, pure_vars] >>
    imp_res_tac minfer_pure_vars >> gvs[SUBSET_DEF]
    )
  >- (
    rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> simp[] >> strip_tac >>
    first_x_assum drule >> simp[] >> strip_tac >> gvs[]
    >- (
      qpat_x_assum `MEM _ (MAP2 _ _ _)` mp_tac >>
      DEP_REWRITE_TAC[MAP2_MAP] >> conj_asm1_tac
      >- (
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
        ) >>
      simp[MEM_MAP, MEM_ZIP, EXISTS_PROD, PULL_EXISTS] >> rw[] >> gvs[]
      )
    >- (
      first_x_assum drule >> rw[SUBSET_DEF] >> gvs[] >>
      first_x_assum drule >> strip_tac >> gvs[]
      >- simp[new_vars_def, pure_vars]
      >- simp[new_vars_def, pure_vars, MEM_MAP, PULL_EXISTS] >>
      disj2_tac >>
      `LENGTH pvars = LENGTH schemes` by (
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
        gvs[oEL_THM] >> goal_assum drule >> simp[]) >>
      gvs[new_vars_def, IN_FRANGE_FLOOKUP, pure_vars, PULL_EXISTS, GSYM DISJ_ASSOC]
      >- (
        Cases_on `k = v` >> gvs[]
        >- (
          ntac 7 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
          goal_assum $ drule_at Any >> simp[SF DNF_ss, pure_vars, get_massumptions_def]
          ) >>
        Cases_on `MEM k pvars` >> gvs[]
        >- (
          ntac 7 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
          goal_assum $ drule_at Any >>
          simp[pure_vars, get_massumptions_def, GSYM DISJ_ASSOC] >>
          simp[MAP2_MAP, MEM_MAP, MEM_ZIP, EL_MAP, PULL_EXISTS, SF DNF_ss, pure_vars] >>
          disj2_tac >> rpt disj1_tac >>
          gvs[MEM_EL] >> goal_assum $ drule_at Any >> simp[]
          )
        >- (
          rpt disj1_tac >> simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >>
          simp[FLOOKUP_maunion] >>
          qsuff_tac `∃v. FLOOKUP (FOLDR maunion FEMPTY final_as) k = SOME v ∧ s ⊆ v` >>
          rw[] >> gvs[SUBSET_DEF]
          >- (CASE_TAC >> gvs[] >> goal_assum drule >> simp[]) >>
          simp[FLOOKUP_FOLDR_maunion, PULL_EXISTS, MEM_EL] >>
          goal_assum $ drule_at Any >> rw[] >- gvs[FLOOKUP_DEF] >>
          rpt $ goal_assum drule >> simp[FLOOKUP_FDIFF]
          )
        )
      >- (
        ntac 7 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        rpt $ goal_assum $ drule_at Any >> simp[]
        )
      >- (
        Cases_on `n` >> gvs[EL] >> ntac 5 disj2_tac >> disj1_tac >>
        simp[MEM_MAP, MEM_EL, PULL_EXISTS] >> qexists_tac `n'` >> simp[] >>
        Cases_on `tys` >> gvs[]
        )
      )
    )
QED

Theorem minfer_constraint_vars:
  ∀ns mset cexp as cs it.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns
  ⇒ BIGUNION (IMAGE constraint_vars cs) ⊆ mset ∪ new_vars as cs it
Proof
  rw[BIGUNION_SUBSET] >>
  rw[SUBSET_DEF, new_vars_def, PULL_EXISTS, GSYM DISJ_ASSOC] >>
  Cases_on `x` >> gvs[]
  >- (
    ntac 2 disj2_tac >> disj1_tac >> goal_assum $ drule_at Any >>
    gvs[constraint_vars_def, new_vars_constraint_def]
    )
  >- (
    ntac 2 disj2_tac >> disj1_tac >> goal_assum $ drule_at Any >>
    PairCases_on `p` >> gvs[constraint_vars_def, new_vars_constraint_def]
    ) >>
  drule_all minfer_constraint_vars_lemma >> strip_tac >>
  gvs[constraint_vars_def]
  >- (
    ntac 2 disj2_tac >> disj1_tac >> goal_assum $ drule_at Any >>
    gvs[constraint_vars_def, new_vars_constraint_def]
    )
  >- (
    gvs[new_vars_def, SUBSET_DEF] >>
    first_x_assum drule >> strip_tac >> gvs[SF SFY_ss]
    )
  >- (
    ntac 2 disj2_tac >> disj1_tac >> goal_assum $ drule_at Any >>
    gvs[constraint_vars_def, new_vars_constraint_def]
    )
QED


(******************** Definitions/apparatus ********************)

Definition ctxt_vars_def:
  ctxt_vars ctxt = BIGUNION (set (MAP (λ(x,vs,t). pure_vars t) ctxt))
End

Theorem ctxt_vars:
  ctxt_vars [] = {} ∧
  ctxt_vars ((x,vs,t)::ctxt) = pure_vars t ∪ ctxt_vars ctxt ∧
  ctxt_vars (ctxt ++ ctxt') = ctxt_vars ctxt ∪ ctxt_vars ctxt'
Proof
  simp[ctxt_vars_def]
QED

Definition subst_ctxt_def:
  subst_ctxt s ctxt = MAP (λ(x,vs,t). (x,vs,pure_walkstar s t)) ctxt
End

Theorem subst_ctxt:
  subst_ctxt s [] = [] ∧
  subst_ctxt s ((x,vs,t)::ctxt) =
    (x,vs,pure_walkstar s t)::(subst_ctxt s ctxt) ∧
  subst_ctxt s (ctxt ++ ctxt') = subst_ctxt s ctxt ++ subst_ctxt s ctxt'
Proof
  simp[subst_ctxt_def]
QED

Theorem ctxt_vars_subst_ctxt:
  pure_wfs s ⇒
  ctxt_vars (subst_ctxt s ctxt) = msubst_vars s (ctxt_vars ctxt)
Proof
  Induct_on `ctxt` >> simp[ctxt_vars, subst_ctxt, msubst_vars_def] >>
  rw[] >> PairCases_on `h` >> simp[ctxt_vars, subst_ctxt, msubst_vars_def] >>
  simp[pure_vars_pure_walkstar_alt]
QED

Definition satisfies_def:
  satisfies tdefs s (mUnify t1 t2) = (pure_walkstar s t1 = pure_walkstar s t2) ∧

  satisfies tdefs s (mInstantiate t (vars, scheme)) = (
    ∃subs.
      LENGTH subs = vars ∧ EVERY (itype_ok tdefs 0) subs ∧
      EVERY (λit. pure_vars it ⊆ pure_vars (pure_walkstar s t)) subs ∧
      pure_walkstar s t = isubst subs (pure_walkstar s scheme)) ∧

  satisfies tdefs s (mImplicit tsub vars tsup) = (
    ∃sub.
      FDOM sub ⊆ pure_vars (pure_walkstar s tsup) DIFF (msubst_vars s vars) ∧
      (∀it. it ∈ FRANGE sub ⇒ itype_ok tdefs 0 it ∧
        pure_vars it ⊆ pure_vars (pure_walkstar s tsub)) ∧
      pure_walkstar s tsub = pure_apply_subst sub (pure_walkstar s tsup))
End

Theorem satisfies_lemmas:
    satisfies tdefs s (mUnify t1 t2) = satisfies tdefs s (mInstantiate t1 (0, t2)) ∧
    (pure_wfs s ⇒
      satisfies tdefs s (mUnify t1 t2) =
      satisfies tdefs s (mImplicit t1 (pure_vars t2) t2)) ∧
    (pure_wfs s ∧ freedbvars (pure_walkstar s t2) = {} ⇒
      satisfies tdefs s (mImplicit t1 vs t2) =
        ∀gen.
          let new = pure_vars (pure_walkstar s t2) DIFF msubst_vars s vs in
          FDOM gen = new ∧
          FRANGE gen = count (CARD new)
        ⇒ satisfies tdefs s $ mInstantiate t1 $
            (CARD new, csubst (DBVar o_f gen) (pure_walkstar s t2)))
Proof
  rpt conj_tac >> rw[satisfies_def]
  >- (
    eq_tac >> rw[] >- (qexists_tac `FEMPTY` >> simp[]) >>
    gvs[msubst_vars_def, PULL_EXISTS] >>
    irule pure_apply_subst_unchanged >>
    simp[pure_vars_pure_walkstar_alt] >> simp[PULL_EXISTS, pure_vars] >>
    simp[Once DISJOINT_SYM] >> rw[DISJOINT_ALT] >>
    gvs[SUBSET_DEF] >> metis_tac[]
    ) >>
  eq_tac >> rw[] >> gvs[]
  >- (
    simp[Once pure_apply_subst_min] >>
    qmatch_goalsub_abbrev_tac `csubst sub'` >>
    qspecl_then [`gen`,`sub'`,`pure_walkstar s t2`]
      mp_tac pure_apply_subst_split_isubst >>
    simp[] >> impl_tac >> rw[]
    >- (
      unabbrev_all_tac >> gvs[FDOM_DRESTRICT] >>
      gvs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
      ) >>
    qmatch_asmsub_abbrev_tac `isubst its` >>
    qexists_tac `its` >> simp[] >>
    DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
    unabbrev_all_tac >> simp[] >>
    simp[EVERY_GENLIST] >> rw[]
    >- (
      simp[pure_apply_subst, FLOOKUP_DRESTRICT] >>
      every_case_tac >> gvs[itype_ok] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >> metis_tac[]
      )
    >- (
      rw[SUBSET_DEF] >>
      simp[pure_vars_pure_apply_subst] >> simp[PULL_EXISTS, pure_vars] >>
      goal_assum drule >>
      qsuff_tac `gm ' n ∈ FDOM gen` >- rw[] >>
      gvs[fmap_linv_alt_def] >> simp[IN_FRANGE_FLOOKUP, FLOOKUP_DEF] >>
      goal_assum drule >> simp[]
      )
    >- simp[Once pure_apply_subst_min]
    )
  >- (
    qmatch_asmsub_abbrev_tac `FDOM _ = diff` >>
    `FINITE diff` by (unabbrev_all_tac >> irule FINITE_DIFF >> simp[]) >>
    drule $ INST_TYPE [beta |-> ``:num``] cardinalTheory.CARD_CARDEQ_I >>
    disch_then $ qspec_then `count (CARD diff)` mp_tac >> simp[] >>
    rw[cardinalTheory.cardeq_def] >>
    first_x_assum $ qspec_then `FUN_FMAP f diff` mp_tac >> simp[] >>
    imp_res_tac BIJ_IMAGE >> rw[] >> simp[] >>
    pop_assum mp_tac >>
    DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >> strip_tac >>
    simp[isubst_pure_apply_subst_alt] >>
    irule_at Any EQ_REFL >> unabbrev_all_tac >> simp[DISJOINT_DIFF] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >> rw[]
    >- (
      rw[isubst_def] >- gvs[EVERY_EL, pure_vars] >>
      irule FALSITY >> pop_assum mp_tac >> simp[] >> gvs[BIJ_IFF_INV]
      ) >>
    reverse $ rw[isubst_def]
    >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> gvs[BIJ_IFF_INV]) >>
    simp[pure_vars_pure_apply_subst] >>
    simp[combinTheory.o_DEF, SUBSET_DEF, PULL_EXISTS] >> rw[] >>
    simp[pure_apply_subst, FLOOKUP_o_f, FLOOKUP_FUN_FMAP] >>
    qexists_tac `x'` >> simp[isubst_def]
    )
QED

Definition generalises_to_def:
  generalises_to mono t sch ⇔
    let new = pure_vars t DIFF mono in
    ∃gen.
      FDOM gen = new ∧ FRANGE gen = count (CARD new) ∧
      sch = (CARD new, csubst (DBVar o_f gen) t)
End

Theorem satisfies_implicit_alt_lemma[local]:
  pure_wfs s ∧ freedbvars (pure_walkstar s t2) = {} ∧ FINITE vs ⇒
  satisfies tdefs s (mImplicit t1 vs t2) =
    ∃gen. let new = pure_vars (pure_walkstar s t2) DIFF msubst_vars s vs in
      FDOM gen = new ∧ FRANGE gen = count (CARD new) ∧
      satisfies tdefs s $ mInstantiate t1 $
        (CARD new, csubst (DBVar o_f gen) (pure_walkstar s t2))
Proof
  rw[satisfies_def] >> reverse eq_tac >> rw[]
  >- (
    pop_assum mp_tac >>
    DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >> rw[] >>
    simp[isubst_pure_apply_subst_alt] >>
    irule_at Any EQ_REFL >> rw[] >> gvs[GSYM IMAGE_FRANGE, isubst_def, EVERY_EL] >>
    simp[pure_vars_pure_apply_subst] >> rw[SUBSET_DEF, PULL_EXISTS] >>
    `∃v. FLOOKUP gen v = SOME x` by simp[GSYM IN_FRANGE_FLOOKUP] >>
    qexists_tac `v` >> simp[pure_apply_subst, FLOOKUP_o_f, isubst_def] >>
    gvs[FLOOKUP_DEF]
    )
  >- (
    `∃svs :num_set. domain svs = msubst_vars s vs ∧ wf svs` by (
      qexists_tac `list_to_num_set (SET_TO_LIST (msubst_vars s vs))` >>
      simp[EXTENSION, domain_list_to_num_set, wf_list_to_num_set] >>
      DEP_REWRITE_TAC[MEM_SET_TO_LIST] >> simp[msubst_vars_def, PULL_EXISTS]) >>
    qabbrev_tac `gen = generalise 0 svs FEMPTY (pure_walkstar s t2)`  >>
    PairCases_on `gen` >> gvs[] >> imp_res_tac generalise_0_FEMPTY >> gvs[] >>
    qmatch_asmsub_abbrev_tac `(new,gen_sub,sch)` >> pop_assum kall_tac >>
    goal_assum drule >> simp[] >>
    qspecl_then [`gen_sub`,`sub`,`pure_walkstar s t2`]
      mp_tac pure_apply_subst_split_isubst >> rw[] >>
    pop_assum $ assume_tac o GSYM >> simp[] >>
    DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
    irule_at Any EQ_REFL >> rw[EVERY_GENLIST]
    >- (irule itype_ok_pure_apply_subst >> simp[itype_ok]) >>
    qpat_x_assum `csubst _ _ = _` $ assume_tac o GSYM >> rw[SUBSET_DEF] >>
    simp[pure_vars_pure_apply_subst] >> simp[PULL_EXISTS, pure_vars] >>
    goal_assum drule >> qsuff_tac `gm ' n ∈ FRANGE gm`
    >- (imp_res_tac fmap_linv_alt_def >> gvs[EXTENSION]) >>
    simp[FRANGE_DEF] >> gvs[fmap_linv_alt_def] >> goal_assum drule >> simp[]
    )
QED

Theorem satisfies_implicit_alt:
  pure_wfs s ∧ freedbvars (pure_walkstar s t2) = {} ∧ FINITE vs ⇒ (
  satisfies tdefs s (mImplicit t1 vs t2) ⇔
  ∃sch.
    generalises_to (msubst_vars s vs) (pure_walkstar s t2) sch ∧
    satisfies tdefs s (mInstantiate t1 sch))
Proof
  rw[satisfies_implicit_alt_lemma] >> simp[generalises_to_def, PULL_EXISTS]
QED

Theorem satisfies_sub:
  satisfies tds sub' (to_mconstraint (subst_constraint sub c)) ∧
  pure_compat sub sub'
  ⇒ satisfies tds sub' (to_mconstraint c)
Proof
  Cases_on `c` >> simp[subst_constraint_def]
  >- (
    rename1 `_ ⇒ _ $ mUnify t1 t2` >> rw[satisfies_def] >>
    gvs[pure_compat_def]
    )
  >- (
    Cases_on `p` >> rename1 `mInstantiate t (vs,sch)` >>
    rw[satisfies_def, subst_constraint_def] >>
    gvs[pure_compat_def] >>
    irule_at Any EQ_REFL >> simp[]
    )
  >- (
    rename1 `_ ⇒ _ $ mImplicit t1 (domain vs) t2` >> rw[satisfies_def] >>
    gvs[pure_compat_def] >>
    qsuff_tac
      `msubst_vars sub' (domain (subst_vars sub vs)) = msubst_vars sub' (domain vs)`
    >- (rw[] >> gvs[pure_compat_def] >> goal_assum drule >> simp[]) >>
    DEP_REWRITE_TAC[subst_vars_msubst_vars] >> gvs[pure_compat_def] >>
    simp[msubst_vars_def, Once EXTENSION, PULL_EXISTS] >> rw[] >> eq_tac >> rw[]
    >- (
      goal_assum $ drule_at Any >>
      qpat_x_assum `∀t. _ = _` $ once_rewrite_tac o single o GSYM >>
      simp[Once pure_vars_pure_walkstar_alt, PULL_EXISTS] >>
      goal_assum drule >> simp[]
      )
    >- (
      qpat_x_assum `_ ∈ pure_vars _` mp_tac >>
      qpat_x_assum `∀t. _ = _` $ rewrite_tac o single o Once o GSYM >>
      rw[Once pure_vars_pure_walkstar_alt, PULL_EXISTS] >> rpt $ goal_assum drule
      )
    )
QED

Theorem generalise_solve_implicit:
  pure_wfs s ∧
  pure_vars t ∩ pure_substvars s ⊆ monos ∧
  generalises_to monos t (gen, sch) ⇒
  generalises_to (msubst_vars s monos) (pure_walkstar s t) (gen, pure_walkstar s sch)
Proof
  rw[generalises_to_def] >>
  DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst] >> conj_tac >> rw[]
  >- (gvs[EXTENSION, SUBSET_DEF, DISJOINT_ALT, pure_substvars] >> metis_tac[]) >>
  qsuff_tac
    `pure_vars (pure_walkstar s t) DIFF msubst_vars s monos =
      pure_vars t DIFF monos`
  >- (
    rw[] >> goal_assum drule >> simp[] >>
    simp[combinTheory.o_DEF, pure_walkstar_alt, SF ETA_ss]
    ) >>
  rw[EXTENSION] >> simp[pure_vars_pure_walkstar_alt] >>
  simp[PULL_EXISTS, pure_vars] >> eq_tac >> rw[] >> gvs[SUBSET_DEF]
  >- (
    rename1 `CVar k` >> Cases_on `k ∈ monos`
    >- gvs[msubst_vars_def, DISJ_EQ_IMP, PULL_FORALL] >>
    `k ∉ FDOM s` by (CCONTR_TAC >> gvs[pure_substvars]) >>
    gvs[pure_walkstar_alt, FLOOKUP_DEF, pure_vars, DISJOINT_ALT]
    )
  >- (
    rename1 `CVar k` >> Cases_on `k ∈ monos`
    >- gvs[msubst_vars_def, DISJ_EQ_IMP, PULL_FORALL] >>
    `k ∉ FDOM s` by (CCONTR_TAC >> gvs[pure_substvars]) >>
    gvs[pure_walkstar_alt, FLOOKUP_DEF, pure_vars, DISJOINT_ALT]
    )
  >- (
    `x ∉ FDOM s ∧ x ∉ pure_rangevars s` by (CCONTR_TAC >> gvs[pure_substvars]) >>
    goal_assum $ drule_at Any >> rw[]
    >- simp[pure_walkstar_alt, FLOOKUP_DEF, pure_vars] >>
    gvs[msubst_vars_def, pure_rangevars, DISJ_EQ_IMP, PULL_FORALL, PULL_EXISTS] >>
    rw[] >> drule_all $ SRULE [SUBSET_DEF] pure_vars_pure_walkstar_SUBSET >>
    rw[pure_vars, GSYM IMAGE_FRANGE, PULL_EXISTS] >> gvs[]
    )
QED


(******************** Constraint generation ********************)

Definition ctxt_rel_def:
  ctxt_rel tdefs sub as ctxt ⇔
    ∀k v. FLOOKUP as k = SOME v ⇒
      ∃vars scheme.
        ALOOKUP ctxt k = SOME (vars,scheme) ∧
        ∀n. n ∈ v ⇒
          ∃inst. LENGTH inst = vars ∧
            EVERY (λit. itype_ok tdefs 0 it ∧
                        pure_vars it ⊆ pure_vars (pure_walkstar sub (CVar n))) inst ∧
            isubst inst (pure_walkstar sub scheme) = pure_walkstar sub (CVar n)
End

Theorem ctxt_rel_mInstantiate:
  pure_wfs sub ∧
  ctxt_rel tdefs sub as ctxt ⇒
    ∀k v. FLOOKUP as k = SOME v ⇒
      ∃vars scheme. ALOOKUP ctxt k = SOME (vars,scheme) ∧
        ∀n. n ∈ v ⇒
          satisfies tdefs sub $ mInstantiate (CVar n) (vars, scheme)
Proof
  rw[ctxt_rel_def] >> first_x_assum drule >> rw[] >> simp[] >>
  rw[] >> first_x_assum drule >> rw[satisfies_def] >>
  irule_at Any EQ_REFL >> simp[] >> gvs[EVERY_MEM]
QED

Theorem ctxt_rel_sub:
  ∀tdefs sub as ctxt as'.
    ctxt_rel tdefs sub as ctxt ∧
    (∀k v. FLOOKUP as' k = SOME v ⇒ ∃v'. FLOOKUP as k = SOME v' ∧ v ⊆ v')
  ⇒ ctxt_rel tdefs sub as' ctxt
Proof
  rw[ctxt_rel_def] >> first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >> simp[] >> rw[] >> gvs[SUBSET_DEF]
QED

Theorem inference_constraints_sound_lemma:
  ∀ns sub.
    namespace_ok ns ∧
    pure_wfs sub ∧
    (∀it. it ∈ FRANGE sub ⇒ itype_ok (SND ns) 0 it) ⇒
  ∀mset cexp as cs it ictxt ctxt db closing t.
    minfer ns mset cexp as cs it ∧
    FINITE mset ∧
    (∀c. c ∈ cs ⇒ satisfies (SND ns) sub c) ∧
    ctxt_rel (SND ns) sub as ictxt ∧
    EVERY (λ(x,vs,it). freedbvars it ⊆ count vs) ictxt ∧
    msubst_vars sub (ctxt_vars ictxt) = msubst_vars sub mset ∧
    (∀n. n ∈ new_vars as cs it ⇒
      pure_vars (pure_walkstar sub (CVar n)) ⊆ FDOM closing) ∧
    (∀it. it ∈ FRANGE closing ⇒ pure_vars it = {} ∧ itype_ok (SND ns) db it) ∧
    LIST_REL (λ(xs,vs,t) (ixs,ivs,it). xs = ixs ∧ vs = ivs ∧
      type_of $ csubst (ishift vs o_f closing) (pure_walkstar sub it) = SOME t)
      ctxt ictxt ∧
    type_of $ csubst closing (pure_walkstar sub it) = SOME t
    ⇒ type_tcexp ns db [] ctxt (tcexp_of cexp) t
Proof
  rpt gen_tac >> strip_tac >>
  ntac 5 gen_tac >> Induct_on `minfer` >> rw[tcexp_of_def] >> gvs[]
  >- ( (* Var *)
    simp[Once type_tcexp_cases] >> gvs[ctxt_rel_def, FLOOKUP_UPDATE] >>
    qspecl_then [`ictxt`,`ctxt`] mp_tac ALOOKUP_SOME_EL_2 >>
    disch_then drule >> gvs[LIST_REL_EL_EQN] >> impl_tac
    >- (
      rw[Once LIST_EQ_REWRITE, EL_MAP] >>
      first_x_assum drule >> rpt (pairarg_tac >> simp[])
      ) >>
    strip_tac >> gvs[] >> rename1 `_ = (v,s)` >> PairCases_on `s` >>
    first_x_assum drule >> rw[specialises_def] >>
    `EVERY (λit. pure_vars it = {}) (MAP (csubst closing) inst)` by (
      gvs[EVERY_MAP, EVERY_MEM] >> rw[] >>
      first_x_assum drule >> rw[] >>
      simp[pure_vars_pure_apply_subst] >> rw[IMAGE_EQ_SING, DISJ_EQ_IMP] >>
      simp[pure_apply_subst] >> reverse CASE_TAC >> gvs[pure_vars]
      >- (gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >> first_x_assum drule >> simp[]) >>
      gvs[new_vars_def, pure_vars] >> gvs[FLOOKUP_DEF, SUBSET_DEF]) >>
    gvs[pure_vars_empty_eq_type_of_MAP] >>
    qexists_tac `ts` >> rw[] >> gvs[]
    >- (
      gvs[MAP_EQ_EVERY2, EVERY_EL, LIST_REL_EL_EQN] >> rw[] >>
      simp[GSYM itype_ok_type_ok] >> first_x_assum drule >> rw[EL_MAP] >>
      drule type_of_SOME >> rw[] >>
      irule itype_ok_pure_apply_subst >> simp[] >>
      last_x_assum drule >> rw[] >> gvs[itype_ok_def]
      )
    >- gvs[MAP_EQ_EVERY2] >>
    simp[GSYM itype_of_11, GSYM isubst_itype_of] >>
    drule type_of_SOME_MAP >> rw[] >>
    imp_res_tac type_of_SOME >> rw[] >>
    simp[GSYM pure_apply_subst_isubst_strong]
    )
  >- ( (* Tuple *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[pure_walkstar_alt, pure_apply_subst] >>
    imp_res_tac $ cj 1 type_of_SOME_lemma >> gvs[] >>
    gvs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MAP_EQ_EVERY2] >> rw[] >>
    last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- (rw[] >> first_x_assum irule >> goal_assum drule >> simp[EL_MEM]) >>
    rpt $ goal_assum $ drule_at Any >> simp[] >> rw[]
    >- (
      gvs[GSYM pure_walkstar_alt] >> first_x_assum irule >>
      irule new_vars_SUBSET >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      simp[pure_vars, SUBSET_DEF, MEM_MAP, MEM_EL, PULL_EXISTS, SF SFY_ss]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      goal_assum drule >> gvs[FLOOKUP_DEF] >>
      simp[SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* Ret *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    last_x_assum irule >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >> rw[] >>
    first_x_assum irule >> irule new_vars_SUBSET >>
    goal_assum drule >> simp[pure_vars]
    )
  >- ( (* Bind *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >>
    `pure_vars (csubst closing (pure_walkstar sub (CVar f1))) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars]) >>
    gvs[pure_vars_empty_eq_type_of] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* Raise *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[GSYM pure_walkstar_alt] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >> rw[]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      imp_res_tac type_of_SOME >> simp[GSYM itype_ok_type_ok] >>
      irule itype_ok_pure_apply_subst >> simp[] >>
      irule itype_ok_pure_walkstar >> rw[itype_ok] >> gvs[itype_ok_def]
      )
    )
  >- ( (* Handle *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* Act *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    last_x_assum irule >> rpt $ goal_assum $ drule_at Any >> rw[] >>
    gvs[GSYM pure_walkstar_alt] >>
    first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
    imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
    )
  >- ( (* Alloc *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* Length *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >>
    `pure_vars (csubst closing (pure_walkstar sub (CVar fresh))) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars]) >>
    gvs[pure_vars_empty_eq_type_of] >> rw[] >>
    first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
    imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
    )
  >- ( (* Deref *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* Update *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 3 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >>
    `pure_vars (csubst closing (pure_walkstar sub (CVar f))) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars]) >>
    gvs[pure_vars_empty_eq_type_of] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> rpt CASE_TAC >> simp[SUBSET_DEF]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> rpt CASE_TAC >> simp[SUBSET_DEF]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> rpt CASE_TAC >> simp[SUBSET_DEF]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* True *)
    simp[Once type_tcexp_cases] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def]
    )
  >- ( (* False *)
    simp[Once type_tcexp_cases] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def]
    )
  >- ( (* Subscript *)
    simp[Once type_tcexp_cases] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def]
    )
  >- ( (* Exception *)
    simp[Once type_tcexp_cases] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    `s ≠ "Subscript"` by gvs[pure_configTheory.reserved_cns_def] >> simp[] >>
    PairCases_on `ns` >> gvs[] >> simp[type_exception_def] >>
    gvs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rw[] >>
    last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- gvs[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> gvs[] >>
    gvs[MAP2_MAP, MEM_MAP, MEM_ZIP, PULL_EXISTS, satisfies_def, type_of_itype_of] >>
    gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF, MEM_EL, SF SFY_ss, PULL_EXISTS]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      goal_assum drule >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* Cons *)
    simp[Once type_tcexp_cases] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst] >>
    drule $ cj 2 type_of_SOME_lemma >> rw[] >>
    PairCases_on `ns` >> gvs[] >> simp[type_cons_def, PULL_EXISTS, oEL_THM] >>
    gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2, EL_ZIP, EL_MAP] >> reverse $ rw[]
    >- (
      gvs[EVERY_EL] >> rw[] >> first_x_assum drule >> strip_tac >>
      imp_res_tac type_of_SOME >> simp[GSYM itype_ok_type_ok] >>
      irule itype_ok_pure_apply_subst >> simp[] >>
      irule itype_ok_pure_walkstar >> simp[itype_ok] >> gvs[itype_ok_def]
      ) >>
    last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- gvs[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF, MEM_EL, SF SFY_ss, PULL_EXISTS]
      )
    >- (
      gvs[MAP2_MAP, MEM_MAP, MEM_ZIP, PULL_EXISTS, satisfies_def] >>
      DEP_REWRITE_TAC[pure_walkstar_isubst] >> conj_tac >- gvs[itype_ok_def] >>
      simp[pure_walkstar_itype_of, pure_apply_subst_isubst_itype_of] >>
      drule $ cj 2 type_of_SOME_lemma >> rw[] >>
      imp_res_tac type_of_SOME_MAP >> pop_assum $ assume_tac o GSYM >>
      simp[isubst_itype_of, type_of_itype_of]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      goal_assum drule >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* AtomOp *)
    simp[Once type_tcexp_cases] >> disj2_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[GSYM pure_walkstar_alt] >>
    imp_res_tac infer_atom_op_LENGTH >> pop_assum $ assume_tac o GSYM >> gvs[] >>
    simp[GSYM infer_atom_op] >> goal_assum $ drule_at Any >> simp[get_PrimTys_SOME] >>
    gvs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MAP2_MAP, MEM_MAP, MEM_ZIP, PULL_EXISTS] >>
    rw[] >> last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- gvs[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> gvs[satisfies_def] >>
    simp[pure_walkstar_alt, pure_apply_subst, type_of_def] >> rw[GSYM pure_walkstar_alt]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF, MEM_EL, SF SFY_ss, PULL_EXISTS]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      goal_assum drule >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* Seq *)
    simp[Once type_tcexp_cases] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    `pure_vars (csubst closing (pure_walkstar sub it)) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      simp[pure_vars_pure_walkstar_alt] >> rw[BIGUNION_SUBSET, PULL_EXISTS] >>
      first_x_assum irule >> imp_res_tac minfer_pure_vars >>
      gvs[SUBSET_DEF, BIGUNION_FRANGE_maunion, new_vars_def, pure_vars] >>
      metis_tac[]) >>
    gvs[pure_vars_empty_eq_type_of] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* App *)
    simp[Once type_tcexp_cases] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_iFunctions, pure_apply_subst_iFunctions] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    irule_at Any $ cj 3 type_of_lemma >> simp[] >>
    `EVERY (λit. pure_vars it = {})
      (MAP (csubst closing) (MAP (pure_walkstar sub) tys))` by (
      rw[EVERY_MAP, EVERY_MEM] >> irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      simp[pure_vars_pure_walkstar_alt] >> rw[BIGUNION_SUBSET, PULL_EXISTS] >>
      rw[] >> first_x_assum irule >> simp[new_vars_def, pure_vars_iFunctions] >>
      simp[MEM_MAP, PULL_EXISTS, SF SFY_ss]) >>
    gvs[pure_vars_empty_eq_type_of_MAP] >> irule_at Any EQ_REFL >>
    `ts ≠ []` by (CCONTR_TAC >> gvs[]) >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >>
      goal_assum drule >> simp[BIGUNION_FRANGE_maunion] >>
      imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      ) >>
    gvs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MAP_EQ_EVERY2] >> rw[] >>
    last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- gvs[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> rw[]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET >>
      qexistsl_tac [`FOLDR maunion FEMPTY ass`,`BIGUNION (set css)`,`CVar f`] >>
      reverse $ conj_tac >- (simp[BIGUNION_FRANGE_maunion] >> simp[SUBSET_DEF]) >>
      irule new_vars_SUBSET_minfer >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      imp_res_tac minfer_pure_vars >>
      simp[SUBSET_DEF, MEM_EL, PULL_EXISTS, SF SFY_ss]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion, FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      rpt CASE_TAC >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* Lam *)
    simp[Once type_tcexp_cases] >>
    gvs[pure_walkstar_iFunctions, pure_apply_subst_iFunctions] >>
    drule $ cj 3 type_of_SOME_lemma >> rw[] >>
    irule_at Any EQ_REFL >> simp[] >> rw[] >>
    imp_res_tac $ cj 1 $ iffLR MAP_EQ_EVERY2 >> gvs[] >>
    `ts ≠ []` by (CCONTR_TAC >> gvs[]) >> rw[]
    >- (
      gvs[EVERY_EL, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      first_x_assum drule >> strip_tac >>
      imp_res_tac type_of_SOME >> simp[GSYM itype_ok_type_ok] >>
      irule itype_ok_pure_apply_subst >> simp[] >>
      irule itype_ok_pure_walkstar >> simp[itype_ok] >> gvs[itype_ok_def]
      ) >>
    last_x_assum irule >> goal_assum $ drule_at Any >> simp[] >>
    qexists_tac `REVERSE (ZIP (xs, MAP ($, 0) (MAP CVar freshes))) ++ ictxt` >> rw[]
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP,
           FLOOKUP_FDIFF, MEM_MAP, GSYM DISJ_ASSOC, get_massumptions_def,
           MAP2_MAP, MEM_ZIP, pure_vars_iFunctions] >>
      reverse $ rw[] >> simp[SF SFY_ss] >>
      reverse $ Cases_on `MEM k xs` >> gvs[] >> simp[SF SFY_ss] >>
      pop_assum mp_tac >> simp[Once MEM_EL] >> strip_tac >> gvs[] >>
      ntac 3 disj2_tac >> disj1_tac >>
      rpt (goal_assum $ drule_at Any >> simp[])
      )
    >- (
      simp[ctxt_vars, msubst_vars_UNION] >>
      AP_THM_TAC >> AP_TERM_TAC >> simp[GSYM ctxt_vars_subst_ctxt] >>
      simp[subst_ctxt_def, ctxt_vars_def, msubst_vars_def] >>
      simp[MAP_REVERSE, ZIP_MAP] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_ZIP_ALT] >>
      AP_TERM_TAC >> rw[Once EXTENSION] >>
      simp[MEM_MAP, MEM_ZIP, PULL_EXISTS, MEM_EL]
      )
    >- gvs[ZIP_MAP, EVERY_MAP, freedbvars_def]
    >- (
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_APPEND_EQN] >> rw[] >>
      simp[ZIP_MAP, GSYM MAP_REVERSE, EL_MAP, EL_REVERSE, EL_ZIP] >> gvs[EL_MAP]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> simp[ALOOKUP_APPEND] >> CASE_TAC
      >- (
        first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_FDIFF] >>
        impl_tac >> rw[] >> gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP]
        ) >>
      PairCases_on `x` >> simp[] >> rw[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP] >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP] >>
      first_x_assum $ drule_at Any >> simp[get_massumptions_def] >>
      disch_then drule >> simp[satisfies_def]
      )
    )
  >- ( (* Let *)
    rename [`Let _ (_ e1) (_ e2)`,
            `minfer _ _ e2 as2 cs2 it2`,`minfer _ _ e1 as1 cs1 it1`] >>
    simp[Once type_tcexp_cases] >>
    last_x_assum $ irule_at Any >> goal_assum $ drule_at Any >>
    `∃smonos : num_set. domain smonos = msubst_vars sub mset ∧ wf smonos` by (
      qexists_tac `list_to_num_set (SET_TO_LIST (msubst_vars sub mset))` >>
      simp[EXTENSION, domain_list_to_num_set, wf_list_to_num_set] >>
      DEP_REWRITE_TAC[MEM_SET_TO_LIST] >> simp[msubst_vars_def, PULL_EXISTS]) >>
    qabbrev_tac `gen = generalise 0 smonos FEMPTY (pure_walkstar sub it1)` >>
    PairCases_on `gen` >> gvs[] >> rename1 `(new_dbvars,gen_sub,let_ity)` >>
    drule_all generalise_0_FEMPTY >> simp[] >> strip_tac >>
    `FDIFF gen_sub (msubst_vars sub mset) = gen_sub` by (
      rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
    gvs[] >>
    pop_assum kall_tac >>
    qmatch_asmsub_abbrev_tac `gen_vars,_,let_ity` >>
    `pure_vars (csubst (ishift gen_vars o_f closing) let_ity) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
      unabbrev_all_tac >> irule SUBSET_TRANS >>
      irule_at Any pure_vars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, pure_vars] >>
      rw[IMAGE_K_EMPTY, DIFF_SUBSET] >>
      qsuff_tac `pure_vars (pure_walkstar sub it1) ⊆ FDOM closing` >- rw[SUBSET_DEF] >>
      simp[pure_vars_pure_walkstar_alt] >> rw[BIGUNION_SUBSET, PULL_EXISTS] >>
      first_x_assum irule >> irule new_vars_SUBSET_minfer >>
      qexistsl_tac [`as1`,`cs1`,`it1`] >> imp_res_tac minfer_pure_vars >>
      simp[BIGUNION_FRANGE_maunion] >> simp[SUBSET_DEF, new_vars_def]) >>
    pop_assum mp_tac >> simp[Once pure_vars_empty_eq_type_of] >> strip_tac >>
    rename1 `SOME let_ty` >>
    qexistsl_tac [`let_ty`,`gen_vars`,
      `FUNION (DBVar o_f gen_sub) (ishift gen_vars o_f closing)`] >>
    DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      simp[FLOOKUP_maunion] >> rw[] >> CASE_TAC >> simp[]
      )
    >- (
      qsuff_tac `pure_vars (pure_walkstar sub (CVar n)) ⊆ FDOM closing`
      >- rw[SUBSET_DEF] >>
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      pop_assum mp_tac >> qid_spec_tac `it` >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      pop_assum mp_tac >> qid_spec_tac `it` >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, itype_ok, type_of_def] >>
      rw[] >> last_x_assum drule >> rw[] >>
      irule itype_ok_ishift >> simp[]
      )
    >- (
      gvs[LIST_REL_EL_EQN] >> rw[EL_MAP] >> ntac 3 (pairarg_tac >> gvs[]) >>
      first_x_assum drule >> simp[] >> PairCases_on `scheme` >> gvs[] >> rw[] >>
      simp[o_f_FUNION] >> DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
      qabbrev_tac `wlkit = pure_walkstar sub it` >>
      `csubst ((ishift ivs o DBVar) o_f gen_sub) wlkit = wlkit` by (
        irule pure_apply_subst_unchanged >> rw[DISJOINT_ALT, DISJ_EQ_IMP] >>
        qpat_x_assum `msubst_vars _ _ = msubst_vars _ _` $ assume_tac o GSYM >>
        simp[GSYM ctxt_vars_subst_ctxt] >>
        simp[ctxt_vars_def, MEM_MAP, PULL_EXISTS, MEM_EL, EXISTS_PROD,
             subst_ctxt_def, EL_MAP] >>
        qpat_x_assum `_ ∈ pure_vars _` kall_tac >> unabbrev_all_tac >>
        rpt $ goal_assum drule >> simp[]) >>
      simp[] >> pop_assum kall_tac >>
      irule shift_shift_let_lemma >> simp[] >>
      unabbrev_all_tac >> irule SUBSET_TRANS >>
      irule_at Any freedbvars_pure_walkstar_SUBSET >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >>
      gvs[EVERY_EL, itype_ok_def] >> first_x_assum drule >> simp[]
      ) >>
    last_x_assum irule >> rpt $ goal_assum drule >> simp[] >>
    qexists_tac `(x,gen_vars,let_ity)::ictxt` >> simp[] >>
    `pure_walkstar sub let_ity = let_ity` by (
      unabbrev_all_tac >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]) >>
    simp[] >> rw[]
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP,
           FLOOKUP_maunion, DOMSUB_FLOOKUP_THM, GSYM DISJ_ASSOC, get_massumptions_def] >>
      rw[] >> simp[SF SFY_ss] >>
      Cases_on `k = x` >> gvs[] >- metis_tac[] >>
      disj1_tac >> Cases_on `FLOOKUP as1 k`
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x' ∪ s`,`k`] >> simp[])
      )
    >- (
      simp[GSYM ctxt_vars_subst_ctxt] >>
      simp[subst_ctxt, ctxt_vars] >> simp[ctxt_vars_subst_ctxt] >>
      irule SUBSET_ANTISYM >> simp[]
      )
    >- (
      unabbrev_all_tac >> irule SUBSET_TRANS >>
      irule_at Any freedbvars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, freedbvars_def] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >> simp[] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      ) >>
    gvs[ctxt_rel_def] >> reverse $ rw[]
    >- (
      first_x_assum $ qspec_then `k` mp_tac >>
      simp[FLOOKUP_maunion, DOMSUB_FLOOKUP_THM] >>
      every_case_tac >> gvs[] >> rw[] >> simp[]
      ) >>
    unabbrev_all_tac >>
    gvs[DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM, PULL_EXISTS] >>
    gvs[get_massumptions_def, satisfies_def] >>
    last_x_assum drule >> strip_tac >> simp[] >>
    qabbrev_tac `wlkit1 = pure_walkstar sub it1` >>
    qspecl_then [`gen_sub`,`sub'`,`wlkit1`] mp_tac pure_apply_subst_split_isubst >>
    simp[] >> impl_tac >> rw[]
    >- (
      unabbrev_all_tac >> once_rewrite_tac[GSYM SUBSET_EMPTY] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
      simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      ) >>
    goal_assum $ drule_at Any >> simp[EVERY_GENLIST] >> rw[]
    >- (irule itype_ok_pure_apply_subst >> simp[itype_ok]) >>
    simp[pure_vars_pure_apply_subst] >>
    simp[SUBSET_DEF, pure_vars, PULL_EXISTS] >> rw[] >>
    goal_assum drule >> qsuff_tac `gm ' n' ∈ FDOM gen_sub` >- simp[] >>
    gvs[fmap_linv_alt_def, IN_FRANGE_FLOOKUP, FLOOKUP_DEF] >>
    goal_assum drule >> simp[]
    )
  >- ( (* Letrec *)
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP] >>
    simp[Once type_tcexp_cases] >> `fns ≠ []` by (CCONTR_TAC >> gvs[]) >> simp[] >>
    last_x_assum $ irule_at Any >> goal_assum $ drule_at Any >> simp[] >>
    `∃smonos : num_set. domain smonos = msubst_vars sub mset ∧ wf smonos` by (
      qexists_tac `list_to_num_set (SET_TO_LIST (msubst_vars sub mset))` >>
      simp[EXTENSION, domain_list_to_num_set, wf_list_to_num_set] >>
      DEP_REWRITE_TAC[MEM_SET_TO_LIST] >> simp[msubst_vars_def, PULL_EXISTS]) >>
    qabbrev_tac `gens =
      MAP (generalise 0 smonos FEMPTY) (MAP (pure_walkstar sub) tys)` >>
    `LIST_REL (λ(new,sub,ty) t.
      CARD (FDOM sub) = new ∧ FDOM sub = pure_vars t DIFF domain smonos ∧
      FRANGE sub = count new ∧ pure_vars ty ⊆ domain smonos ∧
      csubst (DBVar o_f sub) t = ty)
      gens (MAP (pure_walkstar sub) tys)` by (
      unabbrev_all_tac >> rw[LIST_REL_EL_EQN, EL_MAP] >>
      pairarg_tac >> simp[] >> drule generalise_0_FEMPTY >> simp[] >> rw[] >>
      qsuff_tac `FDIFF sub' (msubst_vars sub mset) = sub'` >> rw[] >>
      rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
    `EVERY (λit. pure_vars it = {}) $
      MAP (λ(new,gen_sub,ty). csubst (ishift new o_f closing) ty) gens` by (
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> rw[] >> pairarg_tac >> gvs[] >>
      irule pure_vars_csubst_EMPTY_suff >> simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
      first_x_assum drule >> rw[] >>
      irule SUBSET_TRANS >> irule_at Any pure_vars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, pure_vars] >>
      rw[IMAGE_K_EMPTY, DIFF_SUBSET] >>
      qsuff_tac `pure_vars (pure_walkstar sub (EL n tys)) ⊆ FDOM closing`
      >- rw[SUBSET_DEF] >>
      simp[pure_vars_pure_walkstar_alt] >> rw[BIGUNION_SUBSET, PULL_EXISTS] >>
      first_x_assum irule >>
      simp[new_vars_def, MEM_MAP, MEM_EL, PULL_EXISTS, SF SFY_ss]) >>
    pop_assum mp_tac >> simp[Once pure_vars_empty_eq_type_of_MAP] >> strip_tac >>
    rename1 `MAP SOME fn_tys` >>
    qexists_tac `ZIP (MAP FST gens, fn_tys)` >>
    qexists_tac
      `REVERSE (ZIP (MAP FST fns, MAP (λ(vs,s,t). (vs,t)) gens)) ++ ictxt` >> simp[] >>
    imp_res_tac LIST_REL_LENGTH >> imp_res_tac $ cj 1 $ iffLR MAP_EQ_EVERY2 >> gvs[] >>
    simp[AC (GSYM CONJ_ASSOC) CONJ_COMM] >> rw[]
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, MEM_MAP, MEM_ZIP] >> rw[] >> gvs[SF SFY_ss] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_FDIFF, FLOOKUP_maunion] >>
      Cases_on `¬MEM k (MAP FST fns)` >> gvs[GSYM DISJ_ASSOC]
      >- (
        disj1_tac >> simp[Once SWAP_EXISTS_THM] >>
        qexists_tac `k` >> simp[] >> CASE_TAC >> simp[]
        ) >>
      ntac 4 disj2_tac >> disj1_tac >>
      pop_assum mp_tac >> simp[MEM_MAP, MEM_EL, EXISTS_PROD] >> rw[] >>
      pop_assum $ assume_tac o GSYM >> goal_assum $ drule_at Any >> simp[] >>
      simp[PULL_EXISTS, pure_vars, get_massumptions_def, FLOOKUP_maunion] >>
      qexists_tac `n` >> simp[] >> CASE_TAC >> simp[]
      )
    >- (
      drule type_of_SOME_MAP >> rw[] >>
      gvs[EVERY_EL, EL_ZIP, EL_MAP, LIST_REL_EL_EQN, MAP_EQ_EVERY2] >> rw[] >>
      simp[GSYM itype_ok_type_ok] >>
      ntac 3 (first_x_assum drule >> simp[] >> strip_tac) >>
      pairarg_tac >> gvs[] >>
      irule itype_ok_pure_apply_subst >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >> rw[]
      >- (irule itype_ok_ishift >> simp[]) >>
      irule itype_ok_pure_apply_subst >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >> rw[itype_ok] >>
      irule itype_ok_pure_walkstar >> rw[] >- gvs[itype_ok_def] >>
      last_x_assum drule >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> simp[ALOOKUP_APPEND] >> CASE_TAC >> gvs[]
      >- (
        `¬MEM k (MAP FST fns)` by (
          pop_assum mp_tac >>
          simp[ALOOKUP_NONE, MEM_MAP, MEM_ZIP, PULL_EXISTS, EXISTS_PROD] >>
          simp[Once MONO_NOT_EQ] >> rw[MEM_EL] >> csimp[EL_MAP] >>
          goal_assum $ drule_at Any >> pop_assum $ assume_tac o GSYM >>
          simp[] >> pairarg_tac >> simp[]) >>
        first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_FDIFF] >>
        qsuff_tac
         `∃v'. FLOOKUP (maunion as' (FOLDR maunion FEMPTY ass)) k = SOME v' ∧ v ⊆ v'`
        >- (strip_tac >> simp[] >> rw[] >> gvs[SUBSET_DEF]) >>
        simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
        ) >>
      PairCases_on `x` >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP] >>
      pairarg_tac >> gvs[] >> rw[] >>
      first_x_assum $ drule_at Any >>
      pairarg_tac >> simp[PULL_EXISTS] >>
      simp[get_massumptions_def, FLOOKUP_maunion] >> gvs[] >>
      disch_then $ qspec_then `n'` mp_tac >> impl_tac >- (CASE_TAC >> simp[]) >>
      simp[satisfies_def] >> rw[] >> simp[] >>
      gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[EL_MAP] >> rw[] >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
      qabbrev_tac `wlk = pure_walkstar sub (EL n tys)` >>
      qspecl_then [`s`,`sub'`,`wlk`] mp_tac pure_apply_subst_split_isubst >>
      simp[] >> impl_tac >> rw[]
      >- (
        unabbrev_all_tac >> once_rewrite_tac[GSYM SUBSET_EMPTY] >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
        simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >>
        last_x_assum drule >> simp[EL_ZIP] >> strip_tac >>
        imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
        ) >>
      goal_assum $ drule_at Any >> simp[EVERY_GENLIST] >> rw[]
      >- (irule itype_ok_pure_apply_subst >> simp[itype_ok]) >>
      simp[pure_vars_pure_apply_subst] >>
      simp[SUBSET_DEF, pure_vars, PULL_EXISTS] >> rw[] >>
      goal_assum drule >> qsuff_tac `gm ' n'' ∈ FDOM s` >- simp[] >>
      gvs[fmap_linv_alt_def, IN_FRANGE_FLOOKUP, FLOOKUP_DEF] >>
      goal_assum drule >> simp[]
      )
    >- (
      simp[ctxt_vars, msubst_vars_UNION] >> irule SUBSET_ANTISYM >> simp[] >>
      simp[GSYM ctxt_vars_subst_ctxt] >>
      simp[subst_ctxt_def, ctxt_vars_def,
           ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS, MEM_MAP, MEM_ZIP] >> rw[] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> first_x_assum drule >> simp[] >> rw[] >>
      pairarg_tac >> gvs[] >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      gvs[EVERY_EL, EL_ZIP, EL_MAP] >> rw[] >>
      pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> first_x_assum drule >> simp[] >> strip_tac >>
      pop_assum $ assume_tac o GSYM >> simp[] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, freedbvars_def] >>
      reverse conj_tac >- simp[SUBSET_DEF, PULL_EXISTS] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >> simp[] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >> reverse conj_tac >- gvs[itype_ok_def] >>
      last_x_assum drule >> simp[EL_ZIP] >> pairarg_tac >> simp[] >> strip_tac >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      )
    >- (
      gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2, EL_ZIP, EL_MAP] >> rw[] >>
      simp[EL_APPEND_EQN] >> CASE_TAC >> gvs[] >>
      simp[EL_REVERSE, EL_ZIP, EL_MAP, LAMBDA_PROD] >>
      qmatch_goalsub_abbrev_tac `EL m` >>
      `m < LENGTH fn_tys` by (unabbrev_all_tac >> gvs[]) >>
      rpt (pairarg_tac >> gvs[]) >>
      first_x_assum drule >> simp[] >>
      qsuff_tac `pure_walkstar sub it' = it'` >> rw[] >>
      first_x_assum drule >> simp[] >>
      rw[] >> DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      ) >>
    gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2, EL_ZIP, EL_MAP] >> rw[] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    last_assum drule >> asm_rewrite_tac[] >> simp[] >>
    strip_tac >> pop_assum irule >> conj_tac
    >- (
      rw[] >> qpat_x_assum `∀c s. _ ∧ MEM _ __ ⇒ _` irule >>
      goal_assum $ drule_at Any >> simp[EL_MEM]
      ) >>
    first_assum drule >> pairarg_tac >> asm_rewrite_tac[] >> rw[] >>
    qpat_assum `∀n. n < _ ⇒ _ (pure_walkstar _ _)` drule >>
    asm_rewrite_tac[] >> simp[] >> strip_tac >> gvs[] >>
    qmatch_asmsub_abbrev_tac `EL n gens = (new,gen_sub,ty)` >>
    qexists_tac `FUNION (DBVar o_f gen_sub) (ishift new o_f closing)` >>
    qexists_tac `REVERSE (ZIP (MAP FST fns, MAP (λ(vs,s,t). (vs,t)) gens)) ++ ictxt` >>
    simp[] >> rw[]
    >- (
      pop_assum mp_tac >> qid_spec_tac `it'` >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      pop_assum mp_tac >> qid_spec_tac `it'` >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, itype_ok] >> rw[] >>
      irule itype_ok_ishift >> gvs[itype_ok_def]
      )
    >- (
      simp[EL_APPEND_EQN] >> reverse $ rw[] >> simp[EL_MAP, EL_REVERSE, EL_ZIP]
      >- (
        qmatch_goalsub_abbrev_tac `EL m`  >>
        `m < LENGTH ictxt` by (unabbrev_all_tac >> gvs[]) >>
        rpt (pairarg_tac >> gvs[]) >>
        qpat_x_assum `∀n. _ < LENGTH ictxt ⇒ _` $ qspec_then `m` mp_tac >> rw[] >>
        simp[o_f_FUNION] >> DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
        simp[GSYM IMAGE_FRANGE, PULL_EXISTS, ishift_def, pure_vars] >>
        `csubst ((ishift ivs o DBVar) o_f gen_sub) (pure_walkstar sub it') =
          pure_walkstar sub it'` by (
          irule pure_apply_subst_unchanged >> simp[] >> rw[DISJOINT_ALT] >>
          disj2_tac >> qpat_x_assum `msubst_vars _ _ = _` $ assume_tac o GSYM >>
          simp[GSYM ctxt_vars_subst_ctxt, subst_ctxt_def, ctxt_vars_def] >>
          simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD, MEM_EL] >>
          goal_assum drule >> goal_assum $ drule_at Any o GSYM >> simp[]) >>
        pop_assum SUBST_ALL_TAC >> irule shift_shift_let_lemma >> simp[] >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
        simp[BIGUNION_SUBSET, PULL_EXISTS] >> gvs[EVERY_EL, itype_ok_def] >>
        qpat_x_assum `∀n. n < LENGTH ictxt ⇒ _` $ qspec_then `m` mp_tac >> simp[]
        )
      >- (
        qmatch_goalsub_abbrev_tac `EL m`  >>
        `m < LENGTH fn_tys` by (unabbrev_all_tac >> gvs[]) >>
        rpt (pairarg_tac >> gvs[]) >>
        first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
        DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
        simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
        qmatch_goalsub_abbrev_tac `ishift new'` >>
        simp[o_f_FUNION] >> DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
        simp[GSYM IMAGE_FRANGE, PULL_EXISTS, ishift_def, pure_vars] >>
        `csubst ((ishift new' ∘ DBVar) o_f gen_sub) $
          csubst (DBVar o_f s) (pure_walkstar sub (EL m tys)) =
          csubst (DBVar o_f s) (pure_walkstar sub (EL m tys))` by (
          irule pure_apply_subst_unchanged >> rw[DISJOINT_ALT] >>
          disj2_tac >> pop_assum mp_tac >>
          simp[pure_vars_pure_apply_subst] >>
          csimp[PULL_EXISTS, pure_vars, pure_apply_subst, FLOOKUP_DEF] >>
          gen_tac >> CASE_TAC >> simp[pure_vars] >> rw[]) >>
        pop_assum $ SUBST_ALL_TAC >> irule shift_shift_let_lemma >> gvs[] >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_apply_subst_SUBSET >>
        simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, freedbvars_def] >>
        reverse conj_tac >- (rw[SUBSET_DEF] >> gvs[]) >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
        simp[] >> reverse conj_tac >- gvs[BIGUNION_SUBSET, PULL_EXISTS, itype_ok_def] >>
        last_x_assum drule >> simp[] >> strip_tac >>
        imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
        )
      )
    >- (
      qsuff_tac `pure_vars (pure_walkstar sub (CVar n')) ⊆ FDOM closing`
      >- rw[SUBSET_DEF] >>
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, MEM_MAP, MEM_ZIP, PULL_EXISTS, IN_FRANGE_FLOOKUP,
           FLOOKUP_FDIFF, FLOOKUP_maunion, GSYM DISJ_ASSOC, FORALL_PROD] >>
      reverse $ rw[]
      >- simp[MEM_EL, PULL_EXISTS, SF SFY_ss]
      >- simp[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
      Cases_on `¬MEM k (MAP FST fns)` >> gvs[]
      >- (
        gvs[MEM_MAP, FORALL_PROD] >> disj1_tac >>
        simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
        qsuff_tac `∃v. FLOOKUP (FOLDR maunion FEMPTY ass) k = SOME v ∧ s ⊆ v`
        >- (rw[] >> simp[] >> CASE_TAC >> gvs[SUBSET_DEF]) >>
        simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >>
        gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
        ) >>
      ntac 4 disj2_tac >> disj1_tac >>
      pop_assum mp_tac >> simp[MEM_MAP, EXISTS_PROD, MEM_EL] >> rw[] >>
      goal_assum $ drule_at Any >> pop_assum $ assume_tac o GSYM >>
      simp[get_massumptions_def, FLOOKUP_maunion, PULL_EXISTS, pure_vars] >>
      qexists_tac `n'` >> simp[] >>
      qsuff_tac `∃v. FLOOKUP (FOLDR maunion FEMPTY ass) k = SOME v ∧ s ⊆ v`
      >- (rw[] >> simp[] >> CASE_TAC >> gvs[SUBSET_DEF]) >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      qexists_tac `n` >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    >- (
      simp[ctxt_vars, msubst_vars_UNION] >> irule SUBSET_ANTISYM >> simp[] >>
      simp[GSYM ctxt_vars_subst_ctxt] >>
      simp[subst_ctxt_def, ctxt_vars_def,
           ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS, MEM_MAP, MEM_ZIP] >> rw[] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> first_x_assum drule >> simp[] >> rw[] >>
      pairarg_tac >> gvs[] >>
      first_x_assum drule >> simp[] >> rw[] >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      gvs[EVERY_EL, EL_ZIP, EL_MAP] >> rw[] >>
      pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      first_x_assum drule >> simp[] >> strip_tac >>
      first_x_assum drule >> simp[] >> rw[] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, freedbvars_def] >>
      reverse conj_tac >- simp[SUBSET_DEF, PULL_EXISTS] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >> simp[] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >> reverse conj_tac >- gvs[itype_ok_def] >>
      last_x_assum drule >> simp[EL_ZIP] >> pairarg_tac >> simp[] >> strip_tac >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> simp[ALOOKUP_APPEND] >> CASE_TAC >> gvs[]
      >- (
        `¬MEM k (MAP FST fns)` by (
          pop_assum mp_tac >>
          simp[ALOOKUP_NONE, MEM_MAP, MEM_ZIP, PULL_EXISTS, EXISTS_PROD] >>
          simp[Once MONO_NOT_EQ] >> rw[MEM_EL] >> csimp[EL_MAP] >>
          goal_assum $ drule_at Any >> pop_assum $ assume_tac o GSYM >>
          simp[] >> pairarg_tac >> simp[]) >>
        first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_FDIFF] >>
        qsuff_tac
         `∃v'. FLOOKUP (maunion as' (FOLDR maunion FEMPTY ass)) k = SOME v' ∧ v ⊆ v'`
        >- (strip_tac >> simp[] >> rw[] >> gvs[SUBSET_DEF]) >>
        simp[FLOOKUP_maunion, FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
        IF_CASES_TAC >> gvs[]
        >- (first_x_assum $ qspec_then `n` assume_tac >> gvs[FLOOKUP_DEF])
        >- (CASE_TAC >> simp[SUBSET_DEF, PULL_EXISTS, SF SFY_ss])
        ) >>
      PairCases_on `x` >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP] >>
      pairarg_tac >> gvs[] >> rw[] >>
      qabbrev_tac `n'_fns = EL n' fns` >> PairCases_on `n'_fns` >> gvs[] >>
      qpat_x_assum `∀c n. _ ⇒ satisifes _ _ _` $ drule_at Any >>
      simp[PULL_EXISTS, get_massumptions_def] >>
      `∃v'. FLOOKUP (maunion as' (FOLDR maunion FEMPTY ass)) n'_fns0 =
              SOME v' ∧ v ⊆ v'` by (
        simp[FLOOKUP_maunion, FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
        IF_CASES_TAC >> gvs[]
        >- (first_x_assum $ qspec_then `n` assume_tac >> gvs[FLOOKUP_DEF]) >>
        CASE_TAC >> simp[SUBSET_DEF, PULL_EXISTS, SF SFY_ss]) >>
      simp[satisfies_def] >> disch_then $ qspec_then `n''` mp_tac >>
      impl_tac >- gvs[SUBSET_DEF] >> rw[] >>
      qpat_x_assum `∀n. _ ⇒ _ (pure_walkstar _ _)` drule >> rw[] >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
      qabbrev_tac `wlk = pure_walkstar sub (EL n' tys)` >>
      qspecl_then [`s`,`sub'`,`wlk`] mp_tac pure_apply_subst_split_isubst >>
      simp[] >> impl_tac >> rw[]
      >- (
        unabbrev_all_tac >> once_rewrite_tac[GSYM SUBSET_EMPTY] >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
        simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >>
        last_x_assum drule >> simp[EL_ZIP] >> strip_tac >>
        imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
        ) >>
      goal_assum $ drule_at Any >> simp[EVERY_GENLIST] >> rw[]
      >- (irule itype_ok_pure_apply_subst >> simp[itype_ok]) >>
      rename1 `gm ' foo` >>
      simp[pure_vars_pure_apply_subst] >>
      simp[SUBSET_DEF, pure_vars, PULL_EXISTS] >> rw[] >>
      goal_assum drule >> qsuff_tac `gm ' foo ∈ FDOM s` >- simp[] >>
      gvs[fmap_linv_alt_def, IN_FRANGE_FLOOKUP, FLOOKUP_DEF] >>
      goal_assum drule >> simp[]
      )
    )
  >- ( (* BoolCase *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[GSYM pure_walkstar_alt] >>
    ntac 3 $ last_x_assum $ irule_at Any >>
    ntac 5 $ goal_assum $ drule_at Any >> simp[] >>
    qexistsl_tac [`(v,0,BoolTy)::ictxt`,`(v,0,BoolTy)::ictxt`] >> simp[] >>
    simp[freedbvars_def, pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    simp[GSYM pure_walkstar_alt] >> simp[ctxt_vars, pure_vars] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      gvs[ctxt_rel_def, get_massumptions_def] >> rw[] >- simp[pure_walkstar_alt] >>
      first_x_assum $ qspec_then `k` mp_tac >>
      simp[FLOOKUP_maunion, DOMSUB_FLOOKUP_THM] >>
      every_case_tac >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP, FLOOKUP_maunion,
           DOMSUB_FLOOKUP_THM, GSYM DISJ_ASSOC, get_massumptions_def] >>
      rw[] >> simp[SF SFY_ss] >>
      Cases_on `n = f` >> gvs[] >> simp[SF SFY_ss] >>
      Cases_on `v = k` >> gvs[] >> simp[SF SFY_ss] >> disj1_tac >>
      simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
      every_case_tac >> simp[]
      )
    >- (
      gvs[ctxt_rel_def, get_massumptions_def] >> rw[] >- simp[pure_walkstar_alt] >>
      first_x_assum $ qspec_then `k` mp_tac >>
      simp[FLOOKUP_maunion, DOMSUB_FLOOKUP_THM] >>
      every_case_tac >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP, FLOOKUP_maunion,
           DOMSUB_FLOOKUP_THM, GSYM DISJ_ASSOC, get_massumptions_def] >>
      rw[] >> simp[SF SFY_ss] >>
      Cases_on `n = f` >> gvs[] >> simp[SF SFY_ss] >>
      Cases_on `v = k` >> gvs[] >> simp[SF SFY_ss] >> disj1_tac >>
      simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
      every_case_tac >> simp[]
      )
    )
  >- ( (* TupleCase *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, LEFT_AND_OVER_OR, MAP2_MAP,
        MEM_MAP, MEM_ZIP, EL_MAP, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst] >> gvs[GSYM $ cj 9 pure_walkstar_alt] >>
    last_x_assum $ irule_at $ Pos hd >> rpt $ goal_assum $ drule_at Any >> simp[] >>
    irule_at Any $ cj 1 type_of_lemma >>
    `EVERY (λit. pure_vars it = {}) $
      MAP (csubst closing) $ MAP (pure_walkstar sub) $ MAP CVar freshes` by (
        rw[EVERY_MAP, EVERY_MEM] >> irule pure_vars_csubst_EMPTY_suff >> simp[] >>
        first_x_assum irule >> simp[new_vars_def, pure_vars, MEM_MAP, PULL_EXISTS]) >>
    gvs[pure_vars_empty_eq_type_of_MAP] >> irule_at Any EQ_REFL >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- gvs[MAP_EQ_EVERY2] >>
    last_x_assum irule >> goal_assum $ drule_at Any >> simp[] >>
    qexists_tac `REVERSE (ZIP (pvars,MAP ($, 0) (MAP CVar freshes))) ++
                  (v,0,CVar f)::ictxt` >>
    simp[freedbvars_def, LIST_TO_SET_MAP, IMAGE_EQ_SING, PULL_EXISTS] >> rw[]
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP,
           FLOOKUP_maunion, FLOOKUP_FDIFF, GSYM DISJ_ASSOC, get_massumptions_def,
           MEM_MAP, MEM_ZIP, EL_MAP] >>
      rw[] >> simp[SF SFY_ss] >>
      Cases_on `n = f` >> gvs[] >> simp[SF SFY_ss] >>
      Cases_on `v = k` >> gvs[] >> simp[SF SFY_ss] >>
      Cases_on `MEM k pvars`
      >- (
        gvs[MEM_EL] >> ntac 5 disj2_tac >> disj1_tac >>
        qexistsl_tac [`n'`,`n`] >> simp[]
        ) >>
      disj1_tac >> simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
      CASE_TAC >> simp[]
      )
    >- (
      simp[ctxt_vars, pure_vars, msubst_vars_UNION] >>
      simp[GSYM msubst_vars_UNION] >> AP_TERM_TAC >>
      once_rewrite_tac[INSERT_SING_UNION] >> rewrite_tac[UNION_ASSOC] >>
      AP_THM_TAC >> AP_TERM_TAC >> simp[Once UNION_COMM] >> AP_TERM_TAC >>
      simp[ctxt_vars_def, Once EXTENSION, MEM_MAP, MEM_ZIP,
           MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss, pure_vars] >>
      rw[] >> eq_tac >> rw[] >> goal_assum $ drule_at Any >> simp[]
      )
    >- (rw[EVERY_MEM, MEM_ZIP, MEM_MAP] >> simp[EL_MAP, freedbvars_def])
    >- (
      irule EVERY2_APPEND_suff >> simp[] >>
      simp[pure_apply_subst] >> irule_at Any $ cj 1 type_of_lemma >> simp[] >>
      gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2, EL_ZIP, EL_MAP]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> gvs[ALOOKUP_APPEND, get_massumptions_def] >>
      reverse $ TOP_CASE_TAC >> simp[]
      >- (
        PairCases_on `x` >> rw[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP]
        ) >>
      IF_CASES_TAC >> gvs[] >> first_x_assum $ qspec_then `k` mp_tac >>
      simp[FLOOKUP_maunion, FLOOKUP_FDIFF] >>
      gvs[ALOOKUP_NONE, MEM_MAP, MEM_ZIP, EL_MAP, PULL_EXISTS] >>
      IF_CASES_TAC >- gvs[MEM_EL] >> simp[] >>
      TOP_CASE_TAC >> gvs[] >> rw[] >> simp[]
      )
    )
  >- ( (* ExceptionCase *)
    simp[Once type_tcexp_cases] >> ntac 2 disj2_tac >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, MEM_MAP, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst] >> gvs[GSYM pure_walkstar_alt] >>
    PairCases_on `ns` >> gvs[] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    rw[type_of_def]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      imp_res_tac sortingTheory.PERM_LIST_TO_SET >> gvs[] >>
      qspec_then `FST` drule sortingTheory.PERM_MAP >> rw[] >>
      drule sortingTheory.PERM_LIST_TO_SET >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
      )
    >- (imp_res_tac sortingTheory.PERM_LENGTH >> gvs[]) >>
    gvs[LIST_REL_EL_EQN, EVERY_EL, EL_ZIP, EL_MAP] >> rw[] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >> simp[] >> strip_tac >> simp[] >>
    `c ≠ "Subscript"` by (
      qpat_x_assum `namespace_ok _` assume_tac >>
      gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
      last_x_assum $ qspec_then `"Subscript"` mp_tac >>
      impl_tac >- simp[pure_configTheory.reserved_cns_def] >> strip_tac >>
      CCONTR_TAC >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP]) >>
    simp[] >> rpt conj_asm1_tac
    >- (
      gvs[MEM_FLAT, MEM_MAP, DISJ_EQ_IMP, PULL_EXISTS, EXISTS_PROD, MEM_EL] >>
      metis_tac[]
      )
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
    last_x_assum drule >> simp[] >> strip_tac >> pop_assum irule >> conj_tac
    >- (
      gvs[MEM_EL, PULL_EXISTS] >> rw[] >>
      first_x_assum irule >> goal_assum drule >> simp[]
      ) >>
    goal_assum $ drule_at Any >> simp[] >>
    qexists_tac `REVERSE (ZIP (pvars,MAP ($, 0) (MAP itype_of schemes))) ++
                  (v,0,CVar f)::ictxt` >>
    qpat_x_assum `∀c s. _ ∧ _ ⇒ _` mp_tac >> simp[Once MEM_EL, PULL_EXISTS] >>
    disch_then $ drule_at Any >>
    simp[PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP,
         DISJ_IMP_THM, FORALL_AND_THM, satisfies_def, EL_MAP] >>
    strip_tac >> gvs[] >> rw[]
    >- (
      simp[EL_APPEND_EQN, EL_REVERSE, EL_ZIP, EL_MAP] >>
      reverse $ rw[] >- (Cases_on `n' - LENGTH pvars` >> gvs[freedbvars_def]) >>
      gvs[namespace_ok_def, EVERY_EL, freetyvars_ok_freedbvars] >>
      drule ALOOKUP_MEM >> simp[MEM_EL] >> strip_tac >> pop_assum $ assume_tac o GSYM >>
      last_x_assum drule >> simp[] >>
      disch_then $ qspec_then `PRE (LENGTH pvars − n')` mp_tac >>
      simp[GSYM itype_ok_type_ok, itype_ok_def]
      )
    >- (
      simp[EL_APPEND_EQN, EL_REVERSE, EL_ZIP, EL_MAP] >> rw[type_of_itype_of] >>
      Cases_on `n' - LENGTH pvars` >> gvs[pure_apply_subst, type_of_def]
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
      simp[ctxt_vars, msubst_vars_UNION] >> simp[GSYM msubst_vars_UNION] >>
      AP_TERM_TAC >> simp[pure_vars, UNION_ASSOC] >>
      once_rewrite_tac[INSERT_SING_UNION] >> AP_THM_TAC >> AP_TERM_TAC >>
      simp[ctxt_vars_def, MAP_REVERSE, ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF,
           LAMBDA_PROD, LIST_TO_SET_MAP] >>
      rw[Once EXTENSION, PULL_EXISTS, EXISTS_PROD]
      )
    >- (
      Cases_on `n` >> gvs[] >> simp[EL] >>
      qpat_x_assum `∀t. MEM _ _ ⇒ _` $ qspec_then `EL n' (TL tys)` mp_tac >>
      impl_tac >> rw[] >> gvs[] >> irule EL_MEM >> Cases_on `tys` >> gvs[]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> gvs[ALOOKUP_APPEND, get_massumptions_def] >>
      reverse $ TOP_CASE_TAC >> simp[]
      >- (
        PairCases_on `x` >> rw[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP]
        ) >>
      IF_CASES_TAC >> gvs[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_maunion] >>
      qsuff_tac
        `∃s. FLOOKUP (FOLDR maunion FEMPTY final_as) k = SOME s ∧ v' ⊆ s`
      >- (strip_tac >> simp[] >> CASE_TAC >> rw[] >> gvs[SUBSET_DEF]) >>
      `¬ MEM k pvars` by (
        qpat_x_assum `ALOOKUP _ _ = _` mp_tac >>
        simp[ALOOKUP_NONE, MEM_MAP, FORALL_PROD, MEM_ZIP, EXISTS_PROD] >>
        rw[Once MONO_NOT_EQ, MEM_EL] >> irule_at Any EQ_REFL >> simp[EL_MAP]) >>
      simp[FLOOKUP_FOLDR_maunion] >> rw[MEM_EL, PULL_EXISTS]
      >- (goal_assum drule >> gvs[FLOOKUP_DEF]) >>
      simp[SUBSET_DEF, PULL_EXISTS] >> rw[] >>
      rpt $ goal_assum drule >> simp[FLOOKUP_FDIFF]
      )
    )
  >- ( (* Case *)
    simp[Once type_tcexp_cases] >> rpt disj2_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, MEM_MAP, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst] >> gvs[GSYM $ cj 9 pure_walkstar_alt] >>
    PairCases_on `ns` >> gvs[] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    qexists_tac `id` >> simp[] >>
    irule_at Any $ cj 2 type_of_lemma >>
    `EVERY (λit. pure_vars it = {}) $ MAP (csubst closing) $
      MAP (pure_walkstar sub) $ MAP CVar freshes` by (
      rw[EVERY_MEM, MEM_MAP] >> irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars, MEM_MAP, PULL_EXISTS]) >>
    gvs[pure_vars_empty_eq_type_of_MAP] >> irule_at Any EQ_REFL >>
    imp_res_tac $ cj 1 $ iffLR MAP_EQ_EVERY2 >> gvs[] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      imp_res_tac sortingTheory.PERM_LIST_TO_SET >> gvs[] >>
      qspec_then `FST` drule sortingTheory.PERM_MAP >> rw[] >>
      drule sortingTheory.PERM_LIST_TO_SET >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
      )
    >- (imp_res_tac sortingTheory.PERM_LENGTH >> gvs[]) >>
    gvs[LIST_REL_EL_EQN, EVERY_EL, EL_ZIP, EL_MAP] >> rw[] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >> simp[] >> strip_tac >> simp[] >> rpt conj_asm1_tac
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
      )
    >- (
      gvs[MEM_FLAT, MEM_MAP, DISJ_EQ_IMP, PULL_EXISTS, EXISTS_PROD, MEM_EL] >>
      metis_tac[]
      ) >>
    last_x_assum drule >> simp[] >> strip_tac >> pop_assum irule >> conj_tac
    >- (
      gvs[MEM_EL, PULL_EXISTS] >> rw[] >>
      first_x_assum irule >> goal_assum drule >> simp[]
      ) >>
    goal_assum $ drule_at Any >> simp[] >>
    qexists_tac `REVERSE (ZIP (pvars,MAP ($, 0)
      (MAP (isubst (MAP CVar freshes) o itype_of) schemes))) ++ (v,0,CVar f)::ictxt` >>
    qpat_x_assum `∀c s. _ ∧ _ ⇒ _` mp_tac >> simp[Once MEM_EL, PULL_EXISTS] >>
    disch_then $ drule_at Any >>
    simp[PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP,
         DISJ_IMP_THM, FORALL_AND_THM, satisfies_def, EL_MAP] >>
    strip_tac >> gvs[] >> rw[]
    >- (
      simp[EL_APPEND_EQN, EL_REVERSE, EL_ZIP, EL_MAP] >>
      reverse $ rw[] >- (Cases_on `n' - LENGTH schemes` >> gvs[freedbvars_def]) >>
      gvs[namespace_ok_def, EVERY_EL, freetyvars_ok_freedbvars, oEL_THM] >>
      drule ALOOKUP_MEM >> simp[MEM_EL] >> strip_tac >> pop_assum $ assume_tac o GSYM >>
      last_x_assum kall_tac >> last_x_assum drule >> simp[] >>
      disch_then drule >> simp[] >>
      disch_then $ qspec_then `PRE (LENGTH schemes − n')` mp_tac >>
      rw[GSYM itype_ok_type_ok, itype_ok_def] >>
      irule freedbvars_isubst_EMPTY_suff >> simp[EVERY_MAP, freedbvars_def]
      )
    >- (
      simp[EL_APPEND_EQN, EL_REVERSE, EL_ZIP, EL_MAP] >> rw[type_of_itype_of]
      >- (
        DEP_REWRITE_TAC[pure_walkstar_isubst] >> conj_tac >- gvs[itype_ok_def] >>
        simp[pure_apply_subst_isubst_itype_of] >>
        drule_then (assume_tac o GSYM) type_of_SOME_MAP >>
        simp[isubst_itype_of, type_of_itype_of]
        )
      >- (
        Cases_on `n' - LENGTH schemes` >> gvs[pure_apply_subst] >>
        irule $ cj 2 type_of_lemma >> simp[]
        )
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
      once_rewrite_tac[INSERT_SING_UNION] >> rewrite_tac[msubst_vars_UNION] >>
      simp[ctxt_vars, msubst_vars_UNION, pure_vars, UNION_ASSOC] >>
      AP_THM_TAC >> AP_TERM_TAC >>
      simp[msubst_vars_def, ctxt_vars_def, MAP_REVERSE, ZIP_MAP, MAP_MAP_o,
           combinTheory.o_DEF, LAMBDA_PROD, LIST_TO_SET_MAP, IMAGE_IMAGE,
           pure_vars] >>
      irule SUBSET_ANTISYM >> simp[] >>
      simp[SUBSET_DEF, PULL_EXISTS, MEM_ZIP] >> rw[] >>
      qspecl_then [`MAP CVar freshes`,`itype_of (EL n' schemes)`]
        mp_tac pure_vars_isubst_SUBSET >>
      simp[MAP_MAP_o, combinTheory.o_DEF, pure_vars, LIST_TO_SET_MAP,
           SUBSET_DEF, PULL_EXISTS] >>
      disch_then drule >> simp[SF SFY_ss]
      )
    >- (
      Cases_on `n` >> gvs[] >> simp[EL] >>
      qpat_x_assum `∀t. MEM _ _ ⇒ _` $ qspec_then `EL n' (TL tys)` mp_tac >>
      impl_tac >> rw[] >> gvs[] >> irule EL_MEM >> Cases_on `tys` >> gvs[]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> gvs[ALOOKUP_APPEND, get_massumptions_def] >>
      reverse $ TOP_CASE_TAC >> simp[]
      >- (
        PairCases_on `x` >> rw[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP]
        ) >>
      IF_CASES_TAC >> gvs[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_maunion] >>
      qsuff_tac
        `∃s. FLOOKUP (FOLDR maunion FEMPTY final_as) k = SOME s ∧ v' ⊆ s`
      >- (strip_tac >> simp[] >> CASE_TAC >> rw[] >> gvs[SUBSET_DEF]) >>
      `¬ MEM k pvars` by (
        qpat_x_assum `ALOOKUP _ _ = _` mp_tac >>
        simp[ALOOKUP_NONE, MEM_MAP, FORALL_PROD, MEM_ZIP, EXISTS_PROD] >>
        rw[Once MONO_NOT_EQ, MEM_EL] >> irule_at Any EQ_REFL >> simp[EL_MAP]) >>
      simp[FLOOKUP_FOLDR_maunion] >> rw[MEM_EL, PULL_EXISTS]
      >- (goal_assum drule >> gvs[FLOOKUP_DEF]) >>
      simp[SUBSET_DEF, PULL_EXISTS] >> rw[] >>
      rpt $ goal_assum drule >> simp[FLOOKUP_FDIFF]
      )
    )
QED

Theorem inference_constraints_sound:
  namespace_ok ns ∧ infer ns LN e 0 = SOME ((ty,as,cs), n) ∧
  null as ∧
  pure_wfs sub ∧
  (∀it. it ∈ FRANGE sub ⇒ itype_ok (SND ns) 0 it) ∧
  (∀c. c ∈ set (MAP to_mconstraint cs) ⇒ satisfies (SND ns) sub c) ∧
  generalises_to {} (pure_walkstar sub ty) (db,sch)
  ⇒ ∃t. type_of sch = SOME t ∧ type_tcexp ns db [] [] (tcexp_of e) t
Proof
  rw[] >> irule_at Any inference_constraints_sound_lemma >> simp[] >>
  goal_assum drule >> simp[] >>
  drule infer_minfer >> rw[] >> goal_assum drule >> simp[] >>
  `mas = FEMPTY` by (
    gvs[assumptions_rel_def] >>
    Cases_on `as` >> gvs[null_def] >>
    Cases_on `b` >> gvs[balanced_mapTheory.null_def] >>
    gvs[lookup_def, balanced_mapTheory.lookup_def] >> rw[fmap_eq_flookup]) >>
  gvs[] >> simp[ctxt_rel_def, ctxt_vars_def, msubst_vars_def] >>
  qabbrev_tac `vs = BIGUNION $ IMAGE (pure_vars o pure_walkstar sub o CVar) $
    pure_vars ty ∪
      BIGUNION (IMAGE new_vars_constraint (set (MAP to_mconstraint cs)))` >>
  gvs[generalises_to_def] >>
  qabbrev_tac `close = FUNION (DBVar o_f gen) (FUN_FMAP (K Unit) vs)` >>
  `FINITE vs` by (
    unabbrev_all_tac >> simp[PULL_EXISTS, MEM_MAP] >>
    irule IMAGE_FINITE >> simp[PULL_EXISTS, MEM_MAP] >>
    Cases >> simp[] >> Cases_on `p` >> simp[]) >>
  `pure_vars (csubst close (pure_walkstar sub ty)) = {}` by (
    simp[pure_vars_pure_apply_subst] >> simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >> rw[] >>
    unabbrev_all_tac >> simp[pure_apply_subst] >>
    simp[FLOOKUP_FUNION, FLOOKUP_o_f, FLOOKUP_DEF, pure_vars]) >>
  gvs[pure_vars_empty_eq_type_of] >> goal_assum $ drule_at Any >> rpt conj_tac
  >- (rw[new_vars_def] >> unabbrev_all_tac >> simp[SUBSET_DEF, PULL_EXISTS, SF SFY_ss])
  >- (
    unabbrev_all_tac >> ho_match_mp_tac IN_FRANGE_FUNION_suff >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, MEM_MAP] >> rw[] >>
    simp[type_of_def, itype_ok]
    )
  >- (
    pop_assum mp_tac >> simp[Once pure_apply_subst_min] >>
    qmatch_goalsub_abbrev_tac `csubst foo _` >>
    qsuff_tac `foo = DBVar o_f gen` >> rw[] >> unabbrev_all_tac >>
    simp[DRESTRICTED_FUNION] >> rw[fmap_eq_flookup] >>
    simp[FLOOKUP_FUNION, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
    CASE_TAC >> gvs[FLOOKUP_DEF]
    )
QED

Theorem inference_constraints_safe_itree:
  namespace_ok ns ∧ infer ns LN e 0 = SOME ((ty,as,cs), n) ∧
  null as ∧
  pure_wfs sub ∧
  (∀it. it ∈ FRANGE sub ⇒ itype_ok (SND ns) 0 it) ∧
  (∀c. c ∈ set (MAP to_mconstraint cs) ∨ c = mUnify ty (M Unit)
    ⇒ satisfies (SND ns) sub c)
  ⇒ safe_itree (itree_of (exp_of e))
Proof
  rw[] >> gvs[SF DNF_ss] >>
  drule inference_constraints_sound >> rpt $ disch_then drule >>
  gvs[satisfies_def, pure_walkstar_alt, generalises_to_def, pure_vars] >>
  simp[PULL_EXISTS] >> disch_then $ qspec_then `FEMPTY` mp_tac >> simp[type_of_def] >>
  rw[] >> irule type_soundness_cexp >> rpt $ goal_assum drule
QED


(******************** Constraint solving ********************)

Triviality constraints_ok_subst_constraint:
  constraints_ok ns (set (MAP to_mconstraint cs)) ∧
  pure_wfs sub ∧ (∀it. it ∈ FRANGE sub ⇒ itype_ok ns 0 it) ⇒
  constraints_ok ns (set (MAP to_mconstraint (MAP (subst_constraint sub) cs)))
Proof
  simp[constraints_ok_def] >> strip_tac >>
  gvs[MEM_MAP, PULL_EXISTS] >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `y'` >> simp[subst_constraint_def] >>
  rpt $ irule_at Any itype_ok_pure_walkstar >> simp[] >>
  Cases_on `p` >> simp[subst_constraint_def] >>
  rpt $ irule_at Any itype_ok_pure_walkstar >> gvs[itype_ok_def]
QED

Triviality isubst_irrelevance:
  pure_vars (isubst its it) ⊆ s ⇒
  isubst (MAP
    (λt. if pure_vars t ⊆ s then t else any) its) it =
  isubst its it
Proof
  Induct_on `it` using itype_ind >> rw[isubst_def, EL_MAP] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, pure_vars] >> rw[] >>
  first_x_assum drule >> disch_then irule >>
  gvs[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS]
QED

Triviality pure_unify_FEMPTY:
  pure_unify FEMPTY t1 t2 = SOME s ⇒
    pure_wfs s ∧
    pure_walkstar s t1 = pure_walkstar s t2 ∧
    pure_substvars s ⊆ pure_vars t1 ∪ pure_vars t2
Proof
  strip_tac >>
  drule_at Any pure_unify_uP >> drule_at Any pure_unify_unifier >> rw[] >>
  gvs[pure_uP, pure_allvars]
QED

Triviality subst_constraint_DISJOINT_FDOM:
  ∀s c. pure_wfs s ⇒
    DISJOINT (FDOM s) (mactivevars (to_mconstraint (subst_constraint s c)))
Proof
  rw[] >> Cases_on `c` >> simp[subst_constraint_def, mactivevars_def]
  >- metis_tac[DISJOINT_ALT, pure_walkstar_vars_notin]
  >- (
    Cases_on `p` >> simp[subst_constraint_def, mactivevars_def] >>
    metis_tac[DISJOINT_ALT, pure_walkstar_vars_notin]
    ) >>
  conj_tac >- metis_tac[DISJOINT_ALT, pure_walkstar_vars_notin] >>
  map_every (irule_at Any) [SUBSET_DISJOINT, cj 2 INTER_SUBSET, SUBSET_REFL] >>
  metis_tac[DISJOINT_ALT, pure_walkstar_vars_notin]
QED

Triviality mactivevars_subst_constraint:
  pure_wfs s ⇒
  mactivevars (to_mconstraint (subst_constraint s c)) ⊆
  mactivevars (to_mconstraint c) ∪ pure_substvars s
Proof
  Cases_on `c` >> rw[subst_constraint_def, mactivevars_def]
  >- (
    irule SUBSET_TRANS >> irule_at Any pure_walkstar_vars_in >>
    simp[pure_substvars, pure_rangevars, IMAGE_FRANGE] >> rw[SUBSET_DEF]
    )
  >- (
    irule SUBSET_TRANS >> irule_at Any pure_walkstar_vars_in >>
    simp[pure_substvars, pure_rangevars, IMAGE_FRANGE] >> rw[SUBSET_DEF]
    )
  >- (
    Cases_on `p` >> rw[subst_constraint_def, mactivevars_def] >>
    irule SUBSET_TRANS >> irule_at Any pure_walkstar_vars_in >>
    simp[pure_substvars, pure_rangevars, IMAGE_FRANGE] >> rw[SUBSET_DEF]
    )
  >- (
    irule SUBSET_TRANS >> irule_at Any pure_walkstar_vars_in >>
    simp[pure_substvars, pure_rangevars, IMAGE_FRANGE] >> rw[SUBSET_DEF]
    )
  >- (
    rw[subst_vars_msubst_vars, msubst_vars_def, SUBSET_DEF] >>
    imp_res_tac $ SRULE [SUBSET_DEF] pure_walkstar_vars_in >> gvs[pure_vars] >>
    gvs[pure_substvars, pure_rangevars, GSYM IMAGE_FRANGE] >> metis_tac[]
    )
QED

Triviality msubst_vars_FUNION:
  ∀t s.
    pure_wfs s ∧ pure_wfs t ∧
    DISJOINT (FDOM t) (pure_substvars s)
  ⇒ msubst_vars (FUNION t s) = msubst_vars s o msubst_vars t
Proof
  rw[Once FUN_EQ_THM] >> rw[msubst_vars_def] >>
  rw[Once EXTENSION, PULL_EXISTS] >> eq_tac >> rw[] >>
  gvs[pure_walkstar_FUNION]
  >- (
    qpat_x_assum `_ ∈ pure_vars _` mp_tac >>
    simp[Once pure_vars_pure_walkstar_alt] >> rw[] >> rpt $ goal_assum drule
    )
  >- (
    simp[Once pure_vars_pure_walkstar_alt] >>
    simp[PULL_EXISTS] >> rpt $ goal_assum drule
    )
QED

Triviality pure_substvars_FUNION:
  DISJOINT (FDOM s1) (FDOM s2) ⇒
  pure_substvars (FUNION s1 s2) = pure_substvars s1 ∪ pure_substvars s2
Proof
  rw[pure_substvars, pure_rangevars, FRANGE_FUNION] >>
  simp[AC UNION_ASSOC UNION_COMM]
QED

Triviality satisfies_FUNION:
  ∀c. DISJOINT (FDOM t) (pure_substvars s) ∧ pure_wfs s ∧ pure_wfs t ∧
    satisfies tds s (to_mconstraint (subst_constraint t c)) ⇒
    satisfies tds (FUNION t s) (to_mconstraint c)
Proof
  Cases >> rw[satisfies_def, subst_constraint_def] >> gvs[pure_walkstar_FUNION]
  >- (
    Cases_on `p` >> gvs[satisfies_def, subst_constraint_def, pure_walkstar_FUNION] >>
    irule_at Any EQ_REFL >> simp[]
    )
  >- (
    irule_at Any EQ_REFL >> simp[] >>
    gvs[msubst_vars_FUNION, subst_vars_msubst_vars]
    )
QED

Triviality constraint_vars_subst_constraint_SUBSET:
  pure_substvars s ⊆ X ∧ pure_wfs s ∧
  constraint_vars (to_mconstraint c) ⊆ X
  ⇒ constraint_vars (to_mconstraint (subst_constraint s c)) ⊆ X
Proof
  Cases_on `c` >> rw[] >> gvs[subst_constraint_def, constraint_vars_def] >>
  gvs[pure_substvars, pure_rangevars, IMAGE_FRANGE]
  >- (
    rw[] >> irule SUBSET_TRANS >> irule_at Any pure_vars_pure_walkstar_SUBSET >>
    gvs[SUBSET_DEF] >> metis_tac[]
    )
  >- (
    Cases_on `p` >> gvs[subst_constraint_def, constraint_vars_def] >>
    rw[] >> irule SUBSET_TRANS >> irule_at Any pure_vars_pure_walkstar_SUBSET >>
    gvs[SUBSET_DEF] >> metis_tac[]
    ) >>
  rw[]
  >- (
    irule SUBSET_TRANS >> irule_at Any pure_vars_pure_walkstar_SUBSET >>
    gvs[SUBSET_DEF] >> metis_tac[]
    )
  >- (
    simp[subst_vars_msubst_vars, msubst_vars_def, BIGUNION_SUBSET, PULL_EXISTS] >>
    rw[] >> irule SUBSET_TRANS >> irule_at Any pure_vars_pure_walkstar_SUBSET >>
    gvs[pure_vars, SUBSET_DEF] >> metis_tac[]
    )
  >- (
    irule SUBSET_TRANS >> irule_at Any pure_vars_pure_walkstar_SUBSET >>
    gvs[SUBSET_DEF] >> metis_tac[]
    )
QED

Theorem solve_monad_mono:
  ∀cs n ss m. solve cs n = SOME (ss, m) ⇒ n ≤ m
Proof
  Induct using solve_ind >> simp[Once solve_def] >- gvs[return_def] >>
  rpt gen_tac >> TOP_CASE_TAC >> gvs[fail_def] >>
  TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[]
  >- (
    rename1 `pure_unify _ t1 t2` >> Cases_on `pure_unify FEMPTY t1 t2` >>
    gvs[oreturn_def, infer_bind_def, fail_def, return_def] >>
    CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >> rw[] >>
    first_x_assum drule >> simp[]
    )
  >- (
    CASE_TAC >> simp[fresh_vars_def, infer_bind_def] >>
    rw[] >> gvs[] >> first_x_assum drule >> rw[]
    )
  >- (pairarg_tac >> gvs[])
QED

Theorem solve_sound:
  ∀ns. namespace_ok ns ⇒
  ∀cs sub n m.
    solve cs n = SOME (sub,m) ∧
    constraints_ok (SND ns) (set (MAP to_mconstraint cs)) ∧
    (BIGUNION $ set (MAP (constraint_vars o to_mconstraint) cs) ⊆ count n)
  ⇒ pure_wfs sub ∧
    pure_substvars sub ⊆
      BIGUNION (set (MAP (mactivevars o to_mconstraint) cs)) ∪
      { v | n ≤ v ∧ v < m } ∧
    (∀it. it ∈ FRANGE sub ⇒ itype_ok (SND ns) 0 it) ∧
    (∀c. MEM c cs ⇒ satisfies (SND ns) sub (to_mconstraint c))
Proof
  gen_tac >> strip_tac >> recInduct solve_ind >>
  conj_tac >> rpt gen_tac >> strip_tac >- gvs[solve_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `solve _ _ = _` mp_tac >> once_rewrite_tac[solve_def] >>
  CASE_TAC
  >- (
    qmatch_asmsub_abbrev_tac `get_solveable l` >> gvs[] >>
    imp_res_tac get_solveable_NONE >> gvs[] >>
    strip_tac >> gvs[] >>
    qmatch_asmsub_abbrev_tac `monomorphise_implicit active` >>
    `domain active = BIGUNION (set (MAP (mactivevars o to_mconstraint) l))` by (
      simp[Abbr`active`] >> rpt $ pop_assum kall_tac >>
      Induct_on `l` using SNOC_INDUCT >> rw[] >> simp[FOLDL_SNOC, domain_union] >>
      simp[SNOC_APPEND, domain_activevars, AC UNION_ASSOC UNION_COMM]) >>
    first_x_assum drule >> impl_tac >> simp[]
    >- (
      gvs[BIGUNION_SUBSET, constraints_ok_def, MEM_MAP, PULL_EXISTS] >>
      simp[GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM] >> gen_tac >> strip_tac >>
      rpt (first_x_assum drule >> strip_tac) >> gvs[] >>
      simp[monomorphise_implicit_def] >> pairarg_tac >> simp[] >>
      imp_res_tac generalise_0_FEMPTY >> gvs[] >>
      qmatch_asmsub_abbrev_tac `generalise _ _ _ _ = (new,gen_sub,_)` >>
      `FDIFF gen_sub (domain (union vs active)) = gen_sub` by (
        rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
      pop_assum SUBST_ALL_TAC >> rw[]
      >- (
        irule itype_ok_pure_apply_subst >>
        simp[IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_o_f] >>
        reverse $ rw[] >- gvs[itype_ok_def] >>
        FULL_CASE_TAC >> gvs[] >> simp[itype_ok] >>
        gvs[EXTENSION, FRANGE_FLOOKUP, EQ_IMP_THM, SF DNF_ss] >> res_tac
        )
      >- (
        gvs[constraint_vars_def] >> simp[pure_vars_pure_apply_subst] >>
        simp[BIGUNION_SUBSET, PULL_EXISTS] >> rw[] >>
        simp[pure_apply_subst, FLOOKUP_o_f] >>
        CASE_TAC >> simp[pure_vars] >> gvs[SUBSET_DEF]
        )
      ) >>
    rw[]
    >- (
      irule SUBSET_TRANS >> goal_assum drule >> simp[] >>
      rw[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
      first_x_assum drule >> rw[] >> simp[monomorphise_implicit_def] >>
      pairarg_tac >> gvs[] >> imp_res_tac generalise_0_FEMPTY >> gvs[] >>
      qmatch_asmsub_abbrev_tac `generalise _ _ _ _ = (new,gen_sub,_)` >>
      `FDIFF gen_sub (domain (union vs active)) = gen_sub` by (
        rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
      pop_assum SUBST_ALL_TAC >> rw[mactivevars_def, SUBSET_DEF] >>
      simp[MEM_MAP, PULL_EXISTS]
      >- (disj1_tac >> goal_assum $ drule_at Any >> simp[mactivevars_def]) >>
      pop_assum mp_tac >> simp[pure_vars_pure_apply_subst] >>
      simp[PULL_EXISTS, pure_vars, pure_apply_subst, FLOOKUP_o_f] >>
      gen_tac >> every_case_tac >> rw[] >> gvs[pure_vars, FLOOKUP_DEF, domain_union]
      >- (disj1_tac >> goal_assum $ drule_at Any >> simp[mactivevars_def])
      >- (disj1_tac >> gvs[MEM_MAP, SF SFY_ss])
      )
    >- (
      gvs[MEM_MAP, PULL_EXISTS] >>
      rpt (first_x_assum drule >> strip_tac) >> gvs[monomorphise_implicit_def] >>
      pairarg_tac >> gvs[] >> imp_res_tac generalise_0_FEMPTY >> gvs[] >>
      qmatch_asmsub_abbrev_tac `generalise _ _ _ _ = (new,gen_sub,_)` >>
      `FDIFF gen_sub (domain (union vs active)) = gen_sub` by (
        rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
      pop_assum SUBST_ALL_TAC >> gvs[LIST_TO_SET_MAP, IMAGE_IMAGE] >>
      `BIGUNION $ IMAGE
        (mactivevars o to_mconstraint o monomorphise_implicit active) (set l) =
       BIGUNION $ IMAGE (mactivevars o to_mconstraint) (set l)` by (
        rw[Once EXTENSION, PULL_EXISTS] >> eq_tac >> rw[]
        >- (
          imp_res_tac get_solveable_NONE >> gvs[] >> pop_assum drule >> rw[] >>
          gvs[monomorphise_implicit_def] >> pairarg_tac >> gvs[] >>
          drule generalise_0_FEMPTY >> strip_tac >> gvs[] >>
          qmatch_asmsub_abbrev_tac `generalise _ _ _ _ = (new',gen_sub',_)` >>
          `FDIFF gen_sub' (domain (union vs' active)) = gen_sub'` by (
            rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
          pop_assum SUBST_ALL_TAC >>
          gvs[mactivevars_def, SUBSET_DEF] >> simp[MEM_MAP, PULL_EXISTS]
          >- (goal_assum $ drule_at Any >> simp[mactivevars_def]) >>
          qpat_x_assum `_ ∈ pure_vars _` mp_tac >> simp[pure_vars_pure_apply_subst] >>
          simp[PULL_EXISTS, pure_vars, pure_apply_subst, FLOOKUP_o_f] >>
          gen_tac >> CASE_TAC >> rw[] >> gvs[pure_vars, FLOOKUP_DEF, domain_union] >>
          goal_assum $ drule_at Any >> simp[mactivevars_def]
          )
        >- (
          imp_res_tac get_solveable_NONE >> gvs[] >> pop_assum drule >> rw[] >>
          goal_assum $ drule_at Any >> simp[] >>
          simp[monomorphise_implicit_def] >> pairarg_tac >> gvs[] >>
          drule generalise_0_FEMPTY >> strip_tac >> gvs[] >>
          qmatch_asmsub_abbrev_tac `generalise _ _ _ _ = (new',gen_sub',_)` >>
          `FDIFF gen_sub' (domain (union vs' active)) = gen_sub'` by (
            rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
          pop_assum SUBST_ALL_TAC >>
          gvs[mactivevars_def, SUBSET_DEF] >> simp[MEM_MAP, PULL_EXISTS] >> disj2_tac >>
          simp[pure_vars_pure_apply_subst] >>
          simp[PULL_EXISTS, pure_vars, pure_apply_subst, FLOOKUP_o_f] >>
          goal_assum $ drule_at Any >> simp[] >>
          CASE_TAC >> gvs[pure_vars, FLOOKUP_DEF, domain_union]
          )
        ) >>
      gvs[] >> qpat_x_assum `satisfies _ _ _` mp_tac >>
      rw[satisfies_def] >> simp[] >> gvs[domain_union] >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst] >> simp[] >> conj_asm1_tac
      >- (
        irule DISJOINT_SUBSET >> goal_assum $ drule_at Any >>
        simp[DISJOINT_ALT, SF DNF_ss] >> rw[SF SFY_ss] >>
        rpt disj1_tac >> CCONTR_TAC >> gvs[SUBSET_DEF] >>
        qsuff_tac `x < n` >- simp[] >>
        last_x_assum irule >> simp[PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[constraint_vars_def]
        ) >>
      DEP_REWRITE_TAC[isubst_pure_apply_subst_alt] >> rw[]
      >- (
        gvs[constraints_ok_def, PULL_EXISTS] >> last_x_assum drule >> rw[] >>
        drule_all itype_ok_pure_walkstar >> simp[itype_ok_def]
        ) >>
      simp[combinTheory.o_DEF, pure_walkstar_alt] >> irule_at Any EQ_REFL >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >> rw[]
      >- (
        simp[DIFF_SUBSET] >> rw[SUBSET_DEF, SF DNF_ss] >>
        Cases_on `x ∈ domain vs` >> gvs[] >>
        `x < n` by (
          gvs[SUBSET_DEF, SF DNF_ss] >> last_x_assum irule >>
          goal_assum drule >> simp[constraint_vars_def]) >>
        simp[DISJ_EQ_IMP] >> strip_tac >> gvs[] >>
        `x ∉ pure_substvars sub` by (
          CCONTR_TAC >> gvs[SUBSET_DEF] >> last_x_assum drule >>
          rw[DISJ_EQ_IMP] >> gvs[]) >>
        simp[pure_vars_pure_walkstar_alt] >> simp[PULL_EXISTS, pure_vars] >>
        goal_assum $ drule_at Any >>
        simp[pure_walkstar_alt, FLOOKUP_DEF] >> gvs[pure_substvars, pure_vars] >>
        simp[msubst_vars_def, DISJ_EQ_IMP, PULL_FORALL] >>
        CCONTR_TAC >> gvs[] >>
        drule_all $ SRULE [SUBSET_DEF] pure_vars_pure_walkstar_SUBSET >>
        simp[pure_vars] >> Cases_on `x ≠ x'` >> gvs[] >>
        gvs[GSYM IMAGE_FRANGE, pure_rangevars]
        )
      >- (gvs[GSYM IMAGE_FRANGE, EVERY_EL] >> simp[isubst_def])
      >- (
        simp[isubst_def, pure_vars_pure_apply_subst] >>
        rw[SUBSET_DEF, PULL_EXISTS] >>
        `∃rev_gen. fmap_linv gen_sub rev_gen` by (
          irule $ iffRL CARD_has_fmap_linv >> simp[] >>
          DEP_REWRITE_TAC[CARD_DIFF] >> rw[PULL_EXISTS] >>
          imp_res_tac get_solveable_NONE >> gvs[] >> pop_assum drule >> rw[] >>
          simp[mactivevars_def]) >>
        gvs[fmap_linv_alt_def] >>
        qexists_tac `rev_gen ' x` >>
        simp[pure_apply_subst, FLOOKUP_DEF, FRANGE_DEF] >>
        reverse IF_CASES_TAC >- gvs[] >> pop_assum kall_tac >> simp[] >>
        gvs[DISJOINT_ALT, FRANGE_DEF, PULL_EXISTS] >> last_x_assum drule >> rw[] >>
        `rev_gen ' x ∈ pure_vars t2` by (
          qpat_x_assum `_ DIFF _ = _` mp_tac >>
          simp[Once EXTENSION, EQ_IMP_THM, SF DNF_ss]) >>
        rename1 `foo ∈ _` >>
        simp[pure_vars_pure_walkstar_alt] >> simp[PULL_EXISTS, pure_vars] >>
        goal_assum $ drule_at Any >>
        simp[pure_walkstar_alt, FLOOKUP_DEF] >> gvs[pure_substvars, pure_vars]
        )
      )
    ) >>
  gvs[] >> CASE_TAC >> rename1 `get_solveable (h::t) _ = SOME (c,cs)` >>
  imp_res_tac get_solveable_SOME >> gvs[] >>
  `constraints_ok (SND ns) (set (MAP to_mconstraint (left ++ [c] ++ right)))` by  (
    qpat_x_assum `_::_ = _` $ rewrite_tac o single o GSYM >> simp[]) >>
  qpat_x_assum `constraints_ok _ (_ INSERT _)` kall_tac >>
  `BIGUNION (set (MAP (constraint_vars o to_mconstraint)
    (left ++ [c] ++ right))) ⊆ count n` by  (
    qpat_x_assum `_::_ = _` $ rewrite_tac o single o GSYM >> simp[]) >>
  qpat_x_assum `constraint_vars _ ⊆ _` kall_tac >>
  qpat_x_assum `BIGUNION (set (_ t)) ⊆ _` kall_tac >>
  `∀c'. MEM c' (h::t) ⇔ MEM c' (left ++ [c] ++ right)` by (
    rpt AP_TERM_TAC >> asm_rewrite_tac[]) >>
  pop_assum mp_tac >> simp[] >> disch_then kall_tac >>
  `BIGUNION (set (MAP (mactivevars ∘ to_mconstraint) (h::t))) =
    BIGUNION (set (MAP (mactivevars ∘ to_mconstraint) (left ++ [c] ++ right)))` by (
    rpt AP_TERM_TAC >> simp[]) >>
  pop_assum mp_tac >> simp[] >> disch_then kall_tac >>
  qpat_x_assum `_::_ = _` kall_tac >> CASE_TAC >> gvs[]
  >- (
    rename1 `Unify _ t1 t2` >> simp[infer_bind_def] >>
    Cases_on `pure_unify FEMPTY t1 t2` >> gvs[oreturn_def, fail_def, return_def] >>
    CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >> strip_tac >> gvs[] >>
    imp_res_tac pure_unify_FEMPTY >>
    `∀it. it ∈ FRANGE x ⇒ itype_ok (SND ns) 0 it` by (
      ho_match_mp_tac pure_unify_itype_ok >> qexists_tac `FEMPTY` >> simp[] >>
      goal_assum $ drule_at Any >> gvs[constraints_ok_UNION] >>
      qpat_x_assum `constraints_ok _ {_}` mp_tac >>
      once_rewrite_tac[constraints_ok_def] >> rw[]) >>
    first_x_assum drule >> impl_tac
    >- (
      gvs[constraints_ok_UNION] >>
      rpt $ irule_at Any constraints_ok_subst_constraint >> simp[] >>
      gvs[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> rw[] >>
      irule constraint_vars_subst_constraint_SUBSET >> simp[] >>
      gvs[constraint_vars_def, SUBSET_DEF] >> metis_tac[]
      ) >>
    rename1 `FUNION x sub'` >> strip_tac >>
    `DISJOINT (FDOM x) (pure_substvars sub')` by (
      irule DISJOINT_SUBSET >> goal_assum $ drule_at Any >>
      simp[MEM_MAP, PULL_EXISTS] >> once_rewrite_tac[DISJOINT_SYM] >>
      rw[] >> rpt $ irule_at Any subst_constraint_DISJOINT_FDOM >> simp[] >>
      gvs[constraint_vars_def, pure_substvars] >>
      irule SUBSET_DISJOINT >> goal_assum $ drule_at Any >>
      irule_at Any SUBSET_REFL >>
      simp[DISJOINT_ALT] >> gvs[SUBSET_DEF] >>
      rw[] >> gvs[] >> first_x_assum drule >> simp[]) >>
    irule_at Any pure_wfs_FUNION >> simp[] >>
    DEP_REWRITE_TAC[pure_walkstar_FUNION] >> simp[] >>
    DEP_REWRITE_TAC[FRANGE_FUNION, pure_substvars_FUNION] >> rpt conj_tac
    >- (gvs[pure_substvars] >> simp[Once DISJOINT_SYM])
    >- (
      rw[mactivevars_def] >- gvs[SUBSET_DEF] >>
      irule SUBSET_TRANS >> goal_assum $ drule_at Any >> rw[] >>
      simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> rw[] >>
      irule SUBSET_TRANS >> irule_at Any mactivevars_subst_constraint >> simp[] >>
      gvs[SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> rw[SF SFY_ss]
      )
    >- simp[DISJ_IMP_THM]
    >- (
      rw[]
      >- (
        irule satisfies_FUNION >>
        gvs[MEM_MAP, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]
        )
      >- (irule satisfies_FUNION >> simp[subst_constraint_def, satisfies_def])
      >- (
        irule satisfies_FUNION >>
        gvs[MEM_MAP, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]
        )
      )
    )
  >- (
    CASE_TAC >> rename1 `Instantiate _ t1 (vs,sch)` >>
    simp[fresh_vars_def, infer_bind_def] >>
    qmatch_goalsub_abbrev_tac `MAP CVar freshes` >> strip_tac >> gvs[] >>
    first_x_assum drule >> impl_tac
    >- (
      once_rewrite_tac[INSERT_SING_UNION] >> gvs[constraints_ok_UNION] >>
      qpat_x_assum `constraints_ok _ {_}` mp_tac >> simp[constraints_ok_def] >> rw[]
      >- (
        irule itype_ok_isubst >> simp[EVERY_MAP, itype_ok] >>
        unabbrev_all_tac >> gvs[]
        )
      >- (
        gvs[constraint_vars_def] >>
        conj_tac >- (gvs[SUBSET_DEF] >> rw[] >> res_tac >> simp[]) >>
        irule SUBSET_TRANS >> irule_at Any pure_vars_isubst_SUBSET >> simp[] >>
        conj_tac >- (gvs[SUBSET_DEF] >> rw[] >> res_tac >> simp[]) >>
        unabbrev_all_tac >>
        simp[BIGUNION_SUBSET, MEM_MAP, MEM_GENLIST, PULL_EXISTS, pure_vars]
        ) >>
      gvs[SUBSET_DEF] >> rw[] >> res_tac >> simp[]
      ) >>
    strip_tac >> simp[] >> rpt conj_tac
    >- (
      irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
      simp[mactivevars_def, GSYM CONJ_ASSOC] >> rw[]
      >- gvs[SUBSET_DEF]
      >- (
        irule SUBSET_TRANS >> irule_at Any pure_vars_isubst_SUBSET >> rw[]
        >- (gvs[constraint_vars_def, SUBSET_DEF]) >>
        unabbrev_all_tac >>
        rw[BIGUNION_SUBSET, MEM_MAP, MEM_GENLIST, PULL_EXISTS, pure_vars] >>
        imp_res_tac solve_monad_mono >> gvs[]
        ) >>
      simp[SUBSET_DEF]
      ) >>
    gvs[satisfies_def, SF DNF_ss] >>
    qpat_x_assum `pure_walkstar _ _ = _` $ assume_tac o GSYM >> gvs[] >>
    pop_assum mp_tac >> DEP_REWRITE_TAC[pure_walkstar_isubst] >>
    conj_tac >- gvs[itype_ok_def] >> strip_tac >>
    qexists_tac `MAP (λn.
      if pure_vars (pure_walkstar sub (CVar n)) ⊆ pure_vars (pure_walkstar sub t1)
      then pure_walkstar sub (CVar n)
      else Unit) freshes` >>
    unabbrev_all_tac >>
    rw[EVERY_MAP, EVERY_GENLIST,
       itype_ok, pure_vars, COND_RAND, COND_RATOR, DISJ_EQ_IMP]
    >- (irule itype_ok_pure_walkstar >> simp[itype_ok]) >>
    simp[MAP_MAP_o, combinTheory.o_DEF, MAP_GENLIST] >>
    pop_assum $ assume_tac o GSYM >> simp[] >>
    irule_at Any EQ_TRANS >> irule_at Any $ GSYM isubst_irrelevance >>
    simp[MAP_MAP_o, combinTheory.o_DEF, MAP_GENLIST] >>
    irule_at Any SUBSET_REFL >> qexists_tac `Unit` >> simp[]
    )
  >- (
    pairarg_tac >> imp_res_tac generalise_0_FEMPTY >> gvs[] >>
    qmatch_asmsub_abbrev_tac `generalise _ _ _ _ = (new,gen,sch)` >>
    strip_tac >> rename1 `Implicit _ t1 vs t2` >>
    `pure_vars sch = pure_vars t2 DIFF FDOM gen` by (
      simp[Abbr `sch`, pure_vars_pure_apply_subst] >>
      rw[Once EXTENSION, PULL_EXISTS, pure_apply_subst, FLOOKUP_o_f, FLOOKUP_FDIFF] >>
      eq_tac >> rw[]
      >- (every_case_tac >> gvs[pure_vars])
      >- (every_case_tac >> gvs[pure_vars, FLOOKUP_DEF])
      >- (goal_assum $ drule_at Any >> simp[pure_vars])) >>
    first_x_assum drule >> impl_tac
    >- (
      once_rewrite_tac[INSERT_SING_UNION] >> gvs[constraints_ok_UNION] >>
      qpat_x_assum `constraints_ok _ {_}` mp_tac >> reverse $ rw[constraints_ok_def]
      >- (gvs[constraint_vars_def, DIFF_SUBSET] >> gvs[SUBSET_DEF]) >>
      unabbrev_all_tac >> irule itype_ok_pure_apply_subst >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, itype_ok] >> gvs[itype_ok_def] >>
      rw[] >> drule $ SRULE [SUBSET_DEF] FRANGE_FDIFF_SUBSET >> simp[]
      ) >>
    strip_tac >> gvs[SF DNF_ss, GSYM CONJ_ASSOC] >>
    DEP_REWRITE_TAC[satisfies_implicit_alt] >> simp[] >> rw[]
    >- (
      `itype_ok (SND ns) 0 (pure_walkstar sub t2)` suffices_by rw[itype_ok_def] >>
      irule itype_ok_pure_walkstar >> gvs[constraints_ok_def]
      )
    >- (
      irule SUBSET_TRANS >> goal_assum $ drule_at Any >> rw[]
      >- (gvs[mactivevars_def, DIFF_SUBSET] >> simp[SUBSET_DEF] >> metis_tac[]) >>
      simp[SUBSET_DEF]
      ) >>
    `generalises_to (domain vs) t2 (new,sch)` by (
      simp[generalises_to_def] >> goal_assum drule >> unabbrev_all_tac >> gvs[] >>
      AP_THM_TAC >> rpt AP_TERM_TAC >>
      rw[fmap_eq_flookup, FLOOKUP_FDIFF, FLOOKUP_DEF] >> rw[] >> gvs[]) >>
    irule_at Any generalise_solve_implicit >> simp[] >>
    goal_assum $ drule_at Any >> reverse $ rw[]
    >- (gvs[satisfies_def] >> irule_at Any EQ_REFL >> simp[pure_walkstar_idempotent]) >>
    qpat_x_assum `is_solveable _ _` mp_tac >>
    qpat_x_assum `pure_substvars _ ⊆ _` mp_tac >>
    rw[is_solveable_mis_solveable, mis_solveable_def, SUBSET_DEF] >>
    first_x_assum irule >> simp[PULL_EXISTS, SF DNF_ss, mactivevars_def] >>
    first_x_assum drule >> rw[mactivevars_def] >>
    gvs[MEM_MAP, PULL_EXISTS, SF SFY_ss] >>
    irule FALSITY >> gvs[constraint_vars_def, SUBSET_DEF, SF DNF_ss] >> res_tac >> gvs[]
    )
QED


(******************** Putting it all together ********************)

Theorem infer_top_level_sound:
  namespace_ok ns ∧
  IS_SOME (infer_top_level ns d cexp) ⇒
  safe_itree (itree_of (exp_of cexp))
Proof
  rw[] >> gvs[infer_top_level_def] >>
  gvs[infer_bind_def, infer_ignore_bind_def, fail_def, return_def] >>
  every_case_tac >> gvs[] >> pairarg_tac >> gvs[infer_bind_def] >>
  every_case_tac >> gvs[] >>
  Cases_on `solve (Unify d ty (M Unit)::cs) r` >> gvs[] >>
  irule inference_constraints_safe_itree >> rpt $ goal_assum $ drule_at Any >>
  drule infer_minfer >> simp[] >> strip_tac >> gvs[] >>
  `mas = FEMPTY` by (
    gvs[assumptions_rel_def] >> Cases_on `as` >> gvs[null_def] >>
    Cases_on `b` >> gvs[balanced_mapTheory.null_def] >>
    gvs[lookup_def, balanced_mapTheory.lookup_def] >> rw[fmap_eq_flookup]) >>
  gvs[] >> drule solve_sound >> PairCases_on `x` >> disch_then drule >>
  reverse impl_tac >- (rw[] >> goal_assum drule >> gvs[MEM_MAP, SF DNF_ss]) >>
  simp[] >> once_rewrite_tac[INSERT_SING_UNION] >> simp[constraints_ok_UNION] >>
  drule minfer_constraints_ok >> simp[] >> rw[]
  >- (
    simp[constraints_ok_def, constraint_vars_def, itype_ok] >>
    imp_res_tac minfer_itype_ok
    )
  >- gvs[new_vars_def, SUBSET_DEF, constraint_vars_def, pure_vars]
  >- (
    drule_all minfer_constraint_vars >> gvs[LIST_TO_SET_MAP, IMAGE_IMAGE] >>
    strip_tac >> irule_at Any SUBSET_TRANS >> goal_assum drule >>
    gvs[SUBSET_DEF]
    )
QED


(****************************************)

val _ = export_theory();

