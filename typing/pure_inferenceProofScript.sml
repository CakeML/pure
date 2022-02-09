open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory stringTheory optionTheory pred_setTheory
     listTheory rich_listTheory alistTheory finite_mapTheory sptreeTheory;
open mlmapTheory;
open pure_miscTheory pure_typingTheory pure_typingPropsTheory
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



(******************** Definitions/apparatus ********************)

Definition msubst_vars_def:
  msubst_vars s vars = BIGUNION (IMAGE (pure_vars o pure_walkstar s o CVar) vars)
End

Theorem subst_vars_msubst_vars:
  ∀s vs. pure_wfs s ⇒
    domain (subst_vars s vs) = msubst_vars s (domain vs)
Proof
  rw[subst_vars_def, msubst_vars_def] >>
  qsuff_tac
    `∀m b.
      domain (
        foldi (λn u acc. union acc (freecvars (pure_walkstar s (CVar n)))) m b vs) =
      BIGUNION (IMAGE
        (pure_vars o pure_walkstar s o CVar o (λi. m + sptree$lrnext m * i))
        (domain vs))
        ∪ domain b`
  >- rw[Once lrnext_def, combinTheory.o_DEF] >>
  qid_spec_tac `vs` >> Induct >> rw[foldi_def] >>
  simp[pure_walkstar_alt, freecvars_def, domain_union]
  >- (CASE_TAC >> simp[freecvars_pure_vars, domain_union, Once UNION_COMM]) >>
  simp[IMAGE_IMAGE, combinTheory.o_DEF] >>
  simp[lrnext_lrnext, lrnext_lrnext_2, LEFT_ADD_DISTRIB]
  >- simp[AC UNION_ASSOC UNION_COMM] >>
  qmatch_goalsub_abbrev_tac `BIGUNION A ∪ (BIGUNION B ∪ _ ∪ C) = C' ∪ _ ∪ _ ∪ _` >>
  qsuff_tac `C = C'` >> rw[] >- simp[AC UNION_ASSOC UNION_COMM] >>
  unabbrev_all_tac >> CASE_TAC >> simp[freecvars_pure_vars]
QED

Theorem msubst_vars_UNION:
  msubst_vars s (a ∪ b) = msubst_vars s a ∪ msubst_vars s b
Proof
  simp[msubst_vars_def]
QED

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


(******************** Main results ********************)


(****************************************)

val _ = export_theory();

