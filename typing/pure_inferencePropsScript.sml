open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory stringTheory optionTheory pred_setTheory
     listTheory rich_listTheory alistTheory finite_mapTheory sptreeTheory;
open mlmapTheory;
open pure_miscTheory pure_typingTheory pure_typingPropsTheory
     pure_inference_commonTheory pure_unificationTheory pure_inferenceTheory;

val _ = new_theory "pure_inferenceProps";

(******************* General results ********************)

(********** type_of/itype_of **********)

Theorem type_of_itype_of:
  ∀t. type_of (itype_of t) = SOME t
Proof
  recInduct type_ind >> rw[itype_of_def, type_of_def] >>
  Induct_on `l` >> rw[]
QED

Theorem type_of_SOME:
  ∀it t. type_of it = SOME t ⇒ itype_of t = it
Proof
  recInduct itype_ind >> rw[] >> gvs[type_of_def, itype_of_def] >>
  rpt $ pop_assum mp_tac >> qid_spec_tac `z` >> Induct_on `ts` >> rw[] >> gvs[]
QED

Theorem type_of_SOME_lemma:
  (∀its t. type_of (Tuple its) = SOME t ⇒
    ∃ts. t = Tuple ts ∧ MAP type_of its = MAP SOME ts) ∧
  (∀its id t. type_of (TypeCons id its) = SOME t
    ⇒ ∃ts. t = TypeCons id ts ∧ MAP type_of its = MAP SOME ts) ∧
  (∀its it ft. type_of (iFunctions its it) = SOME ft
    ⇒ ∃ts t. ft = Functions ts t ∧ MAP type_of its = MAP SOME ts ∧ type_of it = SOME t)
Proof
  rpt conj_tac >> Induct >> rw[] >> gvs[type_of_def, iFunctions_def, Functions_def] >>
  first_x_assum drule >> strip_tac >> simp[] >>
  qexists_tac `it1::ts` >> simp[Functions_def]
QED

Theorem type_of_lemma:
  (∀its ts. MAP type_of its = MAP SOME ts ⇒
    type_of (Tuple its) = SOME (Tuple ts)) ∧
  (∀its ts id. MAP type_of its = MAP SOME ts ⇒
    type_of (TypeCons id its) = SOME (TypeCons id ts)) ∧
  (∀its ts it t.
    MAP type_of its = MAP SOME ts ∧ type_of it = SOME t ⇒
    type_of (iFunctions its it) = SOME (Functions ts t))
Proof
  rpt conj_tac >> Induct >> rw[] >> gvs[type_of_def, iFunctions_def, Functions_def] >>
  Cases_on `ts` >> gvs[Functions_def]
QED


(********** pure_vars **********)

Theorem pure_vars_empty_eq_type_of:
  ∀it. pure_vars it = {} ⇔ (∃t. type_of it = SOME t)
Proof
  recInduct itype_ind >> reverse $ rw[pure_vars, type_of_def]
  >- (eq_tac >> rw[] >> rpt $ goal_assum drule >> simp[]) >>
  (
    Induct_on `ts` >> rw[] >> gvs[INSERT_EQ_SING] >> eq_tac >> rw[]
    >- (
      goal_assum drule >>
      first_x_assum $ irule o iffLR >>
      rw[DISJ_EQ_IMP, Once EXTENSION, MEM_MAP] >>
      gvs[LIST_TO_SET_MAP, SUBSET_DEF] >> eq_tac >> rw[] >>
      Cases_on `ts` >> gvs[] >> metis_tac[]
      )
    >- (goal_assum drule)
    >- gvs[LIST_TO_SET_MAP, SUBSET_DEF]
  )
QED

Theorem pure_vars_empty_eq_type_of_MAP:
  ∀its. (EVERY (λit. pure_vars it = {}) its) ⇔ ∃ts. MAP type_of its = MAP SOME ts
Proof
  Induct >> rw[] >> eq_tac >> rw[]
  >- (gvs[pure_vars_empty_eq_type_of] >> qexists_tac `t::ts` >> simp[])
  >- (
    Cases_on `ts` >> gvs[] >>
    irule $ iffRL pure_vars_empty_eq_type_of >>  goal_assum drule
    )
  >- ( Cases_on `ts` >> gvs[] >> irule_at Any EQ_REFL)
QED

Theorem pure_vars_itype_of[simp]:
  ∀t. pure_vars (itype_of t) = {}
Proof
  recInduct type_ind >> rw[itype_of_def, pure_vars] >>
  Induct_on `l` >> gvs[] >> rw[] >> gvs[]
QED

Theorem FINITE_pure_vars[simp]:
  ∀it. FINITE (pure_vars it)
Proof
  recInduct itype_ind >> rw[pure_vars_def]
QED

Theorem pure_vars_iFunctions:
  pure_vars (iFunctions tys ty) = BIGUNION (set (MAP pure_vars tys)) ∪ pure_vars ty
Proof
  Induct_on `tys` >> rw[iFunctions_def, pure_vars] >> simp[UNION_ASSOC]
QED

Theorem pure_vars_ishift[simp]:
  ∀n t. pure_vars (ishift n t) = pure_vars t
Proof
  gen_tac >> recInduct itype_ind >> rw[ishift_def, pure_vars] >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  rpt AP_TERM_TAC >> simp[MAP_EQ_f]
QED

Theorem pure_vars_isubst_SUBSET:
  ∀s t. pure_vars (isubst s t) ⊆ pure_vars t ∪ BIGUNION (set (MAP pure_vars s))
Proof
  recInduct isubst_ind >> rw[isubst_def, pure_vars] >>
  gvs[BIGUNION_SUBSET, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF, PULL_EXISTS] >>
  rw[] >> gvs[SUBSET_DEF, PULL_EXISTS] >> metis_tac[EL_MEM]
QED

Theorem pure_vars_isubst_SUPERSET:
  ∀s t. pure_vars t ⊆ pure_vars (isubst s t)
Proof
  recInduct isubst_ind >> rw[isubst_def, pure_vars] >>
  gvs[BIGUNION_SUBSET, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF, PULL_EXISTS] >>
  rw[] >> gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem pure_vars_pure_apply_subst_SUBSET:
  ∀t s. pure_vars (pure_apply_subst s t) ⊆
    (pure_vars t DIFF FDOM s) ∪ BIGUNION (IMAGE pure_vars (FRANGE s))
Proof
  recInduct itype_ind >> reverse $ rw[pure_apply_subst, pure_vars] >>
  simp[LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF, BIGUNION_SUBSET,
       FLOOKUP_DEF, pure_vars] >>
  gvs[SUBSET_DEF] >> rw[PULL_EXISTS]
  >- (goal_assum drule >> simp[FRANGE_DEF] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem pure_vars_pure_apply_subst_SUPERSET:
  ∀t s. pure_vars t DIFF FDOM s ∪
          BIGUNION (IMAGE (pure_vars o pure_apply_subst s o CVar) (pure_vars t)) ⊆
        pure_vars (pure_apply_subst s t)
Proof
  recInduct itype_ind >> reverse $ rw[pure_apply_subst, pure_vars]
  >- simp[BIGUNION_SUBSET, FLOOKUP_DEF, PULL_EXISTS, pure_vars] >>
  gvs[DIFF_SUBSET, BIGUNION_SUBSET,
      LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF, PULL_EXISTS] >>
  rw[] >> gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem pure_vars_pure_walkstar_SUBSET:
  ∀s t. pure_wfs s ⇒
    pure_vars (pure_walkstar s t) ⊆
      (pure_vars t ∪ BIGUNION (FRANGE (pure_vars o_f s))) DIFF FDOM s
Proof
  assume_tac pure_walkstar_vars_in >>
  assume_tac pure_walkstar_vars_notin >>
  gvs[SUBSET_DEF] >> rw[] >> res_tac
QED

Theorem pure_vars_pure_walkstar_SUPERSET:
  ∀s t.  pure_wfs s ⇒
    pure_vars t DIFF FDOM s ∪
      BIGUNION (IMAGE (pure_vars o pure_walkstar s o CVar) (pure_vars t)) ⊆
    pure_vars (pure_walkstar s t)
Proof
  gen_tac >> simp[GSYM PULL_FORALL] >> strip_tac >>
  qspec_then `s` mp_tac pure_walkstar_alt_ind >> simp[] >>
  disch_then ho_match_mp_tac >> reverse $ rw[] >>
  simp[pure_vars, pure_walkstar_alt]
  >- (gvs[FLOOKUP_DEF] >> IF_CASES_TAC >> gvs[pure_vars]) >>
  gvs[DIFF_SUBSET, BIGUNION_SUBSET, PULL_EXISTS,
      LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF] >>
  rw[] >> gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem pure_vars_pure_walkstar:
  ∀sub. pure_wfs sub ⇒
    ∀it n.
      n ∈ pure_vars (pure_walkstar sub it) ⇒
      ∃cv. cv ∈ pure_vars it ∧ n ∈ pure_vars (pure_walkstar sub (CVar cv))
Proof
  gen_tac >> strip_tac >>
  qspec_then `sub` mp_tac pure_walkstar_alt_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[pure_vars, pure_walkstar_alt] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, MEM_MAP, PULL_EXISTS]
  >- (
    goal_assum $ drule_at Any >>
    first_x_assum drule_all >> strip_tac >> gvs[] >> rpt $ goal_assum drule
    )
  >- (
    goal_assum $ drule_at Any >>
    first_x_assum drule_all >> strip_tac >> gvs[] >> rpt $ goal_assum drule
    )
  >- (
    first_x_assum drule >> strip_tac >> simp[] >>
    irule_at Any OR_INTRO_THM1 >> rpt $ goal_assum drule
    )
  >- (
    first_x_assum drule >> strip_tac >> simp[] >>
    irule_at Any OR_INTRO_THM2 >> rpt $ goal_assum drule
    )
QED


(********** freedbvars/itype_wf/itype_ok **********)

Theorem freetyvars_ok_freedbvars:
  ∀t db. freetyvars_ok db t ⇔ ∀n. n ∈ freedbvars (itype_of t) ⇒ n < db
Proof
  recInduct type_ind >> rw[freetyvars_ok_def, itype_of_def, freedbvars_def] >>
  rw[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> eq_tac >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem type_wf_itype_wf:
  ∀t tdefs. type_wf tdefs t ⇔ itype_wf tdefs (itype_of t)
Proof
  recInduct type_ind >> rw[type_wf_def, itype_wf_def, itype_of_def] >>
  rw[EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem freedbvars_iFunctions:
  ∀ts t. freedbvars (iFunctions ts t) =
    freedbvars t ∪ BIGUNION (set (MAP freedbvars ts))
Proof
  Induct >> rw[iFunctions_def, freedbvars_def] >> rw[AC UNION_ASSOC UNION_COMM]
QED

Theorem freedbvars_pure_apply_subst_SUBSET:
  ∀it sub. freedbvars (pure_apply_subst sub it) ⊆
    freedbvars it ∪ BIGUNION (IMAGE freedbvars (FRANGE sub))
Proof
  recInduct itype_ind >> reverse $ rw[freedbvars_def, pure_apply_subst] >>
  gvs[LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF] >>
  gvs[BIGUNION_SUBSET, PULL_EXISTS, SUBSET_DEF] >> rw[]
  >- (
    every_case_tac >> gvs[freedbvars_def] >>
    gvs[IN_FRANGE_FLOOKUP] >> rpt $ goal_assum drule
    ) >>
  metis_tac[]
QED

Theorem freedbvars_pure_apply_subst_SUPERSET:
  ∀it sub.
    freedbvars it ∪
      BIGUNION (IMAGE (freedbvars o pure_apply_subst sub o CVar) (pure_vars it)) ⊆
    freedbvars (pure_apply_subst sub it)
Proof
  recInduct itype_ind >> reverse $ rw[freedbvars_def, pure_apply_subst, pure_vars] >>
  gvs[LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF] >>
  gvs[BIGUNION_SUBSET, PULL_EXISTS, SUBSET_DEF] >> rw[] >>
  metis_tac[]
QED

Theorem freedbvars_pure_vwalk_SUBSET:
  ∀sub n. pure_wfs sub ⇒
    freedbvars (pure_vwalk sub n) ⊆
      BIGUNION (IMAGE freedbvars (FRANGE sub))
Proof
  gen_tac >> simp[GSYM PULL_FORALL] >> strip_tac >>
  qspec_then `sub` mp_tac pure_vwalk_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[] >>
  simp[Once pure_vwalk] >> every_case_tac >> gvs[freedbvars_def] >>
  gvs[BIGUNION_SUBSET, IN_FRANGE_FLOOKUP, PULL_EXISTS] >> rw[]
  >- (goal_assum $ drule_at Any >> simp[freedbvars_def]) >>
  simp[SUBSET_DEF, IN_FRANGE_FLOOKUP, PULL_EXISTS] >> rw[] >>
  goal_assum $ drule_at $ Pos last >>
  simp[freedbvars_def] >> goal_assum drule >> simp[]
QED

Theorem freedbvars_pure_walk_SUBSET:
  ∀sub it. pure_wfs sub ⇒
    freedbvars (pure_walk sub it) ⊆
      freedbvars it ∪ BIGUNION (IMAGE freedbvars (FRANGE sub))
Proof
  rw[pure_walk] >> CASE_TAC >> gvs[freedbvars_def] >>
  simp[freedbvars_pure_vwalk_SUBSET]
QED

Theorem freedbvars_pure_walkstar_SUBSET:
  ∀sub it. pure_wfs sub ⇒
    freedbvars (pure_walkstar sub it) ⊆
      freedbvars it ∪ BIGUNION (IMAGE freedbvars (FRANGE sub))
Proof
  gen_tac >> simp[GSYM PULL_FORALL] >> strip_tac >>
  qspec_then `sub` mp_tac pure_walkstar_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[] >>
  DEP_ONCE_REWRITE_TAC[pure_walkstar] >> simp[] >>
  drule freedbvars_pure_walk_SUBSET >>
  disch_then $ qspec_then `it` assume_tac >>
  CASE_TAC >> gvs[freedbvars_def]
  >- (
    gvs[Once pure_walk] >> every_case_tac >> gvs[freedbvars_def, PULL_EXISTS] >>
    drule freedbvars_pure_vwalk_SUBSET >>
    disch_then $ qspec_then `n'` mp_tac >> simp[freedbvars_def, PULL_EXISTS]
    ) >>
  gvs[LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF,
      BIGUNION_SUBSET, PULL_EXISTS] >>
  rw[] >> gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem freedbvars_pure_walk_SUPERSET:
  ∀sub it. pure_wfs sub ⇒
    freedbvars it ⊆ freedbvars (pure_walk sub it)
Proof
  rw[pure_walk] >> CASE_TAC >> gvs[freedbvars_def]
QED

Theorem freedbvars_pure_walkstar_SUPERSET:
  ∀sub it. pure_wfs sub ⇒
    freedbvars it ⊆ freedbvars (pure_walkstar sub it)
Proof
  gen_tac >> simp[GSYM PULL_FORALL] >> strip_tac >>
  qspec_then `sub` mp_tac pure_walkstar_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[] >>
  DEP_ONCE_REWRITE_TAC[pure_walkstar] >> simp[] >>
  drule freedbvars_pure_walk_SUPERSET >>
  disch_then $ qspec_then `it` assume_tac >>
  CASE_TAC >> gvs[freedbvars_def] >>
  gvs[LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem itype_wf_pure_apply_subst:
  ∀it tdefs sub.
    (∀it. it ∈ FRANGE sub ⇒ itype_wf tdefs it) ∧
    itype_wf tdefs it ⇒
  itype_wf tdefs (pure_apply_subst sub it)
Proof
  recInduct itype_ind >> rw[pure_apply_subst, itype_wf_def] >>
  gvs[EVERY_MAP, EVERY_MEM] >>
  CASE_TAC >> gvs[itype_wf_def, IN_FRANGE_FLOOKUP, PULL_EXISTS] >> res_tac
QED

Theorem itype_wf_pure_vwalk:
  ∀sub n tdefs. pure_wfs sub ⇒
    (∀it. it ∈ FRANGE sub ⇒ itype_wf tdefs it)
  ⇒ itype_wf tdefs (pure_vwalk sub n)
Proof
  gen_tac >> simp[GSYM PULL_FORALL] >> strip_tac >>
  qspec_then `sub` mp_tac pure_vwalk_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[] >>
  DEP_ONCE_REWRITE_TAC[pure_vwalk] >> simp[] >>
  every_case_tac >> gvs[itype_wf_def, IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
  res_tac >> gvs[itype_wf_def]
QED

Theorem itype_wf_pure_walk:
  ∀sub it tdefs. pure_wfs sub ⇒
    (∀it. it ∈ FRANGE sub ⇒ itype_wf tdefs it) ∧
    itype_wf tdefs it
  ⇒ itype_wf tdefs (pure_walk sub it)
Proof
  rw[pure_walk] >> every_case_tac >> gvs[itype_wf_pure_vwalk]
QED

Theorem itype_wf_pure_walkstar:
  ∀sub it tdefs. pure_wfs sub ⇒
    (∀it. it ∈ FRANGE sub ⇒ itype_wf tdefs it) ∧
    itype_wf tdefs it
  ⇒ itype_wf tdefs (pure_walkstar sub it)
Proof
  gen_tac >> simp[GSYM PULL_FORALL] >> strip_tac >>
  qspec_then `sub` mp_tac pure_walkstar_ind >> impl_tac >- simp[] >>
  disch_then ho_match_mp_tac >> rw[] >>
  DEP_ONCE_REWRITE_TAC[pure_walkstar] >> simp[] >>
  drule_all itype_wf_pure_walk >> strip_tac >>
  CASE_TAC >> gvs[itype_wf_def, EVERY_MAP, EVERY_MEM]
QED

Theorem pure_apply_subst_itype_wf:
  ∀it sub tdefs.
    itype_wf tdefs (pure_apply_subst sub it)
  ⇒ ∀k v. k ∈ pure_vars it ∧ FLOOKUP sub k = SOME v ⇒ itype_wf tdefs v
Proof
  recInduct itype_ind >> rw[itype_wf_def, pure_apply_subst, pure_vars] >>
  gvs[MEM_MAP, EVERY_MAP, EVERY_MEM]
  >- (first_x_assum drule >> rw[] >> last_x_assum $ drule_all >> rw[])
  >- (first_x_assum drule >> rw[] >> last_x_assum $ drule_all >> rw[])
  >- (first_x_assum drule_all >> rw[])
  >- (first_x_assum drule_all >> rw[])
QED

Theorem pure_apply_subst_itype_of[simp]:
  ∀t s. pure_apply_subst s (itype_of t) = itype_of t
Proof
  recInduct type_ind >> rw[itype_of_def, pure_apply_subst] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem itype_ok:
  (∀tds v n. itype_ok tds n (CVar v) ⇔ T) ∧
  (∀tds v n. itype_ok tds n (DBVar v) ⇔ v < n) ∧
  (∀tds p n. itype_ok tds n (PrimTy p) ⇔ T) ∧
  (∀tds n. itype_ok tds n Exception ⇔ T) ∧
  (∀tds ts n c.
    itype_ok tds n (TypeCons c ts) ⇔
    EVERY (λa. itype_ok tds n a) ts ∧
    ∃ctors. LLOOKUP tds c = SOME (LENGTH ts,ctors)) ∧
  (∀tds ts n. itype_ok tds n (Tuple ts) ⇔ EVERY (λa. itype_ok tds n a) ts) ∧
  (∀tds tf t n.
    itype_ok tds n (Function tf t) ⇔ itype_ok tds n tf ∧ itype_ok tds n t) ∧
  (∀tds t n. itype_ok tds n (Array t) ⇔ itype_ok tds n t) ∧
  (∀tds t n. itype_ok tds n (M t) ⇔ itype_ok tds n t)
Proof
  rw[itype_ok_def, itype_wf_def, freedbvars_def] >>
  gvs[EVERY_CONJ] >> eq_tac >> gvs[] >>
  gvs[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, EVERY_MEM] >> rw[]
QED

Theorem itype_ok_iFunctions:
  ∀ts t tds db. itype_ok tds db (iFunctions ts t) ⇔
    EVERY (itype_ok tds db) ts ∧ itype_ok tds db t
Proof
  Induct >> rw[iFunctions_def] >>
  simp[itype_ok] >> eq_tac >> rw[]
QED

Theorem itype_ok_type_ok:
  ∀t tdefs db. itype_ok tdefs db (itype_of t) ⇔ type_ok tdefs db t
Proof
  rw[itype_ok_def, type_ok_def] >>
  simp[freetyvars_ok_freedbvars_alt, GSYM type_wf_itype_wf]
QED

Theorem itype_ok_pure_apply_subst:
  ∀it sub tdefs db.
    itype_ok tdefs db it ∧
    (∀it. it ∈ FRANGE sub ⇒ itype_ok tdefs db it)
  ⇒ itype_ok tdefs db (pure_apply_subst sub it)
Proof
  Induct using itype_ind >> rw[pure_apply_subst, itype_ok] >>
  gvs[EVERY_MAP, EVERY_MEM] >>
  CASE_TAC >> simp[itype_ok] >>
  gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >> res_tac
QED

Theorem itype_ok_pure_walkstar:
  ∀sub. pure_wfs sub ⇒
  ∀it tdefs db.
    (∀it. it ∈ FRANGE sub ⇒ itype_ok tdefs db it) ∧
    itype_ok tdefs db it
  ⇒ itype_ok tdefs db (pure_walkstar sub it)
Proof
  gen_tac >> strip_tac >>
  qspec_then `sub` mp_tac pure_walkstar_alt_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[] >>
  gvs[pure_walkstar_alt, itype_ok, EVERY_MAP, EVERY_MEM] >>
  CASE_TAC >> gvs[itype_ok] >>
  first_x_assum irule >> simp[] >>
  gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >> res_tac
QED

Theorem itype_ok_ishift:
  ∀shift tdefs n t.
    itype_ok tdefs n t ⇒ itype_ok tdefs (n + shift) (ishift shift t)
Proof
  rw[] >> Induct_on `t` using itype_ind >> rw[itype_ok, ishift_def] >>
  gvs[EVERY_MAP, EVERY_MEM]
QED


(********** isubst/ishift **********)

Theorem ishift_0[simp]:
  ∀it. ishift 0 it = it
Proof
  recInduct itype_ind >> rw[ishift_def] >> simp[MAP_ID_ON]
QED

Theorem isubst_NIL[simp]:
  ∀it. isubst [] it = it
Proof
  recInduct itype_ind >> rw[isubst_def] >> simp[MAP_ID_ON]
QED

Theorem isubst_ishift_1:
  ∀it shift its m.
    LENGTH its ≤ shift ⇒
    isubst its (ishift shift it) = ishift (shift - LENGTH its) it
Proof
  recInduct itype_ind >> rw[isubst_def, ishift_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem isubst_ishift_2:
  ∀it shift its m.
    shift ≤ LENGTH its ⇒
    isubst its (ishift shift it) = isubst (DROP shift its) it
Proof
  recInduct itype_ind >> rw[isubst_def, ishift_def] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, EL_DROP]
QED

Theorem isubst_itype_of:
  ∀ts t. isubst (MAP itype_of ts) (itype_of t) = itype_of (subst_db 0 ts t)
Proof
  qsuff_tac
    `∀n:num ts t. isubst (MAP itype_of ts) (itype_of t) = itype_of (subst_db 0 ts t)`
  >- rw[] >>
  ho_match_mp_tac subst_db_ind >>
  rw[subst_db_def, isubst_def, itype_of_def] >>
  rw[EL_MAP, MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem ishift_itype_of:
  ∀n t. ishift n (itype_of t) = itype_of (shift_db 0 n t)
Proof
  gen_tac >> recInduct type_ind >> rw[ishift_def, shift_db_def, itype_of_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem isubst_unchanged:
  ∀its it. freedbvars it = ∅ ⇒ isubst its it = it
Proof
  recInduct isubst_ind >> rw[isubst_def, freedbvars_def] >> gvs[] >>
  rw[miscTheory.MAP_EQ_ID] >> first_x_assum irule >> simp[] >>
  gvs[LIST_TO_SET_EQ_SING, EVERY_MAP, EVERY_MEM]
QED

Theorem ishift_unchanged:
  ∀shift it. freedbvars it = ∅ ⇒ ishift shift it = it
Proof
  recInduct ishift_ind >> rw[ishift_def, freedbvars_def] >> gvs[] >>
  rw[miscTheory.MAP_EQ_ID] >> first_x_assum irule >> simp[] >>
  gvs[LIST_TO_SET_EQ_SING, EVERY_MAP, EVERY_MEM]
QED


(********** pure_apply_subst **********)

Theorem pure_apply_subst_unchanged:
  ∀it sub.
    DISJOINT (pure_vars it) (FDOM sub)
  ⇒ pure_apply_subst sub it = it
Proof
  recInduct itype_ind >> reverse $ rw[pure_apply_subst, pure_vars, FLOOKUP_DEF] >>
  gvs[MEM_MAP, PULL_EXISTS] >> irule MAP_ID_ON >> rw[] >> gvs[]
QED

Theorem pure_apply_subst_same:
  ∀sub sub' it.
    (∀n. n ∈ pure_vars it ⇒ FLOOKUP sub n = FLOOKUP sub' n)
  ⇒ pure_apply_subst sub it = pure_apply_subst sub' it
Proof
  ntac 2 gen_tac >> recInduct itype_ind >> rw[pure_vars, pure_apply_subst] >>
  gvs[MAP_EQ_f, PULL_EXISTS, MEM_MAP] >> rw[] >> metis_tac[]
QED

Theorem pure_apply_subst_min:
  ∀sub it.
    pure_apply_subst sub it = pure_apply_subst (DRESTRICT sub (pure_vars it)) it
Proof
  rw[] >> irule pure_apply_subst_same >> simp[FLOOKUP_DRESTRICT]
QED

Theorem pure_apply_subst_iFunctions:
  ∀s ts t. pure_apply_subst s (iFunctions ts t) =
            iFunctions (MAP (pure_apply_subst s) ts) (pure_apply_subst s t)
Proof
  gen_tac >> Induct >> rw[iFunctions_def, pure_apply_subst]
QED

Theorem pure_apply_subst_FUNION:
  ∀it m1 m2.
    (∀v. v ∈ FRANGE m2 ⇒ pure_vars v = {})
  ⇒ pure_apply_subst m1 (pure_apply_subst m2 it) =
    pure_apply_subst (m2 ⊌ m1) it
Proof
  recInduct itype_ind >> rw[pure_apply_subst] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
  simp[FLOOKUP_FUNION] >> CASE_TAC >> simp[pure_apply_subst] >>
  irule pure_apply_subst_unchanged >>
  gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >> first_x_assum drule >> simp[]
QED

Theorem pure_apply_subst_FUNION_strong:
  ∀it m1 m2.
    pure_apply_subst m1 (pure_apply_subst m2 it) =
    pure_apply_subst (pure_apply_subst m1 o_f m2 ⊌ m1) it
Proof
  recInduct itype_ind >> rw[pure_apply_subst] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
  simp[FLOOKUP_FUNION, FLOOKUP_o_f] >> CASE_TAC >> simp[pure_apply_subst]
QED

Theorem pure_apply_subst_isubst:
  ∀sub it its.
    (∀it. it ∈ FRANGE sub ⇒ freedbvars it = {}) ⇒
    pure_apply_subst sub (isubst its it) =
      isubst (MAP (pure_apply_subst sub) its) (pure_apply_subst sub it)
Proof
  gen_tac >> recInduct itype_ind >> rw[pure_apply_subst, isubst_def] >>
  simp[EL_MAP, MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
  CASE_TAC >> simp[isubst_def] >>
  irule $ GSYM isubst_unchanged >> first_x_assum $ irule o GSYM >>
  simp[IN_FRANGE_FLOOKUP] >> goal_assum drule >> simp[]
QED

Theorem pure_apply_subst_isubst_itype_of:
  ∀t sub its.
    pure_apply_subst sub (isubst its (itype_of t)) =
    isubst (MAP (pure_apply_subst sub) its) (itype_of t)
Proof
  recInduct type_ind >>
  rw[itype_of_def, isubst_def, pure_apply_subst, EL_MAP] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem isubst_pure_apply_subst:
  ∀sub its it.  (∀it. MEM it its ⇒ pure_vars it = {}) ⇒
    isubst its (pure_apply_subst sub it) =
    pure_apply_subst ((isubst its) o_f sub) (isubst its it)
Proof
  ntac 2 gen_tac >> recInduct itype_ind >>
  reverse $ rw[pure_apply_subst, isubst_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, FLOOKUP_o_f]
  >- (CASE_TAC >> simp[isubst_def]) >>
  gvs[pure_vars_empty_eq_type_of, MEM_EL, PULL_EXISTS] >>
  first_x_assum drule >> strip_tac >>
  drule type_of_SOME >> disch_then $ assume_tac o GSYM >> gvs[]
QED


(********** pure_walkstar etc. **********)

Theorem pure_walkstar_iFunctions:
  ∀s ts t. pure_wfs s ⇒
    pure_walkstar s (iFunctions ts t) =
    iFunctions (MAP (pure_walkstar s) ts) (pure_walkstar s t)
Proof
  simp[GSYM PULL_FORALL] >> gen_tac >> strip_tac >>
  Induct >> rw[iFunctions_def, pure_walkstar_alt]
QED

Theorem pure_walkstar_itype_of[simp]:
  ∀t sub. pure_wfs sub ⇒
    pure_walkstar sub (itype_of t) = itype_of t
Proof
  recInduct type_ind >> rw[itype_of_def, pure_walkstar_alt] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem pure_vwalk_isubst:
  ∀sub n its. pure_wfs sub ⇒
    (∀it. it ∈ FRANGE sub ⇒ freedbvars it = {})
  ⇒ isubst its (pure_vwalk sub n) = pure_vwalk sub n
Proof
  gen_tac >> simp[GSYM PULL_FORALL] >> ntac 2 strip_tac >>
  qspec_then `sub` mp_tac pure_vwalk_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[] >>
  DEP_ONCE_REWRITE_TAC[pure_vwalk] >> simp[] >>
  CASE_TAC >> gvs[isubst_def] >>
  CASE_TAC >> gvs[isubst_def] >>
  gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
  first_x_assum drule >> gvs[freedbvars_def] >> rw[] >> gvs[] >>
  rw[miscTheory.MAP_EQ_ID] >> gvs[LIST_TO_SET_EQ_SING, EVERY_MAP, EVERY_MEM] >>
  metis_tac[isubst_unchanged]
QED

Theorem pure_walk_isubst:
  ∀its it sub.
    pure_wfs sub ∧
    (∀it. it ∈ FRANGE sub ⇒ freedbvars it = {})
  ⇒ pure_walk sub (isubst its it) =
      case it of
      | DBVar n => isubst (MAP (pure_walk sub) its) (DBVar n)
      | _ => isubst its (pure_walk sub it)
Proof
  rw[] >> CASE_TAC >> gvs[isubst_def]
  >- (IF_CASES_TAC >> gvs[EL_MAP] >> simp[pure_walk]) >>
  simp[pure_walk, MAP_MAP_o, combinTheory.o_DEF, isubst_def, pure_vwalk_isubst]
QED

Theorem pure_walkstar_isubst:
  ∀sub it its. pure_wfs sub ∧
    (∀it. it ∈ FRANGE sub ⇒ freedbvars it = {}) ⇒
    pure_walkstar sub (isubst its it) =
      isubst (MAP (pure_walkstar sub) its) (pure_walkstar sub it)
Proof
  gen_tac >> simp[GSYM PULL_FORALL] >> strip_tac >>
  qspec_then `sub` mp_tac pure_walkstar_ind >> impl_tac >- simp[] >>
  disch_then ho_match_mp_tac >> rw[] >>
  Cases_on `it` >> gvs[pure_walk, isubst_def, pure_walkstar_alt] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
  >- (simp[EL_MAP] >> IF_CASES_TAC >> gvs[pure_walkstar_alt]) >>
  CASE_TAC >> gvs[isubst_def] >>
  DEP_REWRITE_TAC[isubst_unchanged] >> once_rewrite_tac[GSYM SUBSET_EMPTY] >>
  irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >> simp[] >>
  gvs[IMAGE_EQ_SING, IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
  first_x_assum drule >> simp[]
QED



(******************* Inference results ********************)

Theorem freecvars_pure_vars:
  (∀t. domain (freecvars t) = pure_vars t)
Proof
  ho_match_mp_tac itype_ind >> rw[freecvars_def, pure_vars] >> gvs[SF ETA_ss] >>
  simp[domain_union, pred_setTheory.UNION_ASSOC] >>
  qsuff_tac
    `∀t. domain (FOLDL union t (MAP freecvars ts)) =
        domain t ∪ BIGUNION (set (MAP pure_vars ts))` >> simp[] >>
  Induct_on `ts` >> rw[] >> gvs[domain_union, UNION_ASSOC]
QED

Theorem infer_atom_op_LENGTH:
  infer_atom_op ar aop = SOME (arg_tys, ret_ty) ⇒
  LENGTH arg_tys = ar
Proof
  Cases_on `aop` >> rw[infer_atom_op_def] >> gvs[] >>
  Cases_on `l` >> rw[] >> gvs[infer_atom_op_def]
QED

Theorem infer_atom_op:
  infer_atom_op (LENGTH arg_tys) aop = SOME (arg_tys, ret_ty) ⇔
  type_atom_op aop arg_tys ret_ty
Proof
  rw[] >> Cases_on `aop` >> rw[infer_atom_op_def] >> gvs[] >>
  gvs[Once type_atom_op_cases] >> rw[EQ_IMP_THM] >> gvs[]
  >- (Cases_on `l` >> rw[] >> gvs[infer_atom_op_def])
  >- (Cases_on `l` >> rw[] >> gvs[infer_atom_op_def, Once type_lit_cases])
  >- (Cases_on `l` >> rw[] >> gvs[infer_atom_op_def, Once type_lit_cases])
  >- (pop_assum $ SUBST_ALL_TAC o GSYM >> simp[])
  >- (rw[LIST_EQ_REWRITE, rich_listTheory.EL_REPLICATE] >> gvs[EVERY_EL])
  >- (pop_assum $ SUBST_ALL_TAC o GSYM >> simp[])
  >- (rw[LIST_EQ_REWRITE, rich_listTheory.EL_REPLICATE] >> gvs[EVERY_EL])
QED

Theorem infer_cons_mono:
  ∀n tdefs cname m ar schemes.
    infer_cons n tdefs cname = SOME (m, ar, schemes)
  ⇒ n ≤ m
Proof
  recInduct infer_cons_ind >> rw[infer_cons_def] >>
  every_case_tac >> gvs[]
QED

Theorem infer_cons:
  namespace_ok (exndefs, typedefs) ⇒
  type_cons typedefs (cname, carg_tys) (tyid, tyargs) =
  ∃schemes.
    infer_cons n typedefs cname = SOME (n + tyid, LENGTH tyargs,schemes) ∧
    MAP (tsubst tyargs) schemes = carg_tys
Proof
  rw[] >>
  `ALL_DISTINCT (MAP FST (FLAT (MAP SND typedefs)))` by
    gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
  last_x_assum kall_tac >> pop_assum mp_tac >>
  map_every qid_spec_tac [`tyid`,`n`,`typedefs`] >> Induct >> rw[] >>
  gvs[infer_cons_def, type_cons_def, oEL_THM] >>
  PairCases_on `h` >> gvs[infer_cons_def] >>
  Cases_on `tyid` >> gvs[]
  >- (
    eq_tac >> rw[] >> gvs[] >> every_case_tac >> gvs[] >>
    drule infer_cons_mono >> gvs[]
    ) >>
  rename1 `m < _` >> CASE_TAC >> gvs[]
  >- (
    last_x_assum $ qspecl_then [`SUC n`,`m`] mp_tac >> gvs[ADD_CLAUSES] >>
    disch_then $ DEP_REWRITE_TAC o single >> gvs[ALL_DISTINCT_APPEND]
    )
  >- (
    rw[] >> CCONTR_TAC >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
    imp_res_tac ALOOKUP_MEM >>
    gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD, MEM_FLAT, MEM_EL] >>
    first_x_assum drule >> disch_then drule >>
    rpt $ disch_then (drule o GSYM) >> simp[]
    )
QED

Theorem infer_cons_SOME:
  ∀n typedefs cname m arity schemes exndefs.
    infer_cons n typedefs cname = SOME (m, arity, schemes) ∧
    namespace_ok (exndefs, typedefs)
  ⇒ ∃constructors.
      oEL (m - n) typedefs = SOME (arity, constructors) ∧
      ALOOKUP constructors cname = SOME schemes
Proof
  rw[] >>
  `ALL_DISTINCT (MAP FST (FLAT (MAP SND typedefs)))` by
    gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
  imp_res_tac infer_cons_mono >> imp_res_tac LESS_EQUAL_ADD >> gvs[] >>
  qpat_x_assum `namespace_ok _` kall_tac >> ntac 2 $ pop_assum mp_tac >>
  map_every qid_spec_tac [`p`,`cname`,`typedefs`,`n`] >>
  recInduct infer_cons_ind >> rw[infer_cons_def] >>
  reverse $ every_case_tac >> gvs[oEL_THM]
  >- (`p = 0` by DECIDE_TAC >> pop_assum SUBST_ALL_TAC >> gvs[]) >>
  Cases_on `p` >> gvs[] >- (imp_res_tac infer_cons_mono >> gvs[]) >>
  pop_assum irule >> simp[] >> gvs[ALL_DISTINCT_APPEND]
QED

Theorem get_typedef_mono:
  ∀n tdefs cnames m ar cs.
    get_typedef n tdefs cnames = SOME (m, ar, cs)
  ⇒ n ≤ m
Proof
  recInduct get_typedef_ind >> rw[get_typedef_def] >>
  every_case_tac >> gvs[]
QED

Theorem get_typedef:
  namespace_ok (exndefs, tdefs) ⇒
  (get_typedef n tdefs cnames_arities = SOME (n + m, ar, cs)) =
  (oEL m tdefs = SOME (ar, cs) ∧
   PERM (MAP (λ(cn,ts). (cn, LENGTH ts)) cs) cnames_arities)
Proof
  rw[] >>
  `ALL_DISTINCT (MAP FST (FLAT (MAP SND tdefs)))` by
    gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
  `EVERY (λ(ar,td). td ≠ []) tdefs` by gvs[namespace_ok_def] >>
  last_x_assum kall_tac >> ntac 2 $ pop_assum mp_tac >>
  map_every qid_spec_tac [`m`,`n`,`tdefs`] >> Induct >> rw[] >>
  gvs[get_typedef_def, oEL_THM] >>
  PairCases_on `h` >> gvs[get_typedef_def] >>
  IF_CASES_TAC >> gvs[]
  >- (
    eq_tac >> strip_tac >> gvs[]
    >- (
      Cases_on `m` >> gvs[] >>
      irule PERM_ALL_DISTINCT_LENGTH >> gvs[ALL_DISTINCT_APPEND, EVERY_MEM] >>
      gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
      irule ALL_DISTINCT_MAP_INJ >> imp_res_tac ALL_DISTINCT_MAP >> gvs[] >>
      simp[FORALL_PROD] >> rw[] >>
      qpat_x_assum `ALL_DISTINCT (_ cs)` mp_tac >>
      simp[EL_ALL_DISTINCT_EL_EQ, MEM_EL, EL_MAP] >> gvs[MEM_EL] >>
      ntac 2 $ qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
      disch_then $ qspecl_then [`n`,`n'`] assume_tac >> gvs[]
      ) >>
    Cases_on `m` >> gvs[ALL_DISTINCT_APPEND] >> rename1 `EL m` >>
    gvs[EVERY_MEM] >> Cases_on `h1` >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    PairCases_on `h` >> gvs[] >>
    qpat_x_assum `¬ MEM _ (MAP _ (FLAT _))` mp_tac >> simp[] >>
    simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, EXISTS_PROD, Once MEM_EL] >>
    goal_assum drule >> gvs[] >>
    imp_res_tac sortingTheory.PERM_MEM_EQ >>
    gvs[MEM_MAP, EXISTS_PROD] >> goal_assum drule
    ) >>
  Cases_on `m` >> gvs[]
  >- (
    qspecl_then [`SUC n`,`tdefs`,`cnames_arities`,`n`] assume_tac get_typedef_mono >>
    gvs[] >> rw[] >>
    CCONTR_TAC >> gvs[] >> qpat_x_assum `_ ⇒ _` mp_tac >> simp[] >>
    imp_res_tac sortingTheory.PERM_LENGTH >> gvs[combinTheory.o_DEF] >>
    imp_res_tac $ iffLR sortingTheory.PERM_MEM_EQ >> gvs[EVERY_MEM] >>
    gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD]
    ) >>
  gvs[ALL_DISTINCT_APPEND] >> rename1 `n + SUC m` >>
  last_x_assum $ qspecl_then [`SUC n`,`m`] assume_tac >> gvs[ADD_CLAUSES]
QED

Theorem get_typedef_SOME:
  ∀n tdefs cnames_arities m arity cs exndefs.
    get_typedef n tdefs cnames_arities = SOME (m, arity, cs) ∧
    namespace_ok (exndefs, tdefs)
  ⇒ oEL (m - n) tdefs = SOME (arity, cs) ∧
    PERM (MAP (λ(cn,ts). (cn, LENGTH ts)) cs) cnames_arities
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac get_typedef_mono >> imp_res_tac LESS_EQUAL_ADD >> gvs[] >>
  drule_all $ iffLR get_typedef >> simp[]
QED

Theorem generalise_avoid_all:
  (∀t cv db avoid s.
    pure_vars t ⊆ domain avoid ⇒ generalise db avoid s t = (0, s, t))
Proof
  ho_match_mp_tac itype_ind >> rw[pure_vars, generalise_def] >>
  gvs[pred_setTheory.BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, EVERY_MEM, domain_lookup] >>
  Induct_on `ts` >> rw[generalise_def] >> gvs[] >>
  qmatch_goalsub_abbrev_tac `_ (_ a) = _` >> PairCases_on `a` >> gvs[]
QED

Theorem get_solveable_SOME_LENGTH:
  ∀cs rev_cs c cs'.
    get_solveable cs rev_cs = SOME (c, cs')
  ⇒ 0 < LENGTH (cs ++ rev_cs) ∧ LENGTH cs' = LENGTH (cs ++ rev_cs) - 1
Proof
  rpt gen_tac >> strip_tac >>
  drule get_solveable_SOME >> strip_tac >> gvs[]
QED

Theorem map_ok_singleton[simp]:
  ∀k v. map_ok (singleton k v)
Proof
  rw[singleton_def] >> irule $ cj 1 insert_thm >> simp[]
QED

Theorem cmp_of_singleton[simp]:
  ∀k v. cmp_of (singleton k v) = var_cmp
Proof
  rw[singleton_def]
QED

Theorem lookup_singleton:
  ∀k v k'. lookup (singleton k v) k' = if k = k' then SOME v else NONE
Proof
  rpt gen_tac >> simp[singleton_def] >>
  DEP_REWRITE_TAC[lookup_insert] >> simp[]
QED

Triviality pure_vars_pure_apply_subst_DBVar_o_f[simp]:
  ∀t s.
    pure_vars (pure_apply_subst (DBVar o_f s) t) =
    pure_vars t DIFF FDOM s
Proof
  recInduct freecvars_ind >> rw[pure_apply_subst, pure_vars] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, BIGUNION_DIFF_LIST_TO_SET]
  >- (ntac 2 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- (ntac 2 AP_TERM_TAC >> rw[MAP_EQ_f])
  >- simp[UNION_DIFF_DISTRIBUTE]
  >- simp[FLOOKUP_DEF, pure_vars]
  >- simp[FLOOKUP_DEF, pure_vars]
QED

Theorem generalise:
  (∀t db avoid s new sub ty.
    generalise db avoid s t = (new,sub,ty) ⇒
      s SUBMAP sub ∧
      CARD (FDOM sub DIFF FDOM s) = new ∧
      FDOM s ∪ (pure_vars t DIFF domain avoid) = FDOM sub ∧
      ((∀v. v ∈ FRANGE s ⇒ v < db) ⇒
        FRANGE sub DIFF FRANGE s = {v | db ≤ v ∧ v < db + new}) ∧
      pure_vars ty ⊆ domain avoid ∧
      (∀sup. sub SUBMAP sup ⇒
        pure_apply_subst (DBVar o_f (FDIFF sup (domain avoid))) t = ty)
    ) ∧
  (∀ts db avoid s new sub tys.
    generalise_list db avoid s ts = (new,sub,tys) ⇒
      s SUBMAP sub ∧
      CARD (FDOM sub DIFF FDOM s) = new ∧
      FDOM s ∪ (BIGUNION (set (MAP pure_vars ts)) DIFF domain avoid) = FDOM sub ∧
      ((∀v. v ∈ FRANGE s ⇒ v < db) ⇒
        FRANGE sub DIFF FRANGE s = {v | db ≤ v ∧ v < db + new}) ∧
      BIGUNION (set (MAP pure_vars tys)) ⊆ domain avoid ∧
      (∀sup. sub SUBMAP sup ⇒
        MAP (pure_apply_subst (DBVar o_f (FDIFF sup (domain avoid)))) ts = tys)
      )
Proof
  Induct >> rpt gen_tac >> strip_tac >>
  gvs[generalise_def, pure_vars, pure_apply_subst]
  >- (pairarg_tac >> gvs[pure_vars] >> first_x_assum drule >> strip_tac >> gvs[])
  >- (pairarg_tac >> gvs[pure_vars] >> first_x_assum drule >> strip_tac >> gvs[])
  >- (
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[pure_vars] >>
    ntac 2 (first_x_assum drule >> strip_tac >> gvs[]) >>
    irule_at Any SUBMAP_TRANS >> goal_assum drule >> simp[] >>
    rename1 `s1 SUBMAP s2` >> rename1 `s2 SUBMAP s3` >>
    imp_res_tac SUBMAP_FDOM_SUBSET >> gvs[] >>
    drule_all SUBSET_TRANS >> strip_tac >>
    imp_res_tac SUBSET_INTER2 >> simp[] >>
    imp_res_tac (CARD_SUBSET |> SIMP_RULE std_ss [PULL_FORALL, AND_IMP_INTRO]) >>
    gvs[] >> conj_tac >> rpt $ reverse conj_tac
    >- (gvs[EXTENSION] >> metis_tac[])
    >- (
      rw[] >> first_x_assum irule >> irule SUBMAP_TRANS >>
      goal_assum drule >> simp[]
      ) >>
    rw[] >> gvs[] >> qpat_x_assum `(∀v. _) ⇒ _` mp_tac >> impl_tac
    >- (
      rw[] >> gvs[EXTENSION] >> Cases_on `v ∈ FRANGE s1` >> gvs[] >>
      res_tac >> simp[]
      ) >>
    rw[] >> gvs[EXTENSION, EQ_IMP_THM, FORALL_AND_THM, IMP_CONJ_THM] >>
    rw[] >> gvs[] >> Cases_on `x ∈ FRANGE s2` >> gvs[]
    >- (res_tac >> simp[])
    >- (res_tac >> simp[])
    >- (fs[FRANGE_DEF, SUBMAP_DEF] >> metis_tac[])
    >- (rpt $ first_x_assum $ drule_at Any >> simp[])
    >- (rpt $ first_x_assum $ drule_at Any >> simp[])
    >- (
      CCONTR_TAC >> qpat_x_assum `_ ∉ _` mp_tac >> gvs[] >>
      fs[FRANGE_DEF, SUBMAP_DEF] >> metis_tac[]
      )
    )
  >- (pairarg_tac >> gvs[pure_vars] >> first_x_assum drule >> strip_tac >> gvs[])
  >- (pairarg_tac >> gvs[pure_vars] >> first_x_assum drule >> strip_tac >> gvs[])
  >- (
    gvs[FLOOKUP_o_f, FLOOKUP_FDIFF, domain_lookup] >>
    Cases_on `lookup n avoid` >> gvs[pure_vars, domain_lookup] >>
    last_x_assum mp_tac >> reverse CASE_TAC >> gvs[] >> strip_tac >> gvs[]
    >- (
      conj_tac >- (gvs[FLOOKUP_DEF, pure_vars, EXTENSION] >> metis_tac[]) >>
      rw[] >> gvs[pure_vars, domain_lookup, SUBMAP_FLOOKUP_EQN] >>
      first_x_assum drule >> simp[]
      ) >>
    gvs[FLOOKUP_DEF, INSERT_INTER, SUBMAP_DEF, FAPPLY_FUPDATE_THM,
        pure_vars, domain_lookup] >>
    conj_tac >- (gvs[FLOOKUP_DEF, pure_vars, EXTENSION] >> metis_tac[]) >>
    reverse conj_tac >- metis_tac[] >>
    rw[] >- (first_x_assum drule >> simp[]) >>
    rw[EXTENSION] >> eq_tac >> rw[] >> simp[] >>
    metis_tac[FRANGE_DOMSUB_SUBSET, SUBSET_DEF]
    )
  >- (
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    ntac 2 (first_x_assum drule >> strip_tac >> gvs[]) >>
    irule_at Any SUBMAP_TRANS >> goal_assum drule >> simp[] >>
    rename1 `s1 SUBMAP s2` >> rename1 `s2 SUBMAP s3` >>
    imp_res_tac SUBMAP_FDOM_SUBSET >> gvs[] >>
    drule_all SUBSET_TRANS >> strip_tac >>
    imp_res_tac SUBSET_INTER2 >> simp[] >>
    imp_res_tac (CARD_SUBSET |> SIMP_RULE std_ss [PULL_FORALL, AND_IMP_INTRO]) >>
    gvs[] >> conj_tac >> rpt $ reverse conj_tac
    >- (gvs[EXTENSION] >> metis_tac[])
    >- (
      rw[] >> first_x_assum irule >> irule SUBMAP_TRANS >>
      goal_assum drule >> simp[]
      ) >>
    rw[] >> gvs[] >> qpat_x_assum `(∀v. _) ⇒ _` mp_tac >> impl_tac
    >- (
      rw[] >> gvs[EXTENSION] >> Cases_on `v ∈ FRANGE s1` >> gvs[] >>
      res_tac >> simp[]
      ) >>
    rw[] >> gvs[EXTENSION, EQ_IMP_THM, FORALL_AND_THM, IMP_CONJ_THM] >>
    rw[] >> gvs[] >> Cases_on `x ∈ FRANGE s2` >> gvs[]
    >- (res_tac >> simp[])
    >- (res_tac >> simp[])
    >- (fs[FRANGE_DEF, SUBMAP_DEF] >> metis_tac[])
    >- (rpt $ first_x_assum $ drule_at Any >> simp[])
    >- (rpt $ first_x_assum $ drule_at Any >> simp[])
    >- (
      CCONTR_TAC >> qpat_x_assum `_ ∉ _` mp_tac >> gvs[] >>
      fs[FRANGE_DEF, SUBMAP_DEF] >> metis_tac[]
      )
    )
QED

Theorem generalise_0_FEMPTY:
  ∀avoid t new sub ty.
    generalise 0 avoid FEMPTY t = (new, sub, ty)
  ⇒ CARD (FDOM sub) = new ∧
    FDOM sub = pure_vars t DIFF domain avoid ∧
    FRANGE sub = count new ∧
    pure_vars ty ⊆ domain avoid ∧
    pure_apply_subst (DBVar o_f (FDIFF sub (domain avoid))) t = ty
Proof
  rpt gen_tac >> strip_tac >> drule $ cj 1 generalise >> rw[count_def]
QED

(********************)

val _ = export_theory();

