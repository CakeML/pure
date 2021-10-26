open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory stringTheory optionTheory pred_setTheory
     listTheory rich_listTheory alistTheory finite_mapTheory sptreeTheory;
open mlmapTheory;
open pure_miscTheory pure_typingTheory pure_typingPropsTheory
     pure_inference_commonTheory pure_unificationTheory pure_inferenceTheory;

val _ = new_theory "pure_inferenceProps";

(******************* General results ********************)

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

Theorem pure_vars_isubst_SUBSET:
  ∀s t. pure_vars (isubst s t) ⊆ pure_vars t ∪ BIGUNION (set (MAP pure_vars s))
Proof
  recInduct isubst_ind >> rw[isubst_def, pure_vars] >>
  gvs[LIST_TO_SET_MAP, SUBSET_DEF, PULL_EXISTS] >> rw[]
  >- (goal_assum drule >> simp[EL_MEM]) >>
  last_x_assum drule_all >> strip_tac >> simp[] >> metis_tac[]
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

Theorem pure_vars_iFunctions:
  pure_vars (iFunctions tys ty) = BIGUNION (set (MAP pure_vars tys)) ∪ pure_vars ty
Proof
  Induct_on `tys` >> rw[iFunctions_def, pure_vars] >> simp[UNION_ASSOC]
QED

Theorem pure_vars_itype_of[simp]:
  ∀t. pure_vars (itype_of t) = {}
Proof
  recInduct type_ind >> rw[itype_of_def, pure_vars] >>
  Induct_on `l` >> gvs[] >> rw[] >> gvs[]
QED

Theorem pure_apply_subst_itype_of[simp]:
  ∀t s. pure_apply_subst s (itype_of t) = itype_of t
Proof
  recInduct type_ind >> rw[itype_of_def, pure_apply_subst] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED


(******************* Inference results ********************)

Theorem infer_atom_op_LENGTH:
  infer_atom_op ar aop = SOME (arg_tys, ret_ty) ⇒
  LENGTH arg_tys = ar
Proof
  Cases_on `aop` >> rw[infer_atom_op_def] >> gvs[] >>
  Cases_on `l` >> rw[] >> gvs[infer_atom_op_def]
QED

Theorem infer_atom_op:
  aop ≠ Eq ⇒
  (infer_atom_op (LENGTH arg_tys) aop = SOME (arg_tys, ret_ty) ⇔
    type_atom_op aop arg_tys ret_ty)
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
      (∀v. v ∈ FRANGE sub ∧ v ∉ FRANGE s ⇒ db ≤ v ∧ v < db + new) ∧
      (∀sup. sub SUBMAP sup ⇒
        pure_apply_subst (DBVar o_f (FDIFF sup (domain avoid))) t = ty)
    ) ∧
  (∀ts db avoid s new sub tys.
    generalise_list db avoid s ts = (new,sub,tys) ⇒
      s SUBMAP sub ∧
      CARD (FDOM sub DIFF FDOM s) = new ∧
      (∀v. v ∈ FRANGE sub ∧ v ∉ FRANGE s ⇒ db ≤ v ∧ v < db + new) ∧
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
    gvs[] >> reverse conj_tac
    >- (
      rw[] >> first_x_assum irule >> irule SUBMAP_TRANS >>
      goal_assum drule >> simp[]
      ) >>
    gen_tac >> strip_tac >> Cases_on `v ∈ FRANGE s2` >> gvs[]
    >- (first_x_assum $ drule_at $ Pat `_ ∈ _` >> simp[])
    >- (last_x_assum $ drule_at $ Pat `_ ∈ _` >> simp[])
    )
  >- (pairarg_tac >> gvs[pure_vars] >> first_x_assum drule >> strip_tac >> gvs[])
  >- (pairarg_tac >> gvs[pure_vars] >> first_x_assum drule >> strip_tac >> gvs[])
  >- (
    gvs[FLOOKUP_o_f, FLOOKUP_FDIFF, domain_lookup] >>
    Cases_on `lookup n avoid` >> gvs[] >>
    last_x_assum mp_tac >> reverse CASE_TAC >> gvs[] >> strip_tac >> gvs[]
    >- (rw[] >> gvs[SUBMAP_FLOOKUP_EQN] >> first_x_assum drule >> simp[]) >>
    gvs[FLOOKUP_DEF, INSERT_INTER, SUBMAP_DEF, FAPPLY_FUPDATE_THM] >>
    reverse conj_tac >- metis_tac[] >>
    gen_tac >> strip_tac >> gvs[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM]
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
    gvs[] >> reverse conj_tac
    >- (
      rw[] >> first_x_assum irule >> irule SUBMAP_TRANS >>
      goal_assum drule >> simp[]
      ) >>
    gen_tac >> strip_tac >> Cases_on `v ∈ FRANGE s2` >> gvs[]
    >- (first_x_assum $ drule_at $ Pat `_ ∈ _` >> simp[])
    >- (last_x_assum $ drule_at $ Pat `_ ∈ _` >> simp[])
    )
QED

Theorem generalise_0_FEMPTY:
  ∀avoid t new sub ty.
    generalise 0 avoid FEMPTY t = (new, sub, ty)
  ⇒ CARD (FDOM sub) = new ∧
    (∀v. v ∈ FRANGE sub ⇒ v < new) ∧
    pure_apply_subst (DBVar o_f (FDIFF sub (domain avoid))) t = ty
Proof
  rpt gen_tac >> strip_tac >> drule $ cj 1 generalise >> simp[]
QED

(********************)

val _ = export_theory();

