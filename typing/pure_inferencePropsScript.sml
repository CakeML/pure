open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory stringTheory optionTheory pred_setTheory
     listTheory alistTheory finite_mapTheory sptreeTheory;
open pure_miscTheory pure_typingTheory pure_typingPropsTheory
     pure_inference_commonTheory pure_unificationTheory pure_inferenceTheory;

val _ = new_theory "pure_inferenceProps";

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

val _ = export_theory();

