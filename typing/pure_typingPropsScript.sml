open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open pure_cexpTheory pure_configTheory pure_typingTheory

val _ = new_theory "pure_typingProps";


(******************** Substitutions and shifts ********************)

Theorem shift_db_0[simp]:
  shift_db skip 0 t = t
Proof
  qsuff_tac `∀skip n t. n = 0 ⇒ shift_db skip n t = t` >- gvs[] >>
  recInduct shift_db_ind >> rw[shift_db_def] >>
  rw[LIST_EQ_REWRITE] >> gvs[MEM_EL, PULL_EXISTS, EL_MAP]
QED


(******************** Properties of types ********************)

Theorem freetyvars_ok_mono:
  ∀n t m.
    freetyvars_ok n t ∧
    n ≤ m
  ⇒ freetyvars_ok m t
Proof
  recInduct freetyvars_ok_ind >> rw[freetyvars_ok_def] >> gvs[EVERY_MEM]
QED

Theorem freetyvars_ok_subst_db:
  ∀skip ts t n.
    freetyvars_ok (n + LENGTH ts) t ∧
    EVERY (freetyvars_ok n) ts ∧
    skip ≤ n
  ⇒ freetyvars_ok n (subst_db skip ts t)
Proof
  recInduct subst_db_ind >>
  rw[subst_db_def, freetyvars_ok_def] >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  gvs[MEM_EL, PULL_EXISTS]
QED

Theorem freetyvars_ok_tsubst:
  ∀ts t n.
    freetyvars_ok (n + LENGTH ts) t ∧
    EVERY (freetyvars_ok n) ts
  ⇒ freetyvars_ok n (tsubst ts t)
Proof
  rw[] >> irule freetyvars_ok_subst_db >> simp[]
QED

Theorem freetyvars_ok_shift_db:
  ∀skip shift t n.
    freetyvars_ok n t
  ⇒ freetyvars_ok (n + shift) (shift_db skip shift t)
Proof
  recInduct shift_db_ind >>
  rw[shift_db_def, freetyvars_ok_def] >>
  gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem type_wf_subst_db:
  ∀skip ts t tdefs.
    type_wf tdefs t ∧
    EVERY (type_wf tdefs) ts
  ⇒ type_wf tdefs (subst_db skip ts t)
Proof
  recInduct subst_db_ind >> rw[subst_db_def, type_wf_def] >>
  gvs[EVERY_MAP, EVERY_MEM] >> gvs[MEM_EL, PULL_EXISTS]
QED

Theorem type_wf_shift_db:
  ∀skip shift t tdefs.
    type_wf tdefs t
  ⇒ type_wf tdefs (shift_db skip shift t)
Proof
  recInduct shift_db_ind >> rw[shift_db_def, type_wf_def] >>
  gvs[EVERY_MAP, EVERY_MEM]
QED

Theorem type_ok:
  (∀tds v n. type_ok tds n (TypeVar v) ⇔ v < n) ∧
  (∀tds p n. type_ok tds n (PrimTy p) ⇔ T) ∧
  (∀tds n. type_ok tds n Exception ⇔ T) ∧
  (∀tds ts n c.
    type_ok tds n (TypeCons c ts) ⇔
    EVERY (λa. type_ok tds n a) ts ∧
    ∃ctors. oEL c tds = SOME (LENGTH ts, ctors)) ∧
  (∀tds ts n. type_ok tds n (Tuple ts) ⇔ EVERY (λa. type_ok tds n a) ts) ∧
  (∀tds ts t n.
   type_ok tds n (Function ts t) ⇔
   EVERY (λa. type_ok tds n a) ts ∧ ts ≠ [] ∧ type_ok tds n t) ∧
  (∀tds t n. type_ok tds n (Array t) ⇔ type_ok tds n t) ∧
  (∀tds t n. type_ok tds n (M t) ⇔ type_ok tds n t)
Proof
  rw[type_ok_def, type_wf_def, freetyvars_ok_def] >>
  gvs[EVERY_CONJ] >> eq_tac >> gvs[]
QED


(******************** Typing judgements ********************)

Theorem type_cexp_freetyvars_ok:
  ∀ ns db st env e t.
    EVERY (freetyvars_ok db) st ∧
    EVERY (λ(v,scheme). freetyvars_ok_scheme db scheme) env ∧
    namespace_ok ns ∧
    type_cexp ns db st env e t
  ⇒ freetyvars_ok db t
Proof
  Induct_on `type_cexp` >> rpt conj_tac >>
  rw[type_ok_def, freetyvars_ok_def] >>
  gvs[LIST_REL_EL_EQN, IMP_CONJ_THM, FORALL_AND_THM]
  >- (
    PairCases_on `s` >> gvs[specialises_def] >>
    imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, type_ok_def] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    irule freetyvars_ok_tsubst >> simp[EVERY_MEM]
    )
  >- gvs[EVERY_EL]
  >- gvs[EVERY_EL, type_ok_def]
  >- gvs[oEL_THM, EVERY_EL]
  >- gvs[EVERY_EL, type_ok_def]
  >- (
    first_x_assum irule >>
    gvs[EVERY_MEM, MEM_ZIP, PULL_EXISTS, EL_MAP, MEM_EL, type_ok_def]
    )
  >- (
    ntac 2 $ first_x_assum irule >> gvs[EVERY_MEM, FORALL_PROD] >>
    rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
    first_x_assum drule >> rw[]
    >- (
      drule freetyvars_ok_shift_db >> rename1 `MEM (a,b,c) _` >>
      disch_then $ qspecl_then [`b`,`new`] assume_tac >> gvs[]
      )
    >- (
      drule freetyvars_ok_mono >> disch_then irule >> simp[]
      )
    )
  >- (
    first_x_assum irule >>
    rw[EVERY_EL, EL_ZIP, EL_MAP] >> pairarg_tac >> gvs[EVERY_EL] >>
    last_x_assum kall_tac >> last_x_assum drule >> simp[]
    )
  >- (
    gvs[EVERY_MEM, oEL_THM, namespace_ok_def, type_ok_def] >>
    Cases_on `css` >> gvs[] >- gvs[MEM_EL, FORALL_PROD] >>
    last_x_assum $ qspec_then `h` assume_tac >> gvs[] >>
    pairarg_tac >> gvs[] >>
    qpat_x_assum `_ ⇒ freetyvars_ok db t` irule >>
    simp[MEM_ZIP, EL_MAP, PULL_EXISTS] >>
    gvs[MEM_EL, PULL_EXISTS]
    )
QED

Theorem type_cexp_type_ok:
  ∀ ns db st env e t.
    EVERY (type_ok (SND ns) db) st ∧
    EVERY (λ(v,scheme). type_scheme_ok (SND ns) db scheme) env ∧
    namespace_ok ns ∧
    type_cexp ns db st env e t
  ⇒ type_ok (SND ns) db t
Proof
  Induct_on `type_cexp` >> rpt conj_tac >> rw[type_ok] >>
  gvs[LIST_REL_EL_EQN, IMP_CONJ_THM, FORALL_AND_THM]
  >- (
    PairCases_on `s` >> gvs[specialises_def] >>
    imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, type_ok_def] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    irule_at Any freetyvars_ok_tsubst >> simp[EVERY_MEM] >>
    irule_at Any type_wf_subst_db >> simp[EVERY_MEM]
    )
  >- gvs[EVERY_EL]
  >- gvs[EVERY_EL, type_ok_def]
  >- gvs[type_cons_def]
  >- gvs[oEL_THM, EVERY_EL]
  >- gvs[EVERY_EL, type_ok_def]
  >- (
    first_x_assum irule >>
    gvs[EVERY_MEM, MEM_ZIP, PULL_EXISTS, EL_MAP, MEM_EL, type_ok_def]
    )
  >- (
    ntac 2 $ first_x_assum irule >> gvs[EVERY_MEM, FORALL_PROD] >>
    rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
    first_x_assum drule >> rw[]
    >- (
      gvs[type_ok_def] >>
      drule freetyvars_ok_shift_db >> rename1 `MEM (a,b,c) _` >>
      disch_then $ qspecl_then [`b`,`new`] assume_tac >> gvs[] >>
      irule type_wf_shift_db >> simp[]
      )
    >- (
      gvs[type_ok_def] >>
      drule freetyvars_ok_mono >> disch_then irule >> simp[]
      )
    )
  >- (
    first_x_assum irule >>
    rw[EVERY_EL, EL_ZIP, EL_MAP] >> pairarg_tac >> gvs[EVERY_EL] >>
    last_x_assum kall_tac >> last_x_assum drule >> simp[]
    )
  >- (
    gvs[EVERY_MEM, oEL_THM, namespace_ok_def] >>
    Cases_on `css` >> gvs[] >- gvs[MEM_EL, FORALL_PROD] >>
    last_x_assum $ qspec_then `h` assume_tac >> gvs[] >>
    pairarg_tac >> gvs[] >>
    qpat_x_assum `_ ⇒ type_ok typedefs db t` irule >>
    simp[MEM_ZIP, EL_MAP, PULL_EXISTS] >>
    gvs[MEM_EL, PULL_EXISTS]
    )
QED


(********************)

val _ = export_theory();

