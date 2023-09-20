open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory rich_listTheory alistTheory pred_setTheory finite_mapTheory;
open pure_miscTheory pure_cexpTheory pure_tcexpTheory pure_configTheory
     pure_typingTheory pure_tcexp_lemmasTheory


val _ = new_theory "pure_typingProps";


(******************** Basic lemmas ********************)

Theorem type_ind:
  ∀P.
    (∀n. P (TypeVar n)) ∧ (∀p. P (PrimTy p)) ∧ P Exception ∧
    (∀l. (∀t. MEM t l ⇒ P t) ⇒ ∀n. P (TypeCons n l)) ∧
    (∀l. (∀t. MEM t l ⇒ P t) ⇒ P (Tuple l)) ∧
    (∀tf t. P tf ∧ P t ⇒ P (Function tf t)) ∧
    (∀t. P t ⇒ P (Array t)) ∧ (∀t. P t ⇒ P (M t)) ⇒
    (∀t. P t)
Proof
  ntac 3 strip_tac >>
  completeInduct_on `type_size t` >> rw[] >>
  Cases_on `t` >> gvs[type_size_def] >>
  last_x_assum irule >> rw[] >>
  first_x_assum irule >> simp[] >>
  Induct_on `l` >> rw[] >> gvs[type_size_def]
QED

Theorem type_atom_op_not_Loc:
  type_atom_op op ts t ⇒ ∀n. op ≠ Lit $ Loc n
Proof
  rw[type_atom_op_cases, type_lit_cases]
QED

Theorem type_atom_op_no_Bool:
  type_atom_op op ts t ⇒ ¬ MEM Bool ts
Proof
  rw[type_atom_op_cases] >> gvs[] >> Induct_on `ts` >> gvs[]
QED

Theorem get_PrimTys_SOME:
  ∀ts pts.
    get_PrimTys ts = SOME pts ⇔ ts = MAP PrimTy pts
Proof
  Induct >> rw[get_PrimTys_def] >>
  Cases_on `h` >> gvs[get_PrimTys_def] >>
  Cases_on `pts` >> gvs[] >> eq_tac >> rw[]
QED

Theorem Functions_APPEND:
  ∀as bs a.
    Functions (as ++ bs) a = Functions as (Functions bs a)
Proof
  Induct >> rw[Functions_def]
QED

Theorem Functions_eq_imp:
  ∀as a bs b.
    Functions as a = Functions bs b ⇒
    ∃cs.
      (as = bs ++ cs ∧ b = Functions cs a) ∨
      (bs = as ++ cs ∧ a = Functions cs b)
Proof
  Induct >> rw[Functions_def] >> csimp[Functions_def]
  >- (qexists_tac `bs` >> simp[]) >>
  Cases_on `bs` >> gvs[Functions_def]
QED

Theorem FINITE_reserved_cns[simp]:
  FINITE reserved_cns
Proof
  rw[reserved_cns_def]
QED

Theorem type_exception_Subscript:
  namespace_ok ns ⇒ type_exception (FST ns) («Subscript», [])
Proof
  PairCases_on `ns` >> rw[type_exception_def, namespace_ok_def] >>
  gvs[ALL_DISTINCT_APPEND] >> drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

Theorem cns_arities_ok_simps[simp]:
  cns_arities_ok ns {} ∧
  cns_arities_ok ns (a INSERT b) = (
    ((∃ar. a = {(«»,ar)}) ∨ (∃a'. a' ∈ ns_cns_arities ns ∧ a ⊆ a')) ∧
    cns_arities_ok ns b) ∧
  cns_arities_ok ns (x ∪ y) = (cns_arities_ok ns x ∧ cns_arities_ok ns y) ∧
  cns_arities_ok ns (BIGUNION s) = (∀x. x ∈ s ⇒ cns_arities_ok ns x)
Proof
  rw[cns_arities_ok_def] >> metis_tac[]
QED


(******************** Substitutions and shifts ********************)

Theorem shift_db_0[simp]:
  ∀skip. shift_db skip 0 = I
Proof
  qsuff_tac `∀skip n t. n = 0 ⇒ shift_db skip n t = t` >- rw[FUN_EQ_THM] >>
  recInduct shift_db_ind >> rw[shift_db_def] >>
  rw[LIST_EQ_REWRITE] >> gvs[MEM_EL, PULL_EXISTS, EL_MAP]
QED

Theorem subst_db_NIL[simp]:
  ∀n. subst_db n [] = I
Proof
  qsuff_tac `∀n ts t. ts = [] ⇒ subst_db n ts t = t` >- rw[FUN_EQ_THM] >>
  recInduct subst_db_ind >> rw[subst_db_def] >>
  rw[LIST_EQ_REWRITE] >> gvs[MEM_EL, PULL_EXISTS, EL_MAP]
QED

Theorem subst_db_unchanged:
  ∀skip ts t n.
    freetyvars_ok n t ∧
    n ≤ skip
  ⇒ subst_db skip ts t = t
Proof
  recInduct subst_db_ind >> reverse $ rw[subst_db_def, freetyvars_ok_def]
  >- metis_tac[] >- metis_tac[] >>
  irule MAP_ID_ON >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem shift_db_unchanged:
  ∀skip shift t n.
    freetyvars_ok n t ∧
    n ≤ skip
  ⇒ shift_db skip shift t = t
Proof
  recInduct shift_db_ind >> reverse $ rw[shift_db_def, freetyvars_ok_def]
  >- metis_tac[] >- metis_tac[] >>
  irule MAP_ID_ON >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem subst_db_shift_db_unchanged:
  ∀skip shift t ts m.
    (m - skip) + LENGTH ts ≤ shift ∧
    skip ≤ m
  ⇒ subst_db m ts (shift_db skip shift t) =
    shift_db skip (shift - LENGTH ts) t
Proof
  recInduct shift_db_ind >> rw[subst_db_def, shift_db_def] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem tsubst_tshift:
  ∀shift t ts m.
    LENGTH ts ≤ shift
  ⇒ tsubst ts (tshift shift t) =
    tshift (shift - LENGTH ts) t
Proof
  rw[] >> irule subst_db_shift_db_unchanged >> simp[]
QED

Theorem subst_db_subst_db:
  ∀n tsn t m tsm.
    n ≤ m
  ⇒ subst_db m tsm (subst_db n tsn t) =
    subst_db n (MAP (subst_db m tsm) tsn)
      (subst_db (m + LENGTH tsn) (MAP (shift_db n (LENGTH tsn)) tsm) t)
Proof
  recInduct subst_db_ind >> rw[subst_db_def, EL_MAP]
  >- gvs[subst_db_shift_db_unchanged] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem shift_db_shift_db:
  ∀m shiftm t n shiftn.
    n ≤ m
  ⇒ shift_db (m + shiftn) shiftm (shift_db n shiftn t) =
    shift_db n shiftn (shift_db m shiftm t)
Proof
  recInduct shift_db_ind >> rw[shift_db_def] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem tshift_tshift:
  ∀t s1 s2.
    tshift s1 (tshift s2 t) = tshift (s1 + s2) t
Proof
  ho_match_mp_tac type_ind >> rw[shift_db_def] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem subst_db_shift_db_1:
  ∀n ts t m shift.
    m ≤ n
  ⇒ subst_db (n + shift) (MAP (shift_db m shift) ts) (shift_db m shift t) =
    shift_db m shift (subst_db n ts t)
Proof
  recInduct subst_db_ind >> rw[shift_db_def, subst_db_def, EL_MAP] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
QED

Theorem subst_db_shift_db_2:
  ∀n ts t m shift.
    n ≤ m
  ⇒ subst_db n (MAP (shift_db m shift) ts) (shift_db (m + LENGTH ts) shift t) =
    shift_db m shift (subst_db n ts t)
Proof
  recInduct subst_db_ind >> rw[shift_db_def, subst_db_def, EL_MAP] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
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

Theorem type_ok_mono:
  ∀tdefs n m t.
    type_ok tdefs n t ∧
    n ≤ m
  ⇒ type_ok tdefs m t
Proof
  rw[type_ok_def] >> drule_all freetyvars_ok_mono >> simp[]
QED

Theorem type_ok_subst_db:
  ∀skip ts tdefs n.
    type_ok tdefs (n + LENGTH ts) t ∧
    EVERY (type_ok tdefs n) ts ∧
    skip ≤ n
  ⇒ type_ok tdefs n (subst_db skip ts t)
Proof
  rw[type_ok_def]
  >- (irule freetyvars_ok_subst_db >> gvs[EVERY_MEM, type_ok_def])
  >- (irule type_wf_subst_db >> gvs[EVERY_MEM, type_ok_def])
QED

Theorem type_ok_shift_db:
  ∀skip shift tdefs n t.
    type_ok tdefs n t
  ⇒ type_ok tdefs (n + shift) (shift_db skip shift t)
Proof
  rw[type_ok_def]
  >- (irule freetyvars_ok_shift_db >> gvs[EVERY_MEM, type_ok_def])
  >- (irule type_wf_shift_db >> gvs[EVERY_MEM, type_ok_def])
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
   type_ok tds n (Function tf t) ⇔
    type_ok tds n tf ∧ type_ok tds n t) ∧
  (∀tds t n. type_ok tds n (Array t) ⇔ type_ok tds n t) ∧
  (∀tds t n. type_ok tds n (M t) ⇔ type_ok tds n t)
Proof
  rw[type_ok_def, type_wf_def, freetyvars_ok_def] >>
  gvs[EVERY_CONJ] >> eq_tac >> gvs[]
QED

Theorem freetyvars_ok_Functions:
  ∀ats rt db.
    freetyvars_ok db (Functions ats rt) ⇔
    EVERY (freetyvars_ok db) ats ∧
    freetyvars_ok db rt
Proof
  Induct >> rw[Functions_def, freetyvars_ok_def] >> eq_tac >> rw[]
QED

Theorem type_ok_Functions:
  ∀ats rt tds db.
    type_ok tds db (Functions ats rt) ⇔
    EVERY (type_ok tds db) ats ∧
    type_ok tds db rt
Proof
  Induct >> rw[Functions_def, type_ok] >> eq_tac >> rw[]
QED

Theorem subst_db_Functions:
  ∀ats rt n ts.
    subst_db n ts (Functions ats rt) =
    Functions (MAP (subst_db n ts) ats) (subst_db n ts rt)
Proof
  Induct >> rw[Functions_def, subst_db_def]
QED

Theorem shift_db_Functions:
  ∀ats rt skip shift.
    shift_db skip shift (Functions ats rt) =
    Functions (MAP (shift_db skip shift) ats) (shift_db skip shift rt)
Proof
  Induct >> rw[Functions_def, shift_db_def]
QED


(******************** Typing judgements ********************)

Theorem type_tcexp_freetyvars_ok:
  ∀ ns db st env e t.
    EVERY (freetyvars_ok db) st ∧
    EVERY (λ(v,scheme). freetyvars_ok_scheme db scheme) env ∧
    namespace_ok ns ∧
    type_tcexp ns db st env e t
  ⇒ freetyvars_ok db t
Proof
  Induct_on `type_tcexp` >> rpt conj_tac >>
  rw[type_ok_def, freetyvars_ok_def] >>
  rgs[LIST_REL_EL_EQN, IMP_CONJ_THM, FORALL_AND_THM]
  >- (
    PairCases_on `s` >> gvs[specialises_def] >>
    imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, type_ok_def] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    irule freetyvars_ok_tsubst >> simp[EVERY_MEM]
    )
  >- gvs[EVERY_EL]
  >- gvs[EVERY_EL, type_ok_def]
  >- gvs[oEL_THM, EVERY_EL]
  >- gvs[freetyvars_ok_Functions]
  >- (
    gvs[freetyvars_ok_Functions, EVERY_EL, type_ok_def] >>
    first_x_assum irule >> rw[] >>
    simp[ZIP_MAP, GSYM MAP_REVERSE, EL_MAP, REVERSE_ZIP, EL_ZIP] >>
    DEP_REWRITE_TAC[EL_REVERSE] >> gvs[]
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
      irule freetyvars_ok_shift_db >> first_x_assum irule >> simp[]
      )
    )
  >- (
    first_x_assum irule >> simp[EVERY_REVERSE] >>
    rw[EVERY_EL, EL_ZIP, EL_MAP] >> pairarg_tac >> gvs[EVERY_EL] >>
    first_x_assum drule >> simp[]
    )
  >- (Cases_on `css` >> gvs[] >> PairCases_on `h` >> gvs[])
  >- (
    first_x_assum irule >> simp[EVERY_REVERSE] >>
    gvs[EVERY_MEM, MEM_ZIP, PULL_EXISTS, EL_MAP] >> rw[] >>
    last_x_assum irule >> simp[EL_MEM]
    )
  >- (
    Cases_on `css` >> gvs[] >- gvs[namespace_ok_def] >>
    PairCases_on `h` >> gvs[] >> first_x_assum $ irule >>
    simp[EVERY_REVERSE, EVERY_MEM, MEM_ZIP, EL_MAP, PULL_EXISTS] >> rw[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[namespace_ok_def, EVERY_MEM, FORALL_PROD] >>
    first_x_assum drule >> simp[MEM_EL, PULL_EXISTS] >>
    disch_then drule >> rw[type_ok_def] >>
    irule freetyvars_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )

  >- (
    gvs[EVERY_MEM, oEL_THM, namespace_ok_def, type_ok_def] >>
    Cases_on `css` >> gvs[]
    >- (Cases_on `usopt` >> gvs[MEM_EL, FORALL_PROD] >> PairCases_on `x` >> gvs[]) >>
    first_x_assum $ qspec_then `h` assume_tac >> gvs[] >>
    pairarg_tac >> gvs[] >>
    qpat_x_assum `_ ⇒ freetyvars_ok db t` irule >>
    simp[MEM_ZIP, EL_MAP, PULL_EXISTS] >> rw[] >>
    irule freetyvars_ok_tsubst >> simp[EVERY_MEM] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL, PULL_EXISTS] >>
    qpat_x_assum `∀n. n < _ typedefs ⇒ _` drule >> simp[] >>
    disch_then drule >> simp[] >>
    qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >> simp[] >>
    disch_then drule >> rw[] >>
    irule freetyvars_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )
  >- gvs[oEL_THM, EVERY_EL]
  >- (
    gvs[oEL_THM, EVERY_EL, namespace_ok_def] >>
    drule ALOOKUP_MEM >> simp[MEM_EL] >>
    strip_tac >> pop_assum $ assume_tac o GSYM >>
    first_x_assum drule >> simp[] >> disch_then drule >> rw[type_ok_def] >>
    irule freetyvars_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )
  >- (
    irule freetyvars_ok_tsubst >> gvs[SF ETA_ss] >>
    gvs[oEL_THM, namespace_ok_def, EVERY_EL] >>
    first_x_assum kall_tac >> first_x_assum drule >> simp[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL] >>
    disch_then drule >> qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >> gvs[] >>
    disch_then drule >> rw[type_ok_def] >>
    irule freetyvars_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )
QED

Theorem type_tcexp_type_ok:
  ∀ ns db st env e t.
    EVERY (type_ok (SND ns) db) st ∧
    EVERY (λ(v,scheme). type_scheme_ok (SND ns) db scheme) env ∧
    namespace_ok ns ∧
    type_tcexp ns db st env e t
  ⇒ type_ok (SND ns) db t
Proof
  Induct_on `type_tcexp` >> rpt conj_tac >> rw[type_ok] >>
  rgs[LIST_REL_EL_EQN, IMP_CONJ_THM, FORALL_AND_THM]
  >- (
    PairCases_on `s` >> gvs[specialises_def] >>
    imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    irule type_ok_subst_db >> simp[EVERY_MEM]
    )
  >- gvs[EVERY_EL]
  >- gvs[EVERY_EL]
  >- gvs[type_cons_def]
  >- gvs[oEL_THM, EVERY_EL]
  >- gvs[type_ok_Functions]
  >- (
    gvs[type_ok_Functions, EVERY_EL] >>
    first_x_assum irule >> rw[] >>
    simp[ZIP_MAP, GSYM MAP_REVERSE, EL_MAP, REVERSE_ZIP, EL_ZIP] >>
    DEP_REWRITE_TAC[EL_REVERSE] >> gvs[]
    )
  >- (
    ntac 2 $ first_x_assum irule >> gvs[EVERY_MEM, FORALL_PROD] >>
    reverse $ rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
    first_x_assum drule >> rw[]
    >- (irule type_ok_shift_db >> simp[]) >>
    rename1 `MEM (a,b,c) _` >>
    drule type_ok_shift_db >>
    disch_then $ qspecl_then [`b`,`new`] assume_tac >> gvs[]
    )
  >- (
    first_x_assum irule >> simp[EVERY_REVERSE] >>
    rw[EVERY_EL, EL_ZIP, EL_MAP] >> pairarg_tac >> gvs[EVERY_EL]
    )
  >- (Cases_on `css` >> gvs[] >> PairCases_on `h` >> gvs[])
  >- (
    first_x_assum irule >> simp[EVERY_REVERSE] >>
    gvs[EVERY_MEM, MEM_ZIP, PULL_EXISTS, EL_MAP] >> rw[] >>
    last_x_assum irule >> simp[EL_MEM]
    )
  >- (
    Cases_on `css` >> gvs[] >- gvs[namespace_ok_def] >>
    PairCases_on `h` >> gvs[] >> first_x_assum $ irule >>
    simp[EVERY_REVERSE, EVERY_MEM, MEM_ZIP, EL_MAP, PULL_EXISTS] >> rw[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[namespace_ok_def, EVERY_MEM, FORALL_PROD] >>
    first_x_assum drule >> simp[MEM_EL, PULL_EXISTS] >>
    disch_then drule >> rw[] >>
    irule type_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )
  >- (
    gvs[EVERY_MEM, oEL_THM, namespace_ok_def] >>
    Cases_on `css` >> gvs[]
    >- (Cases_on `usopt` >> gvs[MEM_EL, FORALL_PROD] >> PairCases_on `x` >> gvs[]) >>
    last_x_assum $ qspec_then `h` assume_tac >> gvs[] >>
    pairarg_tac >> gvs[] >>
    qpat_x_assum `_ ⇒ type_ok typedefs db t` irule >>
    simp[MEM_ZIP, EL_MAP, PULL_EXISTS] >> rw[] >>
    irule type_ok_subst_db >> simp[EVERY_MEM] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL, PULL_EXISTS] >>
    qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
    qpat_x_assum `∀n. n < _ typedefs ⇒ _` drule >> simp[] >>
    disch_then drule >> simp[] >> disch_then drule >> rw[] >>
    irule type_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )
  >- gvs[oEL_THM, EVERY_EL]
  >- (
    gvs[oEL_THM, EVERY_EL, namespace_ok_def] >>
    drule ALOOKUP_MEM >> simp[MEM_EL] >>
    strip_tac >> pop_assum $ assume_tac o GSYM >>
    first_x_assum drule >> simp[] >> disch_then drule >> rw[type_ok_def] >>
    irule freetyvars_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )
  >- (
    irule type_ok_subst_db >> gvs[SF ETA_ss] >>
    gvs[oEL_THM, namespace_ok_def, EVERY_EL] >>
    first_x_assum kall_tac >> first_x_assum drule >> simp[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL] >>
    disch_then drule >> qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >> gvs[] >>
    disch_then drule >> rw[] >>
    irule type_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )
QED

Theorem implodeEQ:
  (implode x = y ⇔ (x = explode y)) ∧
  (y = implode x ⇔ (explode y = x))
Proof
  rw[EQ_IMP_THM] >> simp[]
QED

(* TODO move *)
Theorem ALL_DISTINCT_LENGTH_SET:
  LENGTH a = LENGTH b ∧ set a = set b ∧ ALL_DISTINCT a ⇒ ALL_DISTINCT b
Proof
  rw[] >>
  drule PERM_ALL_DISTINCT_LENGTH >>
  disch_then $ qspec_then `b` assume_tac >> gvs[] >>
  metis_tac[sortingTheory.ALL_DISTINCT_PERM]
QED

Theorem type_tcexp_tcexp_wf:
  ∀ ns db st env e t.
    EVERY (type_ok (SND ns) db) st ∧
    EVERY (λ(v,scheme). type_scheme_ok (SND ns) db scheme) env ∧
    namespace_ok ns ∧
    type_tcexp ns db st env e t
  ⇒ tcexp_wf e
Proof
  Induct_on `type_tcexp` >> rw[tcexp_wf_def, type_wf_def, type_ok] >>
  rgs[EVERY_EL, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
  simp[num_args_ok_def, num_monad_args_def] >>~-
  ([‘LLOOKUP somelist i = SOME e’, ‘i < LENGTH somelist’], gvs[oEL_THM])
  >- (
    gvs[type_exception_def, namespace_ok_def, ALL_DISTINCT_APPEND] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, FORALL_PROD] >>
    last_x_assum $ drule_at Concl >> rw[] >>
    gvs[reserved_cns_def, implodeEQ]
    )
  >- (
    gvs[type_cons_def, namespace_ok_def, ALL_DISTINCT_APPEND] >>
    qsuff_tac `explode cname ∉ reserved_cns` >- simp[reserved_cns_def] >>
    `MEM cname (MAP FST (FLAT (MAP SND typedefs)))` by (
      simp[MEM_MAP, MEM_FLAT, EXISTS_PROD, PULL_EXISTS] >>
      simp[Once MEM_EL, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      gvs[oEL_THM] >> goal_assum $ drule_at Any >> simp[] >>
      imp_res_tac ALOOKUP_MEM >> simp[SF SFY_ss]) >>
    first_x_assum $ drule_at Concl >> simp[] >> strip_tac >>
    gvs[MEM_MAP, implodeEQ, FORALL_PROD] >>
    gvs[GSYM implodeEQ] >> gs[mlstringTheory.implode_def]
    )
  >- simp[num_atomop_args_ok_def]
  >- (
    imp_res_tac get_PrimTys_SOME >> gvs[type_atom_op_cases] >>
    simp[num_atomop_args_ok_def]
    )
  >- (
    imp_res_tac type_tcexp_type_ok >>
    gvs[EVERY_EL, LIST_REL_EL_EQN, type_ok, type_wf_def] >>
    Cases_on `es` >> gvs[]
    )
  >- (Cases_on `xs` >> gvs[])
  >- (
    first_x_assum irule >> reverse $ rw[]
    >- (irule type_ok_shift_db >> simp[]) >>
    qpat_abbrev_tac `a = EL n env` >> PairCases_on `a` >> gvs[] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    drule type_ok_shift_db >> simp[]
    )
  >- (
    first_x_assum irule >>
    imp_res_tac type_tcexp_type_ok >> pop_assum irule >>
    rgs[EVERY_EL, LIST_REL_EL_EQN, EL_MAP] >> reverse $ rw[]
    >- (irule type_ok_shift_db >> simp[]) >>
    qpat_abbrev_tac `a = EL n env` >> PairCases_on `a` >> gvs[] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    drule type_ok_shift_db >> simp[]
    )
  >- (
    rw[] >> last_x_assum drule >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
    pop_assum irule >> reverse $ rw[]
    >- (
      first_x_assum drule >> strip_tac >> gvs[] >>
      drule type_ok_shift_db >> simp[]
      )
    >- (
      DEP_REWRITE_TAC[EL_REVERSE] >> simp[] >>
      qmatch_goalsub_abbrev_tac `EL m _` >>
      `m < LENGTH schemes` by (unabbrev_all_tac >> gvs[]) >> simp[EL_ZIP] >>
      Cases_on `EL m schemes` >> gvs[] >> last_x_assum drule >> rw[] >>
      drule type_ok_shift_db >> simp[]
      ) >>
    qmatch_goalsub_abbrev_tac `_ (_ m)` >>
    PairCases_on `m` >> gvs[] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    drule type_ok_shift_db >> simp[]
    )
  >- (
    rw[] >> first_x_assum drule >>
    qmatch_goalsub_abbrev_tac `SND $ SND elem` >> PairCases_on `elem` >> gvs[]
    )
  >- (Cases_on `css` >> gvs[])
  >- (
    gvs[LENGTH_EQ_NUM_compute, EXISTS_PROD, numeral_less_thm] >>
    rw[] >> gvs[EXTENSION, SF DNF_ss]
    )
  >- (
    simp[MEM_FLAT, MEM_MAP, FORALL_PROD, DISJ_EQ_IMP, PULL_EXISTS] >>
    rw[Once MEM_EL] >> pop_assum $ assume_tac o GSYM >>
    first_x_assum drule >> simp[]
    )
  >- (
    gvs[LENGTH_EQ_NUM_compute, EXISTS_PROD, numeral_less_thm] >>
    rw[] >> gvs[EXTENSION, EQ_IMP_THM, SF DNF_ss]
    )
  >- simp[monad_cns_def]
  >- simp[monad_cns_def]
  >- (
    first_x_assum irule >> last_x_assum assume_tac >>
    drule_at (Pos last) type_tcexp_type_ok >> simp[EVERY_EL, type_ok] >> rw[] >>
    DEP_REWRITE_TAC[EL_REVERSE] >> simp[EL_ZIP, EL_MAP]
    )
  >- simp[monad_cns_def] >~
  [‘_ < LENGTH css ⇒ tcexp_wf (SND (SND (EL _ css)))’,
   ‘type_tcexp _ _ _ _ _ Exception’]
  >- (
    rw[] >> first_x_assum drule >> pairarg_tac >> gvs[] >> strip_tac >>
    pop_assum irule >> rw[REVERSE_ZIP, EL_ZIP, GSYM MAP_REVERSE, EL_MAP] >>
    DEP_REWRITE_TAC[EL_REVERSE] >> simp[] >>
    qmatch_goalsub_abbrev_tac `EL m _` >>
    `m < LENGTH tys` by (unabbrev_all_tac >> gvs[]) >>
    imp_res_tac ALOOKUP_MEM >> pop_assum mp_tac >> rw[MEM_EL] >>
    pop_assum $ assume_tac o GSYM >>
    gvs[namespace_ok_def, EVERY_EL, FORALL_PROD] >>
    last_x_assum drule >> simp[] >>
    disch_then drule >> strip_tac >>
    irule type_ok_mono >> goal_assum $ drule_at Any >> simp[]
    )
  >- (Cases_on `css` >> gvs[namespace_ok_def])
  >- (
    rw[] >> first_x_assum drule >> simp[ELIM_UNCURRY] >> strip_tac >> gvs[]
    )
  >- (
    simp[MEM_FLAT, MEM_MAP, EXISTS_PROD, DISJ_EQ_IMP, PULL_EXISTS] >>
    rw[Once MEM_EL] >> pop_assum $ assume_tac o GSYM >>
    first_x_assum drule >> simp[] >> strip_tac >> gvs[]
    )
  >- (
    gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
    irule ALL_DISTINCT_LENGTH_SET >> qexists_tac `MAP FST exndef` >> simp[]
    )
  >- (
    gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
    first_x_assum $ drule_at Concl >> rw[reserved_cns_def] >>
    simp[monad_cns_def, GSYM implodeEQ] >> gvs[MEM_MAP] >>
    rpt strip_tac >> gvs[implodeEQ]) >>~-
  ([‘_ < LENGTH css ⇒ tcexp_wf (SND (SND (EL _ css)))’],
   rw[] >> first_x_assum drule >> pairarg_tac >> gvs[] >> strip_tac >>
   pop_assum irule >> gvs[EL_ZIP, EL_MAP] >> reverse $ rw[]
   >- (imp_res_tac type_tcexp_type_ok >> gvs[type_ok, EVERY_EL]) >>
   imp_res_tac type_tcexp_type_ok >> gvs[type_ok, EVERY_EL] >>
   irule type_ok_subst_db >> simp[EVERY_EL] >>
   gvs[namespace_ok_def, EVERY_EL, oEL_THM] >>
   imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL] >> pop_assum $ assume_tac o GSYM >>
   qpat_x_assum ‘∀n. n < _ typedefs ⇒ _’ drule >> simp[] >>
   disch_then drule >> rw[] >>
   irule type_ok_mono >>
   first_x_assum $ irule_at Any >> simp[]) >~
  [‘type_tcexp _ _ _ _ _ (TypeCons tyid tyargs)’, ‘css ≠ []’]
  >- (
    gvs[namespace_ok_def, oEL_THM, EVERY_EL] >>
    last_x_assum drule >> pairarg_tac >> gvs[] >> rw[] >>
    Cases_on `css` >> gvs[] >>
    Cases_on `usopt` >> gvs[] >> PairCases_on `x` >> gvs[]
    ) >~
  [‘OPTION_ALL _ eopt’]
  >- (
    Cases_on ‘eopt’ >> gvs[] >> pairarg_tac >> gvs[] >>
    rev_drule_at (Pos last) type_tcexp_type_ok >> simp[EVERY_EL, type_ok] >>
    rw[] >> rpt (pairarg_tac >> gvs[]) >>
    last_x_assum drule >> rw[] >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
    first_x_assum $ qspec_then `cn` mp_tac >> simp[Once MONO_NOT_EQ] >> rw[]
    >- (
      disj1_tac >> simp[MEM_MAP] >>
      pop_assum mp_tac >> rw[monad_cns_def, reserved_cns_def] >> gvs[implodeEQ]
      )
    >- (
      gvs[MEM_MAP, MEM_FLAT, PULL_EXISTS, EXISTS_PROD] >>
      simp[Once MEM_EL, PULL_EXISTS] >> gvs[oEL_THM] >>
      goal_assum $ drule_at Any >> simp[] >> imp_res_tac ALOOKUP_MEM >> simp[SF SFY_ss]
      )
    ) >>~-
  ([‘type_tcexp _ _ _ _ _ (TypeCons tyid tyargs)’, ‘¬MEM v (FLAT (MAP _ css))’],
   simp[MEM_FLAT, MEM_MAP, FORALL_PROD, DISJ_EQ_IMP, PULL_EXISTS] >>
   rw[Once MEM_EL] >> pop_assum $ assume_tac o GSYM >>
   last_x_assum drule >> simp[] >> strip_tac >> gvs[]) >>~-
  ([‘explode cn ∉ monad_cns’],
   gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
   `MEM cn (MAP FST (FLAT (MAP SND typedefs)))` by (
     simp[MEM_MAP, MEM_FLAT, EXISTS_PROD, PULL_EXISTS] >>
     simp[Once MEM_EL, PULL_EXISTS, GSYM CONJ_ASSOC] >>
     gvs[oEL_THM] >> goal_assum $ drule_at Any >> simp[] >>
     pop_assum mp_tac >> rw[Once MEM_EL] >> gvs[EL_MAP] >>
     last_x_assum drule >> rw[] >> pairarg_tac >> gvs[] >>
     imp_res_tac ALOOKUP_MEM >> simp[SF SFY_ss]) >>
   last_x_assum $ drule_at Concl >> simp[] >> strip_tac >>
   gvs[reserved_cns_def, monad_cns_def] >>
   simp[GSYM implodeEQ] >> gvs[MEM_MAP] >> rpt strip_tac >> gvs[implodeEQ]
   )
  >- (
    rw[] >> first_x_assum drule >> simp[ELIM_UNCURRY] >> strip_tac >> gvs[]
    )
  >- (Cases_on `usopt` >> gvs[] >> PairCases_on `x` >> gvs[])
QED

Theorem type_tcexp_freevars_tcexp:
  ∀ns db st env e t.
    type_tcexp ns db st env e t
  ⇒ freevars_tcexp e ⊆ set (MAP FST env)
Proof
  Induct_on `type_tcexp` >> rw[] >>
  simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> rw[] >>
  gvs[LIST_REL_EL_EQN, MEM_EL, MAP_ZIP, DIFF_SUBSET, SUBSET_INSERT_DELETE]
  >- (
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL, EXISTS_PROD] >>
    PairCases_on `s` >> goal_assum drule >> goal_assum drule
    )
  >- gvs[MAP_REVERSE, MAP_ZIP, DIFF_SUBSET]
  >- gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
  >- (
    gvs[MAP_REVERSE, MAP_ZIP] >>
    simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> rw[] >>
    pairarg_tac >> gvs[MEM_EL] >> last_x_assum drule >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
    pop_assum mp_tac >> gvs[MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    simp[SF ETA_ss, MAP_ZIP]
    )
  >- (
    gvs[GSYM SUBSET_INSERT_DELETE, BIGUNION_SUBSET, MEM_MAP,
        PULL_EXISTS, FORALL_PROD, EVERY_MEM] >>
    rw[] >> first_x_assum drule >> simp[]
    )
  >- gvs[MAP_REVERSE, MAP_ZIP, DIFF_SUBSET, GSYM SUBSET_INSERT_DELETE]
  >- (
    gvs[GSYM SUBSET_INSERT_DELETE, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >> rw[] >>
    pairarg_tac >> gvs[EVERY_MEM] >>
    first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
    gvs[MAP_REVERSE, MAP_ZIP, DIFF_SUBSET]
    ) >>
  Cases_on `usopt` >> gvs[]
  >- (
    gvs[GSYM SUBSET_INSERT_DELETE, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
    rw[] >> pairarg_tac >> gvs[EVERY_MEM] >>
    first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
    gvs[MAP_REVERSE, MAP_ZIP, DIFF_SUBSET]
    ) >>
  PairCases_on `x` >> gvs[] >>
  gvs[GSYM SUBSET_INSERT_DELETE, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
  rw[] >> pairarg_tac >> gvs[EVERY_MEM] >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
  gvs[MAP_REVERSE, MAP_ZIP, DIFF_SUBSET]
QED

Theorem type_tcexp_env_extensional:
  ∀ns db st env e t env'.
    type_tcexp ns db st env e t ∧
    (∀x. x ∈ freevars_tcexp e ⇒ ALOOKUP env x = ALOOKUP env' x)
  ⇒ type_tcexp ns db st env' e t
Proof
  Induct_on `type_tcexp` >> rw[] >> rw[Once type_tcexp_cases] >>
  rpt $ first_assum $ irule_at Any >> rw[ALOOKUP_MAP]
  >- (
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> rw[] >>
    first_x_assum irule >> goal_assum drule >> simp[EL_MEM]
    )
  >- (
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> rw[] >>
    first_x_assum irule >> goal_assum drule >> simp[EL_MEM]
    )
  >- (
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> rw[] >>
    first_x_assum irule >> goal_assum drule >> simp[EL_MEM]
    )
  >- (
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> rw[] >>
    first_x_assum irule >> goal_assum drule >> simp[EL_MEM]
    )
  >- (
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum drule >> strip_tac >> first_x_assum irule >> rw[] >>
    first_x_assum irule >> disj2_tac >> goal_assum drule >> simp[EL_MEM]
    )
  >- (
    rw[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >>
    first_x_assum irule >> simp[] >> gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP]
    )
  >- (
    rw[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >>
    first_x_assum irule >> simp[] >>
    gvs[LIST_REL_EL_EQN, ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP]
    )
  >- (
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> simp[] >> strip_tac >> first_x_assum irule >> rw[] >>
    simp[ALOOKUP_MAP, ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >>
    AP_TERM_TAC >> first_x_assum irule >> gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP] >>
    gvs[MEM_MAP] >> disj2_tac >> qexists `fn,body` >> simp[MEM_EL] >>
    goal_assum drule >> simp[]
    )
  >- (
    disj1_tac >> gvs[EVERY_MEM] >> rw[] >> rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> simp[] >> strip_tac >> pop_assum irule >> rw[] >>
    first_x_assum irule >> gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[]
    )
  >- (
    disj1_tac >> rpt $ first_x_assum $ irule_at Any >> rw[ALOOKUP_APPEND] >>
    CASE_TAC >> gvs[] >> first_x_assum irule >> disj2_tac >> gvs[] >>
    gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP]
    )
  >- (
    ntac 2 disj2_tac >> disj1_tac >>
    gvs[EVERY_MEM] >> rw[] >> rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
    first_x_assum $ irule_at Any >> rw[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >>
    first_x_assum irule >> disj2_tac >> gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    rpt $ goal_assum $ drule_at Any >> gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP]
    )
  >- (
    rpt disj2_tac >> rpt $ first_x_assum $ irule_at Any >> simp[] >>
    gvs[EVERY_MEM] >> rw[] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
    first_x_assum irule >> rw[ALOOKUP_APPEND] >> CASE_TAC >> gvs[] >>
    first_x_assum irule >> disj2_tac >> gvs[] >> disj2_tac >>
    gvs[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    rpt $ goal_assum $ drule_at Any >> gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP]
    )
  >- (disj1_tac >> first_x_assum $ irule_at Any >> simp[])
  >- (rpt disj2_tac >> rpt $ first_x_assum $ irule_at Any >> simp[])
QED

Theorem type_tcexp_weaken:
  ∀ns db st env e t db' st' env'.
    type_tcexp ns db st env e t
  ⇒ type_tcexp ns (db + db') (st ++ st') (env ++ env') e t
Proof
  ntac 3 gen_tac >>
  Induct_on `type_tcexp` >> rw[] >> rw[Once type_tcexp_cases]
  >- (
    simp[ALOOKUP_APPEND] >> PairCases_on `s` >> gvs[specialises_def] >>
    qexists_tac `subs` >> gvs[] >>
    irule EVERY_MONOTONIC >> rw[] >> goal_assum $ drule_at Any >> rw[] >>
    drule type_ok_mono >> simp[]
    )
  >- gvs[LIST_REL_EL_EQN]
  >- metis_tac[]
  >- (drule type_ok_mono >> simp[])
  >- metis_tac[]
  >- metis_tac[]
  >- (goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN])
  >- (
    goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN] >>
    irule EVERY_MONOTONIC >> rw[] >> goal_assum $ drule_at Any >> rw[] >>
    drule type_ok_mono >> simp[]
    )
  >- gvs[oEL_THM, EL_APPEND_EQN]
  >- (ntac 2 $ goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN])
  >- metis_tac[]
  >- (rpt $ goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN])
  >- (
    irule_at Any EQ_REFL >> simp[] >>
    irule EVERY_MONOTONIC >> goal_assum $ drule_at Any >> rw[] >>
    drule type_ok_mono >> simp[]
    )
  >- (qexistsl_tac [`new`,`t`] >> gvs[])
  >- (
    qexists_tac `schemes` >> gvs[LIST_REL_EL_EQN] >> rw[]
    >- (
      pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      last_x_assum drule >> gvs[]
      )
    >- (
      irule EVERY_MONOTONIC >> rw[] >> goal_assum $ drule_at Any >> rw[] >>
      pairarg_tac >> gvs[] >> drule type_ok_mono >> simp[]
      )
    )
  >- (disj1_tac >> gvs[FORALL_PROD, EVERY_MEM] >> rw[] >> metis_tac[])
  >- (disj1_tac >> first_x_assum $ irule_at Any >> gvs[APPEND_ASSOC_CONS])
  >- (
    disj2_tac >> disj2_tac >> disj1_tac >> gvs[EVERY_MEM, FORALL_PROD] >> rw[] >>
    first_x_assum drule >> strip_tac >> simp[] >> gvs[APPEND_ASSOC_CONS] >>
    pop_assum $ irule_at Any >> simp[]
    )
  >- (
    disj2_tac >> disj2_tac >> disj2_tac >>
    rpt $ goal_assum $ drule_at Any >> gvs[] >>
    irule_at Any EVERY_MONOTONIC >>
    goal_assum $ drule_at Any >> rw[] >> pairarg_tac >> gvs[] >>
    gvs[APPEND_ASSOC_CONS]
    )
  >- (disj1_tac >> rpt $ goal_assum $ drule_at Any >> gvs[])
  >- (disj2_tac >> disj2_tac >> rpt $ first_x_assum $ irule_at Any >> gvs[])
QED

Theorem type_tcexp_NestedCase_free:
  ∀ns db st env e t ce.
    type_tcexp ns db st env e t ∧
    e = tcexp_of ce
  ⇒ NestedCase_free ce
Proof
  Induct_on `type_tcexp` >> rw[pure_cexpTheory.NestedCase_free_def] >>
  rpt (qpat_x_assum ‘tcexp_of _ = _’ (assume_tac o SYM)) >>
  qpat_x_assum ‘_ = tcexp_of _’ assume_tac >>
  pop_assum mp_tac >> simp[Once $ DefnBase.one_line_ify NONE tcexp_of_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rgs[EVERY_EL, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
  gvs[MAP_EQ_CONS, numeral_less_thm] >> rw[] >> gvs[] >>~-
  ([‘NestedCase_free (EL _ _)’], metis_tac[])
  >~ [‘OPTION_ALL _ eopt’]
  >- (Cases_on ‘eopt’ >> gvs[] >> pairarg_tac >> gvs[]) >>
  gvs[ELIM_UNCURRY] >> metis_tac[]
QED

Theorem type_tcexp_cnames_arities:
  ∀ns db st env e t ce.
    type_tcexp ns db st env e t ∧
    namespace_ok ns ∧
    e = tcexp_of ce
  ⇒ cns_arities_ok ns (cns_arities ce)
Proof
  Induct_on `type_tcexp`  >> rw[] >>
  rpt (qpat_x_assum ‘tcexp_of _ = _’ (assume_tac o SYM)) >>
  qpat_x_assum ‘_ = tcexp_of _’ assume_tac >>
  pop_assum mp_tac >> simp[Once $ DefnBase.one_line_ify NONE tcexp_of_def] >>
  strip_tac >> gvs[AllCaseEqs(), pure_cexpTheory.cns_arities_def, monad_cns_def] >>
  rgs[EVERY_EL, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
  simp[MEM_MAP, MEM_EL, PULL_EXISTS] >> gvs[MAP_EQ_CONS, numeral_less_thm] >>
  rw[] >> gvs[] >> res_tac >> gvs[]
  >- (
    rw[DISJ_EQ_IMP] >> gvs[type_exception_def, ns_cns_arities_def] >>
    irule_at Any OR_INTRO_THM1 >> simp[MEM_MAP, EXISTS_PROD] >>
    irule_at Any EQ_REFL >> imp_res_tac ALOOKUP_MEM
    )
  >- (
    PairCases_on `ns` >> simp[ns_cns_arities_def] >>
    irule_at Any OR_INTRO_THM2 >> irule_at Any OR_INTRO_THM1 >> simp[]
    )
  >- (
    PairCases_on `ns` >> simp[ns_cns_arities_def] >>
    irule_at Any OR_INTRO_THM2 >> irule_at Any OR_INTRO_THM1 >> simp[]
    )
  >- (
    rw[DISJ_EQ_IMP] >> gvs[type_cons_def, ns_cns_arities_def] >>
    rpt $ irule_at Any OR_INTRO_THM2 >> simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
    simp[Once MEM_EL, PULL_EXISTS, GSYM CONJ_ASSOC] >> gvs[oEL_THM] >>
    goal_assum drule >> simp[] >> irule_at Any EQ_REFL >>
    imp_res_tac ALOOKUP_MEM
    )
  >- (last_x_assum drule >> rpt (pairarg_tac >> gvs[]))
  >- (
    gvs[LENGTH_EQ_NUM_compute, DISJ_IMP_THM, FORALL_AND_THM] >>
    rpt (pairarg_tac >> gvs[]) >> disj2_tac >>
    PairCases_on `ns` >> simp[ns_cns_arities_def] >>
    irule_at Any OR_INTRO_THM2 >> irule_at Any OR_INTRO_THM1 >> simp[] >>
    gvs[EXTENSION] >> metis_tac[]
    )
  >- (
    gvs[LENGTH_EQ_NUM_compute, DISJ_IMP_THM, FORALL_AND_THM] >>
    rpt (pairarg_tac >> gvs[]) >> disj2_tac >>
    PairCases_on `ns` >> simp[ns_cns_arities_def] >>
    irule_at Any OR_INTRO_THM2 >> irule_at Any OR_INTRO_THM1 >> simp[] >>
    gvs[EXTENSION] >> metis_tac[]
    )
  >- (gvs[DISJ_IMP_THM, FORALL_AND_THM] >> rpt (pairarg_tac >> gvs[]))
  >- (gvs[DISJ_IMP_THM, FORALL_AND_THM] >> rpt (pairarg_tac >> gvs[]))
  >- rpt (pairarg_tac >> gvs[])
  >- (
    disj2_tac >> simp[ns_cns_arities_def] >>
    irule_at Any OR_INTRO_THM1 >> simp[SUBSET_DEF] >>
    gvs[MEM_MAP, EXISTS_PROD] >> rw[Once MEM_EL] >> gvs[] >>
    pop_assum $ assume_tac o GSYM >>
    first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
    imp_res_tac ALOOKUP_MEM >> goal_assum $ drule_at Any >> gvs[]
    )
  >- (last_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[])
  >- (
    Cases_on `eopt` >> gvs[]
    >- (
      disj2_tac >> simp[ns_cns_arities_def] >> rpt $ irule_at Any OR_INTRO_THM2 >>
      simp[SUBSET_DEF, MEM_MAP, EXISTS_PROD, PULL_EXISTS, Once MEM_EL] >>
      gvs[oEL_THM] >> goal_assum drule >> simp[] >>
      rw[Once MEM_EL] >> pop_assum $ assume_tac o GSYM >>
      first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >> goal_assum $ drule_at Any >> gvs[]
      )
    >- (
      pairarg_tac >> gvs[] >>
      disj2_tac >> simp[ns_cns_arities_def] >> rpt $ irule_at Any OR_INTRO_THM2 >>
      simp[SUBSET_DEF, MEM_MAP, EXISTS_PROD, PULL_EXISTS, Once MEM_EL] >>
      gvs[oEL_THM] >> goal_assum drule >> simp[] >>
      conj_tac >> rw[Once MEM_EL] >> pop_assum $ assume_tac o GSYM
      >- (
        last_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
        pairarg_tac >> gvs[] >>
        imp_res_tac ALOOKUP_MEM >> goal_assum $ drule_at Any >> gvs[]
        )
      >- (
        first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
        imp_res_tac ALOOKUP_MEM >> goal_assum $ drule_at Any >> gvs[]
        )
      )
    )
  >- (last_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[])
QED


(******************** Substitutions ********************)

Theorem type_tcexp_subst_db:
  ∀ns db st env e t n ts.
    type_tcexp ns db st env e t ∧
    namespace_ok ns ∧
    EVERY (type_ok (SND ns) (db - LENGTH ts)) ts ∧
    n + LENGTH ts ≤ db
  ⇒ type_tcexp ns (db - LENGTH ts)
      (MAP (subst_db n ts) st)
      (MAP (λ(s,scheme). (s, subst_db_scheme n ts scheme)) env)
      e
      (subst_db n ts t)
Proof
  Induct_on `type_tcexp` >> rw[subst_db_def] >> rw[Once type_tcexp_cases]
  >- (
    simp[ALOOKUP_MAP] >>
    PairCases_on `s` >> gvs[specialises_def] >>
    rw[subst_db_subst_db] >> irule_at (Pos last) EQ_REFL >> simp[] >>
    gvs[EVERY_MEM, MEM_MAP] >> rw[] >>
    irule type_ok_subst_db >> simp[EVERY_MEM]
    )
  >- gvs[LIST_REL_EL_EQN, EL_MAP]
  >- metis_tac[]
  >- (irule type_ok_subst_db >> simp[])
  >- metis_tac[]
  >- metis_tac[]
  >- (
    qexists_tac `carg_ts` >>
    gvs[LIST_REL_EL_EQN] >> rw[] >>
    last_x_assum drule >> strip_tac >> simp[] >>
    pop_assum drule_all >>
    qsuff_tac `subst_db n ts (EL n' carg_ts) = EL n' carg_ts` >> simp[] >>
    irule subst_db_unchanged >> qexists_tac `0` >> simp[] >>
    gvs[namespace_ok_def, EVERY_EL, type_exception_def] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL] >>
    qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >> gvs[] >>
    last_x_assum drule >> simp[type_ok_def]
    )
  >- (
    rgs[LIST_REL_EL_EQN, EVERY_MAP] >>
    qexists_tac `MAP (subst_db n ts) carg_ts` >> simp[EL_MAP] >> rw[]
    >- (gvs[EVERY_MEM] >> rw[] >> irule type_ok_subst_db >> simp[EVERY_MEM]) >>
    gvs[type_cons_def, EL_MAP, MAP_MAP_o, combinTheory.o_DEF] >> rw[MAP_EQ_f] >>
    simp[subst_db_subst_db, SF ETA_ss] >>
    AP_TERM_TAC >> DEP_REWRITE_TAC [subst_db_unchanged] >>
    gvs[namespace_ok_def, EVERY_EL, oEL_THM] >>
    first_x_assum drule >> simp[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL] >>
    qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
    disch_then drule >> simp[] >> disch_then drule >> rw[type_ok_def] >>
    goal_assum drule >> simp[]
    )
  >- gvs[oEL_THM, EL_MAP]
  >- (
    gvs[LIST_REL_EL_EQN] >>
    rpt $ goal_assum $ drule_at Any >> simp[] >> rw[] >>
    last_x_assum drule >> strip_tac >>
    pop_assum drule_all >>
    imp_res_tac get_PrimTys_SOME >> gvs[EL_MAP, subst_db_def]
    )
  >- metis_tac[]
  >- (
    gvs[subst_db_Functions] >> last_x_assum $ irule_at Any >> simp[] >>
    gvs[LIST_REL_EL_EQN, EL_MAP, SF ETA_ss]
    )
  >- (
    gvs[subst_db_Functions] >> irule_at Any EQ_REFL >>
    gvs[EVERY_MAP, EVERY_MEM] >> rw[]
    >- (irule type_ok_subst_db >> simp[EVERY_MEM])
    >- gvs[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF]
    )
  >- (
    first_x_assum drule_all >> disch_then $ irule_at Any >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM subst_db_shift_db_1] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    last_x_assum $ qspecl_then [`n + new`,`MAP (tshift new) ts`] mp_tac >>
    simp[] >> impl_keep_tac
    >- (
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw[] >>
      first_x_assum drule >> strip_tac >> drule type_ok_shift_db >> simp[]
      ) >>
    rw[] >> irule quotientTheory.EQ_IMPLIES >>
    goal_assum drule >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    rw[FUN_EQ_THM] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >> rw[] >>
    simp[GSYM shift_db_shift_db]
    )
  >- (
    gvs[MAP_REVERSE] >>
    gvs[LIST_REL_EL_EQN, MAP_ZIP_ALT] >>
    first_x_assum $ irule_at Any >> simp[] >> reverse $ rw[]
    >- (
      gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rw[] >>
      irule type_ok_subst_db >> simp[] >>
      gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rw[] >>
      first_x_assum drule >> strip_tac >> drule type_ok_shift_db >> simp[]
      ) >>
    simp[EL_MAP] >> last_x_assum drule >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM subst_db_shift_db_1] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    last_x_assum $ qspecl_then [`n + vars`,`MAP (tshift vars) ts`] mp_tac >>
    simp[] >> impl_keep_tac
    >- (
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw[] >>
      first_x_assum drule >> strip_tac >> drule type_ok_shift_db >> simp[]
      ) >>
    rw[] >> irule quotientTheory.EQ_IMPLIES >>
    goal_assum drule >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    reverse (rpt MK_COMB_TAC) >> simp[]
    >- (
      rw[FUN_EQ_THM] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
      simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >> rw[] >>
      simp[GSYM shift_db_shift_db]
      ) >>
    simp[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    simp[GSYM subst_db_shift_db_1, MAP_MAP_o, combinTheory.o_DEF] >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> rw[MAP_EQ_f, FUN_EQ_THM] >>
    rw[GSYM shift_db_shift_db]
    )
  >- (disj1_tac >> gvs[FORALL_PROD, EVERY_MEM] >> rw[] >> metis_tac[])
  >- (
    disj1_tac >> first_x_assum $ irule_at Any >>
    gvs[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
    )
  >- (
    disj2_tac >> disj2_tac >> disj1_tac >> gvs[EVERY_MEM, FORALL_PROD] >> rw[] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    pop_assum drule >> disch_then drule >>
    simp[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF] >>
    qsuff_tac `MAP (λx. (0n,subst_db n ts x)) tys = MAP ($, 0) tys` >> rw[] >>
    rw[MAP_EQ_f] >> irule subst_db_unchanged >> qexists_tac `0` >> simp[] >>
    gvs[namespace_ok_def, EVERY_MEM] >>
    imp_res_tac ALOOKUP_MEM >> gvs[FORALL_PROD, type_ok_def] >>
    first_x_assum drule >> disch_then drule >> simp[]
    ) >>~-
  ([‘type_tcexp _ _ _ _ _ (TypeCons tyid tyargs)’, ‘set (MAP FST css)’,
    ‘EVERY _ css’],
   rpt disj2_tac >>
   first_assum $ irule_at (Pat ‘type_tcexp _ _ _ _ _ _’) >> simp[] >>
   irule MONO_EVERY >> first_x_assum $ irule_at Any >>
   simp[FORALL_PROD, PULL_EXISTS, MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o,
        combinTheory.o_DEF, SF CONJ_ss] >>
   rpt strip_tac >> pop_assum drule_all >>
   qmatch_abbrev_tac
   ‘type_tcexp A B C D1 E1 E2 ⇒ type_tcexp A B C D2 E1 E2’ >>
   ‘D1 = D2’ suffices_by simp[] >> markerLib.UNABBREV_ALL_TAC >>
   simp[] >> AP_TERM_TAC >> AP_TERM_TAC >> simp[MAP_EQ_f] >>
   rw[subst_db_shift_db_1, subst_db_subst_db, SF ETA_ss] >> AP_TERM_TAC >>
   irule subst_db_unchanged >> gs[] >>
   qpat_x_assum ‘namespace_ok _’ mp_tac >> simp[namespace_ok_def] >>
   gs[oEL_THM] >> simp[EVERY_EL] >> rpt strip_tac >>
   first_x_assum drule >> simp[] >> drule ALOOKUP_MEM >>
   simp[MEM_EL, PULL_EXISTS] >> qx_gen_tac ‘cid’ >>
   rpt strip_tac >> qpat_x_assum ‘_ = EL cid _’ (assume_tac o SYM) >>
   first_x_assum drule >> simp[] >> strip_tac >>
   qpat_x_assum ‘MEM _ schemes’ mp_tac >> simp[MEM_EL, PULL_EXISTS] >>
   qx_gen_tac ‘sid’ >> strip_tac >> first_x_assum drule >>
   simp[type_ok_def] >> strip_tac >> qexists ‘LENGTH tyargs’ >> simp[]) >~
  [‘type_tcexp _ _ _ _ _ (TypeCons tyid tyargs)’]
  >- (rpt disj2_tac >>
      first_assum $ irule_at (Pat ‘type_tcexp _ _ _ _ _ _’) >> simp[] >>
      rw[subst_db_shift_db_1, subst_db_subst_db, SF ETA_ss] >> AP_TERM_TAC >>
      simp[Once EQ_SYM_EQ] >>
      irule subst_db_unchanged >> gs[] >>
      qpat_x_assum ‘namespace_ok _’ mp_tac >> simp[namespace_ok_def] >>
      gs[oEL_THM] >> simp[EVERY_EL] >> rpt strip_tac >>
      first_x_assum drule >> simp[] >> drule ALOOKUP_MEM >>
      simp[MEM_EL, PULL_EXISTS] >> qx_gen_tac ‘cid’ >>
      rpt strip_tac >> qpat_x_assum ‘_ = EL cid _’ (assume_tac o SYM) >>
      first_x_assum drule >> simp[] >> strip_tac >>
      qpat_x_assum ‘MEM _ schemes’ mp_tac >> simp[MEM_EL, PULL_EXISTS] >>
      qx_gen_tac ‘sid’ >> strip_tac >> first_x_assum drule >>
      simp[type_ok_def] >> strip_tac >> qexists ‘LENGTH tyargs’ >> simp[]) >~
  [‘type_tcexp _ _ _ _ _ (Tuple _)’]
  >- (disj1_tac >> first_x_assum $ irule_at Any >> gvs[oEL_THM, EL_MAP]) >~
  [‘type_tcexp _ _ _ _ _ Exception’]
  >- (
    disj2_tac >> disj1_tac >> irule $ GSYM subst_db_unchanged >>
    gvs[oEL_THM, namespace_ok_def, EVERY_EL] >> drule ALOOKUP_MEM >>
    rw[MEM_EL] >>
    pop_assum $ assume_tac o GSYM >>
    first_x_assum drule >> simp[] >> disch_then drule >> rw[type_ok_def] >>
    goal_assum $ drule_at Any >> simp[]
    )
QED

Theorem type_tcexp_shift_db:
  ∀ns db st env e t skip shift.
    type_tcexp ns db st env e t ∧
    namespace_ok ns
  ⇒ type_tcexp ns (db + shift)
      (MAP (shift_db skip shift) st)
      (MAP (λ(s,scheme). (s, shift_db_scheme skip shift scheme)) env)
      e
      (shift_db skip shift t)
Proof
  Induct_on `type_tcexp` >> rw[shift_db_def] >> rw[Once type_tcexp_cases]
  >- (
    simp[ALOOKUP_MAP] >>
    PairCases_on `s` >> gvs[specialises_def] >>
    rw[GSYM subst_db_shift_db_2] >> irule_at (Pos last) EQ_REFL >> simp[] >>
    gvs[EVERY_MEM, MEM_MAP] >> rw[] >>
    irule type_ok_shift_db >> simp[EVERY_MEM]
    )
  >- gvs[LIST_REL_EL_EQN, EL_MAP]
  >- metis_tac[]
  >- (irule type_ok_shift_db >> simp[])
  >- metis_tac[]
  >- metis_tac[]
  >- (
    qexists_tac `carg_ts` >>
    gvs[LIST_REL_EL_EQN] >> rw[] >>
    last_x_assum drule >> strip_tac >>
    pop_assum $ qspecl_then [`skip`,`shift`] mp_tac >>
    qsuff_tac `shift_db skip shift (EL n carg_ts) = EL n carg_ts` >> simp[] >>
    irule shift_db_unchanged >> qexists_tac `0` >> simp[] >>
    gvs[namespace_ok_def, EVERY_EL, type_exception_def] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL] >>
    qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >> gvs[] >>
    last_x_assum drule >> simp[type_ok_def]
    )
  >- (
    rgs[LIST_REL_EL_EQN, EVERY_MAP] >>
    qexists_tac `MAP (shift_db skip shift) carg_ts` >> simp[EL_MAP] >> rw[]
    >- (gvs[EVERY_MEM] >> rw[] >> irule type_ok_shift_db >> simp[EVERY_MEM]) >>
    gvs[type_cons_def, EL_MAP, MAP_MAP_o, combinTheory.o_DEF] >> rw[MAP_EQ_f] >>
    rw[GSYM subst_db_shift_db_2, SF ETA_ss] >>
    AP_TERM_TAC >> DEP_REWRITE_TAC [shift_db_unchanged] >>
    gvs[namespace_ok_def, EVERY_EL, oEL_THM] >>
    first_x_assum drule >> simp[] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL] >>
    qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
    disch_then drule >> simp[] >> disch_then drule >> rw[type_ok_def] >>
    goal_assum drule >> simp[]
    )
  >- gvs[oEL_THM, EL_MAP]
  >- (
    gvs[LIST_REL_EL_EQN] >>
    rpt $ goal_assum $ drule_at Any >> simp[] >> rw[] >>
    last_x_assum drule >> strip_tac >>
    pop_assum $ qspecl_then [`skip`,`shift`] mp_tac >>
    imp_res_tac get_PrimTys_SOME >> gvs[EL_MAP, shift_db_def]
    )
  >- metis_tac[]
  >- (
    gvs[shift_db_Functions] >> last_x_assum $ irule_at Any >> simp[] >>
    gvs[LIST_REL_EL_EQN, EL_MAP, SF ETA_ss]
    )
  >- (
    gvs[shift_db_Functions] >> irule_at Any EQ_REFL >>
    gvs[EVERY_MAP, EVERY_MEM] >> rw[]
    >- (irule type_ok_shift_db >> simp[EVERY_MEM])
    >- gvs[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF]
    )
  >- (
    first_x_assum drule_all >> disch_then $ irule_at Any >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM shift_db_shift_db] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    last_x_assum $ qspecl_then [`new + skip`,`shift`] mp_tac >> simp[]
    )
  >- (
    gvs[MAP_REVERSE] >>
    gvs[LIST_REL_EL_EQN, MAP_ZIP_ALT] >>
    first_x_assum $ irule_at Any >> simp[] >> reverse $ rw[]
    >- (
      gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rw[] >>
      first_x_assum drule >> rw[] >>
      drule type_ok_shift_db >> simp[]
      ) >>
    simp[EL_MAP] >> last_x_assum drule >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM shift_db_shift_db] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    last_x_assum $ qspecl_then [`skip + vars`,`shift`] mp_tac >> simp[] >>
    rw[] >> irule quotientTheory.EQ_IMPLIES >>
    goal_assum drule >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    simp[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
    simp[GSYM shift_db_shift_db, MAP_MAP_o, combinTheory.o_DEF]
    )
  >- (disj1_tac >> gvs[FORALL_PROD, EVERY_MEM] >> rw[] >> metis_tac[])
  >- (
    disj1_tac >> first_x_assum $ irule_at Any >>
    gvs[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
    )
  >- (
    disj2_tac >> disj2_tac >> disj1_tac >> gvs[EVERY_MEM, FORALL_PROD] >> rw[] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    gvs[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF] >>
    pop_assum $ qspecl_then [`skip`,`shift`] mp_tac >>
    qsuff_tac `MAP (λx. (0n,shift_db skip shift x)) tys = MAP ($, 0) tys` >> rw[] >>
    rw[MAP_EQ_f] >> irule shift_db_unchanged >> qexists_tac `0` >> simp[] >>
    gvs[namespace_ok_def, EVERY_MEM] >>
    imp_res_tac ALOOKUP_MEM >> gvs[FORALL_PROD, type_ok_def] >>
    first_x_assum drule >> disch_then drule >> simp[]
    ) >>~-
  ([‘type_tcexp _ _ _ _ _ (TypeCons tyid tyargs)’, ‘set (MAP FST css)’,
    ‘EVERY _ css’],
   rpt disj2_tac >> gvs[oEL_THM] >>
   first_assum $ irule_at (Pat ‘type_tcexp _ _ _ _ _’) >> simp[] >>
   gvs[EVERY_MEM, FORALL_PROD] >> rw[] >>
   first_x_assum drule >> strip_tac >>
   goal_assum $ drule_at Any >> simp[] >>
   pop_assum $ qspecl_then [`skip`,`shift`] mp_tac >> rw[] >>
   gvs[MAP_REVERSE, MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
   gvs[GSYM subst_db_shift_db_2] >>
   irule quotientTheory.EQ_IMPLIES >> goal_assum drule >>
   rpt AP_THM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> ntac 3 AP_TERM_TAC >>
   rw[MAP_EQ_f] >> rpt AP_TERM_TAC >>
   DEP_REWRITE_TAC [shift_db_unchanged] >>
   gvs[namespace_ok_def, EVERY_EL, oEL_THM] >>
   first_x_assum drule >> simp[] >>
   imp_res_tac ALOOKUP_MEM >> gvs[MEM_EL] >>
   qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
   disch_then drule >> simp[] >> disch_then drule >> rw[type_ok_def] >>
   goal_assum drule >> simp[]) >~
  [‘type_tcexp _ _ _ _ _ (TypeCons tyid tyargs)’]
  >- (rpt disj2_tac >> first_assum $ irule_at (Pat ‘type_tcexp _ _ _ _ _ _ ’) >>
      simp[] >> gvs[GSYM subst_db_shift_db_2, SF ETA_ss] >> AP_TERM_TAC >>
      ONCE_REWRITE_TAC [EQ_SYM_EQ] >> irule shift_db_unchanged >>
      qpat_x_assum ‘namespace_ok _’ mp_tac >> simp[namespace_ok_def] >>
      gs[oEL_THM] >> simp[EVERY_EL] >> rpt strip_tac >>
      first_x_assum drule >> simp[] >> drule ALOOKUP_MEM >>
      simp[MEM_EL, PULL_EXISTS] >> qx_gen_tac ‘cid’ >>
      rpt strip_tac >> qpat_x_assum ‘_ = EL cid _’ (assume_tac o SYM) >>
      first_x_assum drule >> simp[] >> strip_tac >>
      qpat_x_assum ‘MEM _ schemes’ mp_tac >> simp[MEM_EL, PULL_EXISTS] >>
      qx_gen_tac ‘sid’ >> strip_tac >> first_x_assum drule >>
      simp[type_ok_def] >> strip_tac >> qexists ‘LENGTH tyargs’ >> simp[]) >~
  [‘type_tcexp _ _ _ _ _ (Tuple tyargs)’]
  >- (disj1_tac >> first_x_assum $ irule_at Any >> gvs[oEL_THM, EL_MAP]) >~
  [‘type_tcexp _ _ _ _ _ Exception’]
  >- (disj2_tac >> disj1_tac >> irule $ GSYM shift_db_unchanged >>
      gvs[oEL_THM, namespace_ok_def, EVERY_EL] >> drule ALOOKUP_MEM >>
      rw[MEM_EL] >>
      pop_assum $ assume_tac o GSYM >>
      first_x_assum drule >> simp[] >> disch_then drule >> rw[type_ok_def] >>
      goal_assum $ drule_at Any >> simp[])
QED

Theorem type_tcexp_subst:
  ∀ns db st env' prefix env e t ces.
    type_tcexp ns db st env' e t ∧
    env' = prefix ++ env ∧
    namespace_ok ns ∧
    MAP FST env = MAP FST ces ∧
    LIST_REL (λce (vars,scheme).
        type_tcexp ns (db + vars) (MAP (tshift vars) st) [] ce scheme)
      (MAP SND ces) (MAP SND env)
  ⇒ type_tcexp ns db st prefix
      (subst_tc (FDIFF (FEMPTY |++ REVERSE ces) (set (MAP FST prefix))) e) t
Proof
  Induct_on `type_tcexp` >> rw[subst_tc_def]
  >- (
    rw[FLOOKUP_FDIFF, flookup_fupdate_list] >> gvs[ALOOKUP_APPEND]
    >- (every_case_tac >> gvs[ALOOKUP_NONE] >> rw[Once type_tcexp_cases]) >>
    gvs[GSYM ALOOKUP_NONE] >>
    drule_all ALOOKUP_SOME_EL_2 >> rw[] >> simp[] >>
    PairCases_on `s` >> gvs[specialises_def] >>
    gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> rw[EL_MAP] >>
    drule type_tcexp_subst_db >> simp[] >>
    disch_then $ qspecl_then [`0`,`subs`] mp_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[subst_db_shift_db_unchanged] >> gvs[GSYM LAMBDA_PROD] >> rw[] >>
    drule type_tcexp_weaken >>
    disch_then $ qspecl_then [`0`,`[]`,`prefix`] mp_tac >> simp[]
    ) >>
  rw[Once type_tcexp_cases] >> gvs[]
  >- (gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    gvs[LIST_REL_EL_EQN, EL_MAP] >>
    irule_at Any EQ_REFL >> rw[] >>
    first_x_assum drule >> strip_tac >> gvs[EL_MAP]
    )
  >- (
    gvs[LIST_REL_EL_EQN, EL_MAP] >> irule_at Any EQ_REFL >> rw[] >>
    last_x_assum drule >> strip_tac >> gvs[EL_MAP]
    )
  >- (
    gvs[LIST_REL_EL_EQN, EL_MAP] >> irule_at Any EQ_REFL >> rw[] >>
    last_x_assum drule >> strip_tac >> gvs[EL_MAP]
    )
  >- metis_tac[]
  >- (
    last_x_assum $ drule_at Any >> simp[] >> strip_tac >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> irule_at Any EQ_REFL >> rw[] >>
    last_x_assum drule >> strip_tac >>
    pop_assum $ drule_at Any >> simp[] >>
    disch_then irule >> rw[EL_MAP]
    )
  >- (
    simp[FDIFF_FDIFF] >> irule_at Any EQ_REFL >> simp[] >>
    qmatch_goalsub_abbrev_tac `ZIP z` >>
    last_x_assum $ qspecl_then [`REVERSE (ZIP z) ++ prefix`,`env`,`ces`] mp_tac >>
    simp[] >> unabbrev_all_tac >> simp[MAP_REVERSE, MAP_ZIP] >> simp[Once UNION_COMM]
    )
  >- (
    first_x_assum $ qspecl_then [`(x,new,t)::prefix`,`env`,`ces`] mp_tac >>
    simp[GSYM FDIFF_FDOMSUB, FDIFF_FDOMSUB_INSERT] >>
    disch_then $ irule_at Any >>
    first_x_assum $ qspecl_then
      [`tshift_env new prefix`,`tshift_env new env`,`ces`] mp_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[FST_THM, LAMBDA_PROD] >> disch_then irule >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    qmatch_goalsub_abbrev_tac `_ (_ a)` >> PairCases_on `a` >> gvs[] >>
    first_x_assum drule >> rw[] >> simp[GSYM shift_db_shift_db] >>
    drule type_tcexp_shift_db >> simp[] >>
    disch_then $ qspecl_then [`a1`,`new`] assume_tac >>
    gvs[MAP_MAP_o, combinTheory.o_DEF]
    )
  >- (
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
    first_x_assum $ irule_at Any >> simp[FDIFF_FDIFF] >>
    qmatch_goalsub_abbrev_tac `ZIP z` >>
    first_x_assum $ qspecl_then
      [`REVERSE (ZIP z) ++ prefix`,`env`,`ces`] mp_tac >> simp[] >>
    unabbrev_all_tac >> gvs[MAP_REVERSE] >>
    gvs[LIST_REL_EL_EQN, EL_MAP, MAP_ZIP] >> rw[Once UNION_COMM] >>
    qmatch_goalsub_abbrev_tac `_ (_ a) b` >>
    PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
    last_x_assum drule >> simp[] >> strip_tac >>
    simp[GSYM MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    qmatch_goalsub_abbrev_tac `type_tcexp _ _ _ pre` >>
    first_x_assum $ qspecl_then [`pre`,`tshift_env b0 env`,`ces`] mp_tac >>
    unabbrev_all_tac >>
    simp[GSYM MAP_ZIP_ALT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM LAMBDA_PROD, GSYM FST_THM] >> impl_tac >> rw[] >> gvs[EL_MAP]
    >- (
      qmatch_goalsub_abbrev_tac `_ (_ c)` >> PairCases_on `c` >> gvs[] >>
      last_x_assum drule >> rw[] >> simp[GSYM shift_db_shift_db] >>
      drule type_tcexp_shift_db >> simp[] >>
      disch_then $ qspecl_then [`c1`,`b0`] assume_tac >>
      gvs[MAP_MAP_o, combinTheory.o_DEF]
      ) >>
    irule quotientTheory.EQ_IMPLIES >> goal_assum drule >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> rw[Once UNION_COMM] >> AP_TERM_TAC >>
    rw[EXTENSION, MEM_MAP, MEM_ZIP, PULL_EXISTS, EXISTS_PROD] >> eq_tac >> rw[]
    >- metis_tac[MEM_EL]
    >- (
      gvs[MEM_EL] >> rpt $ goal_assum drule >> Cases_on `EL n' schemes` >> gvs[]
      )
    )
  >- (
    disj1_tac >> gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM] >>
    gvs[FORALL_PROD, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
    first_x_assum $ qspecl_then [`(v,0,PrimTy Bool)::prefix`,`env`,`ces`] mp_tac >>
    simp[FDIFF_FDIFF, Once INSERT_SING_UNION, Once UNION_COMM]
    )
  >- (
    disj1_tac >>
    first_x_assum $ irule_at Any >> simp[FDIFF_FDIFF] >>
    qmatch_goalsub_abbrev_tac `REVERSE (ZIP z) ++ cons::_` >>
    first_x_assum $ qspecl_then
      [`REVERSE (ZIP z) ++ cons::prefix`,`env`,`ces`] mp_tac >>
    simp[] >> unabbrev_all_tac >> simp[] >> rw[] >> gvs[MAP_REVERSE, MAP_ZIP] >>
    irule quotientTheory.EQ_IMPLIES >> goal_assum drule >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    rw[EXTENSION] >> eq_tac >> rw[] >> metis_tac[]
    )
  >- (
    disj2_tac >> disj2_tac >> disj1_tac >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM] >>
    gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    qmatch_asmsub_abbrev_tac `a ++ b ++ c ++ d` >>
    first_x_assum $ qspecl_then [`a ++ b ++ c`] mp_tac >> simp[] >>
    disch_then $ drule_at Any >> simp[] >> strip_tac >>
    unabbrev_all_tac >> gvs[] >> simp[FDIFF_FDIFF] >>
    irule quotientTheory.EQ_IMPLIES >> goal_assum dxrule >>
    simp[APPEND_ASSOC_CONS] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
    simp[MAP_REVERSE] >>
    qmatch_goalsub_abbrev_tac `MAP f (ZIP ls)` >>
    qsuff_tac `MAP f (ZIP ls) = p_1'`
    >- (disch_then SUBST_ALL_TAC >> rw[EXTENSION] >> eq_tac >> rw[] >> simp[]) >>
    unabbrev_all_tac >> rw[Once LIST_EQ_REWRITE, EL_MAP, EL_ZIP]
    ) >>~-
  ([‘type_tcexp _ _ _ _ _ (TypeCons tyid tyargs)’, ‘set(MAP FST css)’,
    ‘EVERY _ (MAP _ css)’],
   rpt disj2_tac >>
   gvs[MAP_MAP_o, combinTheory.o_DEF, PULL_EXISTS, LAMBDA_PROD] >>
   first_assum $ irule_at (Pat ‘type_tcexp _ _ _ _ _ _’) >> simp[] >>
   simp[ELIM_UNCURRY, SF ETA_ss] >> gvs[FORALL_AND_THM, IMP_CONJ_THM] >>
   simp[FORALL_PROD] >>
   rpt (first_assum
        (first_x_assum o resolve_then (Pat ‘LIST_REL _ _ _’) assume_tac)) >>
   gvs[GSYM APPEND, Excl "APPEND", GSYM FDIFF_FDOMSUB,
       GSYM FDIFF_FDOMSUB_INSERT, SF ETA_ss] >>
   simp[EVERY_MAP] >> irule MONO_EVERY >> goal_assum $ drule_at Any >>
   simp[FORALL_PROD, PULL_EXISTS, FDIFF_FDIFF] >> rpt strip_tac >>
   pop_assum (resolve_then (Pos hd) assume_tac EQ_REFL) >>
   first_assum
   (first_x_assum o resolve_then (Pat ‘LIST_REL _ _ _’) assume_tac) >>
   gs[MAP_REVERSE, MAP_ZIP] >>
   pop_assum mp_tac >>
   qmatch_abbrev_tac ‘type_tcexp _ _ _ D1 E1 _ ⇒ type_tcexp _ _ _ D2 E2 _’ >>
   ‘D1 = D2 ∧ E1 = E2’ suffices_by simp[] >>
   rw[Abbr‘D1’, Abbr‘D2’, Abbr‘E1’, Abbr‘E2’] >>
   simp[FDIFF_FDOMSUB_INSERT] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
   simp[EXTENSION] >> metis_tac[]
   )
  >- (disj1_tac >> rpt $ goal_assum $ drule_at Any >> gvs[])
  >- (disj2_tac >> disj2_tac >> rpt $ goal_assum $ drule_at Any >> gvs[])
QED

Theorem type_tcexp_closing_subst:
  ∀ns db st env e t ces.
    type_tcexp ns db st env e t ∧
    namespace_ok ns ∧
    MAP FST env = MAP FST (REVERSE ces) ∧
    LIST_REL (λce (vars,scheme).
        type_tcexp ns (db + vars) (MAP (tshift vars) st) [] ce scheme)
      (MAP SND (REVERSE ces)) (MAP SND env)
  ⇒ type_tcexp ns db st [] (subst_tc (FEMPTY |++ ces) e) t
Proof
  rw[] >> drule type_tcexp_subst >> simp[] >>
  disch_then $ drule_at Any >> simp[]
QED

Theorem type_tcexp_closing_subst1:
  ∀ns db st var tvars scheme e t ce.
    type_tcexp ns db st [var,tvars,scheme] e t ∧
    namespace_ok ns ∧
    type_tcexp ns (db + tvars) (MAP (tshift tvars) st) [] ce scheme
  ⇒ type_tcexp ns db st [] (subst_tc1 var ce e) t
Proof
  rw[finite_mapTheory.FUPDATE_EQ_FUPDATE_LIST] >>
  irule type_tcexp_closing_subst >> simp[PULL_EXISTS, EXISTS_PROD] >>
  goal_assum drule >> simp[]
QED


(******************** Seq (Var _) insertion ********************)

Inductive insert_seq:
  (insert_seq ce ce' ∧ v ∈ freevars_cexp ce'
    ⇒ insert_seq ce (Prim d Seq [Var d' v; ce'])) ∧

  (* corner case in demand analysis functions *)
  (insert_seq ce ce'
    ⇒ insert_seq (Lam d [] ce) ce') ∧

[~trans:]
  (* shouldn't be necessary, but seems easier *)
  (insert_seq ce1 ce2 ∧ insert_seq ce2 ce3
    ⇒ insert_seq ce1 ce3) ∧

(* boilerplate: *)
  insert_seq (Var d v) (Var d' v) ∧

  (LIST_REL insert_seq ce1s ce2s
    ⇒ insert_seq (Prim d cop ce1s) (Prim d' cop ce2s)) ∧

  (LIST_REL insert_seq ce1s ce2s ∧ insert_seq ce1 ce2
    ⇒ insert_seq (App d ce1 ce1s) (App d' ce2 ce2s)) ∧

  (insert_seq ce1 ce2
    ⇒ insert_seq (Lam d xs ce1) (Lam d' xs ce2)) ∧

  (insert_seq ce1 ce2 ∧ insert_seq ce1' ce2'
    ⇒ insert_seq (Let d x ce1 ce1') (Let d' x ce2 ce2')) ∧

  (LIST_REL (λ(fn1,ce1) (fn2,ce2). fn1 = fn2 ∧ insert_seq ce1 ce2) fns1 fns2 ∧
   insert_seq ce1 ce2
    ⇒ insert_seq (Letrec d fns1 ce1) (Letrec d' fns2 ce2)) ∧

  (insert_seq ce1 ce2 ∧
   LIST_REL (λ(cn1,pvs1,ce1) (cn2,pvs2,ce2).
    cn1 = cn2 ∧ pvs1 = pvs2 ∧ insert_seq ce1 ce2) css1 css2 ∧
   OPTREL (λ(cn_ars1,ce1) (cn_ars2,ce2).
    cn_ars1 = cn_ars2 ∧ insert_seq ce1 ce2) usopt1 usopt2
    ⇒ insert_seq (pure_cexp$Case d ce1 x css1 usopt1) (Case d' ce2 x css2 usopt2))
End

Theorem insert_seq_refl:
  ∀ce. NestedCase_free ce ⇒ insert_seq ce ce
Proof
  Induct using NestedCase_free_ind >> rw[NestedCase_free_def] >>
  simp[Once insert_seq_cases] >> rpt disj2_tac >>
  gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL, MEM_EL, PULL_EXISTS, SF SFY_ss] >> rw[]
  >- (pairarg_tac >> gvs[] >> rpt $ first_x_assum drule >> simp[])
  >- (pairarg_tac >> gvs[] >> rpt $ first_x_assum drule >> simp[])
  >- (Cases_on `eopt` >> gvs[OPTREL_THM] >> pairarg_tac >> gvs[])
QED

Theorem insert_seq_NestedCase_free:
  insert_seq a b ⇒ NestedCase_free a ∧ NestedCase_free b
Proof
  Induct_on `insert_seq` >>
  rw[NestedCase_free_def] >>
  gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP]
  >>~- (
    [`OPTION_ALL`],
    gvs[DefnBase.one_line_ify NONE OPTREL_THM] >>
    every_case_tac >> gvs[] >> rpt (pairarg_tac >> gvs[])
    ) >>
  rw[] >> first_x_assum drule >> rpt (pairarg_tac >> gvs[])
QED

Theorem insert_seq_freevars:
  ∀a b. insert_seq a b ⇒ freevars_cexp a = freevars_cexp b
Proof
  Induct_on `insert_seq` >> rw[] >> gvs[]
  >- (rw[EXTENSION] >> eq_tac >> rw[] >> simp[])
  >- (ntac 2 AP_TERM_TAC >> rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN])
  >- (ntac 3 AP_TERM_TAC >> rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN])
  >- (
    reverse $ MK_COMB_TAC
    >- (
      AP_TERM_TAC >> rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN] >>
      rw[] >> first_x_assum drule >> rpt (pairarg_tac >> gvs[])
      ) >>
    ntac 4 AP_TERM_TAC >> rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN] >>
    rw[] >> first_x_assum drule >> rpt (pairarg_tac >> gvs[])
    )
  >- (
    AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> reverse $ MK_COMB_TAC
    >- (
      Cases_on `usopt1` >> Cases_on `usopt2` >> gvs[] >> rpt (pairarg_tac >> gvs[])
      ) >>
    ntac 3 AP_TERM_TAC >> rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN] >>
    rw[] >> first_x_assum drule >> rpt (pairarg_tac >> gvs[])
    )
QED

Theorem insert_seq_preserves_typing:
  ∀ns db st env ce1 t ce2.
    type_tcexp ns db st env (tcexp_of ce1) t ∧
    insert_seq ce1 ce2
  ⇒ type_tcexp ns db st env (tcexp_of ce2) t
Proof
  Induct_on `insert_seq` >> rw[] >> gvs[tcexp_of_def]
  >- (
    ntac 2 $ simp[Once type_tcexp_cases] >>
    imp_res_tac type_tcexp_freevars_tcexp >>
    imp_res_tac insert_seq_NestedCase_free >>
    imp_res_tac insert_seq_freevars >>
    gvs[freevars_tcexp_of, SUBSET_DEF] >>
    first_x_assum drule >> strip_tac >>
    Cases_on `ALOOKUP env v` >> gvs[ALOOKUP_NONE] >>
    PairCases_on `x` >> simp[specialises_def] >>
    qexists_tac `REPLICATE x0 $ PrimTy Bool` >> simp[type_ok]
    )
  >- (
    pop_assum mp_tac >> simp[Once type_tcexp_cases]
    )
  >- (
    pop_assum mp_tac >> once_rewrite_tac[type_tcexp_cases] >>
    rw[] >> gvs[MAP_EQ_CONS] >> gvs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]
    )
  >- (
    pop_assum mp_tac >> once_rewrite_tac[type_tcexp_cases] >>
    rw[] >> gvs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]
    )
  >- (
    pop_assum mp_tac >> once_rewrite_tac[type_tcexp_cases] >>
    rw[] >> gvs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]
    )
  >- (
    pop_assum mp_tac >> once_rewrite_tac[type_tcexp_cases] >>
    rw[] >> gvs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]
    )
  >- (
    pop_assum mp_tac >> once_rewrite_tac[type_tcexp_cases] >>
    rw[] >> gvs[LIST_REL_EL_EQN, EL_MAP] >>
    irule_at Any EQ_REFL >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
    gvs[GSYM LAMBDA_PROD] >>
    `MAP FST fns2 = MAP FST fns1` by (
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[] >>
      last_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
    gvs[] >> reverse $ rw[]
    >- (CCONTR_TAC >> gvs[]) >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >>
    last_x_assum drule >> rw[]
    ) >>
  pop_assum mp_tac >> once_rewrite_tac[type_tcexp_cases] >>
  rw[] >> gvs[LIST_REL_EL_EQN, EL_MAP]
  >- (
    Cases_on `usopt2` >> gvs[OPTREL_THM] >> disj1_tac >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[GSYM LAMBDA_PROD, GSYM FST_THM] >>
    `MAP FST css1 = MAP FST css2` by (
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
    gvs[EVERY_EL, EL_MAP] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> rw[]
    )
  >- (
    Cases_on `usopt2` >> gvs[OPTREL_THM] >> disj1_tac >>
    rpt (pairarg_tac >> gvs[]) >>
    rpt $ first_x_assum $ irule_at Any >> simp[]
    )
  >- (
    Cases_on `usopt2` >> gvs[OPTREL_THM] >> ntac 2 disj2_tac >> disj1_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM LAMBDA_PROD, GSYM FST_THM] >> rw[]
    >- (
      AP_TERM_TAC >> gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[])
      ) >>
    gvs[EVERY_EL, EL_MAP] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
    first_x_assum drule >> rw[] >> gvs[]
    ) >>
  rpt disj2_tac >> rpt $ first_x_assum $ irule_at Any >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  gvs[GSYM LAMBDA_PROD, GSYM FST_THM] >>
  `MAP FST css2 = MAP FST css1` by (
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
  gvs[] >> reverse $ rpt conj_tac
  >- (
    gvs[EVERY_EL, EL_MAP] >> rw[] >>
    ntac 2 $ first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[]
    )
  >- (
    rpt gen_tac >> strip_tac >> gvs[] >>
    Cases_on `usopt1` >> Cases_on `usopt2` >> gvs[] >- (CCONTR_TAC >> gvs[]) >>
    rename1 `foo = (_,_)` >> PairCases_on `foo` >> gvs[] >>
    rename1 `bar = (_,_)` >> PairCases_on `bar` >> gvs[ELIM_UNCURRY] >>
    gvs[EXISTS_PROD] >> CCONTR_TAC >> gvs[]
    )
  >- (
    strip_tac >> gvs[] >> Cases_on `usopt1` >> gvs[]
    )
QED

Theorem insert_seq_preserves_cexp_wf:
  insert_seq a b ∧ cexp_wf a ⇒ cexp_wf b
Proof
  Induct_on `insert_seq` >> rw[cexp_wf_def] >> gvs[num_args_ok_def] >>
  gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >>
  rw[] >> rpt $ first_x_assum drule >> rpt (pairarg_tac >> gvs[])
  >- (CCONTR_TAC >> gvs[])
  >- (CCONTR_TAC >> gvs[])
  >- (CCONTR_TAC >> gvs[])
  >- (
    Cases_on `usopt1` >> Cases_on `usopt2` >> gvs[OPTREL_THM] >>
    rpt (pairarg_tac >> gvs[])
    )
  >- (
    gvs[MEM_FLAT, MEM_MAP, FORALL_PROD] >>
    simp[Once MEM_EL, Once EQ_SYM_EQ] >> rw[DISJ_EQ_IMP] >>
    last_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
    gvs[MEM_EL] >> metis_tac[]
    ) >>
  `MAP FST css2 = MAP FST css1` by (
    rw[MAP_EQ_EVERY2] >> gvs[LIST_REL_EL_EQN] >> rw[] >>
    last_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
  gvs[] >> Cases_on `usopt1` >> Cases_on `usopt2` >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem insert_seq_imps:
  cexp_wf a ∧ type_tcexp ns db st env (tcexp_of a) t ∧ insert_seq a b
  ⇒ cexp_wf b ∧ NestedCase_free b ∧ type_tcexp ns db st env (tcexp_of b) t
Proof
  strip_tac >>
  map_every imp_res_tac [
    insert_seq_preserves_typing,
    insert_seq_preserves_cexp_wf,
    insert_seq_NestedCase_free] >>
  simp[]
QED


(********************)

val _ = export_theory();

