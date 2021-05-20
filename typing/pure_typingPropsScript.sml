open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open pure_miscTheory pure_cexpTheory pure_configTheory pure_typingTheory

val _ = new_theory "pure_typingProps";


(******************** Substitutions and shifts ********************)

Theorem shift_db_0[simp]:
  ∀t skip. shift_db skip 0 t = t
Proof
  qsuff_tac `∀skip n t. n = 0 ⇒ shift_db skip n t = t` >- gvs[] >>
  recInduct shift_db_ind >> rw[shift_db_def] >>
  rw[LIST_EQ_REWRITE] >> gvs[MEM_EL, PULL_EXISTS, EL_MAP]
QED

Theorem subst_db_unchanged:
  ∀skip ts t n.
    freetyvars_ok n t ∧
    n ≤ skip
  ⇒ subst_db skip ts t = t
Proof
  recInduct subst_db_ind >> reverse $ rw[subst_db_def, freetyvars_ok_def]
  >- metis_tac[] >>
  irule MAP_ID_ON >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem shift_db_unchanged:
  ∀skip shift t n.
    freetyvars_ok n t ∧
    n ≤ skip
  ⇒ shift_db skip shift t = t
Proof
  recInduct shift_db_ind >> reverse $ rw[shift_db_def, freetyvars_ok_def]
  >- metis_tac[] >>
  irule MAP_ID_ON >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem subst_db_shift_db:
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
  rw[] >> irule subst_db_shift_db >> simp[]
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
      irule freetyvars_ok_shift_db >> first_x_assum irule >> simp[]
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
    imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    irule type_ok_subst_db >> simp[EVERY_MEM]
    )
  >- gvs[EVERY_EL]
  >- gvs[EVERY_EL]
  >- gvs[type_cons_def]
  >- gvs[oEL_THM, EVERY_EL]
  >- gvs[EVERY_EL]
  >- (
    first_x_assum irule >>
    gvs[EVERY_MEM, MEM_ZIP, PULL_EXISTS, EL_MAP, MEM_EL]
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
    first_x_assum irule >>
    rw[EVERY_EL, EL_ZIP, EL_MAP] >> pairarg_tac >> gvs[EVERY_EL]
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

Theorem type_cexp_cexp_wf:
  ∀ ns db st env e t.
    EVERY (type_ok (SND ns) db) st ∧
    EVERY (λ(v,scheme). type_scheme_ok (SND ns) db scheme) env ∧
    namespace_ok ns ∧
    type_cexp ns db st env e t
  ⇒ cexp_wf e
Proof
  Induct_on `type_cexp` >> rw[cexp_wf_def, type_wf_def, type_ok] >>
  gvs[EVERY_EL, LIST_REL_EL_EQN, EL_ZIP, EL_MAP]
  >- (
    imp_res_tac type_cexp_type_ok >>
    gvs[EVERY_EL, LIST_REL_EL_EQN, type_ok, type_wf_def] >>
    Cases_on `es` >> gvs[]
    )
  >- (
    imp_res_tac type_cexp_type_ok >>
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
    imp_res_tac type_cexp_type_ok >> pop_assum irule >>
    gvs[EVERY_EL, LIST_REL_EL_EQN, EL_MAP] >> reverse $ rw[]
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
      ) >>
    qmatch_goalsub_abbrev_tac `_ (_ m)` >>
    PairCases_on `m` >> gvs[] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    drule type_ok_shift_db >> simp[]
    )
  >- (
    rw[] >> first_x_assum drule >> pairarg_tac >> gvs[] >> strip_tac >>
    pop_assum irule >> gvs[EL_ZIP, EL_MAP] >> rw[] >>
    imp_res_tac type_cexp_type_ok >> gvs[type_ok, EVERY_EL]
    )
  >- (
    gvs[namespace_ok_def, oEL_THM, EVERY_EL] >>
    first_x_assum drule >> pairarg_tac >> gvs[] >> rw[] >>
    imp_res_tac sortingTheory.PERM_LENGTH >>
    Cases_on `css` >> gvs[]
    )
QED

Theorem type_cexp_weaken:
  ∀ns db st env e t db' st' env'.
    type_cexp ns db st env e t
  ⇒ type_cexp ns (db + db') (st ++ st') (env ++ env') e t
Proof
  ntac 3 gen_tac >>
  Induct_on `type_cexp` >> rw[] >> rw[Once type_cexp_cases]
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
  >- (disj1_tac >> goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN])
  >- (
    goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN] >>
    irule EVERY_MONOTONIC >> rw[] >> goal_assum $ drule_at Any >> rw[] >>
    drule type_ok_mono >> simp[]
    )
  >- gvs[oEL_THM, EL_APPEND_EQN]
  >- (ntac 2 $ goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN])
  >- metis_tac[]
  >- (disj1_tac >> qexists_tac `ts` >> gvs[LIST_REL_EL_EQN])
  >- (disj2_tac >> qexists_tac `ts` >> gvs[LIST_REL_EL_EQN])
  >- (
    irule EVERY_MONOTONIC >> rw[] >> goal_assum $ drule_at Any >> rw[] >>
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
  >- (
    rpt $ goal_assum $ drule_at Any >> gvs[] >> qexists_tac `typedef` >>
    irule_at Any EVERY_MONOTONIC >>
    goal_assum $ drule_at Any >> rw[] >> pairarg_tac >> gvs[] >>
    goal_assum $ drule_at Any >> gvs[rich_listTheory.APPEND_ASSOC_CONS] >> rw[] >>
    irule EVERY_MONOTONIC >> rw[] >> goal_assum $ drule_at Any >> rw[] >>
    drule type_ok_mono >> simp[]
    )
QED


(********************)

val _ = export_theory();

