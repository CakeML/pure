open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory rich_listTheory alistTheory pred_setTheory finite_mapTheory;
open pure_miscTheory pure_cexpTheory pure_tcexpTheory pure_configTheory;
open typeclass_typesTheory typeclass_typesPropsTheory 
open typeclass_kindCheckTheory;
open typeclass_typingTheory typeclass_typingPropsTheory;
open pure_tcexp_typingTheory pure_tcexp_lemmasTheory;

val _ = new_theory "pure_typingProps";


(******************** Basic lemmas ********************)

Theorem type_exception_Subscript:
  tcexp_namespace_ok ns ⇒ type_exception (FST ns) («Subscript», [])
Proof
  PairCases_on `ns` >> rw[type_exception_def, tcexp_namespace_ok_def] >>
  gvs[ALL_DISTINCT_APPEND] >> drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

(******************** Typing judgements ********************)
Theorem tcexp_destruct_type_cons_type_ok:
  tcexp_destruct_type_cons ns db t c ts ∧
  kind_ok (SND ns) db kindType t ∧
  tcexp_namespace_ok ns ∧
  n < LENGTH ts ⇒
    kind_ok (SND ns) (FST (EL n ts) ++ db) kindType (SND (EL n ts))
Proof
  simp[oneline tcexp_destruct_type_cons_def] >>
  every_case_tac >> gvs[]
  >- (
    gvs[type_exception_def,tcexp_namespace_ok_def,EVERY_EL] >>
    rw[] >>
    drule_then strip_assume_tac ALOOKUP_SOME_EL >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum drule >>
    rw[EL_MAP,type_ok_def] >>
    first_x_assum $ drule_then assume_tac >>
    drule_then irule kind_ok_mono >>
    simp[]
  ) >>
  strip_tac >>
  every_case_tac >> gvs[tcexp_type_cons_def,EL_MAP]
  >- (
    pairarg_tac >> gvs[] >>
    irule kind_ok_subst_db >>
    gvs[tcexp_namespace_ok_def,EVERY_EL,oEL_THM] >>
    qpat_x_assum `!n. n < LENGTH r ⇒ _ (EL _ r)` drule >>
    pairarg_tac >> rw[] >>
    drule_then strip_assume_tac ALOOKUP_SOME_EL >>
    gvs[] >>
    first_x_assum drule >>
    pairarg_tac >> rw[] >>
    gvs[LIST_REL_EL_EQN] >>
    first_x_assum $ drule_then strip_assume_tac >>
    gvs[oneline type_scheme_ok_def] >>
    first_x_assum $ irule_at (Pos last) >>
    rw[oEL_THM,EL_APPEND_EQN,EL_MAP] >>
    irule kind_ok_shift_db >>
    first_x_assum $ irule_at (Pos last) >>
    rw[oEL_THM,EL_APPEND_EQN]
  )
  >- (
    gvs[split_ty_cons_thm,head_ty_cons_eq_head_ty] >>
    qpat_x_assum `kind_ok _ _ kindType t` mp_tac >>
    rewrite_tac[Once $ GSYM cons_types_head_ty_ty_args] >>
    rw[cons_types_head_ty_ty_args,kind_ok_cons_types,kind_ok,
      kind_arrows_kindType_EQ,LIST_REL_EL_EQN]
  )
QED

Theorem tcexp_type_cepat_type_ok:
  tcexp_namespace_ok ns ⇒
  ∀p tk vts. tcexp_type_cepat ns db p tk vts ⇒
    ∀v t'. kind_ok (SND ns) (FST tk ++ db) kindType (SND tk) ∧
      MEM (v,t') vts ⇒ kind_ok (SND ns) db kindType t'
Proof
  strip_tac >>
  ho_match_mp_tac tcexp_type_cepat_ind >>
  rw[] >>
  gvs[MEM_FLAT,LIST_REL3_EL,MEM_EL]
  >- (
    gvs[oneline specialises_def] >>
    every_case_tac >>
    gvs[LIST_REL_EL_EQN] >>
    drule_then irule kind_ok_subst_db >>
    rw[oEL_THM,EL_APPEND_EQN] >>
    metis_tac[]
  ) >>
  first_x_assum drule >>
  rw[] >>
  first_x_assum irule >>
  rw[] >- metis_tac[] >>
  metis_tac[tcexp_destruct_type_cons_type_ok]
QED

Theorem type_tcexp_type_ok:
  ∀ ns db st env e t.
    EVERY (type_ok (SND ns) db) st ∧
    EVERY (λ(v,scheme). type_scheme_ok (SND ns) db scheme) env ∧
    tcexp_namespace_ok ns ∧
    type_tcexp ns db st env e t
  ⇒ type_ok (SND ns) db t
Proof
  Induct_on `type_tcexp` >> rpt conj_tac >>
  rw[lambdify type_ok_def,lambdify $ oneline type_scheme_ok_def,
    kind_ok_Functions,kind_ok] >>
  rgs[LIST_REL_EL_EQN, IMP_CONJ_THM, FORALL_AND_THM]
  >- (
    PairCases_on `s` >> gvs[specialises_def] >>
    imp_res_tac ALOOKUP_SOME_EL >> gvs[EVERY_EL,LIST_REL_EL_EQN] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    irule kind_ok_subst_db >> simp[] >>
    first_x_assum $ irule_at (Pos last) >>
    simp[oEL_THM,EL_APPEND_EQN]
    )
  >- gvs[kind_ok_cons_types,kind_ok,EVERY_EL,kind_arrows_kindType_EQ,
      LIST_REL_EL_EQN]
  >- simp[kind_arrows_def]
  >- gvs[tcons_to_type_def,kind_ok_cons_types,kind_ok,EVERY_EL,
      kind_arrows_kindType_EQ,LIST_REL_EL_EQN,tcexp_type_cons_def]
  >- gvs[EVERY_EL,oEL_THM]
  >- (
    first_x_assum irule >>
    gvs[EVERY_EL,EL_ZIP,EL_MAP]
  )
  >- gvs[EVERY_EL,MEM_EL]
  >- (
    first_x_assum irule >>
    first_x_assum irule >>
    gvs[EVERY_EL,EL_MAP] >>
    rw[]
    >- (
      first_x_assum drule >>
      pairarg_tac >>
      gvs[] >>
      TOP_CASE_TAC >>
      rw[] >>
      drule_then irule kind_ok_shift_db >>
      rw[oEL_THM,EL_APPEND_EQN]
    ) >>
    first_x_assum $ drule_then assume_tac >>
    drule_then irule kind_ok_shift_db >>
    rw[oEL_THM,EL_APPEND_EQN]
  )
  >- (
    gvs[EVERY_EL,LIST_REL_EL_EQN,MEM_EL,kind_ok_Functions] >>
    first_x_assum irule >>
    rw[EL_ZIP,EL_MAP,pred_type_kind_ok_alt] >>
    TOP_CASE_TAC >>
    first_x_assum drule >>
    rw[]
  )
  >- (
    first_x_assum irule >>
    rw[EVERY_MAP,EVERY_MEM,ELIM_UNCURRY] >>
    drule_then (drule_then irule) tcexp_type_cepat_type_ok >>
    simp[] >>
    metis_tac[PAIR]
  )
  >- (
    Cases_on `usopt` >> gvs[]
    >- (
      `0 < LENGTH css`
      by (
        Cases_on `css` >> simp[] >>
        gvs[oneline get_constructors_def,oneline tcexp_namespace_ok_def] >>
        every_case_tac >> gvs[ELIM_UNCURRY] >>
        every_case_tac >> gvs[oEL_THM,EVERY_EL]
      ) >>
      gvs[EVERY_EL] >>
      first_x_assum drule >>
      simp[ELIM_UNCURRY] >>
      strip_tac >>
      first_x_assum irule >>
      rw[EL_ZIP,EL_MAP] >>
      gvs[] >>
      first_x_assum drule >>
      simp[oneline specialises_def] >>
      TOP_CASE_TAC >>
      rw[LIST_REL_EL_EQN] >>
      pop_assum $ assume_tac o GSYM >>
      drule tcexp_destruct_type_cons_type_ok >>
      rw[] >>
      irule kind_ok_subst_db >>
      rw[] >>
      first_x_assum $ drule_then strip_assume_tac >>
      gvs[] >>
      first_x_assum $ irule_at (Pos last) >>
      rw[oEL_THM,EL_APPEND_EQN] >>
      metis_tac[]
    ) >>
    first_x_assum irule >>
    metis_tac[PAIR]
  )
  >- (
    drule_then drule tcexp_destruct_type_cons_type_ok >>
    rw[] >>
    qpat_x_assum `specialises _ _ _ _` mp_tac >>
    rw[oneline specialises_def,pair_CASE_def,LIST_REL_EL_EQN] >>
    irule kind_ok_subst_db >>
    first_x_assum $ irule_at (Pos last) >>
    gvs[oEL_THM,EL_APPEND_EQN]
  )
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

Theorem type_tcexp_generalise_env:
  ∀ns db st env e t env'.
    type_tcexp ns db st env e t ∧
    (∀x sch. x ∈ freevars_tcexp e ∧ ALOOKUP env x = SOME sch ⇒
       ∃sch'. ALOOKUP env' x = SOME sch' ∧
              (∀n t . specialises (SND ns) (db + n) (tshift_scheme n sch) t
                  ⇒ specialises (SND ns) (db + n) (tshift_scheme n sch') t))
  ⇒ type_tcexp ns db st env' e t
Proof
  Induct_on `type_tcexp` >> rw[] >> simp[Once type_tcexp_cases]
  >- (
    first_x_assum $ qspec_then `0` mp_tac >> simp[] >>
    gvs[ELIM_UNCURRY]
    )
  >- (
    gvs[MEM_EL, EL_MAP, PULL_EXISTS, LIST_REL_EL_EQN, SF CONJ_ss] >>
    metis_tac[]
    )
  >- (rpt $ first_x_assum $ irule_at Any >> simp[])
  >- (rpt $ first_x_assum $ irule_at Any >> simp[])
  >- (rpt $ first_x_assum $ irule_at Any >> simp[])
  >- (
    gvs[MEM_EL, EL_MAP, PULL_EXISTS, LIST_REL_EL_EQN, SF CONJ_ss] >>
    metis_tac[]
    )
  >- (
    gvs[MEM_EL, EL_MAP, PULL_EXISTS, LIST_REL_EL_EQN, SF CONJ_ss] >>
    metis_tac[]
    )
  >- (
    gvs[MEM_EL, EL_MAP, PULL_EXISTS, LIST_REL_EL_EQN, SF CONJ_ss] >>
    metis_tac[]
    )
  >- (rpt $ first_x_assum $ irule_at Any >> simp[])
  >- (
    gvs[MEM_EL, EL_MAP, PULL_EXISTS, LIST_REL_EL_EQN, SF CONJ_ss] >>
    metis_tac[]
    )
  >- (
    first_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >> simp[] >>
    rw[ALOOKUP_APPEND] >> CASE_TAC >> gvs[ALOOKUP_NONE] >>
    gvs[MAP_REVERSE, MAP_ZIP]
    )
  >- (
    rpt $ first_x_assum $ irule_at Any >> simp[] >>
    gvs[ALOOKUP_MAP, PULL_EXISTS] >> rw[] >>
    first_x_assum $ drule_at Any >> strip_tac >>
    gvs[ELIM_UNCURRY, shift_db_twice]
    )
  >- (
    rpt $ first_x_assum $ irule_at Any >> simp[] >>
    drule_at Any EVERY2_MEM_MONO >> disch_then $ irule_at Any >> rw[]
    >- (
      gvs[MEM_ZIP, LIST_REL_EL_EQN] >>
      last_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >>
      first_x_assum irule >> rw[ALOOKUP_APPEND, ALOOKUP_MAP] >>
      CASE_TAC >> gvs[ALOOKUP_NONE, PULL_EXISTS] >>
      last_x_assum $ drule_at Any >> gvs[MAP_REVERSE, MAP_ZIP] >>
      impl_tac >> rw[] >> gvs[ELIM_UNCURRY, shift_db_twice] >>
      simp[MEM_EL, EL_MAP, SF CONJ_ss, PULL_EXISTS] >>
      disj2_tac >> goal_assum $ drule_at Any >> simp[]
      )
    >- (
      gvs[ALOOKUP_APPEND] >> CASE_TAC >> gvs[ALOOKUP_NONE] >>
      imp_res_tac LIST_REL_LENGTH >>
      last_x_assum $ drule_at Any >> gvs[MAP_REVERSE, MAP_ZIP]
      )
    )
  >- (
    disj1_tac >> gvs[EVERY_MEM] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >>
    pop_assum irule >> rw[] >> first_x_assum $ drule_at Any >>
    impl_tac >> rw[] >> gvs[] >>
    simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[]
    )
  >- (
    disj1_tac >> irule_at Any EQ_REFL >> simp[] >>
    first_x_assum irule >> rw[ALOOKUP_APPEND] >>
    CASE_TAC >> gvs[ALOOKUP_NONE] >> first_x_assum $ drule_at Any >>
    impl_tac >> rw[] >> gvs[MAP_REVERSE, MAP_ZIP]
    )
  >- (
    ntac 2 disj2_tac >> disj1_tac >> gvs[EVERY_MEM] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >> simp[] >>
    first_x_assum irule >> rw[ALOOKUP_APPEND] >>
    CASE_TAC >> gvs[ALOOKUP_NONE] >> first_x_assum $ drule_at Any >>
    impl_tac >> rw[] >> gvs[MAP_REVERSE, MAP_ZIP] >>
    simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[]
    )
  >- (
    rpt disj2_tac >> goal_assum $ drule_at Any >> simp[] >>
    rw[] >> gvs[] >- (first_x_assum irule >> rw[]) >>
    gvs[EVERY_MEM] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >> rw[] >> simp[] >>
    first_x_assum irule >> rw[ALOOKUP_APPEND] >>
    CASE_TAC >> gvs[ALOOKUP_NONE] >> first_x_assum $ drule_at Any >>
    impl_tac >> rw[] >> gvs[MAP_REVERSE, MAP_ZIP] >>
    simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    rpt disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[]
    )
  >- (
    disj1_tac >> goal_assum $ drule_at Any >> simp[]
    )
  >- (
    rpt disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[]
    )
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
[~Seq_Var:]
  (insert_seq ce ce' ∧ v ∈ freevars_cexp ce'
    ⇒ insert_seq ce (Prim d Seq [Var d' v; ce']))

[~Lam_NIL:]
  (* corner case in demand analysis functions *)
  (insert_seq ce ce'
    ⇒ insert_seq (Lam d [] ce) ce')

[~trans:]
  (* shouldn't be necessary, but seems easier *)
  (insert_seq ce1 ce2 ∧ insert_seq ce2 ce3
    ⇒ insert_seq ce1 ce3)

[~Var:]
(* boilerplate: *)
  insert_seq (Var d v) (Var d' v)

[~Prim:]
  (LIST_REL insert_seq ce1s ce2s
    ⇒ insert_seq (Prim d cop ce1s) (Prim d' cop ce2s))

[~App:]
  (LIST_REL insert_seq ce1s ce2s ∧ insert_seq ce1 ce2
    ⇒ insert_seq (App d ce1 ce1s) (App d' ce2 ce2s))

[~Lam:]
  (insert_seq ce1 ce2
    ⇒ insert_seq (Lam d xs ce1) (Lam d' xs ce2))

[~Let:]
  (insert_seq ce1 ce2 ∧ insert_seq ce1' ce2'
    ⇒ insert_seq (Let d x ce1 ce1') (Let d' x ce2 ce2'))

[~Letrec:]
  (LIST_REL (λ(fn1,ce1) (fn2,ce2). fn1 = fn2 ∧ insert_seq ce1 ce2) fns1 fns2 ∧
   insert_seq ce1 ce2
    ⇒ insert_seq (Letrec d fns1 ce1) (Letrec d' fns2 ce2))

[~Case:]
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
    disj1_tac >> gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[GSYM LAMBDA_PROD, GSYM FST_THM] >>
    `MAP FST css1 = MAP FST css2` by (
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[])) >>
    gvs[EVERY_EL, EL_MAP] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> rw[]
    )
  >- (
    disj1_tac >> rpt (pairarg_tac >> gvs[]) >>
    rpt $ first_x_assum $ irule_at Any >> simp[]
    )
  >- (
    ntac 2 disj2_tac >> disj1_tac >>
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
