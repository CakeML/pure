open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory rich_listTheory alistTheory pred_setTheory finite_mapTheory;
open pure_miscTheory pure_cexpTheory pure_tcexpTheory pure_configTheory;
open typeclass_typesTheory typeclass_typesPropsTheory
open typeclass_kindCheckTheory;
open typeclass_typingTheory typeclass_typingPropsTheory;
open pure_tcexp_typingTheory pure_tcexp_lemmasTheory;

val _ = new_theory "pure_tcexp_typingProps";


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
  kind_ok tds db kindType t ∧
  tcexp_namespace_ok ns ∧
  tds = SND ns ∧
  MEM (ks,t') ts ⇒
    kind_ok tds (ks ++ db) kindType t'
Proof
  Cases_on `ns` >>
  rw[tcexp_destruct_type_cons_def] >>
  every_case_tac >> gvs[MEM_MAP]
  >- (
    gvs[type_exception_def,tcexp_namespace_ok_def,EVERY_MEM] >>
    drule_then assume_tac ALOOKUP_MEM >>
    first_x_assum drule >>
    rw[type_ok] >>
    first_x_assum $ drule_then assume_tac >>
    drule kind_ok_APPEND >>
    simp[]
  )
  >- (
    gvs[tcexp_type_cons_def,MEM_MAP,EXISTS_PROD] >>
    irule kind_ok_subst_db_APPEND >>
    irule_at (Pat `_ ++ _ = _ ++ _`) EQ_REFL >>
    simp[EVERY2_MAP] >>
    drule_at_then (Pos last) (irule_at Any) LIST_REL_mono >>
    rw[]
    >- (
      irule kind_ok_shift_db_APPEND >>
      simp[] >>
      first_assum $ irule_at (Pat `kind_ok _ _ _ _`) >>
      simp[]
    ) >>
    gvs[tcexp_namespace_ok_def,oEL_THM] >>
    drule_then drule $ iffLR EVERY_EL >>
    pairarg_tac >> rw[] >>
    gvs[] >>
    drule_then drule $ iffLR EVERY_MEM >>
    drule_then assume_tac ALOOKUP_MEM >>
    drule_then drule $ iffLR EVERY_MEM >>
    rw[] >>
    drule_then drule $ iffLR EVERY_MEM >>
    rw[type_scheme_ok_def] >>
    drule_then irule kind_ok_APPEND
  )
  >- (
    gvs[split_ty_cons_thm,head_ty_cons_eq_head_ty] >>
    qpat_x_assum `kind_ok _ _ _ _` mp_tac >>
    rewrite_tac[Once $ GSYM cons_types_head_ty_ty_args] >>
    rw[cons_types_head_ty_ty_args,kind_ok_cons_types,kind_ok,
      kind_arrows_kindType_EQ] >>
    drule_then drule LIST_REL_MEM_IMP_R >>
    simp[MEM_GENLIST,PULL_EXISTS]
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
  >- metis_tac[specialises_kind_ok] >>
  first_x_assum drule >>
  rw[] >>
  first_x_assum irule >>
  rw[] >- metis_tac[] >>
  drule_then irule tcexp_destruct_type_cons_type_ok >>
  simp[] >>
  metis_tac[MEM_EL]
QED

Theorem type_tcexp_type_ok:
  ∀db st env e t.
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
    drule_then irule specialises_kind_ok >>
    imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
    first_x_assum drule >>
    simp[] >>
    TOP_CASE_TAC
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
        gvs[tcexp_get_cases_def] >>
        gvs[oneline tcexp_namespace_ok_def] >>
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
      first_x_assum $ drule_then assume_tac >>
      drule_then irule specialises_kind_ok >>
      drule_then irule tcexp_destruct_type_cons_type_ok >>
      rw[] >>
      metis_tac[MEM_EL]
    ) >>
    first_x_assum irule >>
    metis_tac[PAIR]
  )
  >- (
    drule_then irule specialises_kind_ok >>
    drule_then irule tcexp_destruct_type_cons_type_ok >>
    rw[] >>
    metis_tac[MEM_EL]
  )
QED

Theorem tcexp_namespace_ok_get_cases_not_monad_cns:
  tcexp_namespace_ok ns ∧
  tcexp_get_cases ns t = SOME constructors ∧
  MEM cons constructors ⇒
  explode (FST cons) ∉ monad_cns
Proof
  Cases_on `ns` >>
  simp[tcexp_get_cases_def,tcexp_namespace_ok_def] >>
  rw[pair_CASE_def]
  >- (
    gvs[MEM_MAP,ALL_DISTINCT_APPEND,PULL_EXISTS] >>
    spose_not_then strip_assume_tac >>
    assume_tac monad_cns_SUBSET_reserved_cns_DELETE >>
    drule_then drule $ iffLR SUBSET_DEF >>
    strip_tac >> fs[] >>
    last_x_assum $ drule_then drule >>
    rw[] >>
    metis_tac[]
  ) >>
  pairarg_tac >>
  gvs[] >> every_case_tac >>
  gvs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS]
  >- (
    spose_not_then strip_assume_tac >>
    assume_tac monad_cns_SUBSET_reserved_cns_DELETE >>
    drule_then drule $ iffLR SUBSET_DEF >>
    strip_tac >>
    pairarg_tac >>
    gvs[FORALL_AND_THM,PULL_EXISTS,DISJ_IMP_THM] >>
    first_x_assum $ drule_then drule >>
    rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
    gvs[oEL_THM,MEM_MAP,PULL_EXISTS] >>
    irule_at Any $ iffRL MEM_EL >>
    simp[EXISTS_PROD] >>
    metis_tac[PAIR]
  ) >>
  simp[monad_cns_def]
QED

Theorem type_tcexp_tcexp_wf:
  tcexp_namespace_ok ns ⇒
  ∀db st env e t.
    type_tcexp ns db st env e t
  ⇒ tcexp_wf e
Proof
  Induct_on `type_tcexp` >>
  rw[tcexp_wf_def,EVERY_EL,LIST_REL_EL_EQN] >>
  simp[num_args_ok_def,num_monad_args_def,num_atomop_args_ok_def] >>
  simp[GSYM num_monad_args_def]
  >- (
    gvs[type_exception_def, oneline tcexp_namespace_ok_def,
      pair_CASE_def,ALL_DISTINCT_APPEND] >>
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, FORALL_PROD] >>
    last_x_assum $ drule_at Concl >> rw[] >>
    gvs[reserved_cns_def, implodeEQ,num_monad_args_def]
  )
  >- (
    gvs[tcexp_type_cons_def,oneline tcexp_namespace_ok_def] >>
    every_case_tac >>
    gvs[oEL_THM,ALL_DISTINCT_APPEND,MEM_MAP,EVERY_MEM,PULL_EXISTS,num_args_ok_def] >>
    drule_then strip_assume_tac monad_args_ok_SOME >>
    assume_tac monad_cns_SUBSET_reserved_cns_DELETE >>
    drule_then drule $ iffLR SUBSET_DEF >>
    strip_tac >>
    spose_not_then kall_tac >>
    drule_then strip_assume_tac monad_args_ok_SOME >>
    assume_tac monad_cns_SUBSET_reserved_cns_DELETE >>
    drule_then drule $ iffLR SUBSET_DEF >>
    strip_tac >>
    qpat_x_assum `!e. _ ⇒ ∀y. _ ⇒ ¬MEM y (FLAT (MAP _ _))` $
      qspec_then `cname` mp_tac >>
    fs[implodeEQ] >>
    drule ALOOKUP_SOME_EL >>
    rw[MEM_FLAT,MEM_MAP,MEM_EL,LAMBDA_PROD,
      GSYM PFORALL_THM,GSYM PEXISTS_THM] >>
    simp[PULL_EXISTS] >>
    first_x_assum $ irule_at (Pos last) o GSYM >>
    simp[] >>
    metis_tac[]
  )
  >- (
    gvs[] >>
    first_x_assum drule >>
    pairarg_tac >> gvs[]
  )
  >- (
    imp_res_tac get_PrimTys_SOME >>
    gvs[type_atom_op_cases,num_atomop_args_ok_def]
  )
  >- (Cases_on `es` >> gvs[])
  >- (Cases_on `xs` >> gvs[])
  >- (
    gvs[] >>
    first_x_assum drule >>
    first_x_assum drule >>
    ntac 2 (pairarg_tac >> gvs[EL_MAP])
  )
  >- (
    gvs[] >>
    first_x_assum drule >>
    pairarg_tac >> gvs[EL_MAP] >>
    rw[]
  )
  >- (
    gvs[] >>
    first_x_assum drule >>
    pairarg_tac >> gvs[EL_MAP] >>
    rw[]
  )
  >- (
    Cases_on `css` >> simp[] >>
    gvs[tcexp_get_cases_def] >>
    gvs[oneline tcexp_namespace_ok_def] >>
    every_case_tac >> gvs[ELIM_UNCURRY] >>
    every_case_tac >> gvs[oEL_THM,EVERY_EL] >>
    Cases_on `usopt` >> gvs[] >>
    metis_tac[PAIR]
  )
  >- (
    first_x_assum drule >>
    pairarg_tac >> gvs[] >>
    rw[EL_MAP]
  )
  >- (
    Cases_on `usopt` >> gvs[] >>
    pairarg_tac >> gvs[] >>
    rw[] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >>
    rw[] >>
    drule_then strip_assume_tac ALOOKUP_MEM >>
    drule_then (drule_then drule)
      tcexp_namespace_ok_get_cases_not_monad_cns >>
    simp[]
  )
  >- (
    strip_tac >>
    gvs[MEM_FLAT,MEM_MAP] >>
    gvs[MEM_EL] >>
    first_x_assum drule >>
    pairarg_tac >> strip_tac >> gvs[]
  )
  >- (
    simp[ALL_DISTINCT_APPEND] >>
    CASE_TAC
    >- (rw[] >> gvs[]) >>
    CASE_TAC >>
    gvs[ALL_DISTINCT_APPEND]
  ) >>
  drule_then (drule_then (irule o SRULE[FORALL_PROD]))
    tcexp_namespace_ok_get_cases_not_monad_cns >>
  Cases_on `usopt`
  >- (
    gvs[IN_DEF,LIST_TO_SET_MAP] >>
    metis_tac[PAIR]
  ) >>
  gvs[] >>
  first_x_assum $ resolve_then (Pos hd) strip_assume_tac
    $ GSYM PAIR >>
  gvs[IN_DEF,LIST_TO_SET_MAP] >>
  `IMAGE FST (set css) ⊆ IMAGE FST (set constructors)`
    by metis_tac[SUBSET_UNION] >>
  `(FST x') ∈ IMAGE FST (set css)`
  suffices_by (
    strip_tac >>
    drule_then drule $ iffLR SUBSET_DEF >>
    simp[IN_DEF] >>
    metis_tac[PAIR]
  ) >>
  simp[IN_DEF] >> metis_tac[]
QED

Theorem tcexp_type_cepat_cepat_vars:
  tcexp_type_cepat ns db p t vts ⇒ cepat_vars p = set (MAP FST vts)
Proof
  Induct_on `tcexp_type_cepat` >>
  rw[cepat_vars_def] >>
  pop_assum mp_tac >>
  Induct_on `LIST_REL3` using LIST_REL3_induct >>
  rw[]
QED

Theorem type_tcexp_freevars_tcexp:
  ∀db st env e t.
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
  >- (
    first_x_assum drule >>
    pairarg_tac >> gvs[] >>
    rw[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_THM]
  )
  >- gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
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
    gvs[GSYM SUBSET_INSERT_DELETE, BIGUNION_SUBSET, DIFF_SUBSET,
      MEM_MAP, PULL_EXISTS, FORALL_PROD, EVERY_MEM] >>
    rw[]
    >- (
      drule_then assume_tac tcexp_type_cepat_cepat_vars >>
      gvs[MAP_REVERSE,MAP_MAP_o] >>
      irule SUBSET_TRANS >>
      last_x_assum $ irule_at (Pos hd) >>
      irule $ cj 1 EQ_SUBSET_SUBSET >>
      AP_THM_TAC >> AP_TERM_TAC >>
      AP_TERM_TAC >>
      irule LIST_EQ >>
      rw[EL_MAP] >>
      pairarg_tac >>
      simp[]
    ) >>
    last_x_assum $ drule_then strip_assume_tac >>
    drule tcexp_type_cepat_cepat_vars >>
    rw[] >>
    drule_then irule $ METIS_PROVE [] ``∀a b c. a ⊆ b ∧ b = c ⇒ a ⊆ c`` >>
    AP_THM_TAC >> AP_TERM_TAC >>
    rw[EXTENSION,MEM_MAP,MEM_REVERSE,EQ_IMP_THM] >>
    first_assum $ irule_at (Pos last) >>
    simp[ELIM_UNCURRY]
  )
  >- (
    rpt TOP_CASE_TAC >>
    gvs[GSYM SUBSET_INSERT_DELETE, BIGUNION_SUBSET, DIFF_SUBSET,
      MEM_MAP, PULL_EXISTS, FORALL_PROD, EVERY_MEM] >>
    rw[] >> first_x_assum drule >> rw[] >>
    gvs[MAP_REVERSE, MAP_ZIP, DIFF_SUBSET, GSYM SUBSET_INSERT_DELETE]
  )
QED

Theorem type_tcexp_env_extensional:
  ∀db st env e t env'.
    type_tcexp ns db st env e t ∧
    (∀x. x ∈ freevars_tcexp e ⇒ ALOOKUP env x = ALOOKUP env' x)
  ⇒ type_tcexp ns db st env' e t
Proof
  Induct_on `type_tcexp` >> rw[] >> rw[Once type_tcexp_cases] >>
  rpt $ first_assum $ irule_at Any >> rw[ALOOKUP_MAP]
  >- (
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    disj1_tac >>
    irule_at (Pos hd) EQ_REFL >>
    rw[] >>
    first_x_assum drule >> rw[] >>
    first_x_assum irule >> rw[] >>
    first_x_assum irule >>
    first_x_assum $ irule_at (Pos hd) >>
    simp[EL_MEM]
    )
  >- (
    disj1_tac >>
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum $ irule_at (Pos last) >>
    first_x_assum $ irule_at (Pos last) >>
    rw[]
    )
  >- (
    disj1_tac >>
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum $ irule_at (Pos last) >>
    rw[]
    )
  >- (
    disj1_tac >>
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum $ irule_at (Pos last) >>
    rw[]
    )
  >- (
    disj2_tac >> disj1_tac >>
    gvs[LIST_REL_EL_EQN, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum $ irule_at (Pos last) >>
    rw[] >>
    first_x_assum $ irule o cj 2 >>
    rw[] >>
    metis_tac[MEM_EL]
    )
  >- (
    rpt disj2_tac >>
    irule_at (Pos hd) EQ_REFL >>
    first_x_assum $ irule_at (Pos last) >>
    gvs[PULL_EXISTS,ALOOKUP_APPEND,LIST_REL_EL_EQN] >>
    rw[] >>
    pairarg_tac >> gvs[] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum irule >>
    rw[ALOOKUP_MAP] >>
    AP_TERM_TAC >>
    gvs[MEM_MAP,PULL_EXISTS] >>
    metis_tac[MEM_EL]
    )
  >- (
    gvs[LIST_REL_EL_EQN,PULL_EXISTS] >>
    rw[] >>
    first_x_assum $ drule_then (irule o cj 2) >>
    rw[] >>
    gvs[MEM_MAP,PULL_EXISTS] >>
    metis_tac[MEM_EL]
  )
  >- (
    gvs[LIST_REL_EL_EQN,PULL_EXISTS] >>
    rw[] >>
    first_x_assum $ drule_then (irule o cj 2) >>
    rw[] >>
    gvs[MEM_MAP,PULL_EXISTS] >>
    metis_tac[MEM_EL]
  )
  >- (
    rw[ALOOKUP_APPEND] >>
    TOP_CASE_TAC >>
    gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP]
  )
  >- (
    rw[ALOOKUP_APPEND] >>
    TOP_CASE_TAC >>
    gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP,LIST_REL_EL_EQN]
  )
  >- (
    gvs[LIST_REL_EL_EQN] >>
    rw[] >>
    ntac 2 (pairarg_tac >> gvs[]) >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum irule >>
    rw[ALOOKUP_APPEND,ALOOKUP_MAP,oneline OPTION_MAP_DEF] >>
    CASE_TAC >>
    gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
    ntac 2 AP_THM_TAC >>
    AP_TERM_TAC >>
    first_x_assum irule >>
    rw[] >>
    disj2_tac >>
    first_assum $ irule_at (Pos hd) >>
    gvs[MEM_MAP,MEM_EL,EXISTS_PROD] >>
    metis_tac[]
  )
  >- (
    drule_then strip_assume_tac tcexp_type_cepat_cepat_vars >>
    gvs[ALOOKUP_APPEND,EVERY_MEM] >>
    TOP_CASE_TAC >>
    TOP_CASE_TAC >>
    first_x_assum irule >>
    gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP,MAP_MAP_o,
      combinTheory.o_DEF,ELIM_UNCURRY] >>
    gvs[SF ETA_ss]
  )
 >- (
    gvs[EVERY_MEM] >>
    rw[] >>
    pairarg_tac >> gvs[] >>
    first_x_assum drule >>
    rw[] >>
    first_assum $ irule_at (Pos hd) >>
    first_assum $ irule_at (Pos hd) >>
    rw[ALOOKUP_APPEND] >>
    TOP_CASE_TAC >>
    first_x_assum irule >>
    gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_MAP_o,
      combinTheory.o_DEF,ELIM_UNCURRY] >>
    disj2_tac >> disj2_tac >>
    gvs[MEM_MAP,PULL_EXISTS] >>
    first_assum $ irule_at (Pos last) >>
    drule_then strip_assume_tac tcexp_type_cepat_cepat_vars >>
    gvs[MEM_MAP]
  )
 >- (
    gvs[EVERY_MEM] >>
    rw[] >>
    pairarg_tac >> gvs[] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum $ irule_at (Pos hd) >>
    first_x_assum $ irule_at (Pos hd) >>
    rw[] >>
    first_x_assum irule >>
    rw[ALOOKUP_APPEND] >>
    TOP_CASE_TAC >>
    gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
    first_x_assum irule >>
    gvs[] >>
    disj2_tac >> disj2_tac >>
    gvs[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
    first_x_assum $ irule_at (Pos last) >>
    simp[]
  )
QED

Theorem tcexp_type_cons_db_APPEND:
  tcexp_type_cons tds db c t ⇒
  tcexp_type_cons tds (db ++ db') c t
Proof
  simp[oneline tcexp_type_cons_def] >>
  rpt TOP_CASE_TAC >>
  rw[] >>
  fs[LIST_REL_EL_EQN] >>
  metis_tac[kind_ok_APPEND]
QED

Theorem tcexp_destruct_type_cons_db_APPEND:
  tcexp_destruct_type_cons ns db t c ts ⇒
  tcexp_destruct_type_cons ns (db ++ db') t c ts
Proof
  rw[oneline tcexp_destruct_type_cons_def] >>
  every_case_tac >> gvs[] >>
  every_case_tac >>
  metis_tac[tcexp_type_cons_db_APPEND]
QED

Theorem tcexp_type_cepat_db_APPEND:
  ∀p t vts.
    tcexp_type_cepat ns db p t vts ⇒
    tcexp_type_cepat ns (db ++ db') p t vts
Proof
  ho_match_mp_tac tcexp_type_cepat_ind >>
  rw[] >>
  simp[Once tcexp_type_cepat_cases] >>
  fs[SF ETA_ss] >>
  metis_tac[specialises_db_APPEND,tcexp_destruct_type_cons_db_APPEND]
QED

Theorem type_tcexp_weaken:
  ∀ns db st env e t db' st' env'.
    type_tcexp ns db st env e t
  ⇒ type_tcexp ns (db ++ db') (st ++ st') (env ++ env') e t
Proof
  ntac 3 gen_tac >>
  Induct_on `type_tcexp` >> rw[] >> rw[Once type_tcexp_cases]
  >- (
    simp[ALOOKUP_APPEND] >> PairCases_on `s` >> gvs[specialises_def] >>
    qexists_tac `subs` >> gvs[] >>
    irule LIST_REL_mono >> rw[] >> goal_assum $ drule_at Any >> rw[] >>
    drule kind_ok_APPEND >> simp[]
    )
  >- (
    disj1_tac >>
    irule_at (Pos hd) EQ_REFL >>
    gvs[LIST_REL_EL_EQN]
  )
  >- metis_tac[]
  >- (
    disj1_tac >> gvs[type_ok_def] >>
    drule kind_ok_APPEND >> simp[]
  )
  >- metis_tac[]
  >- metis_tac[]
  >- (
    disj2_tac >> disj1_tac >>
    goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN]
  )
  >- (
    rpt disj2_tac >>
    irule_at (Pos hd) EQ_REFL >>
    drule_then (irule_at (Pos last)) tcexp_type_cons_db_APPEND >>
    gvs[LIST_REL_EL_EQN] >>
    rw[] >>
    pairarg_tac >> gvs[] >>
    first_x_assum drule >>
    gvs[]
    )
  >- gvs[oEL_THM, EL_APPEND_EQN]
  >- (ntac 2 $ goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN])
  >- metis_tac[]
  >- (rpt $ goal_assum $ drule_at Any >> gvs[LIST_REL_EL_EQN])
  >- (
    irule_at Any EQ_REFL >> simp[] >>
    irule EVERY_MONOTONIC >> goal_assum $ drule_at Any >> rw[] >>
    gvs[type_ok_def] >>
    drule kind_ok_APPEND >> simp[]
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
      pairarg_tac >> gvs[type_ok_def] >> drule kind_ok_APPEND >> simp[]
      )
    )
  >- (
    first_assum (irule_at (Pos hd)) >>
    drule_then (irule_at (Pos hd)) tcexp_type_cepat_db_APPEND >>
    PURE_REWRITE_TAC[cj 2 $ GSYM APPEND] >>
    PURE_REWRITE_TAC[APPEND_ASSOC] >>
    first_x_assum $ irule_at (Pos hd) >>
    rw[EVERY_MEM] >>
    pairarg_tac >> gvs[EVERY_MEM] >>
    first_x_assum drule >>
    rw[] >>
    drule_then (irule_at (Pos hd)) tcexp_type_cepat_db_APPEND >>
    first_x_assum irule
  )
  >- (
    first_x_assum $ irule_at (Pos hd) >>
    gvs[EVERY_MEM] >>
    rw[] >>
    first_x_assum drule >>
    pairarg_tac >> gvs[] >>
    rw[] >>
    drule_then (irule_at Any) tcexp_destruct_type_cons_db_APPEND >>
    PURE_REWRITE_TAC[cj 2 $ GSYM APPEND] >>
    PURE_REWRITE_TAC[APPEND_ASSOC] >>
    first_x_assum (irule_at (Pos last)) >>
    gvs[LIST_REL_EL_EQN] >>
    metis_tac[specialises_db_APPEND]
  )
  >- (
    drule_then (irule_at Any) tcexp_destruct_type_cons_db_APPEND >>
    simp[specialises_db_APPEND]
  )
QED

Theorem type_tcexp_generalise_env:
  ∀db st env e t env'.
    type_tcexp ns db st env e t ∧
    (∀x sch. x ∈ freevars_tcexp e ∧ ALOOKUP env x = SOME sch ⇒
       ∃sch'. ALOOKUP env' x = SOME sch' ∧
              (∀n t . specialises (SND ns) (n ++ db)
                        (tshift_kind_scheme (LENGTH n) sch) t
                  ⇒ specialises (SND ns) (n ++ db)
                      (tshift_kind_scheme (LENGTH n) sch') t))
  ⇒ type_tcexp ns db st env' e t
Proof
  Induct_on `type_tcexp` >> rw[] >> simp[Once type_tcexp_cases]
  >- (
    first_x_assum $ qspec_then `[]` mp_tac >> simp[] >>
    gvs[ELIM_UNCURRY]
    )
  >- (
    gvs[MEM_EL, EL_MAP, PULL_EXISTS, LIST_REL_EL_EQN, SF CONJ_ss] >>
    metis_tac[]
    )
  >- (disj1_tac >> rpt $ first_x_assum $ irule_at Any >> simp[])
  >- (disj1_tac >> rpt $ first_x_assum $ irule_at Any >> simp[])
  >- (disj1_tac >> rpt $ first_x_assum $ irule_at Any >> simp[])
  >- (
    disj2_tac >> disj1_tac >> rpt $ first_x_assum $ irule_at Any >>
    gvs[LIST_REL_EL_EQN] >>
    rpt strip_tac >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum irule >>
    rw[] >>
    gvs[MEM_MAP,PULL_EXISTS] >>
    first_x_assum drule >>
    rw[MEM_EL,PULL_EXISTS] >>
    first_x_assum drule >>
    metis_tac[]
  )
  >- (
    rpt disj2_tac >>
    irule_at (Pos hd) EQ_REFL >>
    first_x_assum $ irule_at (Pos last) >>
    gvs[LIST_REL_EL_EQN] >>
    rw[] >>
    first_x_assum drule >>
    pairarg_tac >> gvs[PULL_EXISTS,MEM_MAP] >>
    rw[] >>
    first_x_assum irule >>
    rw[] >>
    first_x_assum drule >>
    rw[MEM_EL,PULL_EXISTS] >>
    first_x_assum drule >>
    rw[] >>
    gvs[ALOOKUP_MAP,ELIM_UNCURRY,shift_db_twice] >>
    gvs[specialises_def,PULL_EXISTS] >>
    rw[] >>
    first_x_assum drule >>
    rw[LENGTH_APPEND]
  )
  >- (
    rpt $ first_x_assum $ irule_at Any >> simp[] >>
    gvs[LIST_REL_EL_EQN,PULL_EXISTS] >>
    rw[] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum irule >>
    rw[] >>
    gvs[MEM_MAP,PULL_EXISTS,MEM_EL] >>
    first_x_assum $ drule_then drule >>
    rw[]
  )
  >- (
    rpt $ first_assum $ irule_at Any >>
    rw[ALOOKUP_MAP,PULL_EXISTS] >>
    first_assum $ resolve_then (Pos hd) mp_tac OR_INTRO_THM1 >>
    disch_then $ drule_all_then strip_assume_tac >>
    gvs[ELIM_UNCURRY,shift_db_twice,GSYM $ LENGTH_APPEND,Excl"LENGTH_APPEND"]
  )
  >- (
    gvs[MEM_EL, EL_MAP, PULL_EXISTS, LIST_REL_EL_EQN, SF CONJ_ss] >>
    metis_tac[]
    )
  >- (
    irule_at (Pos hd) EQ_REFL >>
    gvs[lambdify type_ok_def] >>
    first_x_assum irule >>
    rw[] >>
    gvs[ALOOKUP_APPEND] >>
    TOP_CASE_TAC >> gvs[] >>
    gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP]
  )
  >- (
    rpt $ first_x_assum $ irule_at Any >> simp[] >>
    rw[] >>
    gvs[ALOOKUP_MAP,PULL_EXISTS] >>
    first_x_assum $ drule_at (Pos $ el 2) >>
    rw[] >>
    rw[] >>
    first_x_assum $ qspec_then `n ++ new` mp_tac >>
    gvs[shift_db_twice,ELIM_UNCURRY]
  )
  >- (
    rpt $ first_x_assum $ irule_at Any >> simp[] >>
    gvs[LIST_REL_EL_EQN] >>
    rw[]
    >- (
      gvs[ALOOKUP_APPEND,PULL_EXISTS] >>
      TOP_CASE_TAC >> gvs[] >>
      gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP]
    )
    >- (
      ntac 2 (pairarg_tac >> gvs[]) >>
      first_x_assum drule >>
      rw[] >>
      first_x_assum irule >>
      rw[] >>
      gvs[ALOOKUP_MAP,ALOOKUP_APPEND,AllCaseEqs(),PULL_EXISTS,
        ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP,MEM_MAP] >>
      first_x_assum $ drule_at (Pos last) >>
      impl_tac
      >- (
        gvs[EXISTS_PROD,FORALL_PROD] >>
        rw[]
        >- (
          disj2_tac >>
          first_x_assum $ irule_at Any >>
          metis_tac[MEM_EL]
        ) >>
        strip_tac >>
        qpat_x_assum `!p1 p2. ¬ MEM _ (ZIP (MAP _ _,_))` mp_tac >>
        simp[ZIP_MAP,MEM_MAP,MEM_ZIP] >>
        gvs[MEM_EL] >>
        first_assum $ irule_at (Pos hd) >>
        simp[EL_MAP] >>
        metis_tac[PAIR,FST]
      ) >>
      rw[PULL_EXISTS] >>
      irule_at (Pos hd) OR_INTRO_THM1 >>
      irule_at (Pos hd) EQ_REFL >>
      rw[] >>
      gvs[ELIM_UNCURRY,shift_db_twice,Excl"LENGTH_APPEND",GSYM LENGTH_APPEND]
    )
  )
  >- (
    rpt $ first_assum $ irule_at Any >> simp[] >>
    gvs[EVERY_MEM] >>
    rw[]
    >- (
      gvs[ALOOKUP_APPEND,PULL_EXISTS] >>
      TOP_CASE_TAC >> gvs[] >>
      gvs[ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP] >>
      IF_CASES_TAC >> rw[] >>
      gvs[] >>
      first_x_assum $ drule_at (Pos last) >>
      rw[MEM_MAP,EXISTS_PROD] >>
      first_x_assum irule >>
      drule_then strip_assume_tac tcexp_type_cepat_cepat_vars >>
      gvs[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,SF ETA_ss]
     ) >>
     pairarg_tac >> gvs[] >>
     first_x_assum drule >>
     rw[] >>
     rpt $ first_assum $ irule_at Any >> simp[] >>
     rw[] >>
     gvs[ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE,MAP_REVERSE,MAP_MAP_o]
     >- (
      irule_at (Pos hd) OR_INTRO_THM1 >>
      rw[]
     ) >>
     irule_at (Pos hd) OR_INTRO_THM1 >>
     rw[] >>
     first_x_assum irule >>
     rw[] >>
     disj2_tac >> disj2_tac >>
     simp[PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
     first_assum $ irule_at (Pos last) >>
     drule_then strip_assume_tac tcexp_type_cepat_cepat_vars >>
     gvs[IN_DEF,MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY,SF ETA_ss]
  )
  >- (
    rpt $ first_assum $ irule_at Any >> simp[] >>
    rw[]
    >- (first_x_assum irule >> rw[]) >>
    gvs[EVERY_MEM] >>
    rw[] >>
    pairarg_tac >> gvs[] >>
    first_x_assum drule >>
    rw[] >>
    rpt $ first_assum $ irule_at Any >>
    rw[ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP]
    >- (irule_at (Pos hd) OR_INTRO_THM1 >> rw[])
    >- (
      simp[] >>
      irule_at (Pos hd) OR_INTRO_THM1 >>
      first_x_assum $ drule_at_then (Pos last) irule >>
      gvs[MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
      disj2_tac >> disj2_tac >>
      first_x_assum $ irule_at (Pos last) >>
      simp[]
    )
    >- (
      irule_at (Pos hd) OR_INTRO_THM2 >>
      drule ALOOKUP_MEM >>
      rw[MEM_REVERSE,MEM_ZIP]
    )
  )
  >- (rpt $ first_assum $ irule_at Any >> simp[])
QED

(******************** Substitutions ********************)

Theorem get_PrimTys_freetyvasrs_ok:
  get_PrimTys ts = SOME pts ∧ MEM t ts ⇒
  freetyvars_ok 0 t
Proof
  rw[get_PrimTys_SOME] >>
  gvs[MEM_MAP,freetyvars_ok_def]
QED

Theorem tcexp_namespace_ok_MEM_IMP_type_scheme_ok:
  tcexp_namespace_ok (exns,tds) ∧
  LLOOKUP tds tyid = SOME (argks,constructors) ∧
  MEM (cname,ts) constructors ∧
  MEM t ts ⇒
  type_scheme_ok tds argks t
Proof
  rw[tcexp_namespace_ok_def,oEL_THM] >>
  rw[] >>
  gvs[EVERY_EL] >>
  qpat_x_assum `!n. _ < LENGTH tds ⇒ _` drule >>
  pairarg_tac >> rw[] >>
  gvs[MEM_EL] >>
  rpt $ qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
  rw[] >>
  first_x_assum drule >>
  rw[]
QED

Theorem tcexp_namespace_ok_ALOOKUP_IMP_type_scheme_ok:
  tcexp_namespace_ok (exns,tds) ∧
  LLOOKUP tds tyid = SOME (argks,constructors) ∧
  ALOOKUP constructors cname = SOME ts ∧
  MEM t ts ⇒
  type_scheme_ok tds argks t
Proof
  metis_tac[ALOOKUP_MEM,
    tcexp_namespace_ok_MEM_IMP_type_scheme_ok]
QED

Theorem type_scheme_ok_IMP_freetyvars_ok:
  type_scheme_ok tds aks (ks,t) ⇒
  freetyvars_ok (LENGTH ks + LENGTH aks) t
Proof
  rw[type_scheme_ok_def] >>
  metis_tac[kind_ok_IMP_freetyvars_ok,LENGTH_APPEND,ADD_COMM]
QED

Theorem shift_db_skip_tshift_shift:
  shift_db n m (tshift n x) = tshift (n + m) x
Proof
  qspecl_then [`0`,`m`,`x`,`0`,`n`]
    assume_tac shift_db_shift_db >>
  gvs[shift_db_twice]
QED

Theorem tcexp_type_cons_subst_db:
  tcexp_namespace_ok (exds,tds) ∧
  tcexp_type_cons tds db (cname,carg_ts) (tyid,tyargs) ∧
  db = db'1 ++ tks ++ db'2 /\
  LIST_REL (kind_ok tds db') tks ts ∧
  db' = db'1 ++ db'2 ∧
  n = LENGTH db'1 ⇒
    tcexp_type_cons tds db' (cname,
      MAP (λ(ks,t). (ks,
        subst_db (n + LENGTH ks)
          (MAP (tshift (LENGTH ks)) ts)
          t)) carg_ts)
      (tyid,MAP (subst_db n ts) tyargs)
Proof
  rw[tcexp_type_cons_def] >>
  gvs[LIST_REL_EL_EQN] >>
  rw[EL_MAP]
  >- (
    irule kind_ok_subst_db_APPEND >>
    rw[LIST_REL_EL_EQN] >>
    metis_tac[]
  ) >>
  drule_then (drule_then drule) $
    tcexp_namespace_ok_ALOOKUP_IMP_type_scheme_ok >>
  rw[MEM_EL,PULL_EXISTS] >>
  irule LIST_EQ >>
  rw[EL_MAP] >>
  pairarg_tac >> rw[] >>
  simp[MAP_MAP_o,combinTheory.o_DEF] >>
  DEP_ONCE_REWRITE_TAC[subst_db_subst_db] >>
  simp[MAP_MAP_o,combinTheory.o_DEF] >>
  first_x_assum $ drule_then strip_assume_tac >>
  gvs[] >>
  drule_then assume_tac type_scheme_ok_IMP_freetyvars_ok >>
  drule subst_db_unchanged >>
  rw[] >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[LIST_EQ_REWRITE,EL_MAP] >>
  simp[subst_db_shift_db_1]
QED

Theorem type_exception_subst_db:
  tcexp_namespace_ok (exds,tds) ∧
  type_exception exds (c,ts) ⇒
  type_exception exds
    (c, MAP (subst_db n ts') ts)
Proof
  gvs[type_exception_def] >>
  rw[LIST_EQ_REWRITE,EL_MAP] >>
  drule_then strip_assume_tac ALOOKUP_SOME_EL >>
  gvs[tcexp_namespace_ok_def,EVERY_EL] >>
  first_x_assum drule >>
  rw[] >>
  first_x_assum drule >>
  rw[type_ok_def,EL_MAP] >>
  drule_then assume_tac kind_ok_IMP_freetyvars_ok  >>
  gvs[] >>
  irule EQ_SYM >>
  irule subst_db_unchanged >>
  first_assum $ irule_at (Pat `freetyvars_ok _ _`) >>
  simp[]
QED

Triviality cons_types_not_Exception:
  cons_types (Atom $ TypeCons c) l ≠ Atom Exception
Proof
  rw[cons_types_EQ_Atom]
QED

Theorem tcexp_destruct_type_cons_subst_db:
  tcexp_namespace_ok ns ∧
  tcexp_destruct_type_cons ns (db'1 ++ tks ++ db'2) t c carg_tys ∧
  LIST_REL (kind_ok (SND ns) (db'1 ++ db'2)) tks ts ⇒
  tcexp_destruct_type_cons ns (db'1 ++ db'2)
    (subst_db (LENGTH db'1) ts t) c $
    MAP (subst_db_kind_scheme (LENGTH db'1) ts) carg_tys
Proof
  Cases_on `ns` >> rw[] >>
  gvs[tcexp_destruct_type_cons_def,
    split_ty_cons_thm,head_ty_cons_eq_head_ty] >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  IF_CASES_TAC >>
  rw[]
  >- (
    simp[subst_db_def,EVERY_EL,EL_MAP,MAP_MAP_o,LAMBDA_PROD,
      combinTheory.o_DEF,head_ty_def] >>
    drule_all_then (irule_at Any) type_exception_subst_db >>
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    irule_at Any EQ_REFL
  )
  >- gvs[subst_db_def] >>
  `t = cons_types (Atom $ TypeCons tc') (ty_args t)` by
    metis_tac[cons_types_head_ty_ty_args] >>
  pop_assum SUBST_ALL_TAC >>
  gvs[subst_db_cons_types,cons_types_not_Exception,
    subst_db_def,head_ty_cons_types,ty_args_cons_types,
    ty_args_alt] >>
  every_case_tac >>
  gvs[MAP_MAP_o,combinTheory.o_DEF]
  >- (
    drule_then (drule_then irule) tcexp_type_cons_subst_db >>
    metis_tac[]
  )
QED

Triviality APPEND_ASSOC_four:
  ks ++ db1 ++ tks ++ db2 = (ks ++ db1) ++ tks ++ db2
Proof
  metis_tac[APPEND_ASSOC]
QED

Theorem specialises_subst_db:
  specialises tds (db'1 ++ tks ++ db'2) s t ∧
  LIST_REL (kind_ok tds (db'1 ++ db'2)) tks ts ⇒
  specialises tds (db'1 ++ db'2)
    (subst_db_kind_scheme (LENGTH db'1) ts s)
    (subst_db (LENGTH db'1) ts t)
Proof
  PairCases_on `s` >> gvs[specialises_def,LIST_REL_EL_EQN] >>
  rw[] >>
  imp_res_tac EVERY2_LENGTH >>
  rw[subst_db_subst_db] >>
  irule_at (Pos last) EQ_REFL >> rw[] >>
  rw[EL_MAP] >>
  gvs[] >>
  first_x_assum drule >>
  strip_tac >>
  drule_then irule kind_ok_subst_db_APPEND >>
  metis_tac[LIST_REL_EL_EQN]
QED

Theorem tcexp_type_cepat_subst_db:
  ∀p pt vts.
  tcexp_type_cepat ns (db'1 ++ tks ++ db'2) p pt vts ∧
  tcexp_namespace_ok ns ∧
  LIST_REL (kind_ok (SND ns) (db'1 ++ db'2)) tks ts ⇒
  tcexp_type_cepat ns (db'1 ++ db'2) p
    (subst_db_kind_scheme (LENGTH db'1) ts pt)
    (MAP (λ(v,t). (v,subst_db (LENGTH db'1) ts t)) vts)
Proof
  Induct_on `tcexp_type_cepat` >>
  rw[]
  >- (
    irule tcexp_type_cepat_Var >>
    metis_tac[specialises_subst_db]
  )
  >- irule tcexp_type_cepat_UScore
  >- (
    simp[MAP_FLAT] >>
    irule tcexp_type_cepat_Cons >>
    gvs[LIST_REL3_EL,EL_MAP] >>
    drule_then (drule_then $ irule_at Any)
      tcexp_destruct_type_cons_subst_db >>
    rw[EL_MAP]
  )
QED

Theorem tcexp_get_cases_subst_db:
  tcexp_namespace_ok ns ∧
  tcexp_get_cases ns t = SOME ctys ⇒
  tcexp_get_cases ns (subst_db n db t) =
    SOME (MAP (I ##
      (MAP (λ(ks,t).
        (ks,
        subst_db (n + LENGTH ks)
          (MAP (tshift (LENGTH ks)) db)
          t)))) ctys)
Proof
  Cases_on `ns` >>
  gvs[tcexp_get_cases_def] >>
  IF_CASES_TAC
  >- (
    rw[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
      subst_db_def] >>
    rw[LIST_EQ_REWRITE,EL_MAP,PAIR_MAP] >>
    gvs[tcexp_namespace_ok_def,MAP_EQ_f] >>
    drule_then drule $ iffLR EVERY_EL >>
    pairarg_tac >>
    rw[] >>
    gvs[] >>
    drule_then drule $ iffLR EVERY_EL >>
    rw[type_ok] >>
    drule kind_ok_IMP_freetyvars_ok >>
    rw[] >>
    irule $ GSYM subst_db_unchanged >>
    first_assum $ irule_at (Pat `freetyvars_ok _ _`) >>
    simp[]
  ) >>
  CASE_TAC
  >- (
    rw[EXISTS_PROD,split_ty_cons_thm,
      head_ty_cons_eq_head_ty] >>
    qspec_then `t` assume_tac $
      GSYM $ GEN_ALL cons_types_head_ty_ty_args >>
    pop_assum SUBST_ALL_TAC >>
    gvs[subst_db_cons_types,subst_db_def,head_ty_cons_types,
      cons_types_not_Exception,head_ty_def]
  ) >>
  rw[EXISTS_PROD] >>
  every_case_tac >>
  gvs[EXISTS_PROD,split_ty_cons_thm,head_ty_cons_eq_head_ty,
    subst_db_head_ty,subst_db_ty_args,MAP_MAP_o,
    combinTheory.o_DEF,LAMBDA_PROD] >>
  rw[MAP_EQ_f] >>
  pairarg_tac >> simp[] >>
  rw[MAP_EQ_f] >>
  pairarg_tac >>
  simp[subst_db_subst_db,MAP_MAP_o,combinTheory.o_DEF,
    subst_db_shift_db_1] >>
  AP_TERM_TAC >>
  irule $ GSYM subst_db_unchanged >>
  drule_all_then assume_tac
    tcexp_namespace_ok_MEM_IMP_type_scheme_ok >>
  gvs[] >>
  drule_then (irule_at Any) type_scheme_ok_IMP_freetyvars_ok >>
  simp[]
QED

Theorem tcexp_exhaustive_cepat_subst_db:
  tcexp_namespace_ok ns ⇒
  (∀t ps.
    tcexp_exhaustive_cepat ns t ps ⇒
    ∀n db. tcexp_exhaustive_cepat ns
      (subst_db_kind_scheme n db t) ps) ∧
  (∀ts pss.
    tcexp_exhaustive_cepatl ns ts pss ⇒
    ∀n db. tcexp_exhaustive_cepatl ns
      (MAP (subst_db_kind_scheme n db) ts) pss)
Proof
  strip_tac >>
  ho_match_mp_tac tcexp_exhaustive_cepat_ind >>
  rw[]
  >- metis_tac[tcexp_exhaustive_cepat_Var]
  >- metis_tac[tcexp_exhaustive_cepat_UScore]
  >- (
    Cases_on `ns` >>
    irule tcexp_exhaustive_cepat_Cons >>
    drule_all_then (irule_at Any)
      tcexp_get_cases_subst_db >>
    rw[MEM_MAP,EXISTS_PROD] >>
    first_x_assum drule >>
    rw[] >>
    metis_tac[]
  )
  >- metis_tac[tcexp_exhaustive_cepat_Nil]
  >- (
    irule tcexp_exhaustive_cepat_List >>
    first_x_assum $ irule_at (Pos hd) >>
    gvs[]
  )
QED

Theorem LIST_REL_kind_ok_tshift:
  LIST_REL (kind_ok tds db) tks ts ⇒
  LIST_REL (kind_ok tds (new ++ db)) tks (MAP (tshift (LENGTH new)) ts)
Proof
  rw[LIST_REL_EL_EQN,EL_MAP] >>
  gvs[] >>
  first_x_assum $ drule_then assume_tac >>
  irule kind_ok_shift_db_APPEND >>
  gvs[] >>
  metis_tac[]
QED

Theorem type_tcexp_subst_db:
  tcexp_namespace_ok ns ⇒
  ∀db st env e t n db' db'1 tks db'2 ts.
    type_tcexp ns db st env e t ∧
    db = db'1 ++ tks ++ db'2 ∧
    db' = db'1 ++ db'2 ∧
    LIST_REL (kind_ok (SND ns) db') tks ts ∧
    n = LENGTH db'1
  ⇒ type_tcexp ns db'
      (MAP (subst_db n ts) st)
      (MAP (λ(s,scheme). (s, subst_db_kind_scheme n ts scheme)) env)
      e
      (subst_db n ts t)
Proof
  strip_tac >>
  Induct_on `type_tcexp` >> rw[subst_db_def] >> rw[Once type_tcexp_cases]
  >- (
    simp[ALOOKUP_MAP] >>
    metis_tac[specialises_subst_db]
  )
  >- (
    disj1_tac >>
    gvs[LIST_REL_EL_EQN,EL_MAP,subst_db_cons_types,subst_db_def] >>
    qexists_tac `MAP (subst_db (LENGTH db'1) ts') ts` >>
    rw[EL_MAP]
  )
  >- (
    disj1_tac >>
    rpt $ first_assum $ irule_at Any >> gvs[subst_db_Functions,subst_db_def]
  )
  >- (
    disj1_tac >>
    gvs[type_ok_def] >>
    drule_then irule kind_ok_subst_db_APPEND >>
    metis_tac[]
  )
  >- (
    disj1_tac >>
    gvs[subst_db_Functions,subst_db_def]
  )
  >- (
    disj1_tac >>
    first_x_assum $ irule_at Any >>
    rw[]
  )
  >- (
    disj1_tac >>
    rpt $ first_assum $ irule_at Any >>
    rw[]
  )
  >- (
    disj2_tac >> disj1_tac >>
    rpt $ first_assum $ irule_at Any >>
    gvs[LIST_REL_EL_EQN,oneline tcexp_namespace_ok_def,pair_CASE_def] >>
    rw[] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum $ resolve_then (Pos hd) drule EQ_REFL >>
    rw[] >>
    gvs[EVERY_MEM,type_exception_def] >>
    drule_then strip_assume_tac ALOOKUP_MEM >>
    first_x_assum drule >>
    rw[PULL_EXISTS,MEM_EL] >>
    first_x_assum drule >>
    rw[type_ok_def] >>
    drule_then strip_assume_tac kind_ok_IMP_freetyvars_ok >>
    gvs[] >>
    `subst_db (LENGTH db'1) ts (EL n earg_ts) = EL n earg_ts`
    by (
      drule_then irule subst_db_unchanged >>
      simp[]
    ) >>
    gvs[]
  )
  >- (
    rpt disj2_tac >>
    simp[subst_db_tcons_to_type] >>
    irule_at (Pos hd) EQ_REFL >>
    Cases_on `ns` >>
    gvs[] >>
    (drule_then $ drule_then $ irule_at (Pos last))
      tcexp_type_cons_subst_db >>
    gvs[LIST_REL_EL_EQN,EL_MAP] >>
    irule_at (Pos hd) EQ_REFL >>
    rw[] >>
    pairarg_tac >> gvs[] >>
    first_x_assum drule >>
    pairarg_tac >>
    rw[] >>
    gvs[LAMBDA_PROD] >>
    first_x_assum $ qspecl_then [`ks ++ db'1`,`tks`,`db'2`] mp_tac >>
    disch_then $ qspec_then `MAP (shift_db 0 (LENGTH ks)) ts` mp_tac >>
    impl_tac
    >- (
      rw[EL_MAP] >>
      irule kind_ok_shift_db_APPEND >>
      simp[] >>
      metis_tac[APPEND_ASSOC]
    ) >>
    simp[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD] >>
    `(λx. subst_db (LENGTH db'1 + LENGTH ks) (MAP (tshift (LENGTH ks)) ts) (tshift (LENGTH ks) x)) =
      (λx. tshift (LENGTH ks) (subst_db (LENGTH db'1) ts x))`
    by (
      rw[FUN_EQ_THM] >>
      irule EQ_TRANS >>
      irule_at (Pos hd) subst_db_shift_db_1 >>
      simp[]
    ) >>
    simp[] >>
    pop_assum kall_tac >>
    ho_match_mp_tac $ cj 1 $ iffLR EQ_IMP_THM >>
    AP_THM_TAC >>
    AP_THM_TAC >>
    AP_TERM_TAC >>
    rw[LIST_EQ_REWRITE,EL_MAP] >>
    pairarg_tac >>
    rw[] >>
    irule EQ_TRANS >>
    irule_at (Pos last) subst_db_shift_db_1 >>
    simp[shift_db_twice,MAP_MAP_o,combinTheory.o_DEF,
      shift_db_skip_tshift_shift]
  )
  >- gvs[oEL_THM,EL_MAP]
  >- (
    gvs[LIST_REL_EL_EQN] >>
    first_assum $ irule_at (Pos last) >>
    first_assum $ irule_at (Pos last) >>
    rw[] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then drule >>
    impl_tac >- rw[] >>
    drule get_PrimTys_freetyvasrs_ok >>
    rw[MEM_EL,PULL_EXISTS] >>
    first_x_assum $ drule_then assume_tac >>
    drule subst_db_unchanged >>
    simp[] >>
    metis_tac[]
  )
  >- (
    gvs[] >>
    last_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    drule_then (strip_assume_tac o SRULE[])
      LIST_REL_kind_ok_tshift >>
    pop_assum $ qspec_then `new` assume_tac >>
    disch_then dxrule >>
    simp[MAP_MAP_o,combinTheory.o_DEF,shift_db_twice,
      GSYM subst_db_shift_db_1,LAMBDA_PROD,
      shift_db_skip_tshift_shift] >>
    metis_tac[]
  )
  >- (
    gvs[subst_db_Functions] >>
    first_x_assum $ irule_at (Pos hd) >>
    gvs[LIST_REL_EL_EQN] >>
    rw[] >>
    first_x_assum drule >>
    rw[EL_MAP]
  )
  >- (
    gvs[subst_db_Functions] >>
    irule_at (Pos hd) EQ_REFL >>
    gvs[EVERY_MAP,lambdify type_ok_def,MAP_MAP_o,
      combinTheory.o_DEF,MAP_REVERSE,MAP_ZIP_ALT] >>
    gvs[EVERY_MEM] >>
    rw[] >>
    first_x_assum $ drule_then assume_tac >>
    drule_then irule kind_ok_subst_db_APPEND >>
    metis_tac[]
  )
  >- (
    first_x_assum $ irule_at (Pos last) >>
    gvs[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD] >>
    first_x_assum $ resolve_then (Pos hd)
      mp_tac APPEND_ASSOC_four >>
    disch_then $ qspec_then `MAP (tshift (LENGTH new)) ts` mp_tac >>
    impl_tac
    >- (
      gvs[LIST_REL_EL_EQN] >>
      rw[EL_MAP] >>
      irule kind_ok_shift_db_APPEND >>
      simp[] >>
      metis_tac[APPEND_ASSOC]
    ) >>
    ho_match_mp_tac $ cj 1 $ iffLR EQ_IMP_THM >>
    simp[subst_db_shift_db_1] >>
    ntac 2 AP_THM_TAC >>
    AP_TERM_TAC >>
    rw[LIST_EQ_REWRITE,EL_MAP] >>
    pairarg_tac >>
    rw[MAP_MAP_o,combinTheory.o_DEF,shift_db_twice] >>
    simp[GSYM subst_db_shift_db_1,MAP_MAP_o,combinTheory.o_DEF] >>
    rw[LIST_EQ_REWRITE,EL_MAP,shift_db_skip_tshift_shift]
  )
  >- (
    imp_res_tac EVERY2_LENGTH >>
    gvs[MAP_MAP_o,MAP_REVERSE,MAP_ZIP_ALT] >>
    first_x_assum $ irule_at (Pos last) >>
    gvs[EVERY_MAP,combinTheory.o_DEF,LAMBDA_PROD] >>
    gvs[EVERY_EL,LIST_REL_EL_EQN] >>
    rw[EL_MAP]
    >- (
      last_x_assum drule >>
      ntac 2 (pairarg_tac >> gvs[]) >>
      strip_tac >>
      first_x_assum $ resolve_then (Pos hd) mp_tac APPEND_ASSOC_four >>
      disch_then $ qspec_then `MAP (tshift (LENGTH vars)) ts` mp_tac >>
      impl_tac
      >- (
        rw[EL_MAP] >>
        irule kind_ok_shift_db_APPEND >>
        simp[] >> metis_tac[APPEND_ASSOC]
      ) >>
      gvs[GSYM subst_db_shift_db_1,ZIP_MAP,MAP_MAP_o,
        LAMBDA_PROD,combinTheory.o_DEF,shift_db_twice,
        shift_db_skip_tshift_shift]
    ) >>
    pairarg_tac >> rw[] >>
    first_x_assum drule >>
    rw[type_ok_def] >>
    dxrule_then irule kind_ok_subst_db_APPEND >>
    irule_at (Pos $ el 2) APPEND_ASSOC_four >>
    rw[LIST_REL_EL_EQN,EL_MAP] >>
    first_x_assum $ drule_then strip_assume_tac >>
    dxrule_then irule kind_ok_shift_db_APPEND >>
    simp[]
  )
  >- (
    first_x_assum $ irule_at (Pos hd) >>
    simp[] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then drule >>
    rw[MAP_REVERSE,MAP_MAP_o,MAP_ZIP_ALT,combinTheory.o_DEF,LAMBDA_PROD] >>
    qexists_tac `MAP (λ(v,t). (v,subst_db (LENGTH db'1) ts t)) vts` >>
    rw[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD]
    >- (
      drule_then drule tcexp_type_cepat_subst_db >>
      simp[ELIM_UNCURRY]
    )
    >- (
      gvs[EVERY_EL] >>
      rpt strip_tac >>
      pairarg_tac >> rw[] >>
      first_x_assum drule >>
      rw[] >>
      drule_then drule tcexp_type_cepat_subst_db >>
      rw[ELIM_UNCURRY] >>
      first_x_assum $ irule_at (Pos hd) >>
      rw[LIST_REL_EL_EQN,LAMBDA_PROD] >>
      first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      simp[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD]
    ) >>
    drule_then drule $ cj 1 tcexp_exhaustive_cepat_subst_db >>
    simp[]
  )
  >- (
    last_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then $ irule_at (Pos hd) >>
    simp[] >>
    drule_all_then (irule_at $ Pos hd) tcexp_get_cases_subst_db >>
    rw[] >>
    gvs[EVERY_MEM] >>
    rw[lambdify PAIR_MAP,LAMBDA_PROD,ALOOKUP_MAP] >>
    first_x_assum drule >>
    pairarg_tac >> gvs[] >>
    rw[PULL_EXISTS] >>
    drule_all_then (irule_at $ Pos hd)
      tcexp_destruct_type_cons_subst_db >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    rw[] >>
    gvs[MAP_REVERSE,MAP_ZIP_ALT,LAMBDA_PROD,MAP_MAP_o,
      combinTheory.o_DEF] >>
    qexists_tac `MAP (subst_db (LENGTH db'1) ts) ptys'` >>
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    gvs[LIST_REL_EL_EQN,EL_MAP] >>
    rw[] >>
    irule specialises_subst_db >>
    gvs[LIST_REL_EL_EQN] >>
    metis_tac[]
  )
  >- (
    drule_all_then (irule_at Any) tcexp_destruct_type_cons_subst_db >>
    simp[EL_MAP] >>
    metis_tac[specialises_subst_db]
  )
QED

Theorem specialises_shift_db:
  specialises tds (db1 ++ db2) s t ⇒
  specialises tds (db1 ++ shift_ks ++ db2)
    (shift_db_kind_scheme (LENGTH db1) (LENGTH shift_ks) s)
    (shift_db (LENGTH db1) (LENGTH shift_ks) t)
Proof
  PairCases_on `s` >> gvs[specialises_def,LIST_REL_EL_EQN] >>
  rw[] >>
  imp_res_tac EVERY2_LENGTH >>
  rw[GSYM subst_db_shift_db_2] >>
  irule_at (Pos last) EQ_REFL >>
  rw[EL_MAP] >>
  gvs[] >>
  first_x_assum $ drule_then assume_tac >>
  drule_then irule kind_ok_shift_db_APPEND >>
  metis_tac[]
QED

Theorem tcexp_type_cons_shift_db:
  tcexp_namespace_ok (exs,tds) ∧
  tcexp_type_cons tds (db1 ++ db2)
    (cname,carg_ts) (tyid,tyargs) ⇒
  tcexp_type_cons tds (db1 ++ shift_ks ++ db2)
    (cname,
      MAP (shift_db_kind_scheme (LENGTH db1) (LENGTH shift_ks))
        carg_ts)
    (tyid,MAP (shift_db (LENGTH db1) (LENGTH shift_ks)) tyargs)
Proof
  rw[tcexp_type_cons_def] >>
  gvs[LIST_REL_EL_EQN] >>
  rw[EL_MAP]
  >- (
    irule kind_ok_shift_db_APPEND >>
    rw[LIST_REL_EL_EQN] >>
    metis_tac[]
  ) >>
  drule_then (drule_then drule) $
    tcexp_namespace_ok_ALOOKUP_IMP_type_scheme_ok >>
  rw[MEM_EL,PULL_EXISTS] >>
  irule LIST_EQ >>
  rw[EL_MAP] >>
  pairarg_tac >> rw[] >>
  simp[GSYM subst_db_shift_db_2,MAP_MAP_o,combinTheory.o_DEF,
    shift_db_shift_db] >>
  first_x_assum $ drule_then strip_assume_tac >>
  gvs[] >>
  drule_then assume_tac type_scheme_ok_IMP_freetyvars_ok >>
  drule shift_db_unchanged >>
  gvs[]
QED

Theorem type_exception_shift_db:
  tcexp_namespace_ok (exds,tds) ∧
  type_exception exds (c,carg_tys) ⇒
  type_exception exds
    (c, MAP (shift_db n ts) carg_tys)
Proof
  gvs[type_exception_def] >>
  rw[LIST_EQ_REWRITE,EL_MAP] >>
  drule_then strip_assume_tac ALOOKUP_SOME_EL >>
  gvs[tcexp_namespace_ok_def,EVERY_EL] >>
  first_x_assum drule >>
  rw[] >>
  first_x_assum drule >>
  rw[type_ok_def,EL_MAP] >>
  drule_then assume_tac kind_ok_IMP_freetyvars_ok  >>
  gvs[] >>
  irule $ GSYM shift_db_unchanged >>
  first_assum $ irule_at (Pat `freetyvars_ok _ _`) >>
  simp[]
QED

(* TODO *)
Theorem tcexp_destruct_type_cons_shift_db:
  tcexp_namespace_ok ns ∧
  tcexp_destruct_type_cons ns (db1 ++ db2) t c carg_tys ⇒
  tcexp_destruct_type_cons ns (db1 ++ tks ++ db2)
    (shift_db (LENGTH db1) (LENGTH tks) t) c $
    MAP (shift_db_kind_scheme (LENGTH db1) (LENGTH tks)) carg_tys
Proof
  Cases_on `ns` >> rw[] >>
  gvs[tcexp_destruct_type_cons_def,
    split_ty_cons_thm,head_ty_cons_eq_head_ty] >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  IF_CASES_TAC >>
  rw[]
  >- (
    simp[shift_db_def,EVERY_EL,EL_MAP,MAP_MAP_o,LAMBDA_PROD,
      combinTheory.o_DEF,head_ty_def] >>
    drule_all_then (irule_at Any) type_exception_shift_db >>
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    irule_at Any EQ_REFL
  )
  >- gvs[shift_db_def] >>
  `t = cons_types (Atom $ TypeCons tc') (ty_args t)` by
    metis_tac[cons_types_head_ty_ty_args] >>
  pop_assum SUBST_ALL_TAC >>
  gvs[shift_db_cons_types,cons_types_not_Exception,
    shift_db_def,head_ty_cons_types,ty_args_cons_types,
    ty_args_alt] >>
  every_case_tac >>
  gvs[MAP_MAP_o,combinTheory.o_DEF] >>
  (drule_then $ drule_then irule) tcexp_type_cons_shift_db
QED

Theorem tcexp_type_cepat_shift_db:
  ∀p pt vts.
  tcexp_type_cepat ns (db1 ++ db2) p pt vts ∧
  tcexp_namespace_ok ns ⇒
  tcexp_type_cepat ns (db1 ++ tks ++ db2) p
    (shift_db_kind_scheme (LENGTH db1) (LENGTH tks) pt)
    (MAP (λ(v,t). (v,shift_db (LENGTH db1) (LENGTH tks) t)) vts)
Proof
  Induct_on `tcexp_type_cepat` >>
  rw[]
  >- (
    irule tcexp_type_cepat_Var >>
    metis_tac[specialises_shift_db]
  )
  >- irule tcexp_type_cepat_UScore
  >- (
    simp[MAP_FLAT] >>
    irule tcexp_type_cepat_Cons >>
    gvs[LIST_REL3_EL,EL_MAP] >>
    drule_then (drule_then $ irule_at Any)
      tcexp_destruct_type_cons_shift_db >>
    rw[EL_MAP]
  )
QED

Theorem tcexp_get_cases_shift_db:
  tcexp_namespace_ok ns ∧
  tcexp_get_cases ns t = SOME ctys ⇒
  tcexp_get_cases ns (shift_db n db t) =
    SOME (MAP (I ##
      (MAP (shift_db_kind_scheme n db))) ctys)
Proof
  Cases_on `ns` >>
  gvs[tcexp_get_cases_def] >>
  IF_CASES_TAC
  >- (
    rw[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
      shift_db_def] >>
    rw[LIST_EQ_REWRITE,EL_MAP,PAIR_MAP] >>
    gvs[tcexp_namespace_ok_def,MAP_EQ_f] >>
    drule_then drule $ iffLR EVERY_EL >>
    pairarg_tac >>
    rw[] >>
    gvs[] >>
    drule_then drule $ iffLR EVERY_EL >>
    rw[type_ok] >>
    drule kind_ok_IMP_freetyvars_ok >>
    rw[] >>
    irule $ GSYM shift_db_unchanged >>
    first_assum $ irule_at (Pat `freetyvars_ok _ _`) >>
    simp[]
  ) >>
  CASE_TAC
  >- (
    rw[EXISTS_PROD,split_ty_cons_thm,
      head_ty_cons_eq_head_ty] >>
    qspec_then `t` assume_tac $
      GSYM $ GEN_ALL cons_types_head_ty_ty_args >>
    pop_assum SUBST_ALL_TAC >>
    gvs[shift_db_cons_types,shift_db_def,head_ty_cons_types,
      cons_types_not_Exception,head_ty_def]
  ) >>
  rw[EXISTS_PROD] >>
  every_case_tac >>
  gvs[EXISTS_PROD,split_ty_cons_thm,head_ty_cons_eq_head_ty,
    shift_db_head_ty,shift_db_ty_args,MAP_MAP_o,
    combinTheory.o_DEF,LAMBDA_PROD] >>
  rw[MAP_EQ_f] >>
  pairarg_tac >> simp[] >>
  rw[MAP_EQ_f] >>
  pairarg_tac >>
  simp[GSYM subst_db_shift_db_2,MAP_MAP_o,combinTheory.o_DEF,
    shift_db_shift_db] >>
  AP_TERM_TAC >>
  irule $ GSYM shift_db_unchanged >>
  drule_all_then assume_tac
    tcexp_namespace_ok_MEM_IMP_type_scheme_ok >>
  gvs[] >>
  drule_then (irule_at Any) type_scheme_ok_IMP_freetyvars_ok >>
  simp[]
QED

Theorem tcexp_exhaustive_cepat_shift_db:
  tcexp_namespace_ok ns ⇒
  (∀t ps.
    tcexp_exhaustive_cepat ns t ps ⇒
    ∀skip shift. tcexp_exhaustive_cepat ns
      (shift_db_kind_scheme skip shift t) ps) ∧
  (∀ts pss.
    tcexp_exhaustive_cepatl ns ts pss ⇒
    ∀skip shift. tcexp_exhaustive_cepatl ns
      (MAP (shift_db_kind_scheme skip shift) ts) pss)
Proof
  strip_tac >>
  ho_match_mp_tac tcexp_exhaustive_cepat_ind >>
  rw[]
  >- metis_tac[tcexp_exhaustive_cepat_Var]
  >- metis_tac[tcexp_exhaustive_cepat_UScore]
  >- (
    Cases_on `ns` >>
    irule tcexp_exhaustive_cepat_Cons >>
    drule_all_then (irule_at Any)
      tcexp_get_cases_shift_db >>
    rw[MEM_MAP,EXISTS_PROD] >>
    first_x_assum drule >>
    rw[] >>
    metis_tac[]
  )
  >- metis_tac[tcexp_exhaustive_cepat_Nil]
  >- (
    irule tcexp_exhaustive_cepat_List >>
    first_x_assum $ irule_at (Pos hd) >>
    gvs[]
  )
QED

Theorem type_tcexp_shift_db:
  tcexp_namespace_ok ns ⇒
  ∀db st env e t skip shift db' db1 shift_ks db2.
    type_tcexp ns db st env e t ∧
    db = db1 ++ db2 ∧
    db' = db1 ++ shift_ks ++ db2 ∧
    shift = LENGTH shift_ks ∧
    skip = LENGTH db1
  ⇒ type_tcexp ns db'
      (MAP (shift_db skip shift) st)
      (MAP (λ(s,scheme). (s,shift_db_kind_scheme skip shift scheme)) env)
      e
      (shift_db skip shift t)
Proof
  strip_tac >>
  Induct_on `type_tcexp` >> rw[shift_db_def] >> rw[Once type_tcexp_cases]
  >- (
    simp[ALOOKUP_MAP] >>
    metis_tac[specialises_shift_db]
  )
  >- (
    disj1_tac >>
    gvs[LIST_REL_EL_EQN,EL_MAP,shift_db_cons_types,shift_db_def] >>
    qexists_tac `MAP (shift_db (LENGTH db1) (LENGTH shift_ks)) ts` >>
    rw[EL_MAP]
  )
  >- (
    disj1_tac >>
    rpt $ first_assum $ irule_at Any >>
    gvs[shift_db_Functions,shift_db_def]
  )
  >- (
    disj1_tac >>
    gvs[type_ok_def] >>
    drule_then irule kind_ok_shift_db_APPEND >>
    metis_tac[]
  )
  >- (
    disj1_tac >>
    gvs[shift_db_Functions,shift_db_def]
  )
  >- (
    disj1_tac >>
    first_x_assum $ irule_at Any >>
    rw[]
  )
  >- (
    disj1_tac >>
    rpt $ first_assum $ irule_at Any >>
    rw[]
  )
  >- (
    disj2_tac >> disj1_tac >>
    rpt $ first_assum $ irule_at Any >>
    gvs[LIST_REL_EL_EQN,oneline tcexp_namespace_ok_def,pair_CASE_def] >>
    rw[] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then $ qspec_then `shift_ks` mp_tac >>
    gvs[EVERY_MEM,type_exception_def] >>
    drule_then strip_assume_tac ALOOKUP_MEM >>
    first_x_assum drule >>
    rw[PULL_EXISTS,MEM_EL] >>
    first_x_assum drule >>
    rw[type_ok_def] >>
    drule_then strip_assume_tac kind_ok_IMP_freetyvars_ok >>
    gvs[] >>
    drule_then strip_assume_tac shift_db_unchanged >>
    gvs[]
  )
  >- (
    rpt disj2_tac >>
    simp[shift_db_tcons_to_type] >>
    irule_at (Pos hd) EQ_REFL >>
    Cases_on `ns` >>
    gvs[] >>
    (drule_then $ drule_then $ irule_at (Pos last))
      tcexp_type_cons_shift_db >>
    gvs[LIST_REL_EL_EQN,EL_MAP] >>
    rw[] >>
    pairarg_tac >> gvs[] >>
    first_x_assum drule >>
    pairarg_tac >>
    rw[] >>
    gvs[LAMBDA_PROD] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then $ qspec_then `shift_ks` mp_tac >>
    simp[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
      shift_db_shift_db] >>
    ho_match_mp_tac $ cj 1 $ iffLR EQ_IMP_THM >>
    ntac 2 AP_THM_TAC >>
    AP_TERM_TAC >>
    rw[LIST_EQ_REWRITE,EL_MAP] >>
    pairarg_tac >> rw[] >>
    simp[GSYM shift_db_shift_db]
  )
  >- gvs[oEL_THM,EL_MAP]
  >- (
    gvs[LIST_REL_EL_EQN] >>
    first_assum $ irule_at (Pos last) >>
    first_assum $ irule_at (Pos last) >>
    rw[] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    drule get_PrimTys_freetyvasrs_ok >>
    rw[MEM_EL,PULL_EXISTS] >>
    first_x_assum $ drule_then assume_tac >>
    drule_then strip_assume_tac shift_db_unchanged >>
    gvs[]
  )
  >- (
    gvs[] >>
    last_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    simp[MAP_MAP_o,combinTheory.o_DEF,shift_db_twice,
      GSYM shift_db_shift_db,LAMBDA_PROD,
      shift_db_skip_tshift_shift] >>
    metis_tac[]
   )
  >- (
    gvs[shift_db_Functions] >>
    first_x_assum $ irule_at (Pos hd) >>
    gvs[LIST_REL_EL_EQN] >>
    rw[] >>
    first_x_assum drule >>
    rw[EL_MAP]
  )
  >- (
    gvs[shift_db_Functions] >>
    irule_at (Pos hd) EQ_REFL >>
    gvs[EVERY_MAP,lambdify type_ok_def,MAP_MAP_o,
      combinTheory.o_DEF,MAP_REVERSE,MAP_ZIP_ALT] >>
    gvs[EVERY_MEM] >>
    rw[] >>
    first_x_assum $ drule_then assume_tac >>
    drule_then irule kind_ok_shift_db_APPEND >>
    metis_tac[]
  )
  >- (
    first_x_assum $ irule_at (Pos last) >>
    gvs[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then $ qspec_then `shift_ks` mp_tac >>
    ho_match_mp_tac $ cj 1 $ iffLR EQ_IMP_THM >>
    simp[shift_db_shift_db] >>
    simp[GSYM shift_db_shift_db]
  )
  >- (
    imp_res_tac EVERY2_LENGTH >>
    gvs[MAP_MAP_o,MAP_REVERSE,MAP_ZIP_ALT] >>
    first_x_assum $ irule_at (Pos last) >>
    gvs[EVERY_MAP,combinTheory.o_DEF,LAMBDA_PROD] >>
    gvs[EVERY_EL,LIST_REL_EL_EQN] >>
    rw[EL_MAP]
    >- (
      last_x_assum drule >>
      ntac 2 (pairarg_tac >> gvs[]) >>
      strip_tac >>
      first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      disch_then $ qspec_then `shift_ks` mp_tac >>
      gvs[shift_db_shift_db,ZIP_MAP,MAP_MAP_o,
        LAMBDA_PROD,combinTheory.o_DEF,shift_db_twice,
        shift_db_skip_tshift_shift] >>
      gvs[GSYM shift_db_shift_db]
    ) >>
    pairarg_tac >> rw[] >>
    first_x_assum drule >>
    rw[type_ok_def] >>
    dxrule_then irule kind_ok_shift_db_APPEND >>
    irule_at (Pos hd) APPEND_ASSOC_four >>
    simp[]
  )
  >- (
    first_x_assum $ irule_at (Pos hd) >>
    simp[] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    rw[MAP_REVERSE,MAP_MAP_o,MAP_ZIP_ALT,combinTheory.o_DEF,LAMBDA_PROD] >>
    qexists_tac `MAP (λ(v,t). (v,shift_db (LENGTH db1) (LENGTH shift_ks) t)) vts` >>
    rw[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD]
    >- (
      drule_then drule tcexp_type_cepat_shift_db >>
      simp[ELIM_UNCURRY]
    )
    >- (
      gvs[EVERY_EL] >>
      rpt strip_tac >>
      pairarg_tac >> rw[] >>
      first_x_assum drule >>
      rw[] >>
      drule_then drule tcexp_type_cepat_shift_db >>
      rw[ELIM_UNCURRY] >>
      first_x_assum $ irule_at (Pos hd) >>
      rw[LIST_REL_EL_EQN,LAMBDA_PROD] >>
      first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      simp[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD]
    ) >>
    drule_then drule $ cj 1 tcexp_exhaustive_cepat_shift_db >>
    simp[]
  )
  >- (
    last_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then $ irule_at (Pos hd) >>
    simp[] >>
    drule_then (irule_at $ Pos hd) tcexp_get_cases_shift_db >>
    rw[] >>
    gvs[EVERY_MEM] >>
    rw[lambdify PAIR_MAP,LAMBDA_PROD,ALOOKUP_MAP] >>
    first_x_assum drule >>
    pairarg_tac >> gvs[] >>
    rw[PULL_EXISTS] >>
    drule_all_then (irule_at $ Pos hd)
      tcexp_destruct_type_cons_shift_db >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    rw[] >>
    gvs[MAP_REVERSE,MAP_ZIP_ALT,LAMBDA_PROD,MAP_MAP_o,
      combinTheory.o_DEF] >>
    qexists_tac `MAP (shift_db (LENGTH db1) (LENGTH shift_ks)) ptys'` >>
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    gvs[LIST_REL_EL_EQN,EL_MAP] >>
    rw[] >>
    irule specialises_shift_db >>
    gvs[]
  )
  >- (
    drule_all_then (irule_at Any) tcexp_destruct_type_cons_shift_db >>
    simp[EL_MAP] >>
    metis_tac[specialises_shift_db]
  )
QED

Triviality MAP_FST_tshift_env:
  MAP FST (tshift_env n env) = MAP FST env
Proof
  simp[MAP_MAP_o,combinTheory.o_DEF,FST_THM,LAMBDA_PROD]
QED

Triviality APPEND_SING_APPEND:
  l ++ [x] ++ l' = l ++ x::l'
Proof
  metis_tac[APPEND_ASSOC,APPEND]
QED

Theorem type_tcexp_subst:
  ∀db st env' prefix env e t ces.
    type_tcexp ns db st env' e t ∧
    env' = prefix ++ env ∧
    tcexp_namespace_ok ns ∧
    MAP FST env = MAP FST ces ∧
    LIST_REL (λce (vars,scheme).
        type_tcexp ns (vars ++ db) (MAP (tshift (LENGTH vars)) st) [] ce scheme)
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
    drule_then drule type_tcexp_subst_db >> simp[] >>
    disch_then $ qspec_then `[]` mp_tac >> simp[] >>
    disch_then $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then $ qspec_then `subs` mp_tac >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,LIST_REL_EL_EQN] >>
    simp[subst_db_shift_db_unchanged] >> gvs[GSYM LAMBDA_PROD] >> rw[] >>
    drule type_tcexp_weaken >>
    disch_then $ qspecl_then [`[]`,`[]`,`prefix`] mp_tac >> simp[]
  ) >>
  rw[Once type_tcexp_cases] >> gvs[]
  >- (
    disj1_tac >>
    irule_at (Pos hd) EQ_REFL >>
    gvs[LIST_REL_EL_EQN] >>
    metis_tac[EL_MAP]
  )
  >- (disj1_tac >> metis_tac[])
  >- (disj1_tac >> metis_tac[])
  >- (disj1_tac >> metis_tac[])
  >- (
    disj2_tac >> disj1_tac >>
    first_x_assum $ irule_at (Pos last) >>
    gvs[LIST_REL_EL_EQN,EL_MAP]
  )
  >- (
    rpt disj2_tac >>
    irule_at (Pos hd) EQ_REFL >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >>
    irule_at Any EQ_REFL >> rw[] >>
    last_x_assum drule >>
    pairarg_tac >> rw[EL_MAP] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    simp[MAP_MAP_o,combinTheory.o_DEF,FST_THM,LAMBDA_PROD] >>
    disch_then irule >>
    reverse $ rw[EL_MAP]
    >- gvs[FST_THM,LAMBDA_PROD] >>
    first_x_assum drule >>
    Cases_on `EL n' env` >>
    simp[] >>
    pairarg_tac >> gvs[] >>
    strip_tac >>
    drule_then drule type_tcexp_shift_db >>
    disch_then $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    simp[MAP_MAP_o,combinTheory.o_DEF,shift_db_skip_tshift_shift,
      shift_db_twice]
  )
  >- (
    rpt (first_assum $ irule_at Any) >>
    gvs[LIST_REL_EL_EQN, EL_MAP]
  )
  >- (
    last_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    simp[MAP_FST_tshift_env] >>
    disch_then $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then $ irule_at $ Pos hd >>
    gvs[LIST_REL_EL_EQN,EL_MAP] >>
    rw[] >>
    first_x_assum $ drule >>
    Cases_on `EL  n env` >> simp[] >>
    pairarg_tac >> gvs[] >>
    strip_tac >>
    drule_then drule type_tcexp_shift_db >>
    disch_then $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    simp[MAP_MAP_o,combinTheory.o_DEF,
      shift_db_skip_tshift_shift,shift_db_twice]
  )
  >- (
    first_x_assum $ irule_at (Pos hd) >>
    gvs[LIST_REL_EL_EQN,EL_MAP]
  )
  >- (
    irule_at (Pos hd) EQ_REFL >>
    simp[] >>
    last_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then $ drule >>
    rw[MAP_REVERSE,MAP_ZIP,FDIFF_FDIFF] >>
    metis_tac[UNION_COMM]
  )
  >- (
    last_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    gvs[MAP_FST_tshift_env] >>
    disch_then $ irule_at (Pos hd) >>
    gvs[LIST_REL_EL_EQN,EL_MAP] >>
    rw[]
    >- (
      first_x_assum drule >>
      Cases_on `EL n env` >>
      simp[] >>
      pairarg_tac >> gvs[] >>
      strip_tac >>
      drule_then drule type_tcexp_shift_db >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      simp[MAP_MAP_o,combinTheory.o_DEF,shift_db_skip_tshift_shift,
        shift_db_twice]
    ) >>
    last_x_assum $ resolve_then (Pos hd) mp_tac (GSYM $ cj 2 APPEND) >>
    disch_then drule >>
    simp[EL_MAP,GSYM FDIFF_FDOMSUB_INSERT,FDIFF_FDOMSUB]
  )
  >- (
    gvs[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,GSYM FST_THM] >>
    first_x_assum $ irule_at Any >> simp[FDIFF_FDIFF] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then drule >>
    gvs[MAP_REVERSE,LIST_REL_EL_EQN,EL_MAP,MAP_ZIP] >>
    rw[Once UNION_COMM] >>
    qmatch_goalsub_abbrev_tac `_ (_ a) b` >>
    PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
    last_x_assum drule >> simp[] >> strip_tac >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    simp[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD] >>
    disch_then $ qspec_then `ces` mp_tac >>
    simp[GSYM LAMBDA_PROD,GSYM FST_THM] >>
    impl_tac >> rw[] >> gvs[EL_MAP]
    >- (
      qmatch_goalsub_abbrev_tac `_ (_ c)` >> PairCases_on `c` >> gvs[] >>
      last_x_assum drule >> rw[] >> simp[GSYM shift_db_shift_db] >>
      drule_then drule type_tcexp_shift_db >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      gvs[MAP_MAP_o, combinTheory.o_DEF]
    ) >>
    irule quotientTheory.EQ_IMPLIES >> goal_assum drule >>
    rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> rw[Once UNION_COMM] >> AP_TERM_TAC >>
    rw[EXTENSION, MEM_MAP, MEM_ZIP, PULL_EXISTS, EXISTS_PROD] >> eq_tac >> rw[]
    >- (
      simp[EL_MAP,MEM_EL] >>
      metis_tac[PAIR]
    )
    >- (
      gvs[MEM_EL] >>
      first_assum $ irule_at (Pos hd) >>
      simp[EL_MAP] >>
      metis_tac[PAIR,FST]
    )
  )
  >- (
    gvs[MEM_FLAT,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
      FDIFF_FDIFF] >>
    first_x_assum $ irule_at (Pos hd) >>
    simp[] >>
    first_assum $ irule_at (Pos hd) >>
    last_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    simp[APPEND_SING_APPEND] >>
    disch_then $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    rw[]
    >- (
      gvs[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,GSYM FST_THM] >>
      drule_then assume_tac tcexp_type_cepat_cepat_vars >>
      simp[] >>
      metis_tac[UNION_COMM,INSERT_SING_UNION,UNION_ASSOC]
    )
    >- (
      gvs[EVERY_MAP,EVERY_EL] >>
      rw[] >>
      first_x_assum drule >>
      pairarg_tac >> gvs[] >>
      rw[] >>
      first_assum $ irule_at (Pos hd) >>
      first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      simp[APPEND_SING_APPEND] >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      rw[] >>
      gvs[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,GSYM FST_THM] >>
      drule_then assume_tac tcexp_type_cepat_cepat_vars >>
      simp[] >>
      metis_tac[UNION_COMM,INSERT_SING_UNION,UNION_ASSOC]
    )
    >- (
      simp[GSYM LIST_TO_SET_MAP,MAP_MAP_o,combinTheory.o_DEF,
        LAMBDA_PROD] >>
      simp[GSYM FST_THM,LIST_TO_SET_MAP]
    )
  )
  >- (
    gvs[MEM_FLAT,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
      FDIFF_FDIFF] >>
    first_x_assum $ irule_at (Pos hd) >>
    simp[EVERY_MAP,LAMBDA_PROD,GSYM PEXISTS_THM] >>
    simp[GSYM LAMBDA_PROD,GSYM FST_THM] >>
    rw[]
    >- (
      first_x_assum $ resolve_then (Pos hd) mp_tac (GSYM $ cj 2 APPEND) >>
      disch_then drule >>
      rw[] >>
      gvs[GSYM FDIFF_FDOMSUB_INSERT,FDIFF_FDOMSUB]
    ) >>
    gvs[EVERY_EL] >>
    rw[] >>
    first_x_assum drule >>
    pairarg_tac >> gvs[] >>
    rw[] >>
    first_assum $ irule_at (Pos hd) >>
    first_assum $ irule_at (Pos hd) >>
    rw[] >>
    first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
    disch_then drule >>
    PURE_REWRITE_TAC[APPEND_SING_APPEND] >>
    rw[] >>
    gvs[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,MAP_ZIP] >>
    metis_tac[UNION_COMM,INSERT_SING_UNION,UNION_ASSOC]
  )
  >- (
    first_x_assum $ irule_at (Pat `type_tcexp _ _ _ _ _ _`) >>
    simp[] >>
    metis_tac[]
  )
QED

Theorem type_tcexp_closing_subst:
  ∀ns db st env e t ces.
    type_tcexp ns db st env e t ∧
    tcexp_namespace_ok ns ∧
    MAP FST env = MAP FST (REVERSE ces) ∧
    LIST_REL (λce (vars,scheme).
        type_tcexp ns (vars ++ db) (MAP (tshift (LENGTH vars)) st) [] ce scheme)
      (MAP SND (REVERSE ces)) (MAP SND env)
  ⇒ type_tcexp ns db st [] (subst_tc (FEMPTY |++ ces) e) t
Proof
  rw[] >> drule type_tcexp_subst >> simp[] >>
  disch_then $ drule_at Any >> simp[]
QED

Theorem type_tcexp_closing_subst1:
  ∀ns db st var tvars scheme e t ce.
    type_tcexp ns db st [var,tvars,scheme] e t ∧
    tcexp_namespace_ok ns ∧
    type_tcexp ns (tvars ++ db) (MAP (tshift (LENGTH tvars)) st) [] ce scheme
  ⇒ type_tcexp ns db st [] (subst_tc1 var ce e) t
Proof
  rw[finite_mapTheory.FUPDATE_EQ_FUPDATE_LIST] >>
  irule type_tcexp_closing_subst >> simp[PULL_EXISTS, EXISTS_PROD] >>
  goal_assum drule >> simp[]
QED

Theorem type_tcexp_freevars_tcexp_specialises:
  ∀db st env e t v.
   type_tcexp ns db st env e t ∧
   v ∈ freevars_tcexp e ⇒
   ∃s ks t'. ALOOKUP env v = SOME s ∧ specialises (SND ns) (ks ++ db) s t'
Proof
  Induct_on `type_tcexp` >> rw[] >>
  gvs[LIST_REL_EL_EQN, MEM_EL, MAP_ZIP, PULL_EXISTS, EL_MAP]
  >- metis_tac[APPEND]
  >- metis_tac[APPEND]
  >- metis_tac[APPEND]
  >- (
    first_x_assum drule >>
    pairarg_tac >> rw[] >>
    first_x_assum drule >>
    rw[ALOOKUP_MAP] >>
    gvs[oneline specialises_def] >>
    TOP_CASE_TAC >>
    gvs[] >>
    metis_tac[]
  )
  >- (first_x_assum drule >> rw[])
  >- (
    first_x_assum drule >> rw[] >>
    gvs[ALOOKUP_MAP,oneline specialises_def] >>
    TOP_CASE_TAC >>
    gvs[] >>
    metis_tac[]
  )
  >- (first_x_assum drule >> rw[])
  >- (
    first_x_assum drule >> rw[] >>
    gvs[ALOOKUP_APPEND,AllCaseEqs()]
    >- metis_tac[] >>
    drule ALOOKUP_MEM >>
    rw[MEM_REVERSE,MEM_ZIP] >>
    metis_tac[]
  )
  >- (
    first_x_assum drule >> rw[ALOOKUP_MAP] >>
    gvs[oneline specialises_def] >>
    TOP_CASE_TAC >>
    gvs[] >>
    metis_tac[]
  )
  >- (first_x_assum drule >> rw[])
  >- (
    first_x_assum drule >> rw[] >>
    gvs[ALOOKUP_APPEND,AllCaseEqs()]
    >- metis_tac[] >>
    drule ALOOKUP_MEM >>
    rw[MEM_REVERSE,MEM_ZIP] >>
    metis_tac[]
  )
  >- (
    first_x_assum drule >>
    ntac 2 (pairarg_tac >> gvs[]) >>
    rw[] >>
    first_x_assum drule >> rw[] >>
    gvs[ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_MAP]
    >- (
      gvs[oneline specialises_def] >>
      TOP_CASE_TAC >> gvs[] >>
      metis_tac[]
    ) >>
    drule ALOOKUP_MEM >>
    rw[MEM_REVERSE,MEM_ZIP] >>
    metis_tac[]
  )
  >- (
    first_x_assum drule >>
    rw[ALOOKUP_APPEND,AllCaseEqs()]
    >- metis_tac[] >>
    drule ALOOKUP_MEM >>
    rw[MEM_REVERSE,MEM_ZIP,MEM_MAP] >>
    pairarg_tac >> gvs[] >>
    drule_then assume_tac tcexp_type_cepat_cepat_vars >>
    gvs[MEM_MAP]
  )
  >- (
    pairarg_tac >>
    gvs[EVERY_EL] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum drule >>
    rw[ALOOKUP_APPEND,AllCaseEqs()]
    >- metis_tac[] >>
    drule ALOOKUP_MEM >>
    rw[MEM_REVERSE,MEM_ZIP,MEM_MAP] >>
    pairarg_tac >> gvs[] >>
    imp_res_tac tcexp_type_cepat_cepat_vars >>
    gvs[MEM_MAP]
  )
  >- (
    qpat_x_assum `v' ∈ case usopt of _ => _ | _ => _` mp_tac >>
    TOP_CASE_TAC >> simp[] >>
    TOP_CASE_TAC >> rw[] >>
    gvs[] >>
    first_x_assum drule >>
    rw[]
  )
  >- (
    pairarg_tac >> gvs[EVERY_EL] >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum drule >>
    rw[ALOOKUP_APPEND,AllCaseEqs()]
    >- metis_tac[] >>
    drule ALOOKUP_MEM >>
    rw[MEM_REVERSE,MEM_ZIP] >>
    gvs[MEM_EL]
  )
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
    imp_res_tac type_tcexp_freevars_tcexp_specialises >>
    imp_res_tac insert_seq_freevars >>
    gvs[freevars_tcexp_of] >>
    first_x_assum drule >>
    rw[ALOOKUP_MAP,PULL_EXISTS,pair_CASE_def,
      oneline specialises_def,ELIM_UNCURRY] >>
    metis_tac[]
    )
  >- (
    pop_assum mp_tac >> simp[Once type_tcexp_cases]
    )
  >- (
    pop_assum mp_tac >> once_rewrite_tac[type_tcexp_cases] >>
    rw[] >> gvs[MAP_EQ_CONS] >> gvs[LIST_REL_EL_EQN, EL_MAP]
    >~ [`tcons_to_type _ _ = tcons_to_type _ _`]
    >- (
      rpt disj2_tac >>
      irule_at (Pos hd) EQ_REFL >>
      first_assum $ irule_at (Pos last) >>
      rw[] >>
      first_x_assum drule >>
      pairarg_tac >> rw[]
    ) >> metis_tac[]
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
  rw[] >> gvs[LIST_REL_EL_EQN, EL_MAP, OPTREL_def, MAP_MAP_o,
    combinTheory.o_DEF, LAMBDA_PROD] >>
  gvs[GSYM LAMBDA_PROD, GSYM FST_THM]
  >- (
    `MAP FST css1 = MAP FST css2`
    by (
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[] >>
      first_x_assum drule >> rpt (pairarg_tac >> gvs[])
    ) >>
    gvs[EVERY_EL, EL_MAP] >> rw[] >>
    first_assum $ irule_at (Pat `tcexp_get_cases _ _ = SOME _`) >>
    rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule >> rw[] >>
    metis_tac[]
  ) >>
  `MAP FST css1 = MAP FST css2`
  by (
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[])
  ) >>
  gvs[GSYM PEXISTS_THM] >>
  first_assum $ irule_at (Pat `tcexp_get_cases _ _ = SOME _`) >>
  gvs[EVERY_EL, EL_MAP] >> rw[]
  >- (strip_tac >> gvs[]) >>
  first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `!n. n < LENGTH _ ⇒ _ (EL _ css1) (EL _ css2)` drule >> rw[] >>
  metis_tac[]
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
