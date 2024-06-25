open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory miscTheory;
open listTheory alistTheory relationTheory set_relationTheory pred_setTheory;
open rich_listTheory;
open pure_cexpTheory pure_configTheory;
open typeclass_typesTheory typeclass_kindCheckTheory typeclass_typesPropsTheory;
open pure_tcexpTheory pure_tcexp_typingTheory
pure_tcexp_typingPropsTheory;
open typeclass_texpTheory typeclass_typingTheory typeclass_typingPropsTheory;
open monadsyntax;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "option";

val _ = new_theory "typeclass_typingProof";

Theorem kind_ok_tdefs_to_tcexp_tdefs:
  kind_ok (tdefs_to_tcexp_tdefs tds) = kind_ok tds
Proof
  simp[lambdify kind_ok_def,tdefs_to_tcexp_tdefs_def] >>
  rw[FUN_EQ_THM,typedefs_to_cdb_def,oEL_THM,EL_MAP] >>
  rpt AP_THM_TAC >>
  rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  IF_CASES_TAC >>
  gvs[]
QED

Theorem typedefs_to_cdb_APPEND:
  typedefs_to_cdb (tds ++ tds') c =
  if c < LENGTH tds
  then typedefs_to_cdb tds c
  else OPTION_MAP (λtinfo. kind_arrows (FST tinfo) kindType)
      (LLOOKUP tds' (c - LENGTH tds))
Proof
  IF_CASES_TAC >>
  simp[typedefs_to_cdb_def,oEL_THM,EL_APPEND_EQN] >>
  Cases_on `0 < LENGTH tds'` >>
  gvs[]
QED

Theorem typedefs_to_cdb_SOME_0_LT:
  typedefs_to_cdb tds c = SOME t ⇒ c < LENGTH tds
Proof
  rw[typedefs_to_cdb_def,oEL_THM]
QED

Theorem kind_ok_tdefs_APPEND:
  ∀t k. kind_ok tds db t k ⇒
  kind_ok (tds ++ tds') db t k
Proof
  simp[kind_ok_def] >>
  ho_match_mp_tac kind_wf_ind >>
  rw[typedefs_to_cdb_APPEND,typedefs_to_cdb_SOME_0_LT] >>
  metis_tac[]
QED

Theorem specialises_tdefs_APPEND:
  specialises tds db s t ⇒
    specialises (tds ++ tds') db s t
Proof
  simp[oneline specialises_def] >>
  TOP_CASE_TAC >>
  rw[] >>
  irule_at (Pos last) EQ_REFL >>
  drule_at_then (Pos last) irule LIST_REL_mono >>
  simp[kind_ok_tdefs_APPEND]
QED

Theorem namespace_ok_IMP_tcexp_namespace_ok:
  namespace_ok ns ∧
  ALL_DISTINCT (
    (MAP implode (SET_TO_LIST reserved_cns)) ++
    (MAP FST (FST ns)) ++
    (FLAT (MAP (MAP FST o SND) (SND ns))) ++
    FLAT (MAP (MAP FST o SND) tds)
  ) ∧
  EVERY (λ(ks,td). td ≠ []) tds ∧
  EVERY (λ(ks,td). EVERY (λ(cn,argtys).
    EVERY (
      type_scheme_ok
        (tdefs_to_tcexp_tdefs (SND ns) ++ tds) ks)
        argtys) td) tds
  ⇒
    tcexp_namespace_ok $
      append_ns (namespace_to_tcexp_namespace ns)
      ([],tds)
Proof
  simp[namespace_to_tcexp_namespace_def,
    tdefs_to_tcexp_tdefs_def,pair_CASE_def,
    tcexp_namespace_ok_def,oneline namespace_ok_def,
    EVERY_MAP,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
    type_scheme_ok_def,
    lambdify type_ok_def,MAP_FLAT] >>
  rw[]
  >- (
    gvs[ALL_DISTINCT_APPEND,MEM_MAP,MEM_FLAT,
      GSYM PEXISTS_THM,FORALL_PROD,MEM_FLAT,
      DISJ_IMP_THM,FORALL_AND_THM,PULL_EXISTS] >>
    metis_tac[]
  ) >>
  gvs[EVERY_MEM,FORALL_PROD] >>
  rw[] >>
  irule kind_ok_tdefs_APPEND >>
  simp[SRULE[tdefs_to_tcexp_tdefs_def] kind_ok_tdefs_to_tcexp_tdefs] >>
  first_x_assum $ drule_all_then irule
QED

Theorem class_env_ns_NON_EMPTY:
  ∀ce' l clcons cl_tds.
    class_env_to_ns ce cl_to_tyid clcons ce' = SOME cl_tds ∧
    ce = l ++ ce' ∧
    LENGTH ce' ≤ LENGTH clcons ⇒
    EVERY (λ(ks,td). td ≠ []) cl_tds
Proof
  Induct >>
  rw[class_env_to_ns_def] >>
  Cases_on `clcons` >>
  gvs[class_env_to_ns_def] >>
  last_x_assum drule >>
  rw[] >>
  gvs[oneline class_to_datatype_def,AllCaseEqs()]
QED

Theorem FLOOKUP_ce_to_cl_tyid_map:
  ALL_DISTINCT (MAP FST ce) ⇒
  FLOOKUP (ce_to_cl_tyid_map ns_len ce) cl =
    OPTION_MAP ($+ ns_len) (find_index cl (MAP FST ce) 0)
Proof
  simp[ce_to_cl_tyid_map_def,FLOOKUP_FUPDATE_LIST,oneline OPTION_MAP_DEF] >>
  TOP_CASE_TAC >>
  gvs[AllCaseEqs(),ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP]
  >- gvs[MEM_MAP,GSYM find_index_NOT_MEM] >>
  dxrule_then assume_tac ALOOKUP_MEM >>
  rpt strip_tac >>
  gvs[MEM_REVERSE,MEM_ZIP,EL_MAP,EL_GENLIST] >>
  irule_at (Pos last) ADD_COMM >>
  drule ALL_DISTINCT_INDEX_OF_EL >>
  simp[] >>
  disch_then drule >>
  simp[EL_MAP,find_index_INDEX_OF]
QED

Theorem IMP_translate_predicates_SOME:
  (∀cl. MEM cl l ⇒ ∃k. ce_to_clk ce (FST cl) = SOME k) ∧
  ALL_DISTINCT (MAP FST ce) ⇒
  ∃args.
    translate_predicates (ce_to_cl_tyid_map ns_len ce) l = SOME args
Proof
  Induct_on `l` >>
  rw[translate_predicates_def] >>
  gvs[FORALL_AND_THM,DISJ_IMP_THM,translate_predicate_def] >>
  gvs[FLOOKUP_ce_to_cl_tyid_map,ce_to_clk_def] >>
  metis_tac[ALOOKUP_find_index_SOME]
QED

Theorem EVERY_pred_type_kind_scheme_ok_IMP_translate_env_SOME:
  ALL_DISTINCT (MAP FST ce) ⇒
  ∀env.
  EVERY (λ(v,scheme).
    pred_type_kind_scheme_ok (ce_to_clk ce) tds db scheme) env ⇒
  ∃trans_env. translate_env (ce_to_cl_tyid_map ns_len ce) env =
    SOME (trans_env: (mlstring # type_kind_scheme) list)
Proof
  strip_tac >>
  Induct >>
  rw[translate_env_def] >>
  pairarg_tac >> gvs[translate_env_def] >>
  PairCases_on `scheme` >>
  Cases_on `scheme1` >>
  gvs[pred_type_kind_ok_alt,translate_pred_type_scheme_def,translate_pred_type_def] >>
  metis_tac[IMP_translate_predicates_SOME]
QED

Triviality alist_to_fmap_EQ_FUNUPDATE_LIST:
  alist_to_fmap l = FEMPTY |++ (REVERSE l)
Proof
  PURE_REWRITE_TAC[FUPDATE_LIST_EQ_APPEND_REVERSE] >>
  simp[]
QED

Triviality alist_to_fmap_FUNUPDATE_LIST:
  alist_to_fmap l |++ r = alist_to_fmap (REVERSE r ++ l)
Proof
  PURE_REWRITE_TAC[alist_to_fmap_EQ_FUNUPDATE_LIST,
    REVERSE_APPEND,REVERSE_REVERSE,
    finite_mapTheory.FUPDATE_LIST_APPEND] >>
  simp[]
QED

Theorem alist_to_fmap_DOMSUB_EQ_ID:
  (∀y. ¬MEM (x,y) l)⇒
  alist_to_fmap l \\ x = alist_to_fmap l
Proof
  rw[alist_to_fmap_EQ_FUNUPDATE_LIST,finite_mapTheory.DOMSUB_FUPDATE_LIST,
    combinTheory.o_DEF] >>
  `FILTER (λx'. x ≠ FST x') (REVERSE l) = REVERSE l`
    suffices_by metis_tac[] >>
  gvs[FILTER_REVERSE,FILTER_EQ_ID,EVERY_MEM,MEM_MAP,FORALL_PROD]
QED

Theorem IMP_translate_lie_alist_EXISTS_SOME:
  (∀cl t. (cl,t) ∈ FRANGE (alist_to_fmap (lie_alist:(mlstring # mlstring # type) list)) ⇒
    ∃k. ce_to_clk ce cl = SOME k) ∧
  ALL_DISTINCT (MAP FST ce) ∧
  ALL_DISTINCT (MAP FST lie_alist) ⇒
  ∃lie_env. translate_lie_alist (ce_to_cl_tyid_map ns_len ce) lie_alist =
    SOME (lie_env:(mlstring # type_kind_scheme) list)
Proof
  Induct_on `lie_alist` >>
  rw[translate_lie_alist_def] >>
  PairCases_on `h` >>
  gvs[translate_lie_alist_def,DISJ_IMP_THM,FORALL_AND_THM,FLOOKUP_ce_to_cl_tyid_map,
    ce_to_clk_def] >>
  simp[PULL_EXISTS] >>
  drule ALOOKUP_find_index_SOME >>
  rw[] >>
  gvs[EXISTS_PROD,PULL_EXISTS] >>
  first_x_assum irule >>
  rw[] >>
  last_x_assum irule >>
  gvs[MEM_MAP,FORALL_PROD] >>
  metis_tac[PAIR,alist_to_fmap_DOMSUB_EQ_ID]
QED

Theorem type_tcexp_SmartApp_Var:
  type_tcexp ns db st env (Var x) (Functions arg_tys ret_ty) ∧
  LIST_REL (λd t. type_tcexp ns db st env (tcexp_of d) t) ds arg_tys ⇒
  type_tcexp ns db st env (tcexp_of (SmartApp () (Var () x) ds)) ret_ty
Proof
  Cases_on `ds` >>
  rw[] >>
  gvs[SmartApp_def,cj 1 Functions_def,dest_App_def,tcexp_of_def] >>
  irule type_tcexp_App >>
  first_assum $ irule_at (Pos last) >>
  gvs[LIST_REL_EL_EQN,EL_MAP]
QED

Theorem type_tcexp_SmartLam:
  EVERY (type_ok (SND ns) db) arg_tys ∧ LENGTH arg_tys = LENGTH vs ∧
  type_tcexp ns db st (REVERSE (ZIP (vs,MAP ($, []) arg_tys)) ++ env)
    (tcexp_of e) ret_ty ⇒
  type_tcexp ns db st env (tcexp_of $ SmartLam () vs e)
    (Functions arg_tys ret_ty)
Proof
  strip_tac >>
  Cases_on `vs` >>
  gvs[SmartLam_def,Functions_def] >>
  TOP_CASE_TAC
  >- (
    gvs[tcexp_of_def] >>
    irule type_tcexp_Lam >>
    Cases_on `arg_tys` >>
    gvs[]
  ) >>
  TOP_CASE_TAC >>
  TOP_CASE_TAC
  >- (
    gvs[tcexp_of_def] >>
    irule type_tcexp_Lam >>
    Cases_on `arg_tys` >>
    gvs[]
  ) >>
  Cases_on `e` >>
  gvs[dest_Lam_def,tcexp_of_def] >>
  qpat_x_assum `type_tcexp _ _ _ _ _ _` $ mp_tac o SRULE[Once type_tcexp_cases] >>
  rw[] >>
  simp[GSYM Functions_APPEND] >>
  irule type_tcexp_Lam >>
  gvs[REVERSE_ZIP,REVERSE_APPEND,ZIP_APPEND]
QED

Theorem FST_SND_namespace_to_tcexp_namespace[simp]:
  SND (namespace_to_tcexp_namespace db) = tdefs_to_tcexp_tdefs (SND db) ∧
  FST (namespace_to_tcexp_namespace db) = FST db
Proof
  simp[namespace_to_tcexp_namespace_def]
QED

Theorem ALOOKUP_translate_env:
  ∀trans_env.
  translate_env cl_to_tyid env = SOME trans_env ⇒
  ALOOKUP trans_env s = OPTION_BIND
    (ALOOKUP env s)
    (translate_pred_type_scheme cl_to_tyid)
Proof
  Induct_on `env` >>
  rw[translate_env_def,FORALL_PROD] >>
  PairCases_on `h` >>
  gvs[translate_env_def,ALOOKUP_def] >>
  IF_CASES_TAC >>
  gvs[]
QED

Theorem ALOOKUP_translate_lie_NONE:
  ∀lie_env.
  translate_lie_alist cl_to_tyid lie = SOME lie_env ∧
  ALOOKUP lie s = NONE ⇒
  ALOOKUP lie_env s = NONE
Proof
  Induct_on `lie` >>
  rw[translate_lie_alist_def] >>
  PairCases_on `h` >>
  gvs[translate_lie_alist_def,AllCaseEqs()]
QED

Theorem ALOOKUP_translate_lie_SOME:
  ∀lie_env cl t.
  translate_lie_alist cl_to_tyid lie = SOME lie_env ∧
  ALOOKUP lie s = SOME (cl,t) ⇒
  ∃tyid.
    FLOOKUP cl_to_tyid cl = SOME tyid ∧
    ALOOKUP lie_env s = SOME ([],Cons (UserType tyid) t)
Proof
  Induct_on `lie` >>
  rw[translate_lie_alist_def] >>
  PairCases_on `h` >>
  gvs[translate_lie_alist_def,AllCaseEqs()]
QED

Theorem MEM_FST_translate_lie_alist:
  ∀lie_env x.
    translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
    MEM x lie_env ⇒
    ∃y z. MEM (FST x,y, z) lie_alist
Proof
  Induct_on `lie_alist` >>
  rw[translate_lie_alist_def] >>
  PairCases_on `h` >>
  gvs[translate_lie_alist_def,AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ALOOKUP_translate_ie:
  ∀ie_env.
  translate_ie_alist cl_to_tyid ie = SOME ie_env ⇒
  ALOOKUP ie_env s =
    OPTION_BIND (ALOOKUP ie s) (translate_entailment cl_to_tyid)
Proof
  Induct_on `ie` >>
  rw[translate_ie_alist_def] >>
  PairCases_on `h` >>
  gvs[translate_ie_alist_def] >>
  IF_CASES_TAC >>
  gvs[]
QED

Theorem ALOOKUP_ZIP_EXISTS_EQ:
  LENGTH xs = LENGTH ys ∧ LENGTH xs = LENGTH zs ⇒
  ((∃z. ALOOKUP (ZIP (xs,ys)) k = SOME z) ⇔ (∃z. ALOOKUP (ZIP (xs,zs)) k = SOME
  z))
  ∧
  (ALOOKUP (ZIP (xs,ys)) k = NONE ⇔ ALOOKUP (ZIP (xs,zs)) k = NONE)
Proof
  rw[EQ_IMP_THM] >>
  gvs[ALOOKUP_NONE,MEM_MAP,FORALL_PROD,MEM_ZIP] >>
  drule ALOOKUP_MEM >>
  rw[MEM_ZIP] >>
  simp[ALOOKUP_EXISTS_IFF,MEM_EL] >>
  metis_tac[EL_ZIP]
QED

Theorem freevars_cexp_SmartApp_Var:
  freevars_cexp (SmartApp x (Var y v) ds) =
    {v} ∪ BIGUNION (set (MAP freevars_cexp ds))
Proof
  Cases_on `ds` >>
  gvs[SmartApp_def,freevars_cexp_def,dest_App_def,SF ETA_ss]
QED

Triviality LIST_REL_pred_tsbust:
  ∀ps qs.
    LIST_REL (λ(c,t) (c',t'). c = c' ∧ tsubst subs t = t')
      ((cl,t)::ps) ((cl',t')::qs) ⇔
    cl = cl' ∧
    tsubst subs t = t' ∧
    MAP (I ## tsubst subs) ps = qs
Proof
  Induct_on `ps`
  >- (simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  gvs[LIST_REL_EL_EQN] >>
  rw[EQ_IMP_THM] >>
  ntac 2 (pairarg_tac >> gvs[])
QED

Theorem specialises_inst_alt:
  specialises_inst tds (Entail ks ps (cl,t)) (Entail ks' qs (cl',t')) =
  ∃subs.
    LIST_REL (kind_ok tds ks') ks subs ∧
    cl = cl' ∧
    tsubst subs t = t' ∧
    MAP (I ## tsubst subs) ps = qs
Proof
  simp[specialises_inst_def,LIST_REL_pred_tsbust,SF ETA_ss]
QED

Theorem translate_predicates_LIST_REL:
  ∀ps ps'.
  translate_predicates cl_to_tyid ps = SOME ps' ⇔
  LIST_REL
    (λ(cl,t) t'.
      ∃ut. FLOOKUP cl_to_tyid cl = SOME ut ∧
        t' = Cons (UserType ut) t)
    ps ps'
Proof
  Induct_on `ps` >>
  gvs[translate_predicates_def,translate_predicate_def] >>
  rw[PULL_EXISTS,EQ_IMP_THM] >>
  pairarg_tac >> gvs[]
QED

Theorem translate_predicates_subst:
  ∀ps'.
    translate_predicates cl_to_tyid (MAP (I ## tsubst subs) l) = SOME ps' ⇒
    ∃ps. translate_predicates cl_to_tyid l = SOME ps ∧ MAP (tsubst subs) ps = ps'
Proof
  Induct_on `l` >>
  rw[translate_predicates_def,PULL_EXISTS] >>
  Cases_on `h` >>
  gvs[translate_predicate_def,subst_db_def]
QED

Theorem specialises_inst_translate_entailment:
  specialises_inst tds it (Entail db ps (cl,t)) ∧
  translate_predicates cl_to_tyid ps = SOME ps' ∧
  FLOOKUP cl_to_tyid cl = SOME pid ⇒
  ∃s.
    translate_entailment cl_to_tyid it = SOME s ∧
    specialises (tdefs_to_tcexp_tdefs tds ++ cl_tds) db s
      (Functions ps' (Cons (UserType pid) t))
Proof
  simp[oneline translate_entailment_def] >>
  TOP_CASE_TAC >>
  simp[oneline specialises_inst_alt,AllCaseEqs(),PULL_EXISTS,
    translate_predicate_def] >>
  TOP_CASE_TAC >>
  rw[] >>
  simp[specialises_def,PULL_EXISTS,subst_db_Functions,subst_db_def] >>
  drule translate_predicates_subst >>
  rw[] >>
  simp[] >>
  irule_at (Pos last) EQ_REFL >>
  gvs[LIST_REL_EL_EQN] >>
  rw[] >>
  first_x_assum $ drule_then assume_tac >>
  irule kind_ok_tdefs_APPEND >>
  simp[kind_ok_tdefs_to_tcexp_tdefs]
QED

Theorem specialises_pred_specialises:
  specialises_pred (SND ns) db (q,Pred l t') (Pred ps t) ∧
  translate_predicates (ce_to_cl_tyid_map (LENGTH (SND ns)) ce) ps =
    SOME ps' ⇒
  ∃args.
    translate_predicates (ce_to_cl_tyid_map (LENGTH (SND ns)) ce) l =
      SOME args ∧
    specialises (tdefs_to_tcexp_tdefs (SND ns)) db
      (q,Functions args t') (Functions ps' t)
Proof
  rpt strip_tac >>
  gvs[specialises_pred_def,specialises_def,subst_db_pred_def,
    subst_db_Functions] >>
  drule translate_predicates_subst >>
  rw[] >>
  simp[] >>
  irule_at (Pos last) EQ_REFL >>
  drule_at_then (Pos last) irule $ LIST_REL_mono >>
  rw[kind_ok_tdefs_to_tcexp_tdefs]
QED

Theorem construct_dict_type_tcexp:
  translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  lie = alist_to_fmap lie_alist ∧
  ie = alist_to_fmap ie_alist ∧
  (∀v ent. MEM (v,ent) ie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
  (∀v cl ct. MEM (v,cl,ct) lie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
  (∀v ent cl t. MEM (v,ent) ie_alist ⇒ ¬MEM (v,cl,t) lie_alist) ∧
  (∀v ent cl ks ps t. MEM (v,Entail ks ps (cl,t)) ie_alist ⇒
    ∃pid. FLOOKUP cl_to_tyid cl = SOME pid)
  ⇒
  (∀p d. construct_dict tds db ie lie p d ⇒
    (∀v. v ∈ freevars_cexp d ⇒ v ∈ FDOM ie ∨ v ∈ FDOM lie) ∧
    ∃p'. translate_predicate cl_to_tyid p = SOME p' ∧
    type_tcexp (exnds,tdefs_to_tcexp_tdefs tds ++ cl_tds) db st
      (env ++ lie_env ++ ie_env) (tcexp_of d) p') ∧
  (∀ps ds. construct_dicts tds db ie lie ps ds ⇒
    (∀d v. MEM d ds ∧ v ∈ freevars_cexp d ⇒ v ∈ FDOM ie ∨ v ∈ FDOM lie) ∧
    ∃ps'. translate_predicates cl_to_tyid ps = SOME ps' ∧
    LIST_REL
      (λd t.
        type_tcexp (exnds,tdefs_to_tcexp_tdefs tds ++ cl_tds) db st
          (env ++ lie_env ++ ie_env) (tcexp_of d) t)
      ds ps')
Proof
  strip_tac >>
  ho_match_mp_tac construct_dict_ind >>
  rw[]
  >- (
    imp_res_tac ALOOKUP_MEM >>
    rw[MEM_MAP] >>
    metis_tac[FST]
  )
  >- (
    simp[tcexp_of_def] >>
    irule_at (Pos last) type_tcexp_Var >>
    PairCases_on `p` >>
    simp[ALOOKUP_APPEND] >>
    reverse $ CASE_TAC
    >- (
      imp_res_tac ALOOKUP_MEM >>
      metis_tac[PAIR]
    ) >>
    drule_all ALOOKUP_translate_lie_SOME >>
    rw[] >>
    simp[translate_predicate_def,specialises_def]
  )
  >- (
    imp_res_tac ALOOKUP_MEM >>
    gvs[freevars_cexp_SmartApp_Var,MEM_MAP] >>
    metis_tac[FST]
  )
  >- (
    irule_at (Pos last) type_tcexp_SmartApp_Var >>
    gvs[freevars_cexp_SmartApp_Var,MEM_MAP,PULL_EXISTS,
      DISJ_IMP_THM,LEFT_AND_OVER_OR,FORALL_AND_THM] >>
    qpat_assum `LIST_REL _ _ _` $ irule_at Any >>
    simp[translate_predicate_def,PULL_EXISTS] >>
    irule_at (Pos hd) type_tcexp_Var >>
    simp[ALOOKUP_APPEND] >>
    reverse $ CASE_TAC
    >- (
      imp_res_tac ALOOKUP_MEM >>
      metis_tac[PAIR]
    ) >>
    reverse $ CASE_TAC
    >- (
      imp_res_tac ALOOKUP_MEM >>
      spose_not_then kall_tac >>
      qpat_x_assum `∀v ent cl t. MEM (v,ent) ie_alist ⇒ _` drule >>
      rw[EXISTS_PROD] >>
      drule_all MEM_FST_translate_lie_alist >>
      simp[]
    ) >>
    drule ALOOKUP_translate_ie >>
    simp[] >>
    disch_then kall_tac >>
    rename1 `specialises_inst _ _ (Entail _ _ p)` >>
    PairCases_on `p` >>
    gvs[] >>
    rename1 `translate_entailment _ it = _` >>
    Cases_on `it` >>
    rename1 `Entail _ _ q` >>
    PairCases_on `q` >>
    drule_then drule specialises_inst_translate_entailment >>
    drule_then assume_tac ALOOKUP_MEM >>
    qpat_x_assum `!v cl ks ps t. _ ⇒ ∃pid. FLOOKUP cl_to_tyid _ = SOME _` drule >>
    rw[] >>
    gvs[specialises_inst_alt]
  )
  >- (
    gvs[LIST_REL_EL_EQN,MEM_MAP,MEM_EL] >>
    first_x_assum drule >>
    rw[]
  )
  >- (
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    Induct_on `LIST_REL` >>
    rw[translate_predicates_def,PULL_EXISTS] >>
    gvs[DISJ_IMP_THM,RIGHT_AND_OVER_OR,FORALL_AND_THM] >>
    metis_tac[]
  )
QED

Theorem translate_lie_alist_APPEND_lie_alist_IMP:
  ∀vs lie_alist lie_env'.
    translate_lie_alist cl_to_tyid (vs ++ lie_alist) = SOME lie_env' ⇒
    ∃vs_env lie_env.
      translate_lie_alist cl_to_tyid vs = SOME vs_env ∧
      translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
      lie_env' = vs_env ++ lie_env
Proof
  Induct_on `vs` >>
  rw[translate_lie_alist_def] >>
  PairCases_on `h` >>
  gvs[translate_lie_alist_def,PULL_EXISTS] >>
  metis_tac[]
QED

Theorem translate_lie_alist_translate_predicates_SOME:
  ∀lie_alist lie_env args.
  translate_lie_alist ce_to_tyid lie_alist = SOME lie_env ∧
  translate_predicates ce_to_tyid (MAP SND lie_alist) = SOME args ⇒
  lie_env = ZIP (MAP FST lie_alist, MAP ($, []) args)
Proof
  Induct_on `lie_alist` >>
  rw[translate_lie_alist_def,translate_predicates_def] >>
  PairCases_on `h` >>
  gvs[translate_lie_alist_def,translate_predicates_def,translate_predicate_def]
QED

Theorem translate_predicates_REVERSE:
  translate_predicates cl_to_tyid (REVERSE ps) = SOME (REVERSE ps') ⇔
  translate_predicates cl_to_tyid ps = SOME ps'
Proof
  simp[translate_predicates_LIST_REL]
QED

Triviality ALOOKUP_APPEND_EQ:
  ALOOKUP l x = ALOOKUP l' x ⇒
  ALOOKUP (l ++ r) x = ALOOKUP (l' ++ r) x
Proof
  rw[ALOOKUP_APPEND]
QED

Triviality INTER_EMPTY_IN_NOTIN:
  (a ∩ b = EMPTY) ⇔ (∀x. x ∈ a ⇒ x ∉ b)
Proof
  simp[IN_DEF,INTER_DEF,EXTENSION,IMP_DISJ_THM]
QED

Triviality ALL_DISTINCT_FRANGE_MEM:
  ∀l.
  ALL_DISTINCT (MAP FST l) ⇒
  (x ∈ FRANGE (alist_to_fmap l) ⇔ ∃k. MEM (k,x) l)
Proof
  Induct_on `l` >>
  rw[alist_to_fmap_EQ_FUNUPDATE_LIST,finite_mapTheory.FUPDATE_LIST_APPEND,MEM_MAP,FORALL_PROD,
    EQ_IMP_THM]
  >- (
    Cases_on `h` >>
    gvs[alist_to_fmap_EQ_FUNUPDATE_LIST,finite_mapTheory.FUPDATE_LIST_ALL_DISTINCT_REVERSE,
      GSYM finite_mapTheory.FUPDATE_EQ_FUPDATE_LIST]
    >- metis_tac[] >>
    drule $ SRULE[SUBSET_DEF] finite_mapTheory.FRANGE_DOMSUB_SUBSET >>
    metis_tac[]
  ) >>
  gvs[alist_to_fmap_EQ_FUNUPDATE_LIST,finite_mapTheory.FUPDATE_LIST_ALL_DISTINCT_REVERSE,
    GSYM finite_mapTheory.FUPDATE_EQ_FUPDATE_LIST] >>
  Cases_on `h` >>
  gvs[GSYM finite_mapTheory.FUPDATE_EQ_FUPDATE_LIST,finite_mapTheory.DOMSUB_FUPDATE_LIST] >>
  `FILTER  ((λy. q ≠ y) ∘ FST) l = l`
    suffices_by (rw[] >> metis_tac[]) >>
  rw[FILTER_EQ_ID,EVERY_MEM] >>
  metis_tac[PAIR]
QED

Theorem kindArrow_EQ_kind_arrows_single:
  kindArrow k = kind_arrows [k]
Proof
  rw[FUN_EQ_THM,kind_arrows_def]
QED

Theorem LENGTH_tdefs_to_tcexp_tdefs:
  LENGTH (tdefs_to_tcexp_tdefs l) = LENGTH l
Proof
  simp[tdefs_to_tcexp_tdefs_def]
QED

Theorem translate_env_MEM:
  ∀env trans_env v ks vt.
  translate_env cl_to_tyid env = SOME trans_env ⇒
  (MEM (v,ks,vt) trans_env ⇔
    ∃ks' pt. MEM (v,ks',pt) env ∧
    translate_pred_type_scheme cl_to_tyid (ks',pt) = SOME (ks,vt))
Proof
  Induct_on `env` >>
  rw[translate_env_def] >>
  rw[EQ_IMP_THM]
  >- (
    PairCases_on `h` >>
    gvs[translate_env_def] >>
    metis_tac[]
  )
  >- gvs[translate_env_def]
  >- (
    PairCases_on `h` >>
    gvs[translate_env_def] >>
    metis_tac[]
  )
QED

Theorem elaborated_texp_lambda_vars:
  ∀e e'. elaborated_texp e e' ⇒ lambda_vars e = lambda_vars e'
Proof
  Induct_on `elaborated_texp` >>
  rw[lambda_vars_def,lambda_varsl_def]
  >- (
    ntac 2 AP_TERM_TAC >>
    drule_at_then Any irule $ GSYM pure_miscTheory.LIST_REL_IMP_MAP_EQ >>
    rw[]
  )
  >- (
    ntac 3 AP_TERM_TAC >>
    drule_at_then Any irule $ GSYM pure_miscTheory.LIST_REL_IMP_MAP_EQ >>
    rw[]
  )
  >- (
    `MAP (FST o FST) fns = MAP (FST o FST) fns'`
      by rw[EL_MAP,LIST_EQ_REWRITE] >>
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    AP_THM_TAC >>
    ntac 4 AP_TERM_TAC >>
    rev_drule_at_then Any irule $ GSYM pure_miscTheory.LIST_REL_IMP_MAP_EQ >>
    rw[]
  )
  >- (
    `MAP (cepat_vars ∘ FST) pes = MAP (cepat_vars ∘ FST) pes'`
      by rw[EL_MAP,LIST_EQ_REWRITE] >>
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    `MAP (λx. lambda_vars (SND x)) pes = MAP (λx. lambda_vars (SND x)) pes'`
      by (
        drule_at_then Any irule $ GSYM pure_miscTheory.LIST_REL_IMP_MAP_EQ >>
        rw[]
      ) >>
    simp[]
  )
QED

Theorem type_elaborate_texp_lambda_vars:
  (∀ns clk ie lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
    lambda_vars e = lambda_vars e') ∧
  (∀ns clk ie lie db st env e e' pt.
    pred_type_elaborate_texp ns clk ie lie db st env e e' pt ⇒
    lambda_vars e = lambda_vars e')
Proof
  metis_tac[elaborated_texp_lambda_vars,type_elaborate_texp_elaborated_texp]
QED

Theorem class_env_to_ns_EL:
  ∀ce' clcons cl_tds.
  class_env_to_ns ce cl_to_tyid clcons ce' = SOME cl_tds ∧
  LENGTH ce' ≤ LENGTH clcons ⇒
  LENGTH cl_tds = LENGTH ce' ∧
  (∀i. i < LENGTH ce' ⇒
    ∃c k supers methods method_tys sup_tys.
    EL i ce' = (c,k,supers,methods) ∧
    OPT_MMAP (translate_pred_type_scheme cl_to_tyid) (MAP SND methods) = SOME method_tys ∧
    translate_superclasses cl_to_tyid supers = SOME sup_tys ∧
    EL i cl_tds = ([k],[(EL i clcons,sup_tys ++ method_tys)]))
Proof
  Induct_on `ce'` >>
  rw[class_env_to_ns_def] >>
  PairCases_on `h` >>
  Cases_on `clcons` >>
  gvs[class_env_to_ns_def,IMP_CONJ_THM,FORALL_AND_THM,class_to_datatype_def]
  >- metis_tac[] >>
  Cases_on `i` >>
  gvs[]
QED

Theorem lambda_vars_IMP_lambda_varsl:
  v ∈ lambda_vars (EL n es) ∧ n < LENGTH es ⇒ v ∈ lambda_varsl es
Proof
  rw[lambda_varsl_def,MEM_MAP] >>
  metis_tac[MEM_EL]
QED

Overload tshift_lie_alist = ``λn. MAP (λ(v,cl,t). (v,cl,tshift n t))``;

Theorem tshift_lie_map_alist_to_fmap:
  tshift_lie_map n (alist_to_fmap l) = alist_to_fmap (tshift_lie_alist n l)
Proof
  simp[alist_to_fmap_EQ_FUNUPDATE_LIST,pure_miscTheory.o_f_FUPDATE_LIST,
    MAP_REVERSE,LAMBDA_PROD]
QED

Theorem translate_lie_alist_tshift_lie_alist:
  ∀lie_env. 
  translate_lie_alist cl_to_tyid (tshift_lie_alist n lie_alist) = SOME lie_env ⇔
  ∃lie_env'.
    translate_lie_alist cl_to_tyid lie_alist = SOME lie_env' ∧
    lie_env = tshift_env n lie_env'
Proof
  Induct_on `lie_alist` >>
  rw[translate_lie_alist_def] >>
  PairCases_on `h` >>
  rw[EQ_IMP_THM] >>
  gvs[translate_lie_alist_def,shift_db_def]
QED

Theorem translate_pred_type_shift_db_pred:
  translate_pred_type cl_to_tyid (shift_db_pred n m pt) = SOME t ⇔
  ∃t'. translate_pred_type cl_to_tyid pt = SOME t' ∧ t = shift_db n m t'
Proof
  Cases_on `pt` >>
  rw[shift_db_pred_def,translate_pred_type_def,PULL_EXISTS,shift_db_Functions,
    translate_predicates_LIST_REL,LIST_REL_EL_EQN,EL_MAP,FORALL_PROD] >>
  rw[EQ_IMP_THM]
  >- (
    qexists_tac `MAP (λ(cl,t).
      Cons (UserType (the ARB $ FLOOKUP cl_to_tyid cl)) t) l` >>
    rw[EL_MAP]
    >- (
      pairarg_tac >> gvs[] >>
      Cases_on `FLOOKUP cl_to_tyid cl` >>
      gvs[libTheory.the_def] >>
      first_x_assum drule >>
      rw[]
    ) >>
    simp[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,shift_db_def] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    rw[LIST_EQ_REWRITE,EL_MAP] >>
    pairarg_tac >> gvs[] >>
    first_x_assum drule >>
    rw[] >>
    simp[libTheory.the_def]
  ) >>
  irule_at (Pos last) EQ_REFL >>
  rw[EL_MAP] >>
  Cases_on `EL n' l` >>
  gvs[] >>
  first_x_assum drule >>
  rw[] >>
  simp[shift_db_def]
QED

Theorem translate_env_tshift_env_pred:
  ∀trans_env.
  translate_env cl_to_tyid (tshift_env_pred n env) = SOME trans_env ⇔
  ∃trans_env'.
    translate_env cl_to_tyid env = SOME trans_env' ∧
    trans_env = tshift_env n trans_env'
Proof
  Induct_on `env` >>
  rw[translate_env_def] >>
  PairCases_on `h` >>
  rw[EQ_IMP_THM] >>
  gvs[translate_env_def,PULL_EXISTS,translate_pred_type_scheme_def,
    translate_pred_type_shift_db_pred]
QED

Theorem tshift_env_unchanged:
  (∀v ks t. MEM (v,ks,t) env ⇒ freetyvars_ok (LENGTH ks) t) ⇒
  tshift_env n env = env
Proof
  rw[LAMBDA_PROD,LIST_EQ_REWRITE,EL_MAP,MEM_EL,PULL_EXISTS] >>
  pairarg_tac >>
  rw[] >>
  first_x_assum drule >>
  rw[] >>
  drule_then irule shift_db_unchanged >>
  simp[LESS_EQ_REFL]
QED

Theorem translate_predicates_OPT_MMAP:
  translate_predicates cl_to_tyid ps =
    OPT_MMAP (translate_predicate cl_to_tyid) ps
Proof
  Induct_on `ps` >>
  rw[translate_predicates_def]
QED

Theorem OPT_MMAP_SOME_LIST_REL:
  ∀ys.
  OPT_MMAP f xs = SOME ys ⇔
  LIST_REL (λx y. f x = SOME y) xs ys
Proof
  Induct_on `xs` >>
  gvs[OPT_MMAP_def] >>
  rw[EQ_IMP_THM]
QED

Theorem translate_predicate_type_ok:
  class_env_to_ns ce (ce_to_cl_tyid_map (LENGTH tds) ce) clcons ce =
    SOME cl_tds ∧
  LENGTH ce ≤ LENGTH clcons ∧
  ALL_DISTINCT (MAP FST ce) ∧
  ce_to_clk ce cl = SOME k ∧
  kind_ok (tds ++ cl_tds) ks k t ∧
  translate_predicate (ce_to_cl_tyid_map (LENGTH tds) ce) (cl,t) = SOME t' ⇒
  type_ok (tds ++ cl_tds) ks t'
Proof
  rw[translate_predicate_def,type_ok] >>
  gvs[FLOOKUP_ce_to_cl_tyid_map,kind_ok,
    kindArrow_EQ_kind_arrows_single,kind_arrows_kindType_EQ] >>
  first_assum $ irule_at (Pos hd) >>
  simp[oEL_THM,EL_APPEND_EQN] >>
  drule find_index_LESS_LENGTH >>
  simp[] >>
  drule class_env_to_ns_EL >>
  rw[] >>
  first_x_assum drule >>
  rw[] >>
  simp[] >>
  gvs[ce_to_clk_def] >>
  drule ALOOKUP_find_index_SOME >>
  rw[]
QED

Theorem translate_predicates_type_ok:
  class_env_to_ns ce (ce_to_cl_tyid_map (LENGTH tds) ce) clcons ce =
    SOME cl_tds ∧
  LENGTH ce ≤ LENGTH clcons ∧
  ALL_DISTINCT (MAP FST ce) ∧
  EVERY (λ(c,t'). ∃k. ce_to_clk ce c = SOME k ∧
    kind_ok (tds ++ cl_tds) ks k t') ps ∧
  translate_predicates (ce_to_cl_tyid_map (LENGTH tds) ce) ps = SOME pts ∧
  MEM arg pts ⇒
  type_ok (tds ++ cl_tds) ks arg
Proof
  rw[EVERY_EL,translate_predicates_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,
    LIST_REL_EL_EQN,MEM_EL] >>
  gvs[] >>
  first_x_assum drule >>
  first_x_assum drule >>
  pairarg_tac >>
  rw[] >>
  drule_then irule translate_predicate_type_ok >>
  metis_tac[]
QED

Theorem OPT_MMAP_SOME_APPEND:
  ∀r lr.
    OPT_MMAP f (l ++ r) = SOME lr ⇔
    ∃l' r'.
      OPT_MMAP f l = SOME l' ∧ OPT_MMAP f r = SOME r' ∧
      lr = l' ++ r'
Proof
  Induct_on `l` >>
  rw[EQ_IMP_THM,PULL_EXISTS]
QED

Theorem OPT_MMAP_SOME_REVERSE:
  ∀r.
  OPT_MMAP f (REVERSE l) = SOME r ⇔
    ∃l'. OPT_MMAP f l = SOME l' ∧ r = REVERSE l'
Proof
  Induct_on `l` >> rw[EQ_IMP_THM,PULL_EXISTS,OPT_MMAP_SOME_APPEND]
QED

Theorem translate_env_OPT_MMAP:
  translate_env cl_to_tyid l =
    OPT_MMAP (λ(cl,t). OPTION_MAP ($, cl) $
      translate_pred_type_scheme cl_to_tyid t) l
Proof
  Induct_on `l` >> rw[translate_env_def] >>
  pairarg_tac >> rw[translate_env_def,oneline OPTION_MAP_DEF] >>
  CASE_TAC >>
  rw[]
QED

Theorem translate_env_SOME_APPEND:
  translate_env cl_to_tyid (l ++ r) = SOME lr ⇔
  ∃l' r'.
    translate_env cl_to_tyid l = SOME l' ∧
    translate_env cl_to_tyid r = SOME r' ∧
    lr = l' ++ r'
Proof
  simp[translate_env_OPT_MMAP,OPT_MMAP_SOME_APPEND]
QED

Theorem translate_ie_alist_OPT_MMAP:
  translate_ie_alist cl_to_tyid l =
    OPT_MMAP (λ(v,t). OPTION_MAP ($, v) $
      translate_entailment cl_to_tyid t) l
Proof
  Induct_on `l` >> rw[translate_ie_alist_def] >>
  pairarg_tac >> rw[translate_ie_alist_def,oneline OPTION_MAP_DEF] >>
  CASE_TAC >>
  rw[]
QED

Theorem translate_lie_alist_OPT_MMAP:
  translate_lie_alist cl_to_tyid l =
    OPT_MMAP (λ(name,cl,t).
      OPTION_MAP (λcid.(name,[],Cons (UserType cid) t)) $
        FLOOKUP cl_to_tyid cl) l
Proof
  Induct_on `l` >> rw[translate_lie_alist_def] >>
  pairarg_tac >> rw[translate_lie_alist_def,oneline OPTION_MAP_DEF] >>
  CASE_TAC >> rw[]
QED

Theorem translate_lie_alist_SOME_APPEND:
  translate_lie_alist cl_to_tyid (l ++ r) = SOME lr ⇔
  ∃l' r'.
    translate_lie_alist cl_to_tyid l = SOME l' ∧
    translate_lie_alist cl_to_tyid r = SOME r' ∧
    lr = l' ++ r'
Proof
  simp[translate_lie_alist_OPT_MMAP,OPT_MMAP_SOME_APPEND]
QED

Theorem translate_lie_alist_SOME_REVERSE:
  translate_lie_alist cl_to_tyid (REVERSE l) = SOME r ⇔
  ∃r'. translate_lie_alist cl_to_tyid l = SOME r' ∧ r = REVERSE r'
Proof
  simp[translate_lie_alist_OPT_MMAP,OPT_MMAP_SOME_REVERSE]
QED

Theorem translate_lie_alist_ZIP_SOME:
  ∀vs ps r.
  LENGTH vs = LENGTH ps ⇒ 
  (translate_lie_alist cl_to_tyid $ ZIP (vs,ps) = SOME r ⇔
  ((∀cl t. MEM (cl,t) ps ⇒ ∃cid. FLOOKUP cl_to_tyid cl = SOME cid) ∧
  r = ZIP (vs,MAP (λ(cl,t).
    ([],Cons (UserType (the ARB $ FLOOKUP cl_to_tyid cl)) t)) ps)))
Proof
  Induct_on `vs` >>
  Cases_on `ps` >>
  rw[translate_lie_alist_def,EQ_IMP_THM] >>
  gvs[translate_lie_alist_def] >>
  PairCases_on `h` >>
  gvs[translate_lie_alist_def,FORALL_AND_THM,DISJ_IMP_THM,libTheory.the_def] >>
  metis_tac[]
QED

Theorem entailment_kind_ok_type_ok:
  class_env_to_ns ce (ce_to_cl_tyid_map len ce) clcons ce =
    SOME cl_tds ∧
  LENGTH ce ≤ LENGTH clcons ∧
  len = LENGTH tds ∧
  ALL_DISTINCT (MAP FST ce) ⇒
  ∀env.
  translate_ie_alist (ce_to_cl_tyid_map len ce) ie_alist =
    SOME env ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  (∀ent.
      ent ∈ FRANGE (alist_to_fmap ie_alist) ⇒
      entailment_kind_ok tds (ce_to_clk ce) ent) ⇒
   (∀v ks t. MEM (v,ks,t) env ⇒ type_ok (tds ++ cl_tds) ks t)
Proof
  Induct_on `ie_alist` >>
  rw[translate_ie_alist_def] >>
  PairCases_on `h` >>
  gvs[translate_ie_alist_def,DISJ_IMP_THM,FORALL_AND_THM,MEM_MAP,FORALL_PROD]
  >- (
    Cases_on `h1` >>
    gvs[entailment_kind_ok_def,translate_entailment_def,AllCaseEqs(),
      type_ok_def,kind_ok_Functions] >>
    disj2_tac >>
    rw[]
    >- (
      drule_then irule $ SRULE[type_ok] translate_predicate_type_ok >>
      Cases_on `p` >>
      gvs[] >>
      metis_tac[kind_ok_tdefs_APPEND]
    ) >>
    (drule_at_then (Pos last) $ drule_at_then (Pos last) $ drule_then irule) $
      SRULE[type_ok_def] translate_predicates_type_ok >>
    gvs[EVERY_MEM,FORALL_PROD] >>
    rw[] >>
    first_x_assum drule >>
    rw[] >>
    simp[] >>
    metis_tac[kind_ok_tdefs_APPEND]
  ) >>
  last_x_assum $ drule_at_then (Pos last) irule >>
  rw[] >>
  `alist_to_fmap ie_alist \\ h0 = alist_to_fmap ie_alist`
    suffices_by metis_tac[] >>
  irule alist_to_fmap_DOMSUB_EQ_ID >>
  rw[]
QED

Theorem entailment_kind_ok_tdefs_to_tcexp_tdefs:
  entailment_kind_ok (tdefs_to_tcexp_tdefs tds) = entailment_kind_ok tds
Proof
  rw[FUN_EQ_THM,oneline entailment_kind_ok_def] >>
  CASE_TAC >>
  pairarg_tac >>
  rw[EQ_IMP_THM,EVERY_MEM,FORALL_PROD] >>
  metis_tac[kind_ok_tdefs_to_tcexp_tdefs]
QED

Theorem type_cons_EQ_tcexp_type_cons:
  type_cons tds db (cname,carg_ts) (tyid,tyargs) ⇔
  tcexp_type_cons (tdefs_to_tcexp_tdefs tds) db
    (cname,MAP ($, []) carg_ts) (tyid,tyargs)
Proof
  rw[type_cons_def,tcexp_type_cons_def,oEL_THM,LENGTH_tdefs_to_tcexp_tdefs,
    kind_ok_tdefs_to_tcexp_tdefs,EQ_IMP_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[EL_MAP,tdefs_to_tcexp_tdefs_def,LAMBDA_PROD,lambdify PAIR_MAP] >>
  gvs[ALOOKUP_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
  pairarg_tac >>
  gvs[ALOOKUP_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
  gvs[LIST_EQ_REWRITE,EL_MAP]
QED

Theorem tcexp_type_cons_tdefs_APPEND:
  tcexp_type_cons tds db c t ⇒
  tcexp_type_cons (tds ++ tds') db c t
Proof
  simp[oneline tcexp_type_cons_def] >>
  rpt CASE_TAC >>
  rw[oEL_THM,EL_APPEND_EQN] >>
  simp[] >>
  drule_at_then (Pos last) irule $ LIST_REL_mono >>
  simp[kind_ok_tdefs_APPEND]
QED

Theorem tcexp_destruct_type_cons_tdefs_APPEND:
  tcexp_destruct_type_cons (edef,tds) db t cname carg_ts ⇒
  tcexp_destruct_type_cons (edef,tds ++ tds') db t cname carg_ts
Proof
  simp[oneline tcexp_destruct_type_cons_def] >>
  TOP_CASE_TAC >>
  rw[] >>
  every_case_tac >>
  metis_tac[tcexp_type_cons_tdefs_APPEND]
QED

Theorem tcexp_type_cepat_tdefs_APPEND:
  ∀pat t vts.
  tcexp_type_cepat (edef,tds) db pat t vts ⇒
    tcexp_type_cepat (edef,tds ++ tds') db pat t vts
Proof
  ho_match_mp_tac tcexp_type_cepat_ind >>
  rw[] >>
  simp[Once tcexp_type_cepat_cases]
  >- metis_tac[specialises_tdefs_APPEND] >>
  gvs[SF ETA_ss] >>
  metis_tac[tcexp_destruct_type_cons_tdefs_APPEND]
QED

Theorem destruct_type_cons_EQ_tcexp_destruct_type_cons:
  destruct_type_cons (edef,tds) db t cname carg_ts ⇔
    tcexp_destruct_type_cons (edef,tdefs_to_tcexp_tdefs tds) db t cname
      (MAP ($,[]) carg_ts)
Proof
  rw[destruct_type_cons_def,tcexp_destruct_type_cons_def,EVERY_MAP,
    MAP_MAP_o,combinTheory.o_DEF] >>
  Cases_on `split_ty_cons t` >>
  simp[] >>
  PairCases_on `x` >>
  simp[] >>
  every_case_tac >> gvs[]
  >- metis_tac[type_cons_EQ_tcexp_type_cons] >>
  rw[EQ_IMP_THM,LIST_EQ_REWRITE] >>
  gvs[EL_MAP]
QED

Theorem specialises_REFL:
  specialises tds db ([],t) t
Proof
  simp[specialises_def]
QED

Theorem type_cepat_IMP_tcexp_type_cepat:
  ∀pat t vts.
  type_cepat (edef,tds) db pat t vts ⇒
    tcexp_type_cepat (edef,tdefs_to_tcexp_tdefs tds) db pat ([],t) vts
Proof
  ho_match_mp_tac type_cepat_ind >>
  rw[] >> simp[Once tcexp_type_cepat_cases,specialises_REFL] >>
  (drule_then $ irule_at Any) $ iffLR destruct_type_cons_EQ_tcexp_destruct_type_cons >>
  gvs[LIST_REL3_EL,EL_MAP] >>
  metis_tac[]
QED

(* same as the safe version *)
Theorem unsafe_type_cons_EQ_tcexp_unsafe_type_cons:
  unsafe_type_cons tds (cname,carg_ts) (tyid,tyargs) ⇔
  unsafe_tcexp_type_cons (tdefs_to_tcexp_tdefs tds)
    (cname,MAP ($, []) carg_ts) (tyid,tyargs)
Proof
  rw[unsafe_type_cons_def,unsafe_tcexp_type_cons_def,oEL_THM,
    LENGTH_tdefs_to_tcexp_tdefs,EQ_IMP_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[EL_MAP,tdefs_to_tcexp_tdefs_def,LAMBDA_PROD,lambdify PAIR_MAP] >>
  gvs[ALOOKUP_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
  pairarg_tac >>
  gvs[ALOOKUP_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
  gvs[LIST_EQ_REWRITE,EL_MAP]
QED

Theorem unsafe_tcexp_type_cons_tdefs_APPEND:
  unsafe_tcexp_type_cons tds c t ⇒
  unsafe_tcexp_type_cons (tds ++ tds') c t
Proof
  simp[oneline unsafe_tcexp_type_cons_def] >>
  rpt CASE_TAC >>
  rw[oEL_THM,EL_APPEND_EQN]
QED

Theorem unsafe_tcexp_destruct_type_cons_tdefs_APPEND:
  unsafe_tcexp_destruct_type_cons (edef,tds) t cname carg_ts ⇒
  unsafe_tcexp_destruct_type_cons (edef,tds ++ tds') t cname carg_ts
Proof
  simp[oneline unsafe_tcexp_destruct_type_cons_def] >>
  TOP_CASE_TAC >>
  rw[] >>
  every_case_tac >>
  metis_tac[unsafe_tcexp_type_cons_tdefs_APPEND]
QED

Theorem unsafe_destruct_type_cons_EQ_unsafe_tcexp_destruct_type_cons:
  unsafe_destruct_type_cons (edef,tds) t cname carg_ts ⇔
    unsafe_tcexp_destruct_type_cons (edef,tdefs_to_tcexp_tdefs tds) t cname
      (MAP ($,[]) carg_ts)
Proof
  rw[unsafe_destruct_type_cons_def,unsafe_tcexp_destruct_type_cons_def,EVERY_MAP,
    MAP_MAP_o,combinTheory.o_DEF] >>
  Cases_on `split_ty_cons t` >>
  simp[] >>
  PairCases_on `x` >>
  simp[] >>
  every_case_tac >> gvs[]
  >- metis_tac[unsafe_type_cons_IMP_tcexp_unsafe_type_cons] >>
  rw[EQ_IMP_THM,LIST_EQ_REWRITE] >>
  gvs[EL_MAP]
QED

Triviality CONS_APPEND_APPEND:
  x::(l ++ m ++ r) = x::l ++ m ++ r
Proof
  simp[]
QED

Theorem texp_construct_dict_type_tcexp:
  class_env_to_ns ce (ce_to_cl_tyid_map (LENGTH $ SND ns) ce)
    clcons ce = SOME cl_tds ∧
  LENGTH ce ≤ LENGTH clcons ∧
  ALL_DISTINCT (MAP FST ce) ∧
  clk = ce_to_clk ce ∧
  cl_to_tyid = ce_to_cl_tyid_map (LENGTH $ SND ns) ce ∧
  ie_map = alist_to_fmap ie_alist ∧
  ie = FRANGE (alist_to_fmap ie_alist) ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  (∀ent. ent ∈ ie ⇒ entailment_kind_ok (SND ns) clk ent)
  ⇒
  (∀lie db st env e e' pt.
    pred_type_elaborate_texp ns clk ie lie db st env e e' pt ⇒
      ∀lie_alist de trans_env lie_env.
      translate_env cl_to_tyid env = SOME trans_env ∧
      translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
      lie = FRANGE (alist_to_fmap lie_alist) ∧
      EVERY (type_ok (SND ns) db) st ∧
      EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk (SND ns) db scheme) env ∧
      ALL_DISTINCT (MAP FST lie_alist) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ v ∉ lambda_vars e) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ ∀cl t. ¬MEM (v,cl,t) lie_alist) ∧
      (∀v cl ct. MEM (v,cl,ct) lie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
      (∀v ks vt. MEM (v,ks,vt) lie_alist ⇒ v ∉ lambda_vars e) ∧
      (* lie kind ok *)
      (∀cl t. (cl,t) ∈ lie ⇒ ∃k. clk cl = SOME k ∧ kind_ok (SND ns) db k t) ∧
      pred_texp_construct_dict ns ie_map (alist_to_fmap lie_alist) db
        (set (MAP FST env)) pt e' de ⇒
      ∃trans_pt.
        translate_pred_type cl_to_tyid pt = SOME trans_pt ∧
        type_tcexp
          (append_ns (namespace_to_tcexp_namespace ns) ([],cl_tds))
          db st
          (trans_env ++ lie_env ++ ie_env)
          (tcexp_of de) trans_pt) ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
      ∀lie_alist de trans_env lie_env.
      translate_env cl_to_tyid env = SOME trans_env ∧
      translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧

      lie = FRANGE (alist_to_fmap lie_alist) ∧
      EVERY (type_ok (SND ns) db) st ∧
      EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk (SND ns) db scheme) env ∧
      ALL_DISTINCT (MAP FST lie_alist) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ v ∉ lambda_vars e) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ ∀cl t. ¬MEM (v,cl,t) lie_alist) ∧
      (∀v cl ct. MEM (v,cl,ct) lie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
      (∀v ks vt. MEM (v,ks,vt) lie_alist ⇒ v ∉ lambda_vars e) ∧
      (∀cl t. (cl,t) ∈ lie ⇒ ∃k. clk cl = SOME k ∧ kind_ok (SND ns) db k t) ∧
      texp_construct_dict ns ie_map (alist_to_fmap lie_alist) db
        (set (MAP FST env)) e' de ⇒
      type_tcexp
        (append_ns (namespace_to_tcexp_namespace ns) ([],cl_tds))
        db st
        (trans_env ++ lie_env ++ ie_env)
        (tcexp_of de) t)
Proof
  strip_tac >>
  ho_match_mp_tac type_elaborate_texp_strongind >>
  rw[lambda_vars_def]
  >- (
    (* Var *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[] >>
    irule type_tcexp_SmartApp_Var >>
    irule_at (Pos last) type_tcexp_Var >>
    drule ALOOKUP_translate_env >>
    simp[ALOOKUP_APPEND] >>
    disch_then kall_tac >>
    simp[translate_pred_type_scheme_def,oneline translate_pred_type_def] >>
    rename1 `ALOOKUP env x = SOME xt` >>
    PairCases_on `xt` >>
    CASE_TAC >>
    simp[AllCaseEqs(),PULL_EXISTS,EXISTS_PROD] >>
    (drule_then $ drule_then $ drule_at (Pat `construct_dicts _ _ _ _ _ _`)) $
      cj 2 construct_dict_type_tcexp >>
    disch_then $ qspecl_then [`st`,`FST ns`,`trans_env`,`cl_tds`] mp_tac >>
    gvs[] >>
    impl_tac
    >- (
      rw[]
      >- metis_tac[translate_env_MEM]
      >- metis_tac[translate_env_MEM]
      >- metis_tac[]
      >- (
        gvs[ALL_DISTINCT_FRANGE_MEM,PULL_EXISTS] >>
        last_x_assum drule >>
        rw[entailment_kind_ok_def,ce_to_clk_def] >>
        simp[FLOOKUP_ce_to_cl_tyid_map] >>
        metis_tac[ALOOKUP_find_index_SOME]
      )
    ) >>
    rw[] >>
    first_assum $ irule_at (Pos last) >>
    simp[RIGHT_AND_OVER_OR,EXISTS_OR_THM] >>
    rpt disj2_tac >>
    simp[PULL_EXISTS] >>
    drule_then drule specialises_pred_specialises >>
    rw[] >>
    simp[specialises_tdefs_APPEND]
  )
  >- (
    (* Pred *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[] >>
    qpat_x_assum `texp_construct_dict _ _ _ _ _ _ _` $ strip_assume_tac o
      PURE_REWRITE_RULE[alist_to_fmap_FUNUPDATE_LIST] >>
    last_x_assum $ drule_at (Pat `texp_construct_dict _ _ _ _ _ _ _`) >>
    simp[translate_lie_alist_SOME_APPEND,translate_lie_alist_SOME_REVERSE,
      translate_lie_alist_ZIP_SOME] >>
    impl_tac
    >- (
      conj_tac
      >- (
        gvs[pred_type_kind_ok_alt,FORALL_PROD,FLOOKUP_ce_to_cl_tyid_map,
          ce_to_clk_def,PULL_EXISTS] >>
        metis_tac[ALOOKUP_find_index_SOME]
      ) >>
      conj_tac
      >- (
        DEP_REWRITE_TAC[finite_mapTheory.FRANGE_FUNION] >>
        gvs[FDOM_alist_to_fmap,DISJOINT_DEF,INTER_EMPTY_IN_NOTIN,MEM_MAP,
          MEM_ZIP,FORALL_PROD,PULL_EXISTS] >>
        rw[Once UNION_COMM]
        >- metis_tac[MEM_EL] >>
        AP_THM_TAC >> AP_TERM_TAC >>
        rw[EXTENSION] >>
        DEP_REWRITE_TAC[ALL_DISTINCT_FRANGE_MEM] >>
        simp[REVERSE_ZIP,MEM_ZIP,MEM_EL,MAP_ZIP]
      ) >>
      conj_tac
      >- (
        simp[MAP_REVERSE,ALL_DISTINCT_APPEND,MAP_ZIP,MEM_MAP,FORALL_PROD,
          PULL_EXISTS,MEM_ZIP] >>
        gvs[INTER_EMPTY_IN_NOTIN,MEM_MAP,FORALL_PROD] >>
        metis_tac[MEM_EL]
      ) >>
      gvs[FDOM_alist_to_fmap,DISJOINT_DEF,INTER_EMPTY_IN_NOTIN,MEM_MAP,
        MEM_ZIP,FORALL_PROD,PULL_EXISTS,IMP_CONJ_THM,FORALL_AND_THM] >>
      conj_tac >- gvs[] >>
      conj_tac >- gvs[] >>
      reverse $ rpt strip_tac >>
      gvs[pred_type_kind_ok_alt,FORALL_PROD,INTER_EMPTY_IN_NOTIN,MEM_MAP,
        MEM_ZIP] >>
      metis_tac[MEM_EL,type_elaborate_texp_lambda_vars]
    ) >>
    strip_tac >>
    simp[translate_pred_type_def,PULL_EXISTS] >>
    qspecl_then [`LENGTH (SND ns)`,`ps`,`ce`] mp_tac $
      GEN_ALL IMP_translate_predicates_SOME >>
    impl_tac
    >- (
      gvs[pred_type_kind_ok_alt] >>
      metis_tac[]
    ) >>
    strip_tac >>
    gvs[] >>
    irule type_tcexp_SmartLam >>
    drule $ iffLR translate_predicates_LIST_REL >>
    gvs[LIST_REL_EL_EQN] >>
    rw[EVERY_EL]
    >- (
      gvs[ALL_DISTINCT_FRANGE_MEM,PULL_EXISTS] >>
      first_x_assum drule >>
      pairarg_tac >> rw[] >>
      gvs[type_ok,entailment_kind_ok_def,PULL_EXISTS,oEL_THM,FLOOKUP_ce_to_cl_tyid_map] >>
      simp[kindArrow_EQ_kind_arrows_single,kind_arrows_kindType_EQ] >>
      drule find_index_LESS_LENGTH >>
      qspec_then `SND ns` assume_tac $ GEN_ALL LENGTH_tdefs_to_tcexp_tdefs >>
      rw[EL_APPEND_EQN] >>
      gvs[pred_type_kind_ok_alt,MEM_EL,PULL_EXISTS] >>
      qpat_x_assum `∀n. n < LENGTH _ ⇒
        ∃k. ce_to_clk _ _ = SOME _ ∧ _` drule >>
      rw[ce_to_clk_def] >>
      drule_then strip_assume_tac ALOOKUP_find_index_SOME >>
      gvs[] >>
      drule_all class_env_to_ns_EL >>
      rw[] >>
      first_x_assum drule >>
      rw[] >>
      gvs[] >>
      irule kind_ok_tdefs_APPEND >>
      simp[kind_ok_tdefs_to_tcexp_tdefs]
    ) >>
    drule_then irule type_tcexp_env_extensional >>
    rpt strip_tac >>
    gvs[MAP_ZIP,REVERSE_ZIP,GSYM MAP_REVERSE] >>
    irule ALOOKUP_APPEND_EQ >>
    irule ALOOKUP_APPEND_EQ >>
    simp[ALOOKUP_APPEND,ALOOKUP_ZIP_MAP_SND,oneline OPTION_MAP_DEF] >>
    CASE_TAC
    >- (
      drule_at_then (Pos last) (qspec_then `REVERSE args` strip_assume_tac) $
        iffLR $ cj 2 ALOOKUP_ZIP_EXISTS_EQ >>
      gvs[] >>
      CASE_TAC >> simp[]
    ) >>
    drule_at_then (Pos last) (qspec_then `REVERSE args` strip_assume_tac) $
      SRULE[PULL_EXISTS] $ iffLR $ cj 1 ALOOKUP_ZIP_EXISTS_EQ >>
    gvs[INTER_EMPTY_IN_NOTIN,MEM_MAP,FORALL_PROD,IMP_CONJ_THM,
      FORALL_AND_THM] >>
    imp_res_tac ALOOKUP_find_index_SOME >> 
    gvs[EL_ZIP,MAP_ZIP,EL_REVERSE,translate_predicates_LIST_REL,
      LIST_REL_EL_EQN] >>
    `PRE (LENGTH args - i) < LENGTH args` by fs[] >>
    first_x_assum drule >>
    pairarg_tac >>
    rw[] >>
    gvs[libTheory.the_def] >>
    CASE_TAC >>
    imp_res_tac ALOOKUP_MEM >>
    gvs[GSYM REVERSE_ZIP,MEM_REVERSE] >>
    rename1 `MEM (_,trans_t) trans_env` >>
    PairCases_on `trans_t` >>
    drule_then drule $ iffLR translate_env_MEM >>
    strip_tac >>
    gvs[MEM_ZIP] >>
    metis_tac[MEM_EL]
  )
  >- (
    (* App *)
    qpat_x_assum `texp_construct_dict _ _ _ _ _ (App _ _) _` $ strip_assume_tac o
      SRULE[Once texp_construct_dict_cases] >>
    gvs[FORALL_AND_THM,FORALL_PROD,IMP_CONJ_THM] >>
    first_x_assum $ resolve_then (Pat `FRANGE (alist_to_fmap _) = FRANGE _`)
      mp_tac EQ_REFL >>
    disch_then $ drule_at (Pos last) >>
    simp[] >>
    impl_tac
    >- metis_tac[] >>
    rw[] >>
    simp[tcexp_of_def] >>
    irule type_tcexp_App >>
    first_assum $ irule_at (Pos last) >>
    gvs[LIST_REL_EL_EQN,LIST_REL3_EL] >>
    rw[EL_MAP]
    >- (strip_tac >> gvs[]) >>
    first_x_assum drule >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum $ resolve_then (Pat `FRANGE (alist_to_fmap _) = FRANGE _`)
      mp_tac EQ_REFL >>
    disch_then $ drule_at_then (Pos last) irule >>
    simp[] >>
    metis_tac[lambda_vars_IMP_lambda_varsl]
  )
  >- ( (* Let *)
    qpat_x_assum `texp_construct_dict _ _ _ _ _ (Let _ _ _) _` $
      strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[FORALL_AND_THM,FORALL_PROD,IMP_CONJ_THM,tshift_lie_FRANGE,
      tshift_lie_map_alist_to_fmap,translate_env_def,PULL_EXISTS,
      tcexp_of_def,translate_env_tshift_env_pred,
      translate_pred_type_scheme_def] >>
    first_x_assum $ resolve_then (Pat
      `FRANGE (alist_to_fmap (tshift_lie_alist _ _)) = _`) mp_tac EQ_REFL >>
    simp[translate_lie_alist_tshift_lie_alist] >>
    disch_then $ drule_at (Pos last) >>
    impl_tac
    >- (
      simp[MEM_MAP,FORALL_PROD,EVERY_MAP,PULL_EXISTS,
        MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,EXISTS_PROD] >>
      conj_tac
      >- (
        gvs[EVERY_MEM,lambdify type_ok_def] >>
        rpt strip_tac >>
        qpat_x_assum `!x. MEM x st ⇒ kind_ok _ _ _ _` $
          drule_then strip_assume_tac >>
        drule_then irule kind_ok_shift_db_APPEND >>
        simp[]
      ) >>
      conj_tac
      >- (
        gvs[LAMBDA_PROD,EVERY_MEM,FORALL_PROD] >>
        rw[] >>
        qpat_x_assum `!p1 p2 p3. MEM _ env ⇒ pred_type_kind_ok _ _ _ _` $
          drule_then strip_assume_tac >>
        drule_then irule pred_type_kind_ok_shift_db_pred_APPEND >>
        metis_tac[]
      ) >>
      conj_tac >- simp[GSYM LAMBDA_PROD,GSYM pure_miscTheory.FST_THM] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      rw[] >>
      qpat_x_assum `!cl t. _ ∈ FRANGE (alist_to_fmap _) ⇒
        ∃k. _ ∧ kind_ok _ _ _ _` drule >>
      rw[] >>
      simp[] >>
      drule_then irule kind_ok_shift_db_APPEND >>
      simp[]
    ) >>
    rw[] >>
    irule_at (Pos last) type_tcexp_Let >>
    simp[] >>
    `∀len. tshift_env len ie_env = ie_env`
    by (
      strip_tac >>
      irule tshift_env_unchanged >>
      rpt strip_tac >>
      (drule_then $ drule_at (Pos last)) entailment_kind_ok_type_ok >>
      simp[] >>
      disch_then $ drule_at (Pat `translate_ie_alist _ _ = _`) >>
      disch_then $ qspec_then `tdefs_to_tcexp_tdefs (SND ns)` mp_tac >>
      simp[LENGTH_tdefs_to_tcexp_tdefs] >>
      reverse $ impl_tac
      >- (strip_tac >> drule_then irule type_ok_IMP_freetyvars_ok) >>
      simp[entailment_kind_ok_tdefs_to_tcexp_tdefs]
    ) >>
    simp[] >>
    first_assum $ irule_at (Pos hd) >>
    first_x_assum $ resolve_then (Pat `FRANGE (alist_to_fmap _) = FRANGE _`)
      mp_tac EQ_REFL >>
    disch_then $ drule_at_then (Pos last) irule >>
    simp[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    qpat_x_assum `pred_type_elaborate_texp _ _ _ _ _ _ _ _ _ _` $
     mp_tac o SRULE[Once type_elaborate_texp_cases] >>
    Cases_on `pt` >>
    simp[]
  )
  >- ( (* Lam *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule_at (Pos last) type_tcexp_Lam >>
    imp_res_tac $ cj 1 $ iffLR LIST_REL_EL_EQN >>
    gvs[lambdify type_ok_def] >>
    conj_tac
    >- (
      gvs[EVERY_MEM] >>
      rpt strip_tac >>
      qpat_x_assum `∀t. MEM t arg_tys ⇒ kind_ok _ _ _ _` $
        drule_then strip_assume_tac >>
      irule kind_ok_tdefs_APPEND >>
      simp[kind_ok_tdefs_to_tcexp_tdefs]
    ) >>
    first_x_assum $ resolve_then (Pat `FRANGE (alist_to_fmap _) = _`)
      irule EQ_REFL >>
    gvs[translate_env_SOME_APPEND,ZIP_MAP,MEM_MAP] >>
    conj_tac
    >- (
      rw[MEM_ZIP]
      >- (
        strip_tac >>
        gvs[] >>
        metis_tac[MEM_EL]
      ) >>
      metis_tac[]
    ) >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac
    >- (
      rw[MEM_ZIP]
      >- (
        strip_tac >>
        gvs[] >>
        metis_tac[MEM_EL]
      ) >>
      metis_tac[]
    ) >>
    conj_tac >- metis_tac[] >>
    simp[translate_env_OPT_MMAP,OPT_MMAP_SOME_REVERSE,OPT_MMAP_MAP_o,
      combinTheory.o_DEF,LAMBDA_PROD,MAP_MAP_o,EVERY_MAP,GSYM PFORALL_THM,
      pred_type_kind_ok_alt,translate_pred_type_scheme_def,
      translate_pred_type_def,translate_predicates_def,MAP_REVERSE] >>
    conj_tac
    >- (
      gvs[OPT_MMAP_SOME_LIST_REL,LIST_REL_EL_EQN] >>
      rw[LIST_EQ_REWRITE,EL_MAP] >>
      pairarg_tac >>
      rw[Functions_def]
    ) >>
    conj_tac
    >- (
      gvs[EVERY_EL] >>
      rw[] >>
      pairarg_tac >> gvs[EL_ZIP]
    ) >>
    `MAP (λ((p1,p2),p2'). p1) (ZIP (vs,args_tys)) = MAP FST vs`
    by (
      rw[LIST_EQ_REWRITE,EL_MAP] >>
      pairarg_tac >>
      gvs[EL_ZIP]
    ) >>
    gvs[]
  )
  >- ( (* Letrec *)
    cheat
  )
  >- ( (* Cons *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[LIST_REL3_EL,LIST_REL_EL_EQN,tcexp_of_def] >>
    irule type_tcexp_Cons >>
    rw[LIST_REL_EL_EQN,EL_MAP] >>
    imp_res_tac type_cons_IMP_tcexp_type_cons >>
    drule_then (irule_at $ Pos last) tcexp_type_cons_tdefs_APPEND >>
    rw[EL_MAP,LAMBDA_PROD] >>
    simp[GSYM LAMBDA_PROD] >>
    qpat_x_assum `∀n. n < LENGTH _ ⇒
      type_elaborate_texp _ _ _ _ _ _ _ _ _ _ ∧ _` $ drule >>
    rw[] >>
    first_x_assum irule >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[lambda_vars_IMP_lambda_varsl] >>
    first_x_assum $ irule_at (Pos last) >>
    simp[] >>
    metis_tac[lambda_vars_IMP_lambda_varsl]
  )
  >- ( (* Tuple *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[LIST_REL3_EL,LIST_REL_EL_EQN,tcexp_of_def] >>
    qpat_x_assum `LENGTH ts = LENGTH des` $ assume_tac o GSYM >>
    fs[] >>
    irule type_tcexp_Tuple >>
    rw[LIST_REL_EL_EQN,EL_MAP] >>
    first_x_assum drule >>
    first_x_assum drule >>
    rw[] >>
    first_x_assum irule >>
    rw[]
    >- metis_tac[]
    >- metis_tac[lambda_vars_IMP_lambda_varsl] >>
    first_x_assum $ irule_at (Pos last) >>
    rw[] >>
    metis_tac[lambda_vars_IMP_lambda_varsl]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Ret >> (* metis isn't smart enough to figure this out *)
    metis_tac[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Bind >>
    metis_tac[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Raise >>
    gvs[type_ok_def] >>
    metis_tac[kind_ok_tdefs_to_tcexp_tdefs,kind_ok_tdefs_APPEND]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Handle >>
    metis_tac[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Act >>
    metis_tac[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Alloc >>
    metis_tac[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Length >>
    metis_tac[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Deref >>
    metis_tac[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Update >>
    metis_tac[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Exception >>
    gvs[] >>
    first_assum $ irule_at (Pos hd) >>
    gvs[LIST_REL_EL_EQN,LIST_REL3_EL,EL_MAP] >>
    metis_tac[lambda_vars_IMP_lambda_varsl]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_True
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_False
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Loc >>
    simp[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_AtomOp >>
    first_assum $ irule_at (Pos hd) >>
    gvs[LIST_REL_EL_EQN,LIST_REL3_EL,EL_MAP] >>
    metis_tac[lambda_vars_IMP_lambda_varsl]
  )
  >- ( (* NeestedCase *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_NestedCase >>
    gvs[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,EVERY_MAP,LIST_REL_EL_EQN,
      translate_env_SOME_APPEND,translate_env_SOME_REVERSE] >>
    conj_tac
    >- (
      `∀n. n < LENGTH pes'' ⇒  FST (EL n pes) = FST (EL n pes'')`
      by (
        rpt strip_tac >>
        qpat_x_assum `∀n. n < LENGTH pes'' ⇒ _` drule >>
        qpat_x_assum `∀n. n < LENGTH pes'' ⇒ _` drule >>
        ntac 3 (pairarg_tac >> gvs[])
      ) >>
      `MAP (λ(p1,p2). cepat_vars_l p1) pes'' = MAP (λ(p1,p2). cepat_vars_l p1) pes`
      by (
        rw[LIST_EQ_REWRITE,EL_MAP] >>
        >- (
          first_x_assum drule >>
          ntac 2 (pairarg_tac >> rw[])
        ) >>
        first_x_assum drule >>
        ntac 2 (pairarg_tac >> rw[])
      ) >>
      simp[]
    ) >>
    gvs[PULL_EXISTS,MEM_MAP,FORALL_PROD] >>
    first_x_assum $ drule_at_then (Pos last) $ irule_at (Pos last) >>
    simp[GSYM PULL_EXISTS] >>
    irule_at (Pat `tcexp_type_cepat _ _ _ _ _`) tcexp_type_cepat_tdefs_APPEND >>
    irule_at (Pat `tcexp_type_cepat _ _ _ _ _`) type_cepat_IMP_tcexp_type_cepat >>
    simp[EVERY_EL] >>
    first_assum $ irule_at (Pat `type_cepat _ _ _ _ _`) >>
    assume_tac $ GSYM type_cepat_cepat_vars >>
    gvs[translate_env_def,translate_pred_type_scheme_def,translate_pred_type_def,
      translate_predicates_def,Functions_def] >>
    rw[]
    >- (
      PURE_REWRITE_TAC[CONS_APPEND_APPEND] >>
      PURE_REWRITE_TAC[APPEND_ASSOC] >>
      first_x_assum irule >>
      simp[pred_type_kind_ok_alt,translate_env_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,LAMBDA_PROD,
        LIST_REL_EL_EQN,EL_MAP,translate_pred_type_scheme_def,translate_pred_type_def,
        GSYM PFORALL_THM] >>
      cheat
    ) >>
    cheat
  ) >>
  (* PrimSeq *)
  pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
  gvs[tcexp_of_def,translate_env_tshift_env_pred,translate_lie_alist_tshift_lie_alist,
    tshift_lie_FRANGE,tshift_lie_map_alist_to_fmap] >>
  irule type_tcexp_Seq >>
  conj_tac
  >- metis_tac[] >>
  last_x_assum $ resolve_then
    (Pat `FRANGE (alist_to_fmap (tshift_lie_alist _ _))`) mp_tac EQ_REFL >>
  gvs[translate_lie_alist_tshift_lie_alist,EVERY_MAP,LAMBDA_PROD,
    GSYM PFORALL_THM,GSYM PEXISTS_THM,FORALL_PROD,PULL_EXISTS] >>
  disch_then $ drule_at (Pos last) >>
  reverse $ impl_tac >>
  cheat
QED

Theorem texp_construct_dict_type_tcexp_exists:
  class_env_to_ns ce (ce_to_cl_tyid_map (LENGTH $ SND ns) ce)
    clcons ce = SOME cl_tds ∧
  LENGTH ce ≤ LENGTH clcons ∧
  ALL_DISTINCT (MAP FST ce) ∧
  clk = ce_to_clk ce ∧
  cl_to_tyid = ce_to_cl_tyid_map (LENGTH $ SND ns) ce ∧
  ie_map = alist_to_fmap ie_alist ∧
  ie = FRANGE (alist_to_fmap ie_alist) ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  (∀ent. ent ∈ ie ⇒ entailment_kind_ok (SND ns) clk ent)
  ⇒
  (∀lie db st env e e' pt.
    pred_type_elaborate_texp ns clk ie lie db st env e e' pt ⇒
      ∀lie_alist de.
      lie = FRANGE (alist_to_fmap lie_alist) ∧
      EVERY (type_ok (SND ns) db) st ∧
      EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk (SND ns) db scheme) env ∧
      ALL_DISTINCT (MAP FST lie_alist) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ v ∉ lambda_vars e) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ ∀cl t. ¬MEM (v,cl,t) lie_alist) ∧
      (∀v cl ct. MEM (v,cl,ct) lie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
      (∀v ks vt. MEM (v,ks,vt) lie_alist ⇒ v ∉ lambda_vars e) ∧
      (* lie kind ok *)
      (∀cl t. (cl,t) ∈ lie ⇒ ∃k. clk cl = SOME k ∧ kind_ok (SND ns) db k t) ∧
      pred_texp_construct_dict ns ie_map (alist_to_fmap lie_alist) db
        (set (MAP FST env)) pt e' de ⇒
      ∃trans_env lie_env trans_pt.
        translate_env cl_to_tyid env = SOME trans_env ∧
        translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
        translate_pred_type cl_to_tyid pt = SOME trans_pt ∧
        type_tcexp
          (append_ns (namespace_to_tcexp_namespace ns) ([],cl_tds))
          db st
          (trans_env ++ lie_env ++ ie_env)
          (tcexp_of de) trans_pt) ∧
  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
      ∀lie_alist de.
      lie = FRANGE (alist_to_fmap lie_alist) ∧
      EVERY (type_ok (SND ns) db) st ∧
      EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk (SND ns) db scheme) env ∧
      ALL_DISTINCT (MAP FST lie_alist) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ v ∉ lambda_vars e) ∧
      (∀v ent. MEM (v,ent) ie_alist ⇒ ∀cl t. ¬MEM (v,cl,t) lie_alist) ∧
      (∀v cl ct. MEM (v,cl,ct) lie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
      (∀v ks vt. MEM (v,ks,vt) lie_alist ⇒ v ∉ lambda_vars e) ∧
      (∀cl t. (cl,t) ∈ lie ⇒ ∃k. clk cl = SOME k ∧ kind_ok (SND ns) db k t) ∧
      texp_construct_dict ns ie_map (alist_to_fmap lie_alist) db
        (set (MAP FST env)) e' de ⇒
      ∃trans_env lie_env.
        translate_env cl_to_tyid env = SOME trans_env ∧
        translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
        type_tcexp
          (append_ns (namespace_to_tcexp_namespace ns) ([],cl_tds))
          db st
          (trans_env ++ lie_env ++ ie_env)
          (tcexp_of de) t)
Proof
  rw[] >>
  drule_all_then (qspec_then `LENGTH (SND ns)` strip_assume_tac) $
    EVERY_pred_type_kind_scheme_ok_IMP_translate_env_SOME >>
  simp[] >>
  imp_res_tac IMP_translate_lie_alist_EXISTS_SOME >>
  pop_assum $ qspec_then `LENGTH (SND ns)` mp_tac o SRULE[PULL_FORALL]
  >- (
    impl_tac
    >- metis_tac[] >>
    rw[] >>
    simp[] >>
    (drule_at_then (Pat `translate_env _ _ = _`) $
      drule_at_then (Pat `translate_ie_alist _ _ = _`) $
      drule_at_then (Pat `translate_lie_alist _ _ = _`) $
      irule) $ cj 1 $ SRULE[] texp_construct_dict_type_tcexp >>
    simp[] >>
    rw[] >>
    metis_tac[]
  ) >>
  impl_tac
  >- metis_tac[] >>
  rw[] >>
  simp[] >>
  (drule_at_then (Pat `translate_env _ _ = _`) $
    drule_at_then (Pat `translate_ie_alist _ _ = _`) $
    drule_at_then (Pat `translate_lie_alist _ _ = _`) $
    irule) $ cj 2 $ SRULE[] texp_construct_dict_type_tcexp >>
  simp[] >>
  rw[] >>
  metis_tac[]
QED


(*
Theorem prog_construct_dict_type_tcexp:
Proof
QED
*)

val _ = export_theory();
