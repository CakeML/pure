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

(* smth like this *)
Theorem class_env_kind_ok_IMP_type_scheme_ok:
  class_env_kind_ok tds ce ∧
  class_env_to_ns ce (ce_to_cl_tyid_map ns_len ce) clcons ce = SOME cl_tds ∧
  LENGTH ce ≤ LENGTH clcons ⇒
    EVERY (λ(ks,td). EVERY (λ(cn,argtys).
      EVERY (
        type_scheme_ok
          (SND (namespace_to_tcexp_namespace (exndefs,tds)) ++ cl_tds) ks)
          argtys) td) cl_tds
Proof
  cheat
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
  gvs[alist_to_fmap_EQ_FUNUPDATE_LIST,finite_mapTheory.DOMSUB_FUPDATE_LIST,
    combinTheory.o_DEF] >>
  `FILTER (λx. h0 ≠ FST x) (REVERSE lie_alist) = REVERSE lie_alist`
    suffices_by metis_tac[] >>
  gvs[FILTER_REVERSE,FILTER_EQ_ID,EVERY_MEM,MEM_MAP] >>
  metis_tac[]
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
  strip_tac >>
  ho_match_mp_tac type_elaborate_texp_ind >>
  rw[lambda_vars_def]
  >- (
    (* Var *)
    rfs[Once texp_construct_dict_cases] >>
    drule_all EVERY_pred_type_kind_scheme_ok_IMP_translate_env_SOME >>
    disch_then $ qspec_then `LENGTH (SND ns)` strip_assume_tac >>
    first_assum $ irule_at (Pos hd) >>
    (drule_at_then (Pos last) $ drule_at (Pos last))
      IMP_translate_lie_alist_EXISTS_SOME >>
    disch_then $ qspec_then `LENGTH (SND ns)` mp_tac >>
    impl_tac >- metis_tac[] >>
    strip_tac >>
    simp[] >>
    irule type_tcexp_SmartApp_Var >>
    irule_at (Pos last) type_tcexp_Var >>
    drule ALOOKUP_translate_env >>
    simp[ALOOKUP_APPEND] >>
    disch_then kall_tac >>
    simp[translate_pred_type_scheme_def,oneline translate_pred_type_def] >>
    Cases_on `s` >>
    simp[] >>
    CASE_TAC >>
    simp[AllCaseEqs(),PULL_EXISTS,EXISTS_PROD] >>
    (drule_then $ drule_then $ drule_at (Pat `construct_dicts _ _ _ _ _ _`)) $
      cj 2 construct_dict_type_tcexp >>
    disch_then $ qspecl_then [`st`,`FST ns`,`trans_env`,`cl_tds`] mp_tac >>
    gvs[] >>
    impl_tac
    >- (
      rw[]
      >- (
        rename1 `~MEM (v,ks,vt) trans_env` >>
        last_x_assum drule >>
        rpt strip_tac >>
        qpat_x_assum `∀ks vt. ¬MEM (v,ks,vt) env` mp_tac >>
        simp[] >>
        drule_then (qspec_then `v` mp_tac) ALOOKUP_translate_env >>
        simp[oneline OPTION_BIND_def] >>
        CASE_TAC
        >- (
          gvs[ALOOKUP_NONE,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
          metis_tac[]
        ) >>
        imp_res_tac ALOOKUP_MEM >>
        metis_tac[PAIR]
      )
      >- (
         rename1 `~MEM (v,ks,vt) trans_env` >>
        last_x_assum drule >>
        rpt strip_tac >>
        qpat_x_assum `∀ks vt. ¬MEM (v,ks,vt) env` mp_tac >>
        simp[] >>
        drule_then (qspec_then `v` mp_tac) ALOOKUP_translate_env >>
        simp[oneline OPTION_BIND_def] >>
        CASE_TAC
        >- (
          gvs[ALOOKUP_NONE,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
          metis_tac[]
        ) >>
        imp_res_tac ALOOKUP_MEM >>
        metis_tac[PAIR]
      )
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
    qpat_x_assum `pred_texp_construct_dict _ _ _ _ _ _ _ _` $ strip_assume_tac o
      SRULE[Once texp_construct_dict_cases] >>
    gvs[] >>
    qpat_x_assum `texp_construct_dict _ _ _ _ _ _ _` $ strip_assume_tac o
      PURE_REWRITE_RULE[alist_to_fmap_FUNUPDATE_LIST] >>
    last_x_assum $ drule_at (Pat `texp_construct_dict _ _ _ _ _ _ _`) >>
    impl_tac
    >- (
      simp[MAP_REVERSE,MAP_ZIP,ALL_DISTINCT_APPEND] >>
      DEP_REWRITE_TAC[finite_mapTheory.FRANGE_FUNION] >>
      simp[] >>
      reverse conj_tac
      gvs[]
      cheat
    ) >>
    rw[] >>
    simp[] >>
    drule_all_then (qspec_then `LENGTH (SND ns)` strip_assume_tac)
      EVERY_pred_type_kind_scheme_ok_IMP_translate_env_SOME >>
    simp[] >>
    (drule_at_then (Pos last) $ drule_at (Pos last))
      IMP_translate_lie_alist_EXISTS_SOME >>
    disch_then $ qspec_then `LENGTH (SND ns)` mp_tac >>
    impl_tac >- metis_tac[] >>
    strip_tac >>
    simp[] >>
    drule_then strip_assume_tac translate_lie_alist_APPEND_lie_alist_IMP >>
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
      qpat_x_assum `∀n. n < LENGTH _ ⇒ ∃k. ce_to_clk _ _ = SOME _ ∧ _` drule >>
      rw[ce_to_clk_def] >>
      drule_then strip_assume_tac ALOOKUP_find_index_SOME >>
      gvs[] >>
      cheat (* FST (EL i cl_tds) = [FST (SND (EL i ce))] *)
      (* class constructor type check *)
    ) >>
    drule_then irule type_tcexp_env_extensional >>
    rpt strip_tac >>
    imp_res_tac translate_lie_alist_translate_predicates_SOME >>
    imp_res_tac $ iffRL translate_predicates_REVERSE >>
    gvs[MAP_ZIP,REVERSE_ZIP,GSYM MAP_REVERSE] >>
    irule ALOOKUP_APPEND_EQ >>
    irule ALOOKUP_APPEND_EQ >>
    simp[ALOOKUP_APPEND,ALOOKUP_ZIP_MAP_SND,oneline OPTION_MAP_DEF] >>
    CASE_TAC
    >- (CASE_TAC >> simp[]) >>
    CASE_TAC >>
    imp_res_tac ALOOKUP_MEM >>
    gvs[GSYM REVERSE_ZIP,MEM_REVERSE] >>
    gvs[INTER_EMPTY_IN_NOTIN,MEM_ZIP] >>
    rename1 `([],EL m _)` >>
    `MEM (EL m vs) vs` by metis_tac[MEM_EL] >>
    last_x_assum drule >>
    rw[MEM_MAP,FORALL_PROD] >>
    cheat
  )
QED

(*
Theorem prog_construct_dict_type_tcexp:
Proof
QED
*)

val _ = export_theory();
