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

Theorem OPT_MMAP_SOME_LIST_REL:
  ∀ys.
  OPT_MMAP f xs = SOME ys ⇔
  LIST_REL (λx y. f x = SOME y) xs ys
Proof
  Induct_on `xs` >>
  gvs[OPT_MMAP_def] >>
  rw[EQ_IMP_THM]
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

Theorem FLOOKUP_to_cl_tyid_map:
  ALL_DISTINCT (MAP FST cl_map) ⇒
  FLOOKUP (to_cl_tyid_map tdefs cl_map) cl =
    OPTION_MAP ($+ (LENGTH tdefs)) (find_index cl (MAP FST cl_map) 0)
Proof
  simp[to_cl_tyid_map_def,FLOOKUP_FUPDATE_LIST,oneline OPTION_MAP_DEF] >>
  TOP_CASE_TAC >>
  gvs[AllCaseEqs(),ALOOKUP_NONE,MAP_REVERSE,MAP_ZIP]
  >- gvs[MEM_MAP,GSYM find_index_NOT_MEM,FORALL_PROD] >>
  dxrule_then assume_tac ALOOKUP_MEM >>
  rpt strip_tac >>
  gvs[MEM_REVERSE,MEM_ZIP,EL_MAP,EL_GENLIST] >>
  drule ALL_DISTINCT_INDEX_OF_EL >>
  simp[] >>
  disch_then drule >>
  simp[EL_MAP,find_index_INDEX_OF]
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

Theorem class_map_to_ns_NON_EMPTY:
  ∀cl_to_tyid cl_map cl_tds.
    class_map_to_ns cl_to_tyid cl_map = SOME cl_tds ⇒
    EVERY (λ(ks,td). td ≠ []) cl_tds
Proof
  Induct_on `cl_map` >>
  rw[class_map_to_ns_def] >>
  PairCases_on `h` >>
  gvs[class_map_to_ns_def] >>
  last_x_assum drule >>
  rw[] >>
  gvs[oneline class_to_datatype_def,AllCaseEqs()]
QED

Theorem class_map_to_ns_EL:
  ∀cl_to_tyid cl_map cl_tds.
  class_map_to_ns cl_to_tyid cl_map = SOME cl_tds ⇒
  LENGTH cl_tds = LENGTH cl_map ∧
  (∀i c cl. i < LENGTH cl_map ∧ EL i cl_map = (c,cl) ⇒
    ∃method_tys sup_tys.
    OPT_MMAP (translate_pred_type_scheme cl_to_tyid) (MAP SND cl.methods) = SOME method_tys ∧
    translate_superclasses cl_to_tyid (super_classes cl) =
      SOME sup_tys ∧
    EL i cl_tds = ([cl.kind],[(cl.constructor,sup_tys ++ method_tys)]))
Proof
  Induct_on `cl_map` >>
  rw[class_map_to_ns_def] >>
  PairCases_on `h` >>
  gvs[class_map_to_ns_def,IMP_CONJ_THM,FORALL_AND_THM,class_to_datatype_def]
  >- metis_tac[] >>
  Cases_on `i` >>
  gvs[]
QED

Theorem translate_superclasses_OPT_MMAP:
  translate_superclasses cl_to_tyid supers =
  OPT_MMAP (λc. OPTION_MAP (λsid. [],Cons (UserType sid) (TypeVar 0))
    (FLOOKUP cl_to_tyid c)) supers
Proof
  Induct_on `supers` >>
  rw[translate_superclasses_def,oneline OPTION_MAP_DEF] >>
  CASE_TAC >>
  gvs[]
QED

Theorem translate_superclasses_MEM_type_ok:
  class_map_kind_ok tds cl_map ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  MEM (c,cl) cl_map ∧
  class_map_to_ns (to_cl_tyid_map tds cl_map) cl_map = SOME cl_tds ∧
  translate_superclasses (to_cl_tyid_map tds cl_map)
    (super_classes cl) = SOME sup_tys ∧
  MEM (ks,t) sup_tys ⇒
  kind_ok (tdefs_to_tcexp_tdefs tds ++ cl_tds) (ks ++ [cl.kind])
    kindType t
Proof
  rw[translate_superclasses_OPT_MMAP,OPT_MMAP_SOME_LIST_REL] >>
  drule_all LIST_REL_MEM_IMP_R >>
  rw[FLOOKUP_to_cl_tyid_map] >>
  simp[kind_ok,oEL_THM,kindArrow_EQ_kind_arrows_single,kind_arrows_kindType_EQ,
    LENGTH_tdefs_to_tcexp_tdefs,EL_APPEND_EQN] >>
  drule find_index_LESS_LENGTH >>
  simp[] >>
  strip_tac >>
  drule class_map_to_ns_EL >>
  rw[] >>
  first_x_assum drule >>
  rw[] >>
  gvs[class_map_kind_ok_def] >>
  last_x_assum drule >>
  rw[EVERY_MEM] >>
  qpat_x_assum `∀s. MEM s (super_classes _) ⇒ _` drule >>
  rw[class_map_to_clk_def] >>
  rename1 `EL j cl_tds` >>
  Cases_on `EL j cl_tds` >>
  drule ALOOKUP_find_index_SOME >>
  rw[] >>
  Cases_on `EL j cl_map` >>
  fs[]
QED

Theorem translate_predicates_OPT_MMAP:
  translate_predicates cl_to_tyid ps =
    OPT_MMAP (translate_predicate cl_to_tyid) ps
Proof
  Induct_on `ps` >>
  rw[translate_predicates_def]
QED

Theorem translate_predicates_LIST_REL:
  translate_predicates cl_to_tyid ps = SOME ps' ⇔
  LIST_REL
    (λ(cl,t) t'.
      ∃ut. FLOOKUP cl_to_tyid cl = SOME ut ∧
        t' = Cons (UserType ut) t)
    ps ps'
Proof
  simp[translate_predicates_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,
    translate_predicate_def,LAMBDA_PROD] >>
  ntac 2 AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM] >>
  rw[EQ_IMP_THM]
QED

Theorem translate_predicate_type_ok:
  class_map_to_ns (to_cl_tyid_map tds cl_map) cl_map = SOME cl_tds ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_to_clk cl_map cl = SOME k ∧
  kind_ok (tds ++ cl_tds) ks k t ∧
  translate_predicate (to_cl_tyid_map tds cl_map) (cl,t) = SOME t' ⇒
  type_ok (tds ++ cl_tds) ks t'
Proof
  rw[translate_predicate_def,type_ok] >>
  gvs[FLOOKUP_to_cl_tyid_map,kind_ok,
    kindArrow_EQ_kind_arrows_single,kind_arrows_kindType_EQ] >>
  first_assum $ irule_at (Pos hd) >>
  simp[oEL_THM,EL_APPEND_EQN] >>
  drule find_index_LESS_LENGTH >>
  simp[] >>
  drule class_map_to_ns_EL >>
  rw[] >>
  first_x_assum drule >>
  rw[] >>
  simp[] >>
  gvs[class_map_to_clk_def] >>
  drule ALOOKUP_find_index_SOME >>
  rw[] >>
  rename1 `EL j cl_map` >>
  Cases_on `EL j cl_map` >>
  gvs[]
QED

Theorem translate_predicates_type_ok:
  class_map_to_ns (to_cl_tyid_map tds cl_map) cl_map = SOME cl_tds ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  EVERY (λ(c,t'). ∃k. class_map_to_clk cl_map c = SOME k ∧
    kind_ok (tds ++ cl_tds) ks k t') ps ∧
  translate_predicates (to_cl_tyid_map tds cl_map) ps = SOME pts ∧
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

Theorem translate_predicates_type_ok_relax:
  class_map_to_ns cl_to_tyid cl_map = SOME cl_tds ∧
  cl_to_tyid = to_cl_tyid_map tds cl_map ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  EVERY (λ(c,t'). ∃k. class_map_to_clk cl_map c = SOME k ∧
    kind_ok (tds ++ cl_tds) ks k t') ps ∧
  translate_predicates cl_to_tyid ps = SOME pts ∧
  MEM arg pts ⇒
  type_ok (tds ++ cl_tds) ks arg
Proof
  metis_tac[translate_predicates_type_ok]
QED

Theorem pred_type_kind_ok_IMP_type_ok:
  pred_type_kind_ok (class_map_to_clk cl_map) tds db pt ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_to_ns cl_to_tyid cl_map = SOME cl_tds ⇒
  ∃t. translate_pred_type (to_cl_tyid_map tds cl_map) pt = SOME t ∧
    type_ok (tdefs_to_tcexp_tdefs tds ++ cl_tds) db t
Proof
  Cases_on `pt` >>
  rw[pred_type_kind_ok_alt,translate_pred_type_def,PULL_EXISTS,
    type_ok_def,FORALL_PROD] >>
  simp[translate_predicates_LIST_REL,LIST_REL_EL_EQN] >>
  qexists_tac `MAP (λ(cl,t).
    Cons (UserType (the ARB $ FLOOKUP (to_cl_tyid_map tds cl_map) cl)) t) l` >>
  rw[kind_ok_Functions,EL_MAP,MEM_MAP]
  >- (
    pairarg_tac >>
    rw[FLOOKUP_to_cl_tyid_map] >>
    gvs[MEM_EL,PULL_EXISTS] >>
    first_x_assum drule >>
    rw[class_map_to_clk_def] >>
    drule ALOOKUP_find_index_SOME >>
    rw[] >>
    simp[libTheory.the_def]
  )
  >- (
    disj2_tac >>
    rw[PULL_EXISTS,kind_ok,FORALL_PROD]
    >- (
      irule kind_ok_tdefs_APPEND >>
      simp[kind_ok_tdefs_to_tcexp_tdefs]
    ) >>
    first_x_assum drule >>
    rw[FLOOKUP_to_cl_tyid_map,class_map_to_clk_def] >>
    drule ALOOKUP_find_index_SOME >>
    strip_tac >>
    drule class_map_to_ns_EL >>
    strip_tac >>
    first_x_assum drule >>
    Cases_on `EL i cl_map` >>
    simp[libTheory.the_def,oEL_THM,LENGTH_tdefs_to_tcexp_tdefs,
      kindArrow_EQ_kind_arrows_single,kind_arrows_kindType_EQ,EL_APPEND_EQN] >>
    rw[PULL_EXISTS] >>
    irule kind_ok_tdefs_APPEND >>
    fs[kind_ok_tdefs_to_tcexp_tdefs]
  )
QED

Theorem class_map_to_ns_EVERY_type_scheme_ok_aux:
  ∀cl_map' cl_tds' rest_cl_map.
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_to_ns (to_cl_tyid_map tds cl_map) cl_map = SOME cl_tds ∧
  class_map_to_ns (to_cl_tyid_map tds cl_map) cl_map' = SOME cl_tds' ∧
  class_map_kind_ok tds cl_map ∧
  cl_map = rest_cl_map ++ cl_map' ⇒
  EVERY (λ(ks,td). EVERY (λ(cn,argtys).
    EVERY (
      type_scheme_ok
        (tdefs_to_tcexp_tdefs tds ++ cl_tds) ks)
        argtys) td) cl_tds'
Proof
  Induct >>
  rw[class_map_to_ns_def] >>
  PairCases_on `h` >>
  gvs[DISJ_IMP_THM,FORALL_AND_THM] >>
  gvs[class_map_to_ns_def] >>
  pairarg_tac >>
  gvs[class_to_datatype_def,OPT_MMAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
    EVERY_MEM,FORALL_PROD] >>
  rw[type_scheme_ok_def]
  >- (
    (drule_then $ drule_at_then (Pos last) $ drule_at_then (Pos last) $ irule)
      translate_superclasses_MEM_type_ok >>
    simp[] >>
    metis_tac[]
  ) >>
  gvs[OPT_MMAP_SOME_LIST_REL,LAMBDA_PROD] >>
  drule_all LIST_REL_MEM_IMP_R >>
  rw[EXISTS_PROD] >>
  gvs[translate_pred_type_scheme_def] >>
  rev_drule_at (Pat `class_map_to_ns _ _ = _`)
    pred_type_kind_ok_IMP_type_ok >>
  simp[type_ok_def] >>
  rename1 `translate_pred_type _ pt = SOME trans_pt` >>
  disch_then $ qspecl_then [`tds`,`pt`] mp_tac >>
  simp[] >>
  disch_then irule >>
  rw[oneline pred_type_kind_ok_alt] >>
  TOP_CASE_TAC >>
  gvs[class_map_kind_ok_def,DISJ_IMP_THM,FORALL_AND_THM,EVERY_MEM,FORALL_PROD] >>
  rw[]
  >- (
    first_x_assum drule >>
    simp[pred_type_kind_ok_alt,class_map_to_clk_def]
  ) >>
  first_x_assum drule >>
  rw[pred_type_kind_ok_alt,class_map_to_clk_def,PULL_EXISTS,FORALL_PROD]
QED

Theorem class_map_to_ns_EVERY_type_scheme_ok:
  class_map_to_ns (to_cl_tyid_map tds cl_map) cl_map = SOME cl_tds ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_kind_ok tds cl_map ⇒
  EVERY (λ(ks,td). EVERY (λ(cn,argtys).
    EVERY (
      type_scheme_ok
        (tdefs_to_tcexp_tdefs tds ++ cl_tds) ks)
        argtys) td) cl_tds
Proof
  rw[] >>
  (drule_then $ drule_then irule) class_map_to_ns_EVERY_type_scheme_ok_aux >>
  rw[] >>
  first_assum $ irule_at (Pos last) >>
  simp[]
QED

Theorem IMP_translate_predicates_SOME:
  (∀cl. MEM cl l ⇒ ∃k. class_map_to_clk cl_map (FST cl) = SOME k) ∧
  ALL_DISTINCT (MAP FST cl_map) ⇒
  ∃args.
    translate_predicates (to_cl_tyid_map ns cl_map) l = SOME args
Proof
  Induct_on `l` >>
  rw[translate_predicates_def] >>
  gvs[FORALL_AND_THM,DISJ_IMP_THM,translate_predicate_def] >>
  gvs[FLOOKUP_to_cl_tyid_map,class_map_to_clk_def] >>
  metis_tac[ALOOKUP_find_index_SOME]
QED

Theorem EVERY_pred_type_kind_scheme_ok_IMP_translate_env_SOME:
  ALL_DISTINCT (MAP FST cl_map) ⇒
  ∀env.
  EVERY (λ(v,scheme).
    pred_type_kind_scheme_ok (class_map_to_clk cl_map) tds db scheme) env ⇒
  ∃trans_env. translate_env (to_cl_tyid_map ns cl_map) env =
    SOME (trans_env: (mlstring # type_kind_scheme) list)
Proof
  strip_tac >>
  Induct >>
  rw[translate_env_def] >>
  pairarg_tac >> gvs[translate_env_def] >>
  PairCases_on `scheme` >>
  gvs[translate_pred_type_scheme_def,oneline translate_pred_type_def] >>
  TOP_CASE_TAC >>
  gvs[pred_type_kind_ok_alt] >>
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

Triviality alist_to_fmap_DOMSUB_EQ_ID:
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
    ∃k. class_map_to_clk cl_map cl = SOME k) ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  ALL_DISTINCT (MAP FST lie_alist) ⇒
  ∃lie_env. translate_lie_alist (to_cl_tyid_map tds cl_map) lie_alist =
    SOME (lie_env:(mlstring # type_kind_scheme) list)
Proof
  Induct_on `lie_alist` >>
  rw[translate_lie_alist_def] >>
  PairCases_on `h` >>
  gvs[translate_lie_alist_def,DISJ_IMP_THM,FORALL_AND_THM,FLOOKUP_to_cl_tyid_map,
    class_map_to_clk_def] >>
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
  specialises_inst tds (Entailment ks ps (cl,t)) (Entailment ks' qs (cl',t')) =
  ∃subs.
    LIST_REL (kind_ok tds ks') ks subs ∧
    cl = cl' ∧
    tsubst subs t = t' ∧
    MAP (I ## tsubst subs) ps = qs
Proof
  simp[specialises_inst_def,LIST_REL_pred_tsbust,SF ETA_ss]
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
  specialises_inst tds it (Entailment db ps (cl,t)) ∧
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
  specialises_pred tds db (q,PredType l t') (PredType ps t) ∧
  translate_predicates cl_to_tyid ps = SOME ps' ⇒
  ∃args.
    translate_predicates cl_to_tyid l = SOME args ∧
    specialises (tdefs_to_tcexp_tdefs tds) db
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

Theorem translate_env_SOME_REVERSE:
  translate_env cl_to_tyid (REVERSE l) = SOME r ⇔
  ∃r'. translate_env cl_to_tyid l = SOME r' ∧ r = REVERSE r'
Proof
  simp[translate_env_OPT_MMAP,OPT_MMAP_SOME_REVERSE]
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
  class_map_to_ns cl_tyid cl_map = SOME cl_tds ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  translate_ie_alist cl_tyid ie_alist = SOME env ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  cl_tyid = to_cl_tyid_map tds cl_map ∧
  (∀ent.
      ent ∈ FRANGE (alist_to_fmap ie_alist) ⇒
      entailment_kind_ok tds (class_map_to_clk cl_map) ent) ⇒
   (∀v ks t. MEM (v,ks,t) env ⇒ type_ok (tds ++ cl_tds) ks t)
Proof
  qid_spec_tac `env` >>
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
      rw[] >>
      rename1 ` translate_predicate (to_cl_tyid_map tds cl_map) pred = SOME _` >>  
      Cases_on `pred` >>
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
Theorem unsafe_type_cons_EQ_unsafe_tcexp_type_cons:
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
  >- metis_tac[unsafe_type_cons_EQ_unsafe_tcexp_type_cons] >>
  rw[EQ_IMP_THM,LIST_EQ_REWRITE] >>
  gvs[EL_MAP]
QED

Triviality CONS_APPEND_APPEND:
  x::(l ++ m ++ r) = x::l ++ m ++ r
Proof
  simp[]
QED

Theorem EVERY_type_ok_tshift:
  EVERY (type_ok tds db) st ⇒
  EVERY (λx. type_ok tds (new ++ db) (tshift (LENGTH new) x)) st
Proof
  gvs[EVERY_MEM,lambdify type_ok_def] >>
  rpt strip_tac >>
  qpat_x_assum `!x. MEM x st ⇒ kind_ok _ _ _ _` $
    drule_then strip_assume_tac >>
  drule_then irule kind_ok_shift_db_APPEND >>
  simp[]
QED

Theorem EVERY_pred_type_kind_ok_shift_db_pred:
  EVERY (λ(v,scheme).
    pred_type_kind_scheme_ok (ce_to_clk ce) tds db scheme) env ⇒
  EVERY (λ(p1,p1',p2).
    pred_type_kind_ok (ce_to_clk ce) tds (p1' ++ new ++ db)
      (shift_db_pred (LENGTH p1') (LENGTH new) p2)) env
Proof
  gvs[LAMBDA_PROD,EVERY_MEM,FORALL_PROD] >>
  rw[] >>
  qpat_x_assum `!p1 p2 p3. MEM _ env ⇒ pred_type_kind_ok _ _ _ _` $
    drule_then strip_assume_tac >>
  drule_then irule pred_type_kind_ok_shift_db_pred_APPEND >>
  metis_tac[]
QED

Triviality FST_3:
  (λ(p1,p1',p2). p1) = FST
Proof
  simp[GSYM LAMBDA_PROD,GSYM pure_miscTheory.FST_THM]
QED

Triviality FST_o_FST:
  (λ((p1,p2),p2'). p1) = (FST o FST)
Proof
  simp[combinTheory.o_DEF,FST,LAMBDA_PROD]
QED

Theorem class_map_to_clk_kind_ok_tshift:
  (∀cl t.
     (cl,t) ∈ FRANGE (alist_to_fmap lie_alist) ⇒
     ∃k. class_map_to_clk cl_map cl = SOME k ∧ kind_ok tds db k t) ∧
  (cl,pt) ∈ FRANGE (alist_to_fmap (tshift_lie_alist (LENGTH new) lie_alist)) ⇒
  ∃k. class_map_to_clk cl_map cl = SOME k ∧ kind_ok tds (new ++ db) k pt
Proof
  rw[GSYM tshift_lie_map_alist_to_fmap,GSYM tshift_lie_FRANGE,
    PULL_EXISTS,FORALL_PROD] >>
  first_x_assum drule >>
  rw[] >>
  first_assum $ irule_at (Pos hd) >>
  drule_then irule kind_ok_shift_db_APPEND >>
  simp[]
QED

Theorem to_cl_tyid_map_LENGTH_EQ:
  LENGTH tds = LENGTH tds' ⇒
    to_cl_tyid_map tds cl_map = to_cl_tyid_map tds' cl_map
Proof
  simp[to_cl_tyid_map_def]
QED

Theorem tdefs_to_tcexp_tdefs_to_cl_tyid_map:
  to_cl_tyid_map (tdefs_to_tcexp_tdefs tds) cl_map =
    to_cl_tyid_map tds cl_map
Proof
  metis_tac[LENGTH_tdefs_to_tcexp_tdefs,to_cl_tyid_map_LENGTH_EQ]
QED

Theorem tshift_env_ie_unchanged:
  class_map_to_ns (to_cl_tyid_map (tds:typedefs) cl_map) cl_map =
    SOME cl_tds ∧
  translate_ie_alist (to_cl_tyid_map tds cl_map) ie_alist =
    SOME ie_env ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  (∀ent.
    ent ∈ FRANGE (alist_to_fmap ie_alist) ⇒
    entailment_kind_ok tds (class_map_to_clk cl_map) ent)
  ⇒
  ∀len. tshift_env len ie_env = ie_env
Proof
  rpt strip_tac >>
  irule tshift_env_unchanged >>
  rpt strip_tac >>
  drule_at (Pat `translate_ie_alist _ _ = SOME _`) entailment_kind_ok_type_ok >>
  simp[] >>
  disch_then (drule_then $ drule_at (Pos last)) >>
  simp[] >>
  disch_then $ qspec_then `tdefs_to_tcexp_tdefs tds` mp_tac >>
  simp[entailment_kind_ok_tdefs_to_tcexp_tdefs,
    tdefs_to_tcexp_tdefs_to_cl_tyid_map] >>
  strip_tac >> drule_then irule type_ok_IMP_freetyvars_ok
QED

Theorem pred_type_elaborate_texp_IMP_pred_type_kind_ok:
  pred_type_elaborate_texp ns clk ie lie db st env e e' pt ⇒
  pred_type_kind_ok clk (SND ns) db pt
Proof
  Cases_on `pt` >>
  simp[Once type_elaborate_texp_cases]
QED

Theorem destructable_type_LE:
  destructable_type n t ∧ n ≤ m ⇒
  destructable_type m t
Proof
  rw[destructable_type_def] >>
  every_case_tac >> gvs[]
QED

Theorem unsafe_tcexp_type_cons_tdefs_APPEND_EQ:
  unsafe_tcexp_type_cons tds c (tcons,args) ⇔
  (unsafe_tcexp_type_cons (tds ++ tds') c (tcons,args) ∧ tcons < LENGTH tds)
Proof
  simp[oneline unsafe_tcexp_type_cons_def] >>
  rpt CASE_TAC >>
  rw[oEL_THM,EL_APPEND_EQN]
QED

Theorem tcexp_exhaustive_cepat_tdefs_APPEND:
  (∀tk pes.
    tcexp_exhaustive_cepat (exnds,tds) tk pes ⇒
    tcexp_exhaustive_cepat (exnds,tds ++ cl_tds) tk pes) ∧
  (∀tks pess.
    tcexp_exhaustive_cepatl (exnds,tds) tks pess ⇒
    tcexp_exhaustive_cepatl (exnds,tds ++ cl_tds) tks pess)
Proof
  ho_match_mp_tac tcexp_exhaustive_cepat_ind >>
  rw[]
  >- metis_tac[tcexp_exhaustive_cepat_Var]
  >- metis_tac[tcexp_exhaustive_cepat_UScore]
  >- (
    irule tcexp_exhaustive_cepat_Cons >>
    reverse $ rw[]
    >- (drule_then irule destructable_type_LE >> simp[]) >>
    gvs[destructable_type_def,unsafe_tcexp_destruct_type_cons_def,
      AllCaseEqs(),split_ty_cons_eq_split_ty,split_ty_thm] >>
    last_x_assum mp_tac >>
    TOP_CASE_TAC >>
    `t ≠ Atom Exception` by (
      strip_tac >>
      gvs[head_ty_cons_eq_head_ty,head_ty_def]
    ) >>
    gvs[head_ty_cons_eq_head_ty] >>
    every_case_tac
    >- (
      rw[] >>
      drule_all $ iffRL unsafe_tcexp_type_cons_tdefs_APPEND_EQ >>
      metis_tac[]
    ) >>
    metis_tac[]
  )
  >- metis_tac[tcexp_exhaustive_cepat_Nil]
  >- metis_tac[tcexp_exhaustive_cepat_List]
QED

Triviality MAP_PROD_EQ_MAP_FST:
  MAP (λ(ks,t). (ks, f ks t)) l = MAP ($, h) l' ⇔
  (l' = MAP (λ(ks,t). f ks t) l ∧ EVERY ($= h o FST) l)
Proof
  rw[LIST_EQ_REWRITE,EVERY_EL,EQ_IMP_THM] >>
  gvs[EL_MAP] >>
  first_x_assum drule >>
  pairarg_tac >> rw[] >>
  simp[]
QED

Theorem exhaustive_cepat_tdefs_IMP_tcexp_exhaustive_cepat:
  namespace_ok (exds,tds) ⇒
  (∀t pes. exhaustive_cepat (exds,tds) t pes ⇒
    tcexp_exhaustive_cepat (exds,tdefs_to_tcexp_tdefs tds) ([],t) pes) ∧
  (∀ts pess. exhaustive_cepatl (exds,tds) ts pess ⇒
    tcexp_exhaustive_cepatl (exds,tdefs_to_tcexp_tdefs tds) (MAP ($, []) ts) pess)
Proof
  strip_tac >>
  ho_match_mp_tac exhaustive_cepat_ind >>
  rw[]
  >- metis_tac[tcexp_exhaustive_cepat_Var]
  >- metis_tac[tcexp_exhaustive_cepat_UScore]
  >- (
    irule tcexp_exhaustive_cepat_Cons >>
    reverse $ rw[]
    >- (drule_then irule destructable_type_LE >>
      simp[LENGTH_tdefs_to_tcexp_tdefs]) >>
    gvs[destructable_type_def,unsafe_tcexp_destruct_type_cons_def,
      unsafe_destruct_type_cons_def,
      AllCaseEqs(),split_ty_cons_eq_split_ty,split_ty_thm]
    >- (
      first_x_assum drule >>
      rw[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD] >>
      first_assum $ irule_at (Pos last) >>
      `MAP (λ(p1,p2). ([],p2)) ts = ts` suffices_by (strip_tac >> gvs[]) >>
      rw[LIST_EQ_REWRITE,EL_MAP] >>
      pairarg_tac >> rw[] >>
      gvs[EVERY_EL] >>
      metis_tac[FST]
    ) >>
    qpat_x_assum `option_CASE (head_ty_cons t) _ _` mp_tac >>
    TOP_CASE_TAC >>
    `t ≠ Atom Exception` by (
      strip_tac >>
      gvs[head_ty_cons_eq_head_ty,head_ty_def]
    ) >>
    gvs[head_ty_cons_eq_head_ty] >>
    every_case_tac
    >- (
      rw[] >>
      gvs[unsafe_type_cons_EQ_unsafe_tcexp_type_cons,
        unsafe_tcexp_type_cons_def,PULL_EXISTS] >>
      first_x_assum drule >>
      simp[MAP_PROD_EQ_MAP_FST] >>
      impl_keep_tac
      >- (
        gvs[namespace_ok_def,oEL_THM,tdefs_to_tcexp_tdefs_def,EL_MAP] >>
        Cases_on `EL x tds` >>
        rename1 `EL x tds = (k,cons)` >>
        gvs[ALOOKUP_MAP,lambdify PAIR_MAP,LAMBDA_PROD,EVERY_MAP]
      ) >>
      rw[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD] >>
      first_x_assum $ irule_at (Pos last) >>
      pop_assum mp_tac >>
      ho_match_mp_tac $ cj 1 $ iffLR EQ_IMP_THM >>
      AP_THM_TAC >> AP_TERM_TAC >>
      rw[LIST_EQ_REWRITE,EL_MAP] >>
      gvs[EVERY_EL] >>
      pairarg_tac >> rw[] >>
      first_x_assum drule >> simp[]
    ) >>
    gvs[] >>
    metis_tac[]
  )
  >- metis_tac[tcexp_exhaustive_cepat_Nil]
  >- metis_tac[tcexp_exhaustive_cepat_List]
QED

Triviality DISJOINT_NOT_IN_R:
  DISJOINT a b ⇔ (∀x. x ∈ a ⇒ x ∉ b)
Proof
  rw[DISJOINT_DEF,EXTENSION] >>
  metis_tac[]
QED

Triviality DISJOINT_NOT_IN_L:
  DISJOINT a b ⇔ (∀x. x ∈ b ⇒ x ∉ a)
Proof
  rw[DISJOINT_DEF,EXTENSION] >>
  metis_tac[]
QED

Theorem DISJOINT_trans_env:
  translate_env cl_to_tyid env = SOME trans_env ∧
  DISJOINT s (set (MAP FST env)) ⇒
  DISJOINT s (set (MAP FST trans_env))
Proof
  rw[DISJOINT_NOT_IN_L,MEM_MAP,FORALL_PROD,PULL_EXISTS] >>
  metis_tac[translate_env_MEM]
QED

Theorem DISJOINT_lambda_varsl_IMP:
  DISJOINT s (lambda_varsl es) ∧ n < LENGTH es ⇒
  DISJOINT s (lambda_vars (EL n es))
Proof
  simp[DISJOINT_NOT_IN_R] >>
  metis_tac[lambda_vars_IMP_lambda_varsl]
QED

Theorem construct_dict_type_tcexp:
  translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  ALL_DISTINCT (MAP FST lie_alist ++ MAP FST ie_alist) ∧
  DISJOINT (set (MAP FST lie_alist ++ MAP FST ie_alist)) (set (MAP FST env)) ∧
(*
  (∀v ent. MEM (v,ent) ie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
  (∀v cl ct. MEM (v,cl,ct) lie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
  (∀v ent cl t. MEM (v,ent) ie_alist ⇒ ¬MEM (v,cl,t) lie_alist) ∧
*)
  (∀v ent cl ks ps t. MEM (v,Entailment ks ps (cl,t)) ie_alist ⇒
    ∃pid. FLOOKUP cl_to_tyid cl = SOME pid) ∧
  lie = alist_to_fmap lie_alist ∧
  ie = alist_to_fmap ie_alist ∧
  trans_ns = (exnds,tdefs_to_tcexp_tdefs tds ++ cl_tds) ∧
  trans_env = env ++ lie_env ++ ie_env
  ⇒
  (∀p d. construct_dict tds db ie lie p d ⇒
    (∀v. v ∈ freevars_cexp d ⇒ v ∈ FDOM ie ∨ v ∈ FDOM lie) ∧
    ∃p'. translate_predicate cl_to_tyid p = SOME p' ∧
    type_tcexp trans_ns db st trans_env (tcexp_of d) p') ∧
  (∀ps ds. construct_dicts tds db ie lie ps ds ⇒
    (∀d v. MEM d ds ∧ v ∈ freevars_cexp d ⇒ v ∈ FDOM ie ∨ v ∈ FDOM lie) ∧
    ∃ps'. translate_predicates cl_to_tyid ps = SOME ps' ∧
    LIST_REL
      (λd t. type_tcexp trans_ns db st trans_env (tcexp_of d) t)
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
      gvs[LIST_TO_SET_APPEND] >>
      qpat_x_assum `DISJOINT (set (MAP FST lie_alist)) _` $
        assume_tac o SRULE[DISJOINT_NOT_IN_R] >>
      gvs[MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
      first_x_assum drule >>
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
      gvs[DISJOINT_NOT_IN_R,MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
      qpat_x_assum `∀x p. MEM _ ie_alist ⇒ _` drule >>
      metis_tac[PAIR]
    ) >>
    reverse $ CASE_TAC
    >- (
      imp_res_tac ALOOKUP_MEM >>
      spose_not_then kall_tac >>
      gvs[ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
      pop_assum mp_tac >>
      simp[] >>
      first_x_assum irule >>
      drule_all MEM_FST_translate_lie_alist >>
      simp[]
    ) >>
    drule ALOOKUP_translate_ie >>
    simp[] >>
    disch_then kall_tac >>
    rename1 `specialises_inst _ _ (Entailment _ _ p)` >>
    PairCases_on `p` >>
    gvs[] >>
    rename1 `translate_entailment _ it = _` >>
    Cases_on `it` >>
    rename1 `Entailment _ _ q` >>
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

Definition translate_ns_def:
  translate_ns ns cl_tds =
    append_ns (namespace_to_tcexp_namespace ns) ([],cl_tds)
End

Theorem pred_type_elaborate_texp_IMP_translate_pred_type:
  pred_type_elaborate_texp ns clk ie lie db st env e e' pt ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_to_ns cl_to_tyid cl_map = SOME cl_tds ∧
  clk = class_map_to_clk cl_map ⇒
  pred_type_kind_ok (class_map_to_clk cl_map) (SND ns) db pt ∧
  ∃t. translate_pred_type (to_cl_tyid_map (SND ns) cl_map) pt = SOME t ∧
      type_ok (tdefs_to_tcexp_tdefs (SND ns) ++ cl_tds) db t
Proof
  rw[Once type_elaborate_texp_cases] >>
  drule pred_type_kind_ok_IMP_type_ok >>
  rw[] >>
  metis_tac[]
QED

Theorem texp_construct_dict_type_tcexp:
  namespace_ok ns ∧
  class_map_to_ns cl_to_tyid cl_map = SOME cl_tds ∧
  (* class names are distinct *)
  ALL_DISTINCT (MAP FST cl_map) ∧
  (* well-formed ie *)
  (∀ent. ent ∈ ie ⇒ entailment_kind_ok tds clk ent) ∧

  (* abbreviate *)
  tds = SND ns ∧
  clk = class_map_to_clk cl_map ∧
  cl_to_tyid = to_cl_tyid_map tds cl_map ∧
  ie_map = alist_to_fmap ie_alist ∧
  ie = FRANGE (alist_to_fmap ie_alist) ∧
  new_ns = translate_ns ns cl_tds ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ⇒

  (* mutual induction *)
  (∀lie db st env e e' pt.
    pred_type_elaborate_texp ns clk ie lie db st env e e' pt ⇒
      ∀lie_alist de trans_env lie_env new_env lie_map lie env_set tcexp_de
        trans_pt.
      translate_env cl_to_tyid env = SOME trans_env ∧
      translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
      translate_pred_type cl_to_tyid pt = SOME trans_pt ∧
      (* well-formed st *)
      EVERY (type_ok tds db) st ∧
      (* well-formed env *)
      EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk tds db scheme) env ∧
      (* distinct variables in ie and lie *)
      ALL_DISTINCT (MAP FST lie_alist ++ MAP FST ie_alist) ∧
      DISJOINT (set (MAP FST lie_alist ++ MAP FST ie_alist))
        (set (MAP FST env) ∪ lambda_vars e) ∧
      (* abbreviate *)
      new_env = trans_env ++ lie_env ++ ie_env ∧
      lie_map = alist_to_fmap lie_alist ∧
      lie = FRANGE lie_map ∧
      env_set = set (MAP FST env) ∧
      tcexp_de = tcexp_of de ∧
      (* lie kind ok *)
      (∀cl t. (cl,t) ∈ lie ⇒ ∃k. clk cl = SOME k ∧ kind_ok tds db k t) ∧
      pred_texp_construct_dict ns ie_map lie_map db env_set pt e' de ⇒
        type_tcexp new_ns db st new_env tcexp_de trans_pt) ∧

  (∀lie db st env e e' t.
    type_elaborate_texp ns clk ie lie db st env e e' t ⇒
      ∀lie_alist de trans_env lie_env new_env lie_map lie env_set tcexp_de.
      translate_env cl_to_tyid env = SOME trans_env ∧
      translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
      (* well-formed st *)
      EVERY (type_ok tds db) st ∧
      (* well-formed env *)
      EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk tds db scheme) env ∧
      (* distinct variables in ie and lie *)
      ALL_DISTINCT (MAP FST lie_alist ++ MAP FST ie_alist) ∧
      DISJOINT (set (MAP FST lie_alist ++ MAP FST ie_alist))
        (set (MAP FST env) ∪ lambda_vars e) ∧
      (* lie kind ok *)
      (∀cl t. (cl,t) ∈ lie ⇒ ∃k. clk cl = SOME k ∧ kind_ok tds db k t) ∧
      (* abbreviate *)
      new_env = trans_env ++ lie_env ++ ie_env ∧
      lie_map = alist_to_fmap lie_alist ∧
      lie = FRANGE (alist_to_fmap lie_alist) ∧
      env_set = set (MAP FST env) ∧
      tcexp_de = tcexp_of de ∧
      texp_construct_dict ns ie_map lie_map db env_set e' de ⇒
      type_tcexp new_ns db st new_env tcexp_de t)
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
    fs[] >>
    CASE_TAC >>
    simp[AllCaseEqs(),PULL_EXISTS,EXISTS_PROD] >>
    (drule_then $ drule_then $ drule_then $
      drule_at (Pat `construct_dicts _ _ _ _ _ _`)) $
      (SRULE[GSYM CONJ_ASSOC] $ cj 2 construct_dict_type_tcexp) >>
    simp[] >>
    disch_then $ qspecl_then [`st`,`FST ns`,`trans_env`,`cl_tds`] mp_tac >>
    gvs[] >>
    impl_tac
    >- (
      rw[]
      >- metis_tac[DISJOINT_trans_env]
      >- metis_tac[DISJOINT_trans_env] >>
      simp[FLOOKUP_to_cl_tyid_map] >>
      `∃v. ALOOKUP cl_map cl = SOME v`
        suffices_by metis_tac[ALOOKUP_find_index_SOME] >>
      `ALL_DISTINCT (MAP FST ie_alist)`
        by gvs[ALL_DISTINCT_APPEND] >>
      gvs[ALL_DISTINCT_FRANGE_MEM,PULL_EXISTS] >>
      last_x_assum drule >>
      simp[entailment_kind_ok_def,class_map_to_clk_def,PULL_EXISTS]
    ) >>
    rw[] >>
    simp[translate_ns_def] >>
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
    qpat_x_assum `pred_texp_construct_dict _ _ _ _ _ _ _ _` $
      strip_assume_tac o SRULE[cj 1 $ Once texp_construct_dict_cases] >>
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
        gvs[pred_type_kind_ok_alt,FORALL_PROD,FLOOKUP_to_cl_tyid_map,
          class_map_to_clk_def,PULL_EXISTS] >>
        metis_tac[ALOOKUP_find_index_SOME]
      ) >>
      conj_tac
      >- (
        simp[ALL_DISTINCT_APPEND,MAP_REVERSE,MAP_ZIP] >>
        gvs[ALL_DISTINCT_APPEND,GSYM DISJOINT_DEF] >>
        simp[DISJ_IMP_THM] >>
        gvs[DISJOINT_NOT_IN_L]
      ) >>
      conj_tac
      >- (
        simp[MAP_REVERSE,MAP_ZIP] >>
        gvs[ALL_DISTINCT_APPEND,GSYM DISJOINT_DEF] >>
        conj_tac >- metis_tac[DISJOINT_SYM] >>
        `lambda_vars e = lambda_vars e'`
          suffices_by metis_tac[DISJOINT_SYM] >>
        metis_tac[type_elaborate_texp_lambda_vars]
      ) >>
      rw[] >>
      pop_assum mp_tac >>
      DEP_REWRITE_TAC[finite_mapTheory.FRANGE_FUNION] >>
      simp[FDOM_alist_to_fmap,MAP_REVERSE,MAP_ZIP] >>
      gvs[GSYM DISJOINT_DEF] >>
      conj_tac >- metis_tac[DISJOINT_SYM] >>
      rw[]
      >- (
        gvs[pred_type_kind_ok_alt,FORALL_PROD] >>
        dxrule_at (Pos last) (iffLR ALL_DISTINCT_FRANGE_MEM) >>
        rw[MAP_REVERSE,MAP_ZIP,MEM_ZIP] >>
        drule EL_MEM >>
        rw[]
      ) >>
      metis_tac[]
    ) >>
    strip_tac >>
    gvs[translate_pred_type_def] >>
    irule type_tcexp_SmartLam >>
    drule $ iffLR translate_predicates_LIST_REL >>
    gvs[LIST_REL_EL_EQN] >>
    rw[EVERY_EL]
    >- (
      gvs[ALL_DISTINCT_FRANGE_MEM,PULL_EXISTS] >>
      first_x_assum drule >>
      pairarg_tac >> rw[] >>
      gvs[type_ok,entailment_kind_ok_def,PULL_EXISTS,oEL_THM,
        FLOOKUP_to_cl_tyid_map] >>
      simp[kindArrow_EQ_kind_arrows_single,kind_arrows_kindType_EQ,
        translate_ns_def] >>
      drule find_index_LESS_LENGTH >>
      qspec_then `SND ns` assume_tac $ GEN_ALL LENGTH_tdefs_to_tcexp_tdefs >>
      rw[EL_APPEND_EQN] >>
      gvs[pred_type_kind_ok_alt,MEM_EL,PULL_EXISTS] >>
      qpat_x_assum `∀n. n < LENGTH _ ⇒
        ∃k. ce_to_clk _ _ = SOME _ ∧ _` drule >>
      rw[class_map_to_clk_def] >>
      drule_then strip_assume_tac ALOOKUP_find_index_SOME >>
      gvs[] >>
      rename1 `EL j cl_map` >>
      Cases_on `EL j cl_map` >>
      drule_all class_map_to_ns_EL >>
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
    first_x_assum $ drule_at (Pat `translate_lie_alist _ _ = SOME _`) >>
    rw[tcexp_of_def] >>
    first_x_assum $ drule_then strip_assume_tac >>
    irule type_tcexp_App >>
    first_assum $ irule_at (Pos last) >>
    gvs[LIST_REL_EL_EQN,LIST_REL3_EL] >>
    rw[EL_MAP]
    >- (strip_tac >> gvs[]) >>
    first_x_assum drule >>
    first_x_assum drule >>
    rw[] >>
    first_assum $ drule_then irule >>
    simp[DISJOINT_lambda_varsl_IMP]
  )
  >- ( (* Let *)
    qpat_x_assum `texp_construct_dict _ _ _ _ _ (Let _ _ _) _` $
      strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[FORALL_AND_THM,FORALL_PROD,IMP_CONJ_THM,tshift_lie_FRANGE,
      tshift_lie_map_alist_to_fmap,translate_env_def,PULL_EXISTS,
      tcexp_of_def,translate_env_tshift_env_pred,
      translate_pred_type_scheme_def] >>
    irule type_tcexp_Let >>
    first_x_assum $ irule_at (Pos $ el 2) >>
    (drule_then $ drule_then drule)
      pred_type_elaborate_texp_IMP_translate_pred_type >>
    rw[] >>
    first_assum $ irule_at (Pat `translate_lie_alist _ _ = _`) >>
    gvs[] >>
    `∀n. tshift_env n ie_env = ie_env`
    by (
      drule_then (drule_then irule) tshift_env_ie_unchanged >>
      rw[] >>
      metis_tac[ALL_DISTINCT_APPEND]
    ) >>
    simp[] >>
    first_x_assum irule >>
    first_x_assum $ irule_at (Pat `pred_texp_construct_dict _ _ _ _ _ _ _ _`) >>
    simp[translate_lie_alist_tshift_lie_alist,MAP_MAP_o,
      combinTheory.o_DEF,LAMBDA_PROD,FST_3,EVERY_MAP,
      EVERY_type_ok_tshift,EVERY_pred_type_kind_ok_shift_db_pred] >>
    metis_tac[class_map_to_clk_kind_ok_tshift]
  )
  >- ( (* Lam *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Lam >>
    imp_res_tac $ cj 1 $ iffLR LIST_REL_EL_EQN >>
    gvs[lambdify type_ok_def] >>
    conj_tac
    >- (
      gvs[EVERY_MEM,translate_ns_def] >>
      rpt strip_tac >>
      qpat_x_assum `∀t. MEM t arg_tys ⇒ kind_ok _ _ _ _` $
        drule_then strip_assume_tac >>
      irule kind_ok_tdefs_APPEND >>
      simp[kind_ok_tdefs_to_tcexp_tdefs]
    ) >>
    first_x_assum irule >>
    first_assum $ irule_at (Pat `translate_lie_alist _ _ = SOME _`) >>
    simp[translate_env_SOME_APPEND,MAP_REVERSE,MAP_ZIP] >>
    rw[translate_env_OPT_MMAP,translate_pred_type_scheme_def,
      OPT_MMAP_SOME_REVERSE,OPT_MMAP_MAP_o,
      combinTheory.o_DEF,LAMBDA_PROD]
    >- (
      simp[OPT_MMAP_SOME_LIST_REL,LIST_REL_EL_EQN] >>
      rw[LIST_EQ_REWRITE,EL_MAP,EL_ZIP,Functions_def,
        translate_pred_type_def,translate_predicates_def]
    ) >>
    gvs[EVERY_EL,EL_ZIP,EL_MAP,pred_type_kind_ok_alt]
  )
  >- ( (* Letrec *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def,tshift_lie_FRANGE,tshift_lie_map_alist_to_fmap,
       translate_env_tshift_env_pred] >>
    irule type_tcexp_Letrec >>
    conj_tac
    >- (Cases_on `dfns` >> gvs[]) >>
    qexists_tac `MAP (the ARB o
      translate_pred_type_scheme (to_cl_tyid_map (SND ns) cl_map))
      kind_schemes` >>
    gvs[LIST_REL3_EL,LIST_REL_EL_EQN] >>
    simp[EVERY_EL,EL_MAP] >>
    qpat_x_assum `∀n. n < LENGTH dfns ⇒ _` $
      markerLib.ASSUME_NAMED_TAC "construct_dict_asm" >>
    qpat_x_assum `∀n. n < LENGTH dfns ⇒ _` $
      markerLib.ASSUME_NAMED_TAC "type_elaborate_asm" >>
    `MAP (FST ∘ FST) fns' = MAP (FST ∘ FST) fns`
    by (
      rw[LIST_EQ_REWRITE,EL_MAP] >>
      markerLib.LABEL_ASSUM "type_elaborate_asm" drule >>
      ntac 3 (pairarg_tac >> simp[])
    ) >>
    ho_match_mp_tac $ METIS_PROVE [] ``C ∧ (A ∧ B) ⇒ A ∧ B ∧ C`` >>
    reverse conj_tac
    >- (
      simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
      rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
            markerLib.LABEL_ASSUM "construct_dict_asm" drule >>
      markerLib.LABEL_ASSUM "type_elaborate_asm" drule >>
      ntac 4 (pairarg_tac >> simp[]) >>
      rpt (disch_then strip_assume_tac) >>
      drule_then assume_tac pred_type_elaborate_texp_IMP_pred_type_kind_ok >>
      drule_all pred_type_kind_ok_IMP_type_ok >>
      rw[translate_pred_type_scheme_def,type_ok_def]
      >- simp[translate_ns_def,libTheory.the_def] >>
      simp[libTheory.the_def] >>
      `ALL_DISTINCT (MAP FST ie_alist) ∧ ALL_DISTINCT (MAP FST lie_alist)`
      by (
        drule $ iffLR ALL_DISTINCT_APPEND >>
        metis_tac[]
      ) >>
      drule_all_then assume_tac tshift_env_ie_unchanged >>
      gvs[] >>
      first_x_assum irule >>
      irule_at (Pat `translate_lie_alist _ _ = SOME _`) $
        iffRL translate_lie_alist_tshift_lie_alist >>
      first_x_assum $ irule_at (Pos hd) >>
      irule_at (Pos hd) EQ_REFL >>
      conj_tac
      >- (
        simp[translate_env_tshift_env_pred,translate_env_SOME_APPEND,
          translate_env_SOME_REVERSE,PULL_EXISTS] >>
        irule_at (Pos last) EQ_REFL >>
        simp[translate_env_OPT_MMAP,OPT_MMAP_SOME_LIST_REL] >>
        simp[LIST_REL_EL_EQN,EL_ZIP,EL_MAP] >>
        rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
        simp[translate_pred_type_scheme_def] >>
        markerLib.LABEL_ASSUM "type_elaborate_asm" drule >>
        markerLib.LABEL_ASSUM "construct_dict_asm" drule >>
        ntac 4 (pairarg_tac >> simp[]) >>
        rw[] >>
        drule_then assume_tac pred_type_elaborate_texp_IMP_pred_type_kind_ok >>
        drule_all pred_type_kind_ok_IMP_type_ok >>
        rw[] >>
        simp[libTheory.the_def]
      ) >>
      simp[MAP_ZIP,MAP_REVERSE,MAP_MAP_o,
        combinTheory.o_DEF,LAMBDA_PROD,FST_3] >>
      simp[FST_o_FST] >>
      qmatch_goalsub_abbrev_tac `DISJOINT (set _) (lambda_vars exp)` >>
      `exp = EL n (MAP SND fns)` by simp[EL_MAP] >>
      simp[] >>
      DEP_REWRITE_TAC[DISJOINT_lambda_varsl_IMP] >>
      simp[Abbr`exp`] >>
      pop_assum kall_tac >>
      conj_tac
      >- (
        simp[EVERY_MAP,LAMBDA_PROD] >>
        drule_at_then (Pos last) irule $ MONO_EVERY >>
        simp[FORALL_PROD] >>
        rpt strip_tac >>
        drule_then irule pred_type_kind_ok_shift_db_pred_APPEND >>
        irule_at (Pos hd) EQ_REFL >>
        simp[]
      ) >>
      conj_tac
      >- (
        simp[EVERY_MAP,LAMBDA_PROD] >>
        rw[EVERY_EL,EL_ZIP,EL_MAP] >>
        qmatch_goalsub_abbrev_tac `_ (EL m _)` >>
        `m < LENGTH dfns` by fs[Abbr`m`] >>
        markerLib.LABEL_ASSUM "type_elaborate_asm" dxrule >>
        ntac 3 (pairarg_tac >> simp[]) >>
        rw[] >>
        drule_then assume_tac
          pred_type_elaborate_texp_IMP_pred_type_kind_ok >>
        drule_then irule pred_type_kind_ok_shift_db_pred_APPEND >>
        irule_at (Pos hd) EQ_REFL >>
        simp[]
      ) >>
      conj_tac
      >- (
        simp[EVERY_MAP] >>
        drule_then irule EVERY_type_ok_tshift
      ) >>
      conj_tac
      >- metis_tac[class_map_to_clk_kind_ok_tshift] >>
      metis_tac[UNION_COMM]
    ) >>
    first_x_assum irule >>
    first_assum $ irule_at (Pat `translate_lie_alist _ _ = _`) >>
    simp[translate_env_SOME_REVERSE,translate_env_SOME_APPEND] >>
    simp[MAP_REVERSE,MAP_ZIP] >>
    conj_tac
    >- (
      rw[translate_env_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,LIST_REL_EL_EQN] >>
      simp[EL_ZIP,EL_MAP] >>
      simp[translate_pred_type_scheme_def] >>
      markerLib.LABEL_ASSUM "type_elaborate_asm" drule >>
      markerLib.LABEL_ASSUM "construct_dict_asm" drule >>
      ntac 4 (pairarg_tac >> simp[]) >>
      rw[] >>
      drule_then assume_tac pred_type_elaborate_texp_IMP_pred_type_kind_ok >>
      drule_all pred_type_kind_ok_IMP_type_ok >>
      rw[] >>
      simp[libTheory.the_def]
    ) >>
    conj_tac
    >- (
      simp[EVERY_MAP,LAMBDA_PROD] >>
      rw[EVERY_EL,EL_ZIP,EL_MAP] >>
      qmatch_goalsub_abbrev_tac `_ (EL m _)` >>
      `m < LENGTH dfns` by fs[Abbr`m`] >>
      markerLib.LABEL_ASSUM "type_elaborate_asm" dxrule >>
      ntac 3 (pairarg_tac >> simp[]) >>
      rw[] >>
      drule_then irule
        pred_type_elaborate_texp_IMP_pred_type_kind_ok
    ) >>
    metis_tac[UNION_COMM]
  )
  >- ( (* Cons *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[LIST_REL3_EL,LIST_REL_EL_EQN,tcexp_of_def] >>
    irule type_tcexp_Cons >>
    rw[LIST_REL_EL_EQN,EL_MAP] >>
    gvs[type_cons_EQ_tcexp_type_cons,translate_ns_def] >>
    drule_then (irule_at $ Pos last) tcexp_type_cons_tdefs_APPEND >>
    rw[EL_MAP,LAMBDA_PROD] >>
    simp[GSYM LAMBDA_PROD] >>
    qpat_x_assum `∀n. n < LENGTH _ ⇒
      type_elaborate_texp _ _ _ _ _ _ _ _ _ _ ∧ _` $ drule >>
    rw[] >>
    first_x_assum irule >>
    first_assum $ irule_at (Pat `translate_lie_alist _ _ = _`) >>
    DEP_REWRITE_TAC[DISJOINT_lambda_varsl_IMP] >>
    simp[]
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
    first_assum $ irule_at (Pat `translate_lie_alist _ _ = _`) >>
    DEP_REWRITE_TAC[DISJOINT_lambda_varsl_IMP] >>
    rw[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Ret >>
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
    gvs[type_ok_def,translate_ns_def] >>
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
    rpt $ first_assum $ irule_at Any >>
    rw[] >> metis_tac[]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_Exception >>
    gvs[translate_ns_def] >>
    first_assum $ irule_at (Pos hd) >>
    gvs[LIST_REL_EL_EQN,LIST_REL3_EL,EL_MAP] >>
    metis_tac[DISJOINT_lambda_varsl_IMP]
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
    metis_tac[DISJOINT_lambda_varsl_IMP]
  )
  >- ( (* PrimSeq *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def,translate_env_tshift_env_pred,translate_lie_alist_tshift_lie_alist,
      tshift_lie_FRANGE,tshift_lie_map_alist_to_fmap] >>
    irule type_tcexp_Seq >>
    conj_tac
    >- metis_tac[] >>
    `∀n. tshift_env n ie_env = ie_env`
    by (
      gvs[ALL_DISTINCT_APPEND] >> metis_tac[tshift_env_ie_unchanged]
    ) >>
    gvs[] >>
    first_x_assum $ irule_at (Pos hd) >>
    irule_at (Pos hd) $ iffRL translate_lie_alist_tshift_lie_alist >>
    first_assum $ irule_at (Pos hd) >>
    irule_at (Pos hd) EQ_REFL >>
    simp[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_3] >>
    (drule_then $ drule_then drule)
      pred_type_elaborate_texp_IMP_translate_pred_type >>
    rw[] >>
    simp[EVERY_MAP,LAMBDA_PROD] >>
    conj_tac
    >- drule_then irule EVERY_type_ok_tshift >>
    conj_tac
    >- (
      drule_at_then (Pos last) irule MONO_EVERY >>
      simp[FORALL_PROD] >>
      rpt strip_tac >>
      drule_then irule pred_type_kind_ok_shift_db_pred_APPEND >>
      irule_at (Pos hd) EQ_REFL >>
      rw[]
    ) >>
    metis_tac[class_map_to_clk_kind_ok_tshift]
  )
  >- ( (* NestedCase *)
    pop_assum $ strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
    gvs[tcexp_of_def] >>
    irule type_tcexp_NestedCase >>
    gvs[Excl "EVERY_DEF",MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,EVERY_MAP,LIST_REL_EL_EQN,
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
        rw[LIST_EQ_REWRITE,EL_MAP]
        >- (
          first_x_assum drule >>
          ntac 2 (pairarg_tac >> rw[])
        ) >>
        first_x_assum drule >>
        ntac 2 (pairarg_tac >> rw[])
      ) >>
      simp[]
    ) >>
    first_x_assum $ drule_at_then (Pos last) $ irule_at (Pos last) >>
    simp[Excl "EVERY_DEF",translate_ns_def] >>
    qmatch_goalsub_abbrev_tac `EVERY _ patterns` >>
    rw[]
    >- (
      rw[EVERY_EL] >>
      pairarg_tac >> simp[] >>
      irule_at (Pat `tcexp_type_cepat _ _ _ _ _`) tcexp_type_cepat_tdefs_APPEND >>
      irule_at (Pat `tcexp_type_cepat _ _ _ _ _`) type_cepat_IMP_tcexp_type_cepat >>
      gvs[MAP_REVERSE,MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF,FST_3,
        LAMBDA_PROD,PULL_EXISTS,translate_env_def,EXISTS_PROD] >>
      Cases_on `n` >>
      gvs[Abbr`patterns`,EL_MAP]
      >- (
        first_assum $ irule_at (Pos hd) >>
        gvs[SRULE[] $ GSYM translate_ns_def] >>
        `REVERSE (MAP (λ(v,t). (v,[],t)) vts) ++
           (v,[],t')::(trans_env ++ lie_env ++ ie_env) =
           REVERSE (MAP (λ(v,t). (v,[],t)) vts) ++
             [v,[],t'] ++ trans_env ++ lie_env ++ ie_env`
         by metis_tac[GSYM CONS_APPEND,APPEND_ASSOC] >>
        simp[] >>
        first_x_assum irule >>
        pop_assum kall_tac >>
        first_assum $ irule_at (Pat `translate_lie_alist _ _ = _`) >>
        simp[translate_pred_type_scheme_def,translate_pred_type_def,
          translate_predicates_def,pred_type_kind_ok_alt,Functions_def] >>
        simp[translate_env_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,LIST_REL_EL_EQN,LAMBDA_PROD,
          EL_MAP,translate_pred_type_scheme_def] >>
        conj_tac
        >- (
          rw[] >>
          Cases_on `EL n vts` >>
          simp[PULL_EXISTS,translate_pred_type_def,translate_predicates_def,Functions_def]
        ) >>
        drule_then assume_tac $ GSYM type_cepat_cepat_vars >>
        gvs[GSYM pure_miscTheory.FST_THM] >>
        (drule_then $ rev_drule_then drule) $ cj 2 type_elaborate_type_ok >>
        simp[LAMBDA_PROD,type_ok_def] >>
        strip_tac >>
        drule_then drule type_cepat_type_ok >>
        simp[EVERY_MEM,FORALL_PROD] >>
        strip_tac >>
        conj_tac >- (rw[] >> first_x_assum $ drule_then irule) >>
        metis_tac[UNION_COMM,INSERT_UNION_EQ]
      ) >>
      pop_assum mp_tac >>
      pairarg_tac >>
      rw[] >>
      first_x_assum drule >>
      first_x_assum drule >>
      ntac 2 (pairarg_tac >> simp[]) >>
      rw[] >>
      first_assum $ irule_at (Pos hd) >>
      gvs[SRULE[] $ GSYM translate_ns_def] >>
      `REVERSE (MAP (λ(v,t). (v,[],t)) vts') ++
         (v,[],t')::(trans_env ++ lie_env ++ ie_env) =
         REVERSE (MAP (λ(v,t). (v,[],t)) vts') ++
           [v,[],t'] ++ trans_env ++ lie_env ++ ie_env`
       by metis_tac[GSYM CONS_APPEND,APPEND_ASSOC] >>
       simp[] >>
       first_x_assum irule >>
       pop_assum kall_tac >>
       first_assum $ irule_at (Pat `translate_lie_alist _ _ = _`) >>
       simp[translate_pred_type_scheme_def,translate_pred_type_def,
         translate_predicates_def,pred_type_kind_ok_alt,Functions_def] >>
       simp[translate_env_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,LIST_REL_EL_EQN,LAMBDA_PROD,
         EL_MAP,translate_pred_type_scheme_def] >>
       conj_tac
      >- (
        rw[] >>
        Cases_on `EL n vts'` >>
        simp[PULL_EXISTS,translate_pred_type_def,translate_predicates_def,Functions_def]
      ) >>
      gvs[MEM_MAP,FORALL_PROD,PULL_EXISTS] >>
      rename1`EL n' pes = (CEPAT,exp)` >>
      `MEM (EL n' pes) pes` by metis_tac[MEM_EL] >>
      gvs[] >>
      first_x_assum drule >>
      drule_then assume_tac $ GSYM type_cepat_cepat_vars >>
      gvs[GSYM pure_miscTheory.FST_THM] >>
      strip_tac >>
      `exp = EL n' (MAP SND pes)` by simp[EL_MAP] >>
      simp[] >>
      DEP_REWRITE_TAC[DISJOINT_lambda_varsl_IMP] >>
      simp[] >>
      (drule_then $ rev_drule_then drule) $ cj 2 type_elaborate_type_ok >>
      simp[LAMBDA_PROD,type_ok_def] >>
      strip_tac >>
      drule_then drule type_cepat_type_ok >>
      simp[EVERY_MEM,FORALL_PROD] >>
      strip_tac >>
      conj_tac >- (rw[] >> first_x_assum $ drule_then irule) >>
      metis_tac[UNION_COMM,INSERT_UNION_EQ]
    ) >>
    simp[LIST_TO_SET_MAP,IMP_translate_lie_alist_EXISTS_SOME,IMAGE_IMAGE,
      combinTheory.o_DEF,LAMBDA_PROD,GSYM pure_miscTheory.FST_THM] >>
    `IMAGE FST (set pes'') = IMAGE FST (set pes)`
    by (
      simp[GSYM LIST_TO_SET_MAP] >>
      AP_TERM_TAC >>
      rw[LIST_EQ_REWRITE,EL_MAP] >>
      first_x_assum drule >>
      last_x_assum drule >>
      ntac 3 (pairarg_tac >> gvs[]) >>
      rw[]
    ) >>
    simp[] >>
    irule $ cj 1 tcexp_exhaustive_cepat_tdefs_APPEND >>
    irule $ cj 1 exhaustive_cepat_tdefs_IMP_tcexp_exhaustive_cepat >>
    rw[]
  )
QED

Theorem texp_construct_dict_type_tcexp_exists:
  namespace_ok ns ∧
  class_map_to_ns ce (ce_to_cl_tyid_map (LENGTH $ SND ns) ce)
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

Theorem select_nth_cepat_thm:
  ∀n m v.
  select_nth_cepat n m v =
    REPLICATE n cepatUScore ++ (cepatVar v::REPLICATE m cepatUScore)
Proof
  Induct_on `n` >>
  rw[select_nth_cepat_def]
QED

Theorem tcexp_exhaustive_cepat_SUBSET:
  (∀t ps.
    tcexp_exhaustive_cepat ns t ps ⇒
    ∀ps'. ps ⊆ ps' ⇒
      tcexp_exhaustive_cepat ns t ps') ∧
  (∀ts pss.
    tcexp_exhaustive_cepatl ns ts pss ⇒
    ∀pss'. pss ⊆ pss' ⇒
      tcexp_exhaustive_cepatl ns ts pss')
Proof
  ho_match_mp_tac tcexp_exhaustive_cepat_ind >>
  rw[]
  >- (
    irule tcexp_exhaustive_cepat_Var >>
    metis_tac[SUBSET_DEF]
  )
  >- (
    irule tcexp_exhaustive_cepat_UScore >>
    metis_tac[SUBSET_DEF]
  )
  >- (
    irule tcexp_exhaustive_cepat_Cons >>
    rw[] >>
    first_x_assum drule >>
    rw[] >>
    irule_at (Pat `_ ⊆ _`) SUBSET_TRANS >>
    first_assum $ irule_at (Pat `_ ⊆ _`) >>
    simp[]
  )
  >- (
    irule tcexp_exhaustive_cepat_Nil >>
    metis_tac[SUBSET_DEF]
  )
  >- (
    irule tcexp_exhaustive_cepat_List >>
    irule_at (Pat `_ ⊆ _`) SUBSET_TRANS >>
    first_assum $ irule_at (Pat `IMAGE _ _ ⊆ _`) >>
    simp[]
  )
QED

Theorem tcexp_exhaustive_cepatl:
  ∀ts pss.
  LIST_REL (tcexp_exhaustive_cepat ns) ts pss ⇒
  ∀pss'.
  pss' = FOLDR (λh tl. IMAGE (UNCURRY CONS) (h × tl)) {[]} pss ⇒
  tcexp_exhaustive_cepatl ns ts pss'
Proof
  ho_match_mp_tac LIST_REL_ind >>
  rw[]
  >- (
    irule tcexp_exhaustive_cepat_Nil >>
    simp[]
  ) >>
  irule tcexp_exhaustive_cepat_List >>
  first_assum $ irule_at (Pos last) >>
  first_assum $ irule_at (Pos last) >>
  simp[]
QED

Theorem FOLDR_REPLICATE:
  FOLDR f y (REPLICATE n x) = FUNPOW (f x) n y
Proof
  Induct_on `n` >>
  simp[FUNPOW_SUC]
QED

Theorem FUNPOW_IMAGE_CONS_SING:
  FUNPOW (λtl. IMAGE (UNCURRY CONS) ({cepatUScore} × tl)) n s =
  IMAGE (λs. REPLICATE n cepatUScore ++ s) s
Proof
  Induct_on `n` >>
  rw[FUNPOW_SUC] >>
  rw[EXTENSION,EXISTS_PROD,EQ_IMP_THM]
QED

Theorem nth_from_dict_type_tcexp:
  LLOOKUP tds cid = SOME (ks,[(clcon,ts)]) ∧
  LIST_REL (kind_ok tds db) ks targs ∧
  SND ns = tds ∧
  LENGTH ts = len ∧
  n < len ∧
  EL n ts = (ks',t') ∧
  specialises tds db
    (ks',subst_db (LENGTH ks') (MAP (tshift (LENGTH ks')) targs) t') t
  ⇒
  type_tcexp ns db st env (tcexp_of (nth_from_dict clcon len n))
    (Functions [cons_types (UserType cid) targs] t)
Proof
  rw[tcexp_of_def,nth_from_dict_def] >>
  irule type_tcexp_Lam >>
  simp[type_ok,kind_ok_cons_types,EXISTS_PROD,kind_arrows_kindType_EQ] >>
  rw[] >>
  irule type_tcexp_NestedCase >>
  rw[PULL_EXISTS]
  >- (
    simp[select_nth_cepat_thm] >>
    simp[MEM_FLAT]
  ) >>
  irule_at (Pos last) type_tcexp_Var >>
  simp[specialises_def] >>
  irule_at (Pos hd) tcexp_type_cepat_Cons >>
  rw[oneline tcexp_destruct_type_cons_def] >>
  TOP_CASE_TAC >>
  gvs[split_ty_cons_eq_split_ty,split_ty_thm,head_ty_cons_types,head_ty_def] >>
  simp[cons_types_EQ_Atom,ty_args_cons_types,
    PULL_EXISTS,tcexp_type_cons_def] >>
  simp[ty_args_def,ty_args_aux_def,select_nth_cepat_thm] >>
  simp[LIST_REL3_EL,arithmeticTheory.ADD1,EL_MAP] >>
  qexists_tac `REPLICATE n [] ++
    ([(«y»,t)]::REPLICATE (LENGTH ts - (n + 1)) [])` >>
  simp[EL_APPEND_EQN,EL_REPLICATE,MAP_FLAT,FLAT_REPLICATE_NIL] >>
  rw[]
  >- irule tcexp_type_cepat_UScore
  >- (
    reverse $ Cases_on `n' - n` >>
    gvs[EL_REPLICATE]
    >- irule tcexp_type_cepat_UScore >>
    irule tcexp_type_cepat_Var >>
    `n = n'` by fs[] >>
    gvs[]
  )
  >- (
    irule type_tcexp_Var >>
    rw[specialises_def]
  )
  >- (
    irule tcexp_exhaustive_cepat_Cons >>
    reverse $ conj_asm2_tac
    >- (
      rw[destructable_type_def,cons_types_EQ_Atom] >>
      CASE_TAC
      >- (
        pop_assum mp_tac >>
        `∃x. head_ty_cons (cons_types (UserType cid) targs) = SOME x`
          suffices_by (rw[] >> simp[]) >>
        simp[head_ty_cons_eq_head_ty,head_ty_cons_types,head_ty_def]
      ) >>
      gvs[head_ty_cons_eq_head_ty,head_ty_cons_types,head_ty_def,
        oEL_THM]
    ) >>
    simp[unsafe_tcexp_destruct_type_cons_def,cons_types_EQ_Atom,
      split_ty_cons_eq_split_ty,split_ty_thm,head_ty_cons_types,
      ty_args_cons_types,head_ty_def,ty_args_def,ty_args_aux_def] >>
    rw[unsafe_tcexp_type_cons_def] >>
    qexists_tac `{select_nth_cepat n (LENGTH ts - (n + 1)) «y»}` >>
    simp[select_nth_cepat_thm] >>
    irule tcexp_exhaustive_cepatl >>
    qexists_tac `MAP (λx. {x}) $
      select_nth_cepat n (LENGTH ts - (n + 1)) «y»` >>
    rw[LIST_REL_EL_EQN,select_nth_cepat_thm,FOLDR_APPEND]
    >- simp[FOLDR_REPLICATE,FUNPOW_IMAGE_CONS_SING] >>
    simp[EL_MAP,EL_REPLICATE,EL_APPEND_EQN] >>
    IF_CASES_TAC
    >- (
      irule tcexp_exhaustive_cepat_UScore >>
      simp[]
    ) >>
    Cases_on `n' - n` >>
    simp[EL_REPLICATE]
    >- (
      irule tcexp_exhaustive_cepat_Var >>
      simp[]
    ) >>
    irule tcexp_exhaustive_cepat_UScore >>
    simp[]
  )
QED

Triviality translate_methods_aux_lem:
  ∀n.
  len = LENGTH l + n ⇒
  translate_methods_aux cons len n l =
    ZIP (l, REVERSE $ GENLIST (λi. nth_from_dict cons len (len - 1 - i)) (LENGTH l))
Proof
  Induct_on `l` >>
  rw[translate_methods_aux_def,GENLIST] >>
  simp[arithmeticTheory.ADD1]
QED

Theorem translate_methods_aux_thm:
  len = LENGTH l + n ⇒
  translate_methods_aux cons len n l =
    ZIP (l, GENLIST (λm. nth_from_dict cons len (n + m)) (LENGTH l))
Proof
  rw[translate_methods_aux_lem] >>
  simp[REVERSE_GENLIST] >>
  Cases_on `LENGTH l` >>
  simp[arithmeticTheory.ADD1] >>
  ntac 2 AP_TERM_TAC >>
  rw[LIST_EQ_REWRITE]
QED

Triviality Functions_CONS_alt:
  Functions (at::ats) t = Functions [at] (Functions ats t)
Proof
  simp[Functions_def]
QED

Triviality Cons_eq_cons_types:
  Cons t t' = cons_types t [t']
Proof
  simp[cons_types_def]
QED

(* shift the opposite direction of unshift_db *)
Definition unshift_db_def:
  (unshift_db skip n (TypeVar db) =
    if skip ≤ db then TypeVar (db - n) else TypeVar db) ∧
  (unshift_db skip n (Cons t1 t2) =
    Cons (unshift_db skip n t1) (unshift_db skip n t2)) ∧
  (unshift_db skip n t = t)
End

Theorem subst_db_GENLIST:
  subst_db n (GENLIST (λm. TypeVar (n + m)) m) t = unshift_db (n + m) m t
Proof
  Induct_on `t` using type_ind >>
  rw[subst_db_def,unshift_db_def]
QED

Theorem unshift_db_shift_db:
  unshift_db n m (shift_db n m t) = t
Proof
  Induct_on `t` using type_ind >>
  rw[shift_db_def,unshift_db_def]
QED

Theorem subst_db_sub_tshift_TypeVar:
  freetyvars_ok (n + 1) t ⇒
  subst_db n [tshift n (TypeVar m)] t = shift_db n m t
Proof
  Induct_on `t` using type_ind >>
  rw[shift_db_def,subst_db_def,freetyvars_ok_def] >>
  `n' = n` by gvs[] >>
  simp[]
QED

Theorem freetyvars_ok_Functions:
  freetyvars_ok n (Functions l t) ⇔
  (freetyvars_ok n t ∧ ∀x. MEM x l ⇒ freetyvars_ok n x)
Proof
  Induct_on `l` >>
  rw[Functions_def,freetyvars_ok_def,DISJ_IMP_THM] >>
  rw[EQ_IMP_THM]
QED

class Functor m => Monad m where
  bind :: m a -> (a -> m b) -> m b
  ret :: a -> m a

data MonadDict m = Monad (FunctorDict m, forall a b.m a -> (a -> m b) -> m
b,..)


bind :: MonadDict m -> m a -> (a -> m b) -> m b
bind m = case m of
         | Monad func bind ret => bind

Monad m => Functor m
getFunctor :: MonadDict m -> FunctorDict m

MonadDict .., ..., ...

Theorem class_map_construct_dict_type_tcexp:
  ∀cons sup_vs ce' fns' rest_ce rest_cons.
  class_map_to_ns ce cl_to_tyid clcons ce = SOME cl_ns ∧
  ALL_DISTINCT (MAP FST ce) ∧
  class_map_kind_ok (SND ns) ce ∧
  LENGTH ce ≤ LENGTH clcons ∧
  cl_to_tyid = ce_to_cl_tyid_map (LENGTH $ SND ns) ce ∧
  ce = rest_ce ++ ce' ∧
  clcons = rest_cons ++ cons ∧
  LENGTH rest_ce = LENGTH rest_cons ∧
  LENGTH (FLAT (MAP (λ(cl,k,supers,meths). supers) ce')) = LENGTH sup_vs ∧
  class_map_construct_dict cons sup_vs ce' = fns' ⇒

  (∀n. n < LENGTH sup_vs ⇒
    ∃f k t.
      MEM (EL n sup_vs,f) fns' ∧
      translate_entailment cl_to_tyid (EL n (class_map_to_ie ce')) =
        SOME ([k],t) ∧
      type_tcexp (append_ns (namespace_to_tcexp_namespace ns) ([],cl_ns))
        [k] st env (tcexp_of f) t) ∧

   (∀cl k supers meths meth_name meth_ty.
      MEM (cl,k,supers,meths) ce' ∧
      MEM (meth_name,meth_ty) meths ⇒
      ∃f ks cid targs t. MEM (meth_name,f) fns' ∧
        translate_pred_type_scheme cl_to_tyid (get_method_type cl k meth_ty) =
          SOME (ks,t) ∧
        FLOOKUP cl_to_tyid cl = SOME cid ∧
        type_tcexp (append_ns (namespace_to_tcexp_namespace ns) ([],cl_ns))
          ks st env (tcexp_of f) t)
Proof
  recInduct class_map_construct_dict_ind >>
  reverse $ rw[class_map_construct_dict_def] >>
  gvs[]
  >- (
    first_x_assum $ drule_then drule >>
    rw[] >>
    first_x_assum $ irule_at (Pat `type_tcexp _ _ _ _ _ _`) >>
    simp[]
  )
  >- (
    irule_at (Pos hd) OR_INTRO_THM1 >>
    ntac 2 $ pop_assum kall_tac >>
    simp[translate_methods_aux_thm,oneline get_method_type_def,translate_pred_type_scheme_def,
      MEM_ZIP,EL_TAKE,EL_APPEND_EQN,PULL_EXISTS,LAMBDA_PROD,
      FLOOKUP_ce_to_cl_tyid_map,find_index_ALL_DISTINCT_EL_eq] >>
    drule_then (strip_assume_tac o GSYM) $ iffLR MEM_EL >>
    CONV_TAC $ RESORT_EXISTS_CONV (sort_vars ["n","z"]) >>
    qexistsl [`LENGTH supers + n`,`LENGTH rest_cons`] >>
    simp[EL_MAP] >>
    CASE_TAC >>
    CASE_TAC >>
    simp[] >>
    irule_at (Pos last) nth_from_dict_type_tcexp >>
    simp[translate_pred_type_def] >>
    rename1 `(cl,TypeVar (LENGTH tks))::l` >>
    qspecl_then [`LENGTH (SND ns)`,`(cl,TypeVar (LENGTH tks))::l`,
      `(rest_ce ++ [(cl,k,supers,meths)] ++ ce')`] mp_tac $
      GEN_ALL IMP_translate_predicates_SOME >>
    simp[ce_to_clk_def] >>
    impl_tac
    >- (
      rw[]
      >- (
        simp[ALOOKUP_EXISTS_IFF] >>
        metis_tac[]
      ) >>
      gvs[class_map_kind_ok_def,DISJ_IMP_THM,FORALL_AND_THM,EVERY_MEM] >>
      first_x_assum drule >>
      rw[pred_type_kind_ok_alt] >>
      first_x_assum drule >>
      rw[ce_to_clk_def] >>
      simp[]
    ) >>
    strip_tac >>
    gvs[translate_predicates_def,translate_predicate_def] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_TRANS >>
    irule_at (Pat `_ = Functions [cons_types _ _] _`) Functions_CONS_alt >>
    `Cons (UserType pid) (TypeVar (LENGTH tks)) =
      cons_types (UserType pid) [TypeVar (LENGTH tks)]`
      by simp[cons_types_def] >>
    simp[] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    gvs[FLOOKUP_ce_to_cl_tyid_map,oEL_THM,find_index_ALL_DISTINCT_EL_eq] >>
    rename1 `EL m (MAP FST rest_ce ++ [cl] ++ MAP FST ce')` >>
    `m = LENGTH rest_ce`
    by (
      gvs[EL_ALL_DISTINCT_EL_EQ] >>
      first_x_assum $ irule o iffLR >>
      rw[] >>
      irule EQ_TRANS >>
      first_x_assum $ irule_at (Pos hd) o GSYM >>
      simp[EL_APPEND_EQN]
    ) >>
    simp[LENGTH_tdefs_to_tcexp_tdefs,EL_APPEND_EQN] >>
    drule class_map_to_ns_EL >>
    rw[] >>
    first_x_assum $ qspec_then `LENGTH rest_cons` mp_tac >>
    rw[] >>
    gvs[EL_APPEND_EQN,kind_ok,oEL_THM] >>
    gvs[translate_superclasses_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,
      LIST_REL_EL_EQN] >>
    qpat_x_assum
      `∀n. n < LENGTH method_tys ⇒ translate_pred_type_scheme _ _ = _` $
      drule >>
    rw[EL_MAP,translate_pred_type_scheme_def,translate_pred_type_def] >>
    first_x_assum $ assume_tac o GSYM >>
    simp[specialises_def] >>
    qexists `GENLIST TypeVar (LENGTH tks)` >>
    rw[LIST_REL_EL_EQN,kind_ok,oEL_THM,EL_APPEND_EQN] >>
    gvs[class_map_kind_ok_def,FORALL_AND_THM,DISJ_IMP_THM,EVERY_MEM,
      FORALL_PROD] >>
    qpat_x_assum `!meth ks pt. MEM _ methods ⇒ pred_type_kind_ok _ _ _ _`
      drule >>
    rw[pred_type_kind_ok_alt] >>
    irule EQ_TRANS >>
    irule_at (Pat `_ = Functions _ _`) unshift_db_shift_db >>
    simp[SRULE[] $ INST [``n:num`` |-> ``0n``] $ subst_db_GENLIST] >>
    qexistsl [`LENGTH tks`,`LENGTH tks`] >>
    DEP_REWRITE_TAC[subst_db_sub_tshift_TypeVar] >>
    rw[freetyvars_ok_Functions]
    >- (
      drule kind_ok_IMP_freetyvars_ok >>
      simp[]
    ) >>
    gvs[translate_predicates_LIST_REL,LIST_REL_EL_EQN] >>
    drule $ iffLR MEM_EL >>
    rw[] >>
    first_x_assum drule >>
    pairarg_tac >> rw[] >>
    simp[freetyvars_ok_def] >>
    qpat_x_assum `!cl. MEM _ _ ⇒ ∃k. _ ∧ kind_ok _ _ _ _` $
      assume_tac o SRULE[PULL_EXISTS,MEM_EL] >>
    gvs[] >>
    first_x_assum drule >>
    rw[] >>
    drule kind_ok_IMP_freetyvars_ok >>
    simp[]
  ) >>
  Cases_on `LENGTH supers ≤ n`
  >- (
    last_x_assum $ qspec_then `n - LENGTH supers` mp_tac >>
    rw[] >>
    gvs[EL_DROP] >>
    qexists_tac `f` >>
    fs[class_map_to_ie_def] >>
    simp[class_map_to_ie_def,EL_APPEND_EQN,class_to_entailments_def]
  )
  >- (
    `n < LENGTH supers` by gvs[] >>
    gvs[] >>
    simp[translate_methods_aux_def,translate_entailment_def,class_map_to_ie_def,
      class_to_entailments_def,EL_MAP,PULL_EXISTS,EL_APPEND_EQN,
      translate_predicates_def,translate_predicate_def] >>
    irule_at (Pos hd) OR_INTRO_THM1 >>
    simp[translate_methods_aux_thm,MEM_ZIP,PULL_EXISTS] >>
    CONV_TAC (RESORT_EXISTS_CONV rev) >>
    qexists_tac `n` >>
    simp[EL_APPEND_EQN,EL_TAKE] >>
    `∀pid. Cons (UserType pid) (TypeVar 0) =
      cons_types (UserType pid) [TypeVar 0]`
      by simp[cons_types_def] >>
    simp[] >>
    irule_at (Pos last) nth_from_dict_type_tcexp >>
    simp[PULL_EXISTS] >>
    drule class_map_to_ns_EL >>
    rw[] >>
    simp[oEL_THM,EL_APPEND_EQN,LENGTH_tdefs_to_tcexp_tdefs] >>
    CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["cid","x"])) >>
    qexists_tac `LENGTH (SND ns) + LENGTH rest_ce` >>
    first_x_assum $ qspec_then `LENGTH rest_cons` mp_tac >>
    rw[] >>
    gvs[EL_APPEND_EQN,translate_superclasses_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,
      LIST_REL_EL_EQN] >>
    simp[kind_ok,oEL_THM] >>
    first_x_assum drule >>
    rw[] >>
    simp[specialises_def,subst_db_cons_types,subst_db_def] >>
    simp[FLOOKUP_to_cl_tyid_map,find_index_ALL_DISTINCT_EL_eq,EL_APPEND_EQN]
  )
QED

Theorem impl_construct_dict_type_tcexp:
  namespace_ok ns ∧
  class_map_to_ns ce (ce_to_cl_tyid_map (LENGTH (SND ns)) ce) clcons ce =
    SOME cl_tds ∧
  LENGTH ce ≤ LENGTH clcons ∧ ALL_DISTINCT (MAP FST ce) ∧
  clk = ce_to_clk ce ∧
  cl_to_tyid = ce_to_cl_tyid_map (LENGTH (SND ns)) ce ∧
  ie_map = alist_to_fmap ie_alist ∧ ie = FRANGE (alist_to_fmap ie_alist) ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  (∀ent. ent ∈ ie ⇒ entailment_kind_ok (SND ns) clk ent) ∧
  (∀v ent. MEM (v,ent) ie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
  (∀v ent. MEM (v,ent) ie_alist ⇒ v ∉ lambda_vars e) ∧
  (∀v ent. MEM (v,ent) ie_alist ⇒ ∀cl t. ¬MEM (v,cl,t) lie_alist) ∧
  (∀v cl ct. MEM (v,cl,ct) lie_alist ⇒ ∀ks vt. ¬MEM (v,ks,vt) env) ∧
  (∀v ks vt. MEM (v,ks,vt) lie_alist ⇒ v ∉ lambda_vars e) ∧

  pred_type_elaborate_texp ns clk ie (set cstrs) (meth_ks ++ varks)
    st env e e'
    (subst_db_pred (LENGTH meth_ks) [inst_t] pt) ∧
  impl_construct_dict ns ie_map env_vs vs cstrs ks pt e de ∧
  env_vs = set (MAP FST env) ∧
  translate_env cl_to_tyid env = SOME trans_env ∧
  translate_predicates cl_to_tyid cstrs = SOME arg_ts ∧
  translate_pred_type cl_to_tyid pt = SOME ret_t ∧
  t = Functions arg_ts (subst_db (LENGTH meth_ks) [inst_t] ret_t) ⇒
  type_tcexp (append_ns (namespace_to_tcexp_namespace ns) ([],cl_tds))
    (meth_ks ++ varks) st (trans_env ++ ie_env) (tcexp_of de) t
Proof
QED


Theorem construct_dict_main_type_tcexp:
  env = default_env ++ cl_env ∧
  ie_map = FEMPTY |++ cl_ie_alist |++ inst_ie_alist ∧
  trans_ns = (append_ns (namespace_to_tcexp_namespace ns) ([],cl_tds)) ∧
  trans_fns = translated_ie ++ translated_ce ++
     translated_defaults ++ fns'' ∧
  type_elaborate_texp ns clk (FRANGE ie_map) EMPTY [] st env
    (Letrec fns (Var any v))
    (Letrec fns' (Var ps v')) (Monad t) ∧
  texp_construct_dict ns ie_map FEMPTY []
    (set (MAP FST env)) (Letrec fns' (Var ps v'))
    (Letrec () fns'' trans_main_exp) ⇒
  type_tcexp trans_ns [] st []
    (tcexp_of (Letrec () trans_fns trans_main_exp))
    (Monad t)
Proof
  rw[tcexp_of_def] >>
  qpat_x_assum `type_elaborate_texp _ _ _ _ _ _ _ _ _ _` $
    strip_assume_tac o SRULE[Once type_elaborate_texp_cases] >>
  qpat_x_assum `texp_construct_dict _ _ _ _ _ _ _` $
    strip_assume_tac o SRULE[Once texp_construct_dict_cases] >>
  irule type_tcexp_Letrec >>
  rw[]
  >- gvs[LIST_REL_EL_EQN] >>
  (* TODO: tidy up the induction theorem *)
  irule_at (Pos last) $ cj 2 texp_construct_dict_type_tcexp

QED

val _ = export_theory();
