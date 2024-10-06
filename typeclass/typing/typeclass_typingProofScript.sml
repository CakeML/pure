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

Theorem LIST_REL3_LIST_REL:
  ∀a b c. LIST_REL3 P a b c ⇒
  (∀x y z. P x y z ⇒ Q x y) ⇒
  LIST_REL Q a b
Proof
  ho_match_mp_tac LIST_REL3_induct >>
  rw[] >>
  metis_tac[]
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

Theorem translate_predicate_type_ok_relax:
  class_map_to_ns cl_tyid_map cl_map = SOME cl_tds ∧
  cl_tyid_map = to_cl_tyid_map tds cl_map ∧
  tds' = tds ++ cl_tds ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_to_clk cl_map cl = SOME k ∧
  kind_ok (tds ++ cl_tds) ks k t ∧
  translate_predicate cl_tyid_map (cl,t) = SOME t' ⇒
  type_ok tds' ks t'
Proof
  simp[] >> metis_tac[translate_predicate_type_ok]
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

Theorem alist_to_fmap_EQ_FUPDATE_LIST_REVERSE:
  alist_to_fmap l = FEMPTY |++ (REVERSE l)
Proof
  PURE_REWRITE_TAC[FUPDATE_LIST_EQ_APPEND_REVERSE] >>
  simp[]
QED

Theorem FUPDATE_LIST_EQ_alist_to_fmap_REVERSE:
  FEMPTY |++ l = alist_to_fmap (REVERSE l)
Proof
  irule EQ_SYM >>
  simp[alist_to_fmap_EQ_FUPDATE_LIST_REVERSE]
QED

Theorem alist_to_fmap_FUPDATE_LIST:
  alist_to_fmap l |++ r = alist_to_fmap (REVERSE r ++ l)
Proof
  PURE_REWRITE_TAC[alist_to_fmap_EQ_FUPDATE_LIST_REVERSE,
    REVERSE_APPEND,REVERSE_REVERSE,
    finite_mapTheory.FUPDATE_LIST_APPEND] >>
  simp[]
QED

Theorem alist_to_fmap_DOMSUB_EQ_ID:
  (∀y. ¬MEM (x,y) l)⇒
  alist_to_fmap l \\ x = alist_to_fmap l
Proof
  rw[alist_to_fmap_EQ_FUPDATE_LIST_REVERSE,finite_mapTheory.DOMSUB_FUPDATE_LIST,
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

Theorem translate_predicates_subst_db:
    ∀ps'.
    translate_predicates cl_to_tyid (MAP (I ## subst_db len subs) l) = SOME ps' ⇒
    ∃ps. translate_predicates cl_to_tyid l = SOME ps ∧
      MAP (subst_db len subs) ps = ps'
Proof
  Induct_on `l` >>
  rw[translate_predicates_def,PULL_EXISTS] >>
  Cases_on `h` >>
  gvs[translate_predicate_def,subst_db_def]
QED

Theorem translate_predicates_tsubst:
  ∀ps'.
    translate_predicates cl_to_tyid (MAP (I ## tsubst subs) l) = SOME ps' ⇒
    ∃ps. translate_predicates cl_to_tyid l = SOME ps ∧ MAP (tsubst subs) ps = ps'
Proof
  metis_tac[translate_predicates_subst_db]
QED

Theorem translate_predicates_IMP_translate_predicates_subst_db:
  ∀l ps. 
  translate_predicates cl_to_tyid l = SOME ps ⇒
  translate_predicates cl_to_tyid (MAP (I ## subst_db len subs) l) =
    SOME $ MAP (subst_db len subs) ps
Proof
  Induct >>
  gvs[translate_predicates_def] >>
  rw[] >>
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
  drule translate_predicates_tsubst >>
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
  drule translate_predicates_tsubst >>
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
  rw[alist_to_fmap_EQ_FUPDATE_LIST_REVERSE,finite_mapTheory.FUPDATE_LIST_APPEND,MEM_MAP,FORALL_PROD,
    EQ_IMP_THM]
  >- (
    Cases_on `h` >>
    gvs[alist_to_fmap_EQ_FUPDATE_LIST_REVERSE,finite_mapTheory.FUPDATE_LIST_ALL_DISTINCT_REVERSE,
      GSYM finite_mapTheory.FUPDATE_EQ_FUPDATE_LIST]
    >- metis_tac[] >>
    drule $ SRULE[SUBSET_DEF] finite_mapTheory.FRANGE_DOMSUB_SUBSET >>
    metis_tac[]
  ) >>
  gvs[alist_to_fmap_EQ_FUPDATE_LIST_REVERSE,finite_mapTheory.FUPDATE_LIST_ALL_DISTINCT_REVERSE,
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
  simp[alist_to_fmap_EQ_FUPDATE_LIST_REVERSE,pure_miscTheory.o_f_FUPDATE_LIST,
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
    pred_type_kind_scheme_ok clk tds db scheme) env ⇒
  EVERY (λ(p1,p1',p2).
    pred_type_kind_ok clk tds (p1' ++ new ++ db)
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

Theorem MAP_FST_trans_env:
  ∀env trans_env. 
  translate_env cl_to_tyid env = SOME trans_env ⇒
  MAP FST trans_env = MAP FST env
Proof
  Induct_on `env` >>
  rw[translate_env_def] >>
  Cases_on `h` >>
  gvs[translate_env_def]
QED

Theorem DISJOINT_trans_env:
  translate_env cl_to_tyid env = SOME trans_env ∧
  DISJOINT s (set (MAP FST env)) ⇒
  DISJOINT s (set (MAP FST trans_env))
Proof
  strip_tac >>
  drule MAP_FST_trans_env >>
  simp[]
QED

Theorem DISJOINT_lambda_varsl_IMP:
  DISJOINT s (lambda_varsl es) ∧ n < LENGTH es ⇒
  DISJOINT s (lambda_vars (EL n es))
Proof
  simp[DISJOINT_NOT_IN_R] >>
  metis_tac[lambda_vars_IMP_lambda_varsl]
QED

Theorem DISJOINT_lambda_varsl_MEM:
  DISJOINT s (lambda_varsl es) ∧ MEM e es ⇒
  DISJOINT s (lambda_vars e)
Proof
  metis_tac[DISJOINT_lambda_varsl_IMP,MEM_EL]
QED

Theorem construct_dict_type_tcexp:
  translate_lie_alist cl_to_tyid lie_alist = SOME lie_env ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  ALL_DISTINCT (MAP FST lie_alist ++ MAP FST ie_alist) ∧
  DISJOINT (set (MAP FST lie_alist ++ MAP FST ie_alist)) (set (MAP FST env)) ∧
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

Theorem DISJOINT_ALOOKUP_APPEND:
  DISJOINT (set $ MAP FST a) (set $ MAP FST b) ⇒
  ALOOKUP (a ++ b) x = ALOOKUP (b ++ a) x
Proof
  rw[ALOOKUP_APPEND] >>
  TOP_CASE_TAC >>
  TOP_CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[DISJOINT_NOT_IN_R,MEM_MAP,PULL_EXISTS] >>
  spose_not_then kall_tac >>
  last_x_assum drule >>
  simp[EXISTS_PROD] >>
  first_assum $ irule_at (Pos hd)
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
        (set (MAP FST env) ∪ lambda_vars e') ∧
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
        (set (MAP FST env) ∪ lambda_vars e') ∧
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
      PURE_REWRITE_RULE[alist_to_fmap_FUPDATE_LIST] >>
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
        metis_tac[DISJOINT_SYM]
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
        ∃k. class_map_to_clk _ _ = SOME _ ∧ _` drule >>
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
      `exp = EL n (MAP SND fns')` by simp[EL_MAP] >>
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
      simp[EL_MAP] >>
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
    conj_tac >- metis_tac[DISJOINT_SYM] >>
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
      rename1`EL n' pes' = (cepat,exp)` >>
      `MEM (EL n' pes') pes'` by metis_tac[MEM_EL] >>
      gvs[] >>
      first_x_assum drule >>
      drule_then assume_tac $ GSYM type_cepat_cepat_vars >>
      gvs[GSYM pure_miscTheory.FST_THM] >>
      strip_tac >>
      `exp = EL n' (MAP SND pes')` by simp[EL_MAP] >>
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

Triviality ALL_DISTINCT_APPEND_DISJOINT:
  ALL_DISTINCT (a ++ b) ⇔
    ALL_DISTINCT a ∧ ALL_DISTINCT b ∧
    DISJOINT (set a) (set b)
Proof
  simp[ALL_DISTINCT_APPEND,DISJOINT_NOT_IN_R]
QED

(* show that the translated namespace is ok *)
Theorem namespace_ok_IMP_tcexp_namespace_ok:
  namespace_ok ns ∧
  ALL_DISTINCT (FLAT (MAP (MAP FST ∘ SND) tds)) ∧
  DISJOINT (set $ FLAT (MAP (MAP FST ∘ SND) tds))
    (set $ (MAP implode (SET_TO_LIST reserved_cns)) ++
      (MAP FST (FST ns)) ++
      (FLAT (MAP (MAP FST o SND) (SND ns)))) ∧
  EVERY (λ(ks,td). td ≠ []) tds ∧
  EVERY (λ(ks,td). EVERY (λ(cn,argtys).
    EVERY (
      type_scheme_ok
        (tdefs_to_tcexp_tdefs (SND ns) ++ tds) ks)
        argtys) td) tds
  ⇒
    tcexp_namespace_ok $ translate_ns ns tds
Proof
  simp[namespace_to_tcexp_namespace_def,translate_ns_def,
    tdefs_to_tcexp_tdefs_def,pair_CASE_def,
    tcexp_namespace_ok_def,oneline namespace_ok_def,
    EVERY_MAP,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
    type_scheme_ok_def,
    lambdify type_ok_def,MAP_FLAT] >>
  rw[]
  >- (
    gvs[ALL_DISTINCT_APPEND_DISJOINT] >>
    gvs[DISJOINT_NOT_IN_R,MEM_MAP,PULL_EXISTS]
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

Triviality LENGTH_SUM_1:
  (∀x. MEM x xs ⇒ f x = 1) ⇒
  SUM (MAP f xs) = LENGTH xs
Proof
  Induct_on `xs` >>
  rw[]
QED

Theorem class_dict_constructor_names_EQ:
  ∀cl_map cl_ns. 
  class_map_to_ns cl_to_tyid cl_map = SOME cl_ns ⇒
  class_dict_constructor_names cl_map =
    FLAT (MAP (MAP FST ∘ SND) cl_ns)
Proof
  Induct_on `cl_map` >>
  gvs[class_map_to_ns_def,class_dict_constructor_names_def] >>
  rw[] >>
  Cases_on `h` >>
  gvs[class_map_to_ns_def,class_to_datatype_def]
QED

Theorem translate_ns_and_class_datatypes_IMP_tcexp_namespace_ok:
  namespace_ok ns ∧
  translate_ns_and_class_datatypes ns cl_map tcexp_ns ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_kind_ok (SND ns) cl_map ∧
  ALL_DISTINCT (class_dict_constructor_names cl_map) ∧
  DISJOINT (set $ class_dict_constructor_names cl_map)
    (set $ (MAP implode (SET_TO_LIST reserved_cns)) ++
      (MAP FST (FST ns)) ++
      (FLAT (MAP (MAP FST ∘ SND) (SND ns)))) ⇒
  tcexp_namespace_ok tcexp_ns
Proof
  rw[translate_ns_and_class_datatypes_def] >>
  drule_then irule
    namespace_ok_IMP_tcexp_namespace_ok >>
  drule_then (irule_at Any) class_map_to_ns_NON_EMPTY >>
  drule_then (irule_at Any)
    class_map_to_ns_EVERY_type_scheme_ok >>
  drule_then assume_tac
    class_dict_constructor_names_EQ >>
  gvs[]
QED

Theorem method_names_thm:
  method_names cl_map =
    FLAT (MAP (λx. MAP FST (SND x).methods) cl_map)
Proof
  Induct_on `cl_map` >>
  rw[method_names_def] >>
  PairCases_on `h` >>
  rw[method_names_def]
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
  tds = SND ns ∧
  LENGTH ts = len ∧
  n < len ∧
  EL n ts = (ks',t') ∧
  specialises tds db
    (ks',subst_db (LENGTH ks') (MAP (tshift (LENGTH ks')) targs) t') t ∧
  func_t = Functions [cons_types (UserType cid) targs] t
  ⇒
  type_tcexp ns db st env (tcexp_of (nth_from_dict clcon len n)) func_t
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
  LENGTH l ≤ len ⇒
  translate_methods_aux cons len n l =
    ZIP (l, REVERSE $ GENLIST (λi. nth_from_dict cons len
      (LENGTH l + n - 1 - i)) (LENGTH l))
Proof
  Induct_on `l` >>
  rw[translate_methods_aux_def,GENLIST] >>
  simp[arithmeticTheory.ADD1]
QED

Theorem translate_methods_aux_thm:
  LENGTH l ≤ len ⇒
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

Theorem tsubst_GENLIST_APPEND:
  freetyvars_ok (n + LENGTH ts) t ⇒
  tsubst (GENLIST (λx. TypeVar x) n ++ ts) t =
  subst_db n ts (unshift_db (n + LENGTH ts) k t)
Proof
  Induct_on `t` using type_ind >>
  rw[] >>
  gvs[subst_db_def,shift_db_def,unshift_db_def,freetyvars_ok_def] >>
  simp[EL_APPEND_EQN,EL_GENLIST] >>
  IF_CASES_TAC >>
  gvs[]
QED

Theorem freetyvars_ok_shift_db_skip:
  freetyvars_ok skip t ⇒
  freetyvars_ok skip (shift_db skip shift t)
Proof
  Induct_on `t` using type_ind >>
  rw[] >>
  gvs[freetyvars_ok_def,shift_db_def]
QED

Theorem specialises_tshift:
  t' = tshift (LENGTH db) t ∧
  freetyvars_ok (LENGTH ks) t ∧
  db' = db ++ ks ⇒
  specialises tds db' (ks,t) t'
Proof
  rw[specialises_def] >>
  qexists `GENLIST (λm. TypeVar (m + LENGTH db)) (LENGTH ks)` >>
  pop_assum mp_tac >>
  Induct_on `t` using type_ind >>
  rw[shift_db_def,subst_db_def,freetyvars_ok_def] >>
  simp[LIST_REL_EL_EQN,kind_ok,LLOOKUP_THM,EL_APPEND_EQN]
QED

Theorem freetyvars_ok_Functions:
  freetyvars_ok n (Functions l t) ⇔
  (freetyvars_ok n t ∧ ∀x. MEM x l ⇒ freetyvars_ok n x)
Proof
  Induct_on `l` >>
  rw[Functions_def,freetyvars_ok_def,DISJ_IMP_THM] >>
  rw[EQ_IMP_THM]
QED

Theorem translate_ie_alist_SOME_APPEND:
  translate_ie_alist cl_to_tyid (l ++ r) = SOME lr ⇔
    ∃l' r'. translate_ie_alist cl_to_tyid l = SOME l' ∧
      translate_ie_alist cl_to_tyid r = SOME r' ∧
      lr = l' ++ r'
Proof
  simp[translate_ie_alist_OPT_MMAP,OPT_MMAP_SOME_APPEND]
QED

Theorem class_map_to_ns_OPT_MMAP:
  class_map_to_ns cl_to_tyid cl_map =
    OPT_MMAP (λ(clname,cl).class_to_datatype cl_to_tyid cl) cl_map
Proof
  Induct_on `cl_map` >>
  rw[class_map_to_ns_def] >>
  PairCases_on `h` >>
  rw[class_map_to_ns_def]
QED

Theorem FLOOKUP_to_cl_tyid_map_IMP:
  ∀class_map cl_to_tyid c tyid trans_ns trans_tds.
  FLOOKUP cl_to_tyid c = SOME tyid ∧
  ALL_DISTINCT (MAP FST class_map) ∧
  translate_ns_and_class_datatypes ns class_map trans_ns ∧
  cl_to_tyid = to_cl_tyid_map tds class_map ∧
  tds = SND ns ∧
  trans_tds = SND trans_ns ⇒
  ∃cl datatype.
    ALOOKUP class_map c = SOME cl ∧
    LLOOKUP trans_tds tyid = SOME datatype ∧
    class_to_datatype cl_to_tyid cl = SOME datatype
Proof
  rw[translate_ns_and_class_datatypes_def,translate_ns_def] >>
  gvs[FLOOKUP_to_cl_tyid_map,LLOOKUP_THM,LENGTH_tdefs_to_tcexp_tdefs,
    EL_APPEND_EQN] >>
  drule_then strip_assume_tac $ cj 1 class_map_to_ns_EL >>
  gvs[find_index_ALL_DISTINCT_EL_eq] >>
  gvs[class_map_to_ns_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,LIST_REL_EL_EQN] >>
  irule_at (Pos hd) ALOOKUP_ALL_DISTINCT_MEM >>
  simp[] >>
  irule_at (Pos hd) $ iffRL MEM_EL >>
  first_assum $ irule_at (Pos hd) >>
  simp[EL_MAP] >>
  irule_at (Pos hd) PAIR >>
  first_x_assum drule >>
  pairarg_tac >> simp[]
QED

Theorem MEM_to_cl_tyid_map_thm:
  ∀class_map cl_to_tyid c cl trans_ns trans_tds.
  MEM (c,cl) class_map ∧
  ALL_DISTINCT (MAP FST class_map) ∧
  translate_ns_and_class_datatypes ns class_map trans_ns ∧
  cl_to_tyid = to_cl_tyid_map tds class_map ∧
  tds = SND ns ∧
  trans_tds = SND trans_ns ⇒
  ∃tyid datatype.
    FLOOKUP cl_to_tyid c = SOME tyid ∧
    LLOOKUP trans_tds tyid = SOME datatype ∧
    class_to_datatype cl_to_tyid cl = SOME datatype
Proof
  rw[translate_ns_and_class_datatypes_def,translate_ns_def] >>
  gvs[FLOOKUP_to_cl_tyid_map,LLOOKUP_THM,LENGTH_tdefs_to_tcexp_tdefs,
    EL_APPEND_EQN,PULL_EXISTS] >>
  drule_then strip_assume_tac $ cj 1 class_map_to_ns_EL >>
  gvs[find_index_ALL_DISTINCT_EL_eq,MEM_EL] >>
  first_assum $ irule_at (Pat `_ < LENGTH class_map`) >>
  simp[EL_MAP] >>
  qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >>
  gvs[class_map_to_ns_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,LIST_REL_EL_EQN] >>
  first_x_assum drule >>
  simp[]
QED

Definition cl_to_tyid_cl_map_rel_def:
  cl_to_tyid_cl_map_rel tds cl_to_tyid cl_map ⇔
  (∀c cl. MEM (c,cl) cl_map ==>
    ∃tyid datatype.
      FLOOKUP cl_to_tyid c = SOME tyid ∧
      LLOOKUP tds tyid = SOME datatype ∧
      class_to_datatype cl_to_tyid cl = SOME datatype)
End

Theorem cl_to_tyid_cl_map_rel_alt:
  (∀tds cl_to_tyid. cl_to_tyid_cl_map_rel tds cl_to_tyid [] ⇔ T) ∧
  (∀tds cl_to_tyid c cl cl_map.
  cl_to_tyid_cl_map_rel tds cl_to_tyid ((c,cl)::cl_map) ⇔
    (∃tyid datatype.
        FLOOKUP cl_to_tyid c = SOME tyid ∧
        LLOOKUP tds tyid = SOME datatype ∧
        class_to_datatype cl_to_tyid cl = SOME datatype) ∧
    cl_to_tyid_cl_map_rel tds cl_to_tyid cl_map)
Proof
  rw[cl_to_tyid_cl_map_rel_def,DISJ_IMP_THM,FORALL_AND_THM,LEFT_AND_OVER_OR]
QED

Theorem class_map_super_accessors_type_tcexp:
  ∀cl_map cl_env cl_types supers_accessors. 
  class_map_super_accessors_env cl_to_tyid cl_map = SOME cl_env ∧
  cl_types = MAP SND cl_env ∧
  supers_accessors = class_map_construct_super_accessors cl_map ∧
  typed = (λ(fname,func) (ks,ty).
    type_tcexp trans_ns ks (MAP (tshift (LENGTH ks)) st)
    (tshift_env (LENGTH ks) env) (tcexp_of func) ty) ∧
  tds = SND trans_ns ∧
  cl_to_tyid_cl_map_rel tds cl_to_tyid cl_map
  ⇒
  LIST_REL typed supers_accessors cl_types
Proof
  Induct_on `cl_map` >>
  rw[class_map_super_accessors_env_def,class_map_to_ie_def,
    class_map_construct_super_accessors_def,
    translate_ie_alist_def] >>
  Cases_on `h`  >>
  gvs[class_map_to_ie_def,class_map_construct_super_accessors_def,LIST_REL_EL_EQN,
    translate_ie_alist_SOME_APPEND,class_to_entailments_def] >>
  gvs[translate_ie_alist_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,EVERY2_MAP,
    translate_methods_aux_thm] >>
  gvs[LIST_REL_EL_EQN,cl_to_tyid_cl_map_rel_alt] >>
  rw[] >>
  gvs[EL_ZIP,EL_MAP,EL_APPEND_EQN] >>
  Cases_on `n < LENGTH l'` >>
  rw[] >>
  Cases_on `EL n l'` >>
  rename1 `EL n l' = (ignore,type_scheme)` >>
  PairCases_on `type_scheme` >>
  simp[] >>
  irule nth_from_dict_type_tcexp >>
  rw[] >>
  last_x_assum drule >>
  Cases_on `EL n r.supers` >>
  simp[translate_entailment_def,translate_predicates_def,
    translate_predicate_def] >>
  rw[] >>
  gvs[class_to_datatype_def] >>
  first_assum $ irule_at (Pat `LLOOKUP _ _ = SOME _`) >>
  gvs[EVERY2_MAP,translate_superclasses_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,
    super_classes_def] >>
  imp_res_tac $ cj 1 $ iffLR LIST_REL_EL_EQN >>
  qpat_x_assum `LIST_REL _ r.methods _` kall_tac >>
  gvs[super_classes_def,LIST_REL_EL_EQN] >>
  first_x_assum drule >>
  rw[EL_APPEND_EQN,PULL_EXISTS] >>
  irule_at (Pos hd) $ METIS_PROVE[] ``f = g ∧ x = y ⇒ f x = g y`` >>
  simp[cons_types_def] >>
  irule_at (Pos hd) EQ_REFL >>
  simp[kind_ok,LLOOKUP_THM,specialises_def,subst_db_def]
QED

Triviality class_map_super_accessors_entailment_kind_ok_aux:
  ∀cl_map' c ent rest.
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_kind_ok tds cl_map ∧
  cl_map = rest ++ cl_map' ∧
  MEM (c,ent) (class_map_to_ie cl_map') ⇒
  entailment_kind_ok tds (class_map_to_clk cl_map) ent
Proof
  Induct_on `cl_map'` >>
  rw[class_map_to_ie_def,class_map_to_clk_def]
  >- (
    gvs[oneline class_to_entailments_def] >>
    pop_assum mp_tac >> CASE_TAC >>
    rw[MEM_MAP] >>
    rename1 `MEM super cl.supers` >>
    PairCases_on `super` >>
    gvs[entailment_kind_ok_def,PULL_EXISTS,kind_ok,LLOOKUP_THM,MEM_MAP,
      FORALL_PROD] >>
    gvs[class_map_kind_ok_def,DISJ_IMP_THM,FORALL_AND_THM,super_classes_def,
      EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
    first_x_assum drule >>
    simp[class_map_to_clk_def] >>
    rw[] >>
    simp[] >>
    irule_at (Pos hd) ALOOKUP_ALL_DISTINCT_MEM >>
    simp[] >>
    metis_tac[]
  ) >>
  gvs[class_map_to_clk_def,class_map_to_ie_def] >>
  first_x_assum drule >>
  simp[]
QED

Theorem class_map_super_accessors_entailment_kind_ok:
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_kind_ok tds cl_map ∧
  MEM (c,ent) (class_map_to_ie cl_map) ⇒
  entailment_kind_ok tds (class_map_to_clk cl_map) ent
Proof
  strip_tac >>
  (drule_then $ drule_at_then (Pos last) irule)
    class_map_super_accessors_entailment_kind_ok_aux >>
  rw[]
QED

Theorem class_map_methods_type_tcexp:
  ∀cl_map meth_env method_types.
  class_map_methods_translate_env cl_to_tyid cl_map = SOME meth_env ∧
  method_types = MAP SND meth_env ∧
  tds = SND trans_ns ∧
  EVERY (λ(ks,td). EVERY (λ(cn,argtys).
    EVERY (type_scheme_ok tds ks) argtys) td) tds ∧ 
  cl_to_tyid_cl_map_rel tds cl_to_tyid cl_map
  ⇒
  LIST_REL
    (λ(fname,func) (ks,ty).
      type_tcexp trans_ns ks (MAP (tshift (LENGTH ks)) st)
      (tshift_env (LENGTH ks) env) (tcexp_of func) ty)
    (class_map_construct_methods cl_map) method_types
Proof
  Induct_on `cl_map` >>
  rw[]
  >- gvs[class_map_construct_methods_def,class_map_methods_translate_env_def,
    class_map_to_env_def,translate_env_def] >>
  PairCases_on `h` >>
  gvs[class_map_methods_translate_env_def,class_map_to_env_def,
    class_map_construct_methods_def,translate_env_SOME_APPEND,
    cl_to_tyid_cl_map_rel_alt] >>
  irule LIST_REL_APPEND_suff >>
  simp[] >>
  gvs[translate_methods_aux_thm,LIST_REL_EL_EQN,translate_env_OPT_MMAP,
    OPT_MMAP_SOME_LIST_REL,EL_ZIP,EL_MAP] >>
  rw[] >>
  pairarg_tac >> simp[] >>
  irule nth_from_dict_type_tcexp >>
  simp[] >>
  first_x_assum drule >>
  pairarg_tac >> rw[] >>
  gvs[class_to_datatype_def,OPT_MMAP_SOME_LIST_REL,
    translate_superclasses_OPT_MMAP] >>
  first_assum $ irule_at (Pat `LLOOKUP _ _ = SOME _`) >>
  gvs[LIST_REL_EL_EQN,EL_APPEND_EQN,super_classes_def] >>
  qpat_x_assum `∀n. n < LENGTH method_tys ⇒ _` drule >>
  Cases_on `EL n h1.methods` >>
  rename1 `EL n h1.methods = (method_name,meth_pred_type)` >>
  PairCases_on `meth_pred_type` >>
  Cases_on `meth_pred_type1` >>
  gvs[EL_MAP,get_method_type_def,translate_pred_type_scheme_def,
    oneline translate_pred_type_def,PULL_EXISTS] >>
  gvs[translate_predicates_def,translate_predicate_def] >>
  disch_then $ assume_tac o GSYM >>
  simp[] >>
  irule_at (Pat `Functions _ _ = Functions _ _`) EQ_TRANS >>
  irule_at (Pat `Functions (_::_) _ = _`) Functions_CONS_alt >>
  simp[cons_types_def] >>
  irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
  simp[kind_ok,LLOOKUP_THM,EL_APPEND_EQN,specialises_def] >>
  qrefine `GENLIST TypeVar (LENGTH meth_pred_type0)` >>
  rw[LIST_REL_EL_EQN,kind_ok,oEL_THM,EL_APPEND_EQN] >>
  DEP_REWRITE_TAC[subst_db_sub_tshift_TypeVar] >>
  simp[SRULE[] $ Q.INST [`n` |-> `0n`] $ subst_db_GENLIST,
    unshift_db_shift_db] >>
  gvs[EVERY_EL,LLOOKUP_THM] >>
  qpat_x_assum `∀n. n < LENGTH (SND trans_ns) ⇒ _` drule >>  
  rw[] >>
  first_x_assum $ qspec_then `n + LENGTH sup_tys` mp_tac >>
  simp[EL_APPEND_EQN] >>
  rw[type_scheme_ok_def,type_ok] >>
  drule kind_ok_IMP_freetyvars_ok >>
  simp[]
QED

Theorem type_ok_Functions:
  type_ok tds ks (Functions as r) ⇔
  (type_ok tds ks r ∧ (∀arg. MEM arg as ⇒ type_ok tds ks arg))
Proof
  simp[type_ok_def,kind_ok_Functions] >>
  rw[EQ_IMP_THM] >>
  gvs[]
QED

Theorem class_map_methods_type_ok_aux:
  ∀cl_map' meth_env method_types rest_cl_map.
  class_map_methods_translate_env cl_to_tyid cl_map' = SOME meth_env ∧
  class_map_to_ns cl_to_tyid cl_map = SOME cl_tds ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_kind_ok tds cl_map ∧
  cl_map = rest_cl_map ++ cl_map' ∧
  cl_to_tyid = to_cl_tyid_map tds cl_map ∧
  method_types = MAP SND meth_env ∧
  trans_tds = tdefs_to_tcexp_tdefs tds ++ cl_tds
  ⇒
  EVERY (λ(ks,ty). type_ok trans_tds ks ty) method_types
Proof
  Induct_on `cl_map'` >>
  rw[]
  >- gvs[class_map_methods_translate_env_def,class_map_to_env_def,
    translate_env_def] >>
  PairCases_on `h` >>
  Cases_on `h1` >>
  gvs[class_map_methods_translate_env_def,class_map_to_env_def,
    translate_env_SOME_APPEND] >>
  gvs[translate_env_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,LIST_REL_EL_EQN,
    EL_MAP,EVERY_MAP,LAMBDA_PROD] >>
  rw[EVERY_EL] >>
  last_x_assum drule >>
  rename1 `_ ((I ## get_method_type _ _) (EL n methods)) = _` >> 
  Cases_on `EL n methods` >>
  rename1 `EL n methods = (method_name,method_pred_type)` >>
  PairCases_on `method_pred_type` >>
  Cases_on `method_pred_type1` >>
  simp[get_method_type_def,PULL_EXISTS,FORALL_PROD] >>
  rpt strip_tac >>
  gvs[translate_pred_type_scheme_def] >>
  gvs[class_map_kind_ok_def,DISJ_IMP_THM,FORALL_AND_THM] >>
  qpat_x_assum `EVERY _ methods` $ mp_tac o SRULE[EVERY_EL] >>
  rw[] >>
  first_x_assum drule >>
  rw[LAMBDA_PROD] >>
  drule pred_type_kind_ok_IMP_type_ok >>
  gvs[translate_pred_type_def] >>
  rw[PULL_EXISTS] >>
  first_x_assum drule >>
  rw[] >>
  gvs[type_ok_Functions,translate_predicates_def] >>
  rw[]
  >- (
    irule translate_predicate_type_ok >>
    gvs[tdefs_to_tcexp_tdefs_to_cl_tyid_map] >>
    first_assum $ irule_at (Pat `translate_predicate _ _`) >>
    rw[kind_ok,LLOOKUP_THM,EL_APPEND_EQN] >>
    simp[class_map_to_clk_def] >>
    irule_at (Pos hd) ALOOKUP_ALL_DISTINCT_MEM >>
    simp[EXISTS_OR_THM,RIGHT_AND_OVER_OR]
  ) >>
  metis_tac[]
QED

Theorem class_map_methods_type_ok:
  class_map_methods_translate_env cl_to_tyid cl_map = SOME meth_env ∧
  translate_ns_and_class_datatypes ns cl_map trans_ns ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  class_map_kind_ok (SND ns) cl_map ∧
  cl_to_tyid = to_cl_tyid_map (SND ns) cl_map ∧
  method_types = MAP SND meth_env ∧
  trans_tds = SND trans_ns
  ⇒
  EVERY (λ(ks,ty). type_ok trans_tds ks ty) method_types
Proof
  rw[translate_ns_and_class_datatypes_def] >>
  drule_then (drule_then irule) class_map_methods_type_ok_aux >>
  simp[] >>
  irule_at (Pos hd) EQ_REFL >>
  simp[translate_ns_def]
QED

Theorem default_impl_type_tcexp:
  namespace_ok ns ∧
  translate_ns_and_class_datatypes ns cl_map new_ns ∧
  type_elaborate_default_impl ns clk ie st env e e' cl k pt ∧
  default_impl_construct_dict ns ie_map env_vs e' de cl k pt ∧
  translate_env cl_to_tyid env = SOME trans_env ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  translate_pred_type_scheme cl_to_tyid pred_method_ty_scheme =
    SOME (method_ks,method_t) ∧
  EVERY (type_ok tds []) st ∧
  EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk tds [] scheme) env ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  DISJOINT (set $ MAP FST ie_alist) (set (MAP FST env)) ∧
  DISJOINT (set $ MAP FST ie_alist) (lambda_vars e') ∧
  (∀ent. ent ∈ ie ⇒ entailment_kind_ok tds clk ent) ∧
  cl_to_tyid = to_cl_tyid_map tds cl_map ∧
  ie_map = alist_to_fmap ie_alist ∧
  ie = FRANGE ie_map ∧ 
  tds = SND ns ∧
  clk = class_map_to_clk cl_map ∧
  env_vs = set $ MAP FST env ∧
  new_env = trans_env ++ ie_env ∧
  tcexp_de = tcexp_of de ∧
  pred_method_ty_scheme = get_method_type cl k pt ∧
  shifted_st = MAP (tshift $ LENGTH method_ks) st ∧
  shifted_env = tshift_env (LENGTH method_ks) new_env ⇒
  type_tcexp new_ns method_ks shifted_st shifted_env tcexp_de method_t
Proof
  rw[type_elaborate_default_impl_def,default_impl_construct_dict_def,
    translate_ns_and_class_datatypes_def,translate_pred_type_scheme_def] >>
  drule_then irule $ cj 1 texp_construct_dict_type_tcexp >>
  simp[] >>
  irule_at (Pos hd) EQ_REFL >>
  `∀a (b:(mlstring # type_kind_scheme) list). a ++ b = a ++ [] ++ b`
    by simp[] >>
  pop_assum $ irule_at (Pos hd) >>
  simp[translate_lie_alist_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,EVERY_MAP] >>
  first_assum $ irule_at (Pat `ALL_DISTINCT (MAP FST cl_map)`) >>
  first_assum $ irule_at (Pat `ALL_DISTINCT (MAP FST ie_alsit)`) >>
  irule_at (Pat `translate_ns _ _ = translate_ns _ _`) EQ_REFL >> 
  first_assum $ irule_at (Pat `translate_pred_type _ _ = _`) >>
  Cases_on `get_method_type cl k pt` >>
  rename1 `get_method_type cl k pt = (method_ks,method_pred_type)` >>
  gvs[] >>
  irule_at (Pat `translate_env _ _ = SOME (tshift_env _ _)`) $
    SRULE[PULL_EXISTS] $ iffRL $ translate_env_tshift_env_pred >>
  first_assum $ irule_at (Pat `translate_env _ _ = SOME _`) >>
  irule_at (Pat `_ = tshift_env _ _`) $ EQ_SYM >>
  irule_at (Pat `tshift_env _ _ = _`) tshift_env_ie_unchanged >>
  first_assum $ irule_at (Pos hd) >>
  first_assum $ irule_at (Pos hd) >>
  simp[] >>
  qexistsl [`∅`, `e'`,`e`] >>
  rw[EVERY_MAP,LAMBDA_PROD]
  >- (
    irule $ SRULE[] $ Q.INST [`db` |-> `[]`]
      EVERY_pred_type_kind_ok_shift_db_pred >>
    simp[]
  )
  >- (
    irule $ SRULE[] $ Q.INST [`db` |-> `[]`]
      EVERY_type_ok_tshift >>
    simp[]
  )
QED

Triviality ALL_DISTINCT_method_names_EL_LT_IMP_class_EQ:
  ALL_DISTINCT (method_names cl_map) ∧
  i < j ∧ j < LENGTH cl_map ∧
  EL i cl_map = (clname,cl) ∧
  EL j cl_map = (clname',cl') ∧
  ALOOKUP cl.methods meth = SOME pt ∧
  ALOOKUP cl'.methods meth = SOME pt' ⇒
  clname = clname'
Proof
  rw[] >>
  spose_not_then assume_tac >>
  gvs[ALL_DISTINCT_FLAT,method_names_thm,EL_MAP,MEM_MAP,PULL_EXISTS] >>
  first_x_assum $ drule_then drule >>
  simp[] >>
  imp_res_tac ALOOKUP_MEM >>
  first_assum $ irule_at Any >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem ALL_DISTINCT_method_names_MEM_IMP_class_EQ:
  ALL_DISTINCT (method_names cl_map) ∧
  MEM (clname,cl) cl_map ∧ MEM (clname',cl') cl_map ∧
  ALOOKUP cl.methods meth = SOME pt ∧
  ALOOKUP cl'.methods meth = SOME pt' ⇒
  clname = clname'
Proof
  rw[MEM_EL] >>
  rpt (qpat_x_assum `(_,_) = EL _ _` $ assume_tac o GSYM) >>
  Cases_on `n < n'`
  >- drule_all_then irule ALL_DISTINCT_method_names_EL_LT_IMP_class_EQ >>
  Cases_on `n' < n`
  >- (drule_all ALL_DISTINCT_method_names_EL_LT_IMP_class_EQ >> simp[]) >>
  `n = n'` by fs[] >>
  gvs[]
QED

Theorem ALL_DISTINCT_method_names_ALOOKUP_IMP_class_EQ:
  ALL_DISTINCT (method_names cl_map) ∧
  ALOOKUP cl_map clname = SOME cl ∧
  ALOOKUP cl_map clname' = SOME cl' ∧
  ALOOKUP cl.methods meth = SOME pt ∧
  ALOOKUP cl'.methods meth = SOME pt' ⇒
  clname = clname'
Proof
  rw[] >>
  imp_res_tac ALOOKUP_MEM >>
  drule_all_then irule ALL_DISTINCT_method_names_MEM_IMP_class_EQ
QED

Theorem default_impls_type_tcexp:
  namespace_ok ns ∧
  translate_ns_and_class_datatypes ns cl_map new_ns ∧
  type_elaborate_default_impls cl_map ns ie st env defaults defaults'
    default_meth_pred_tys ∧
  default_impls_construct_dict ns cl_map ie_map env_vs defaults' trans_defaults ∧
  translate_env cl_to_tyid env = SOME trans_env ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  OPT_MMAP (translate_pred_type_scheme cl_to_tyid) default_meth_pred_tys =
    SOME default_meth_tys ∧
  EVERY (type_ok tds []) st ∧
  EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk tds [] scheme) env ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  ALL_DISTINCT (method_names cl_map) ∧
  DISJOINT (set $ MAP FST ie_alist) (set (MAP FST env)) ∧
  DISJOINT (set $ MAP FST ie_alist) (lambda_varsl $ MAP (SND ∘ SND) defaults') ∧
  (∀ent. ent ∈ ie ⇒ entailment_kind_ok tds clk ent) ∧
  cl_to_tyid = to_cl_tyid_map tds cl_map ∧
  ie_map = alist_to_fmap ie_alist ∧
  ie = FRANGE ie_map ∧ 
  tds = SND ns ∧
  clk = class_map_to_clk cl_map ∧
  env_vs = set $ MAP FST env ∧
  new_env = trans_env ++ ie_env ∧
  typed = (λ(fname,func) (ks,ty).
      type_tcexp new_ns ks (MAP (tshift (LENGTH ks)) st)
      (tshift_env (LENGTH ks) new_env) (tcexp_of func) ty)
  ⇒
  LIST_REL typed trans_defaults default_meth_tys
Proof
  rw[type_elaborate_default_impls_def,default_impls_construct_dict_def,
    OPT_MMAP_SOME_LIST_REL] >>
  gvs[LIST_REL_EL_EQN,LIST_REL3_EL] >>
  rw[] >>
  ntac 2 (pairarg_tac >> simp[]) >>
  irule default_impl_type_tcexp >>
  irule_at (Pat `tcexp_of _ = tcexp_of _`) EQ_REFL >>
  irule_at (Pat `MAP (tshift _) st = _`) EQ_REFL >>
  simp[] >>
  first_assum $ irule_at (Pat `namespace_ok _`) >>
  first_assum $ irule_at (Pat `translate_env _ _ = SOME _`) >>
  first_assum $ irule_at (Pat `translate_ie_alist _ _ = SOME _`) >>
  simp[] >>
  first_x_assum drule >>
  first_x_assum drule >>
  first_x_assum drule >>
  ntac 2 (pairarg_tac >> simp[]) >>
  rw[] >>
  gvs[] >>
  first_assum $ irule_at (Pat `translate_pred_type_scheme _ _ = SOME _`) >>
  `clname = clname'`
  by (
    drule_then irule ALL_DISTINCT_method_names_ALOOKUP_IMP_class_EQ >>
    simp[] >>
    metis_tac[]
  ) >>
  gvs[] >>
  first_assum $ irule_at (Pat `type_elaborate_default_impl _ _ _ _ _ _ _ _ _ _ `) >>
  simp[] >>
  drule DISJOINT_lambda_varsl_IMP >>
  simp[LENGTH_MAP,EL_MAP] >>
  disch_then drule >>
  simp[]
QED

Theorem class_map_to_env_CONS:
  class_map_to_env (h::cl_map) =
  MAP (I ## get_method_type (FST h) (SND h).kind) (SND h).methods ++ class_map_to_env cl_map
Proof
  simp[class_map_to_env_def] >>
  pairarg_tac >>
  gvs[]
QED

Theorem MEM_methods_MEM_class_map_to_env:
  ∀cl_map clname cl meth_name pt.
  MEM (clname,cl) cl_map ∧
  MEM (meth_name,pt) cl.methods⇒
  MEM (meth_name,get_method_type clname cl.kind pt) (class_map_to_env cl_map)
Proof
  Induct_on `cl_map` >>
  rw[]
  >- (
    PairCases_on `pt` >>
    gvs[MEM_MAP,EXISTS_PROD,class_map_to_env_def] >>
    metis_tac[]
  ) >>
  rw[class_map_to_env_CONS]
QED

Theorem default_method_pred_types_MEM_class_map_methods_types:
  type_elaborate_default_impls cl_map ns ie st env defaults defaults'
    default_meth_pred_tys ∧
  OPT_MMAP (translate_pred_type_scheme cl_to_tyid) default_meth_pred_tys =
    SOME default_meth_tys ∧
  class_map_methods_translate_env cl_to_tyid cl_map = SOME meth_env ∧
  method_types = MAP SND meth_env ∧
  MEM t default_meth_tys ⇒
  MEM t method_types
Proof
  rw[type_elaborate_default_impls_def,OPT_MMAP_SOME_LIST_REL,
    class_map_methods_translate_env_def,translate_env_OPT_MMAP] >>
  gvs[LIST_REL_EL_EQN,LIST_REL3_EL,MEM_MAP] >>
  drule_then strip_assume_tac $ iffLR MEM_EL >>
  last_x_assum drule >>
  ntac 2 (pairarg_tac >> simp[]) >>
  rw[] >>
  imp_res_tac ALOOKUP_MEM >>
  drule_all MEM_methods_MEM_class_map_to_env >>
  rw[MEM_EL] >>
  first_x_assum drule >>
  qpat_x_assum `(_,_) = EL _ _` $ assume_tac o GSYM >>
  gvs[] >>
  first_x_assum drule >>
  rw[PULL_EXISTS] >>
  first_assum $ irule_at (Pat `_ < LENGTH meth_env`) >>
  simp[]
QED

Triviality SmartLam_EQ_LENGHT_LT_IMP:
  SmartLam () vs e = SmartLam () vs' e' ∧
  LENGTH vs < LENGTH vs' ⇒
  ∃us. vs' = vs ++ us ∧
    e = SmartLam () us e'
Proof
  simp[SmartLam_def] >>
  IF_CASES_TAC >>
  IF_CASES_TAC >>
  gvs[NULL_EQ] >>
  every_case_tac >>
  gvs[]
  >- (
    rw[] >>
    rw[] >>
    Cases_on `e` >>
    gvs[dest_Lam_def]
  )
  >- (
    rw[] >>
    rw[] >>
    Cases_on `e'` >>
    gvs[dest_Lam_def] >>
    Cases_on `e` >>
    gvs[dest_Lam_def]
  ) >>
  rw[] >>
  Cases_on `e` >>
  gvs[dest_Lam_def] >>
  Cases_on `e'` >>
  gvs[dest_Lam_def] >>
  gvs[APPEND_EQ_APPEND] >>
  irule_at (Pos hd) $ METIS_PROVE[] ``a = b ⇒ a = b ∨ b = (a:mlstring list)`` >>
  simp[] >>
  IF_CASES_TAC >>
  gvs[]
QED

Triviality NOT_EMPTY_IMP_LENGTH_SUC:
  l ≠ [] ⇒ ∃n. LENGTH l = SUC n
Proof
  Cases_on `l` >>
  simp[]
QED

Triviality SmartLam_EQ_LENGTH_EQ_IMP:
  SmartLam () vs e = SmartLam () vs' e' ∧
  LENGTH vs = LENGTH vs' ⇒
  vs = vs' ∧ e = e'
Proof
  simp[SmartLam_def] >>
  IF_CASES_TAC >>
  IF_CASES_TAC >>
  gvs[NULL_EQ] >>
  gvs[oneline dest_Lam_def] >>
  Cases_on `e` >>
  Cases_on `e'` >>
  gvs[] >>
  IF_CASES_TAC >>
  gvs[LENGTH_APPEND] >>
  rw[] >>
  drule_then strip_assume_tac NOT_EMPTY_IMP_LENGTH_SUC >>
  gvs[APPEND_EQ_APPEND] >>
  Cases_on `l''` >>
  gvs[]
QED

Theorem SmartLam_EQ_IMP:
  SmartLam () vs e = SmartLam () vs' e' ∧
  LENGTH vs ≤ LENGTH vs' ⇒
  ∃us. vs' = vs ++ us ∧
    e = SmartLam () us e'
Proof
  Cases_on `LENGTH vs < LENGTH vs'` >>
  rw[]
  >- drule_all_then irule SmartLam_EQ_LENGHT_LT_IMP >>
  `LENGTH vs = LENGTH vs'` by fs[] >>
  qexists_tac `[]` >>
  simp[] >>
  drule_all SmartLam_EQ_LENGTH_EQ_IMP >>
  simp[SmartLam_def]
QED

Theorem translate_pred_type_subst_db_pred:
  translate_pred_type cl_to_tyid pt = SOME trans_pt ⇒
  translate_pred_type cl_to_tyid (subst_db_pred len ts pt) =
    SOME (subst_db len ts trans_pt)
Proof
  Cases_on `pt` >>
  simp[translate_pred_type_def,subst_db_pred_def] >>
  rw[] >>
  drule translate_predicates_IMP_translate_predicates_subst_db >>
  rw[subst_db_Functions]
QED

Triviality type_size_Functions:
  type_size (Functions [] x) = type_size x ∧
  type_size (Functions (arg::args) x) = type_size arg + type_size
  (Functions args x) + 3 + atom_ty_size (CompPrimTy Function)
Proof
  rw[Functions_def,type_size_def]
QED

Triviality self_EQ_Functions_self:
  x = Functions args x ⇒ args = []
Proof
  `args ≠ [] ⇒ type_size x < type_size (Functions args x)`
  by (
    Induct_on `args` >>
    simp[type_size_Functions] >>
    rw[] >>
    Cases_on `args`
    >- simp[Functions_def] >>
    gvs[]
  ) >>
  Cases_on `args` >>
  gvs[] >>
  spose_not_then assume_tac >>
  `type_size x = type_size (Functions (h::t) x)`
    by (AP_TERM_TAC >> simp[]) >>
  gvs[]
QED

Theorem Functions_arg_EQ_IMP:
  Functions args ret = Functions args ret' ⇔
  ret = ret'
Proof
  rw[EQ_IMP_THM] >>
  drule Functions_eq_imp >>
  rw[] >>
  simp[Functions_def]
QED

Theorem Functions_return_EQ_IMP:
  Functions args ret = Functions args' ret ⇔
  args = args'
Proof
  rw[EQ_IMP_THM] >>
  drule Functions_eq_imp >>
  rw[] >>
  drule self_EQ_Functions_self >>
  gvs[]
QED

Theorem impl_type_tcexp:
  namespace_ok ns ∧
  translate_ns_and_class_datatypes ns cl_map new_ns ∧
  type_elaborate_impl ns clk ie st env varks ctxt inst_t meth_ks pt e e' ∧
  impl_construct_dict ns ie_map env_vs varks ctxt inst_t vs meth_ks pt e' de ∧
  translate_pred_type cl_to_tyid pt = SOME trans_pt ∧
  translate_predicates cl_to_tyid ctxt = SOME arg_tys ∧
  translate_env cl_to_tyid env = SOME trans_env ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  entailment_kind_ok tds clk (Entailment varks ctxt (cl,inst_t)) ∧
  LENGTH vs = LENGTH ctxt ∧
  EVERY (type_ok tds []) st ∧
  EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk tds [] scheme) env ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  DISJOINT (set $ MAP FST ie_alist) (set (MAP FST env)) ∧
  DISJOINT (set $ MAP FST ie_alist) (lambda_vars e') ∧
  (∀ent. ent ∈ ie ⇒ entailment_kind_ok tds clk ent) ∧

  (* subst_pt = subst_db_pred (LENGTH meth_ks) [inst_t] pt ∧ *)
  t = subst_db (LENGTH meth_ks) [tshift (LENGTH meth_ks) inst_t] trans_pt ∧
  cl_to_tyid = to_cl_tyid_map tds cl_map ∧
  tds = SND ns ∧
  clk = class_map_to_clk cl_map ∧
  ie_map = alist_to_fmap ie_alist ∧
  ie = FRANGE ie_map ∧
  env_vs = set $ MAP FST env ∧
  ks = meth_ks ++ varks ∧
  shifted_st = MAP (tshift $ LENGTH meth_ks + LENGTH varks) st ∧
  shifted_env = tshift_env (LENGTH meth_ks + LENGTH varks) (trans_env ++ ie_env) ∧
  new_env = REVERSE (ZIP
    (vs,MAP ($, [] ∘ tshift (LENGTH meth_ks)) arg_tys)) ++
    shifted_env ∧
  tcexp_de = tcexp_of de
  ⇒
  type_tcexp new_ns ks shifted_st new_env tcexp_de t
Proof
  Cases_on `pt` >>
  rw[type_elaborate_impl_def,impl_construct_dict_def,subst_db_pred_def,
    impl_construct_dict_instantiated_def,
    translate_ns_and_class_datatypes_def,
    cj 1 type_elaborate_texp_cases,cj 1 texp_construct_dict_cases] >>
  drule_then (qspecl_then
      [`[tshift (LENGTH meth_ks) inst_t]`,`LENGTH meth_ks`] $
      assume_tac o SRULE[subst_db_pred_def])
    translate_pred_type_subst_db_pred >>
  drule SmartLam_EQ_IMP >>
  rw[] >>
  `LENGTH ctxt = LENGTH arg_tys`
    by (gvs[translate_predicates_LIST_REL,LIST_REL_EL_EQN]) >>
  gvs[LENGTH_APPEND,translate_pred_type_def,subst_db_Functions] >>
  irule type_tcexp_SmartLam >>
  gvs[] >>
  conj_asm1_tac
  >- (gvs[translate_predicates_LIST_REL,LIST_REL_EL_EQN]) >>
  gvs[Functions_return_EQ_IMP] >>
  rw[EVERY_MEM]
  >- (
    simp[translate_ns_def] >>
    drule_then (drule_at_then (Pos last) irule) translate_predicates_type_ok_relax >>
    simp[tdefs_to_tcexp_tdefs_to_cl_tyid_map] >>
    first_assum $ irule_at (Pat `translate_predicates _ _ = _`) >>
    simp[EVERY_MAP,LAMBDA_PROD] >>
    rw[EVERY_MEM] >>
    gvs[pred_type_kind_ok_alt,MEM_MAP,PULL_EXISTS] >>
    last_x_assum drule >>
    pairarg_tac >>
    rw[] >>
    simp[] >>
    irule kind_ok_tdefs_APPEND >>
    simp[kind_ok_tdefs_to_tcexp_tdefs]
  ) >>
  qmatch_asmsub_abbrev_tac `translate_predicates _ (MAP _ _) =
    SOME subst_args` >>
  qmatch_goalsub_abbrev_tac `type_tcexp _ _ _ _ _ subst_t` >>
  `type_tcexp (translate_ns ns cl_ns) (meth_ks ++ varks)
      (MAP (tshift (LENGTH meth_ks + LENGTH varks)) st)
      (tshift_env (LENGTH meth_ks + LENGTH varks) trans_env ++
        (REVERSE (ZIP (us,MAP ($, []) subst_args)) ++
         REVERSE (ZIP (vs,MAP ($, [] ∘ tshift (LENGTH meth_ks)) arg_tys))) ++
        tshift_env (LENGTH meth_ks + LENGTH varks) ie_env)
      (tcexp_of de') subst_t`
  suffices_by (
    strip_tac >>
    drule_then irule type_tcexp_env_extensional >>
    rpt strip_tac >>
    irule ALOOKUP_APPEND_EQ >>
    irule DISJOINT_ALOOKUP_APPEND >>
    gvs[GSYM DISJOINT_DEF,translate_predicates_OPT_MMAP,
      OPT_MMAP_SOME_LIST_REL] >>
    simp[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_3] >>
    DEP_REWRITE_TAC[cj 1 MAP_ZIP] >>
    rw[]
    >- gvs[LIST_REL_EL_EQN] >>
    drule_then irule DISJOINT_trans_env >>
    drule_then irule $ iffLR DISJOINT_SYM
  ) >>
  irule $ cj 2 texp_construct_dict_type_tcexp >>
  irule_at (Pat `tcexp_of _ = _`) EQ_REFL >>
  irule_at (Pat `_ ++ _ ++ _ = _ ++ _ ++ _`) EQ_REFL >>
  first_assum $ irule_at (Pat `texp_construct_dict _ _ _ _ _ _ _`) >>
  first_assum $ irule_at (Pat `type_elaborate_texp _ _ _ _ _ _ _ _ _ _`) >>
  simp[translate_env_tshift_env_pred,PULL_EXISTS] >>
  first_assum $ irule_at (Pat `translate_env _ _ = _`) >>
  irule_at (Pat `translate_ie_alist _ _ = _`) EQ_TRANS >>
  first_assum $ irule_at (Pat `translate_ie_alist _ _ = _`) >>
  simp[] >>
  irule_at (Pat `_ = tshift_env _ _`) EQ_SYM >>
  drule_then (drule_then $ irule_at (Pat `tshift_env _ _ = _`))
    tshift_env_ie_unchanged >>
  simp[FUPDATE_LIST_EQ_alist_to_fmap_REVERSE] >>
  irule_at (Pat `alist_to_fmap _ = alist_to_fmap _`) $ EQ_REFL >>
  conj_tac
  >- (
    simp[PFORALL_THM,ELIM_UNCURRY] >>
    ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
    simp[FORALL_PROD,MAP_REVERSE,MAP_ZIP] >>
    rw[MEM_MAP,EXISTS_PROD,PAIR_MAP_THM]
    >- (
      gvs[entailment_kind_ok_def,EVERY_MEM] >>
      first_x_assum drule >>
      rw[] >>
      simp[] >>
      drule_then irule kind_ok_shift_db_APPEND >>
      simp[]
    ) >>
    gvs[pred_type_kind_ok_alt,MEM_MAP,PULL_EXISTS,PAIR_MAP_THM] >>
    first_x_assum drule >>
    rw[]
  ) >>
  gvs[REVERSE_ZIP,REVERSE_APPEND,MAP_ZIP,translate_lie_alist_ZIP_SOME,
    translate_lie_alist_SOME_APPEND,translate_lie_alist_SOME_REVERSE,
    GSYM ZIP_APPEND,MAP_REVERSE,GSYM DISJOINT_DEF,APPEND_11_LENGTH,
    ALL_DISTINCT_APPEND_DISJOINT] >>
  gvs[DISJOINT_SYM,MEM_MAP,EXISTS_PROD] >>
  gvs[EVERY2_MAP,translate_predicates_LIST_REL] >>
  conj_tac
  >- (
    conj_asm1_tac
    >- (
      rw[] >>
      drule_all LIST_REL_MEM_IMP >>
      rw[] >> simp[]
    ) >>
    rw[Abbr`subst_args`] >>
    AP_TERM_TAC >>
    rw[LIST_EQ_REWRITE,EL_MAP] >>
    fs[LIST_REL_EL_EQN] >>
    first_x_assum drule >>
    rw[PAIR_MAP,ELIM_UNCURRY] >>
    gvs[libTheory.the_def,shift_db_def,EL_MAP]
  ) >>
  gvs[LAMBDA_PROD,EVERY_MAP] >>
  drule_then (qspec_then `meth_ks ++ varks` mp_tac) EVERY_type_ok_tshift >>
  simp[] >>
  disch_then kall_tac >>
  drule_then (qspec_then `meth_ks ++ varks` mp_tac) $ SRULE[LAMBDA_PROD] $
    Q.INST[`db` |-> `[]`] $ EVERY_pred_type_kind_ok_shift_db_pred >>
  simp[]
QED

Theorem translate_predicate_tcons_to_type:
  translate_predicate cl_to_tyid (cl,ty) = SOME t' ⇒
  ∃pid. FLOOKUP cl_to_tyid cl = SOME pid ∧
    t' = tcons_to_type (INL pid) [ty]
Proof
  rw[translate_predicate_def] >>
  simp[tcons_to_type_def,cons_types_def]
QED

Theorem MEM_FRANGE_alist_to_fmap:
  ALL_DISTINCT (MAP FST l) ∧
  MEM x l ∧ y = SND x ⇒
  y ∈ FRANGE (alist_to_fmap l)
Proof
  Cases_on `x` >>
  rw[finite_mapTheory.IN_FRANGE_FLOOKUP] >>
  drule_all_then assume_tac ALOOKUP_ALL_DISTINCT_MEM >>
  first_assum $ irule_at Any
QED

Theorem translate_superclasses_translate_predicates:
  ∀sup_tys. 
  translate_superclasses cl_to_tyid supers = SOME sup_tys ⇒
  ∃trans_pred_tys.
    translate_predicates cl_to_tyid (MAP (λsuper. (super,t)) supers) =
      SOME trans_pred_tys ∧
    MAP (λ(ks,scheme).
      (ks,subst_db (LENGTH ks) [tshift (LENGTH ks) t] scheme))
      sup_tys =
    MAP ($, []) trans_pred_tys
Proof
  Induct_on `supers` >>
  rw[translate_superclasses_def] >>
  simp[PULL_EXISTS,subst_db_def,translate_predicates_def,
    translate_predicate_def]
QED

Theorem translate_lie_alist_ZIP_translate_predicates:
  ∀ctxt vs pts r.
  translate_predicates cl_to_tyid ctxt = SOME pts ∧
  LENGTH vs = LENGTH ctxt ⇒
  (translate_lie_alist cl_to_tyid (ZIP (vs,ctxt)) = SOME r ⇔
    r = ZIP (vs:mlstring list,MAP ($, ([]:Kind list)) pts))
Proof
  Induct >>
  simp[translate_lie_alist_def,translate_predicates_def] >>
  rw[] >>
  Cases_on `vs` >>
  fs[] >> PairCases_on `h` >>
  gvs[translate_lie_alist_def,translate_predicate_def] >>
  first_x_assum drule >>
  rw[] >>
  gvs[EQ_IMP_THM,PULL_EXISTS] >>
  qrefine `_::r` >>
  simp[]
QED

Theorem tshift_env_twice:
  tshift_env a (tshift_env b env) = tshift_env (a + b) env
Proof
  rw[LIST_EQ_REWRITE,EL_MAP] >>
  Cases_on `EL x env` >>
  Cases_on `r` >>
  rw[shift_db_twice]
QED

Theorem ALOOKUP_SOME_DISJOINT_ALOOKUP:
  ALOOKUP xs x = SOME y ∧
  DISJOINT (set $ MAP FST xs) (set $ MAP FST zs) ⇒
  ALOOKUP (zs ++ xs) x = SOME y
Proof
  rw[ALOOKUP_APPEND] >>
  CASE_TAC >>
  spose_not_then kall_tac >>
  drule $ iffLR DISJOINT_NOT_IN_R >>
  imp_res_tac ALOOKUP_MEM >>
  rw[MEM_MAP,PULL_EXISTS] >>
  first_assum $ irule_at (Pos hd) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem translate_ie_alist_MAP_FST:
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ⇒
  MAP FST ie_env = MAP FST ie_alist
Proof
  simp[translate_ie_alist_OPT_MMAP,OPT_MMAP_SOME_LIST_REL] >>
  rw[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP] >>
  gvs[] >>
  first_assum drule >>
  Cases_on `EL x ie_alist` >>
  rw[] >> simp[]
QED

Theorem translate_pred_type_scheme_get_method_type:
  translate_pred_type_scheme cl_to_tyid (get_method_type c k (ks,pt))
    = SOME t
  ⇔
  ∃t' class_t.
    translate_pred_type cl_to_tyid pt = SOME t' ∧
    translate_predicate cl_to_tyid (c,TypeVar (LENGTH ks)) =
      SOME class_t ∧
    t = (SNOC k ks,Functions [class_t] t')
Proof
  Cases_on `pt` >>
  simp[get_method_type_def,translate_pred_type_scheme_def,
    translate_pred_type_def,PULL_EXISTS,translate_predicates_def] >>
  rw[EQ_IMP_THM] >>
  simp[GSYM Functions_CONS_alt]
QED

(* relating default implemenations and the translated env *)
Definition defaults_env_rel_def:
  defaults_env_rel cl_to_tyid cl_map
    (defaults :Kind list default_trans_impls)
    (env :(mlstring # type_kind_scheme) list) ⇔
  (∀c cl name pred_type_scheme t default_name default_impl.
    ALOOKUP cl_map c = SOME cl ∧
    MEM (name,pred_type_scheme) cl.methods ∧
    translate_pred_type_scheme cl_to_tyid
      (get_method_type c cl.kind pred_type_scheme) = SOME t ∧
    ALOOKUP defaults name = SOME (default_name,default_impl) ⇒
    ALOOKUP env default_name = SOME t)
End

Theorem ALL_DISTINCT_method_names_IMP_ALL_DISTINCT_methods:
  ALL_DISTINCT (method_names cl_map) ∧
  MEM (c,cl) cl_map ⇒
  ALL_DISTINCT (MAP FST cl.methods)
Proof
  rw[ALL_DISTINCT_FLAT,method_names_thm,MEM_MAP,PULL_EXISTS] >>
  first_x_assum drule >>
  simp[]
QED

Theorem instance_type_tcexp:
  type_elaborate_instance ns cl_map ie st env inst inst' ∧
  instance_construct_dict ns cl_map ie_map env_vs defaults
    inst' trans_inst ∧
  ALOOKUP ie_env inst'.dict_name = SOME (ks,inst_ty) ∧
  defaults_env_rel cl_to_tyid cl_map defaults trans_env ∧
  translate_entailment cl_to_tyid (instance_to_entailment inst') =
    SOME (ks,inst_ty) ∧
  translate_env cl_to_tyid env = SOME trans_env ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  namespace_ok ns ∧
  translate_ns_and_class_datatypes ns cl_map new_ns ∧
  EVERY (type_ok tds []) st ∧
  EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk tds [] scheme) env ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  DISJOINT (set $ MAP FST ie_alist) (set (MAP FST env)) ∧
  DISJOINT (set $ MAP FST ie_alist)
    (lambda_varsl (MAP SND inst'.impls)) ∧
  (∀ent. ent ∈ ie ⇒ entailment_kind_ok tds clk ent) ∧
  instance_kind_ok tds clk inst' ∧
  class_map_kind_ok tds cl_map ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  ALL_DISTINCT (method_names cl_map) ∧

  cl_to_tyid = to_cl_tyid_map tds cl_map ∧
  tds = SND ns ∧
  clk = class_map_to_clk cl_map ∧
  ie_map = alist_to_fmap ie_alist ∧
  ie = FRANGE ie_map ∧
  env_vs = set (MAP FST env) ∧
  shifted_st = MAP (tshift $ LENGTH ks) st ∧
  new_env = tshift_env (LENGTH ks) $ trans_env ++ ie_env ∧
  tcexp_inst = tcexp_of (SND trans_inst)
  ⇒
  type_tcexp new_ns ks shifted_st new_env tcexp_inst inst_ty
Proof
  PairCases_on `trans_inst` >>
  rw[type_elaborate_instance_def,instance_construct_dict_def,
    type_elaborate_impls_def,instance_to_entailment_def,
    instance_kind_ok_def,translate_entailment_def] >>
  irule type_tcexp_SmartLam >>
  simp[tcexp_of_def] >>
  conj_asm1_tac
  >- gvs[translate_predicates_LIST_REL,LIST_REL_EL_EQN] >>
  conj_asm1_tac
  >- (
    gvs[translate_ns_def,translate_ns_and_class_datatypes_def] >>
    rw[EVERY_MEM] >>
    drule_then irule translate_predicates_type_ok_relax >>
    simp[tdefs_to_tcexp_tdefs_to_cl_tyid_map] >>
    first_assum $ irule_at (Pat `translate_predicates _ _ = _`) >>
    gvs[entailment_kind_ok_def,EVERY_MEM] >>
    rw[] >>
    first_x_assum drule >>
    pairarg_tac >> rw[] >>
    metis_tac[kind_ok_tdefs_to_tcexp_tdefs,kind_ok_tdefs_APPEND]
  ) >>
  drule translate_predicate_tcons_to_type >>
  rw[] >>
  irule type_tcexp_Cons >>
  simp[tcexp_type_cons_def,PULL_EXISTS] >>
  drule $ cj 1 $ SRULE[] $ iffLR entailment_kind_ok_def >>
  rw[class_map_to_clk_def] >>
  (drule_then $ drule_then drule) FLOOKUP_to_cl_tyid_map_IMP >>
  rw[class_to_datatype_def] >>
  simp[] >>
  reverse conj_tac
  >- (
    gvs[translate_ns_def,translate_ns_and_class_datatypes_def] >>
    irule kind_ok_tdefs_APPEND >>
    simp[kind_ok_tdefs_to_tcexp_tdefs]
  ) >>
  irule $ cj 1 $ iffLR LIST_REL_APPEND >>
  rw[]
  >- ( (* super classes *)
    drule_then (qspec_then `inst'.type` strip_assume_tac)
      translate_superclasses_translate_predicates >>
    simp[] >>
    (drule_at_then (Pat `translate_ie_alist _ _ = _`) $
      drule_at (Pat `construct_dicts _ _ _ _ _ _`)) $
      cj 2 construct_dict_type_tcexp >>
    simp[FUPDATE_LIST_EQ_alist_to_fmap_REVERSE] >>
    disch_then $ resolve_then (Pat `alist_to_fmap _ = alist_to_fmap _`)
      mp_tac EQ_REFL >>
    simp[translate_lie_alist_SOME_REVERSE,MAP_REVERSE,MAP_ZIP] >>
    rev_drule_then drule $
      translate_lie_alist_ZIP_translate_predicates >>
    rw[PULL_EXISTS] >>
    pop_assum $ qspecl_then [
      `MAP (tshift $ LENGTH inst'.kinds) st`,
      `FST ns`,
      `tshift_env (LENGTH inst'.kinds) trans_env`] mp_tac >>
    drule $ iffLR translate_ns_and_class_datatypes_def >>
    rw[] >>
    rename1 `class_map_to_ns _ _ = SOME cl_ns` >>
    pop_assum $ qspec_then `cl_ns` mp_tac >>
    impl_tac
    >- (
      simp[ALL_DISTINCT_APPEND_DISJOINT,MAP_MAP_o,combinTheory.o_DEF,
        LAMBDA_PROD,FST_3] >>
      fs[FDOM_alist_to_fmap] >>
      drule_then (irule_at Any) DISJOINT_trans_env >>
      drule_then (irule_at Any) DISJOINT_trans_env >>
      simp[] >>
      rw[] >>
      drule_then drule MEM_FRANGE_alist_to_fmap >>
      rw[] >>
      first_x_assum drule >>
      rw[entailment_kind_ok_def,class_map_to_clk_def,
        FLOOKUP_to_cl_tyid_map] >>
      metis_tac[ALOOKUP_find_index_SOME]
    ) >>
    rw[SRULE[] $ GSYM translate_ns_def] >>
    simp[EVERY2_MAP] >>
    drule_at_then (Pos last) irule LIST_REL_mono >>
    (drule_then $ drule_then drule) tshift_env_ie_unchanged >>
    simp[] >>
    disch_then kall_tac >>
    simp[ELIM_UNCURRY] >>
    rw[LAMBDA_PROD] >>
    drule_then irule type_tcexp_env_extensional >>
    rw[] >>
    irule ALOOKUP_APPEND_EQ >>
    irule DISJOINT_ALOOKUP_APPEND >>
    simp[MAP_REVERSE,MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
      FST_3] >>
    irule $ iffLR DISJOINT_SYM >>
    drule_then (drule_then irule) DISJOINT_trans_env
  ) >>
  gvs[OPT_MMAP_SOME_LIST_REL,EVERY2_MAP,
    translate_pred_type_scheme_def] >>
  gvs[LIST_REL_EL_EQN] >>
  rw[] >>
  first_x_assum drule >>
  first_x_assum drule >>
  pairarg_tac >> simp[] >>
  rw[] >>
  qpat_x_assum `(_,_) = EL _ method_tys` $ assume_tac o GSYM >>
  simp[tshift_env_twice,MAP_MAP_o,combinTheory.o_DEF,shift_db_twice] >>
  qpat_x_assum `option_CASE (ALOOKUP inst'.impls _) _ _` mp_tac >>
  TOP_CASE_TAC
  >- ( (* default implementation *)
    rw[] >>
    simp[tcexp_of_def] >>
    irule type_tcexp_App >>
    qrefine `[_]` >>
    simp[] >>
    irule_at Any type_tcexp_SmartApp_Var >>
    irule_at (Pos hd) type_tcexp_Var >>
    gvs[translate_ns_and_class_datatypes_def] >>
    (drule_then $ drule_then drule) tshift_env_ie_unchanged >>
    simp[] >> disch_then assume_tac >>
    irule_at (Pos hd) ALOOKUP_SOME_DISJOINT_ALOOKUP >>
    drule_then assume_tac translate_ie_alist_MAP_FST >>
    simp[MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,MAP_REVERSE,FST_3,
      MAP_ZIP,EXISTS_PROD] >>
    irule_at Any $ iffLR DISJOINT_SYM >>
    (drule_then $ irule_at Any) DISJOINT_trans_env >>
    irule_at Any specialises_tshift >>
    simp[freetyvars_ok_Functions,shift_db_Functions,
      shift_db_tcons_to_type] >>
    irule_at (Pat `Functions _ _ = Functions _ _`) EQ_REFL >>
    conj_tac
    >- (
      irule $ INST_TYPE [``:'a`` |->
        ``:(mlstring # (type_kind_scheme list)) list``]
        kind_ok_IMP_freetyvars_ok >>
      simp[kind_ok_cons_types,tcons_to_type_def,PULL_EXISTS,kind_ok] >>
      first_assum $ irule_at (Pat `LLOOKUP _ _ = _`) >>
      gvs[entailment_kind_ok_def] >>
      irule_at (Pat `kind_arrows _ _ = _`) EQ_REFL >>
      simp[translate_ns_def] >>
      irule kind_ok_tdefs_APPEND >>
      simp[kind_ok_tdefs_to_tcexp_tdefs]
    ) >>
    conj_tac
    >- (
      rw[] >>
      gvs[EVERY_MEM] >>
      first_x_assum $ drule_then assume_tac >>
      drule_then irule type_ok_IMP_freetyvars_ok
    ) >>
    conj_tac
    >- (
      simp[EVERY2_MAP,tcexp_of_def] >>
      rw[LIST_REL_EL_EQN] >>
      irule type_tcexp_Var >>
      simp[ALOOKUP_APPEND] >>
      DEP_REWRITE_TAC[alookup_distinct_reverse] >>
      conj_tac
      >- simp[MAP_MAP_o,combinTheory.o_DEF,FST_3,LAMBDA_PROD,MAP_ZIP] >>
      CASE_TAC
      >- (
        spose_not_then kall_tac >>
        pop_assum mp_tac >>
        simp[ALOOKUP_NONE,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
          FST_3,MAP_ZIP] >>
        metis_tac[MEM_EL]
      ) >>
      drule_then strip_assume_tac ALOOKUP_find_index_SOME >>
      gvs[EL_MAP,MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
        FST_3,EL_ZIP] >>
      simp[specialises_REFL]
    ) >>
    irule type_tcexp_Var >>
    irule_at (Pos hd) $ cj 1 ALOOKUP_prefix >>
    irule_at (Pos hd) ALOOKUP_SOME_DISJOINT_ALOOKUP >>
    simp[MAP_REVERSE,MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
      EXISTS_PROD,FST_3] >>
    irule_at Any $ iffLR DISJOINT_SYM >>
    drule_all_then (irule_at Any) DISJOINT_trans_env >>
    (drule_then $ drule_then $ drule_at (Pat `ALOOKUP _ _ = _`)) $
      iffLR defaults_env_rel_def >>
    qmatch_asmsub_abbrev_tac `EL n cl.methods = (name,pred_ty_scheme)` >>
    disch_then $ qspec_then `pred_ty_scheme` mp_tac >>
    rw[MEM_EL,PULL_EXISTS] >>
    first_x_assum drule >>
    simp[Abbr`pred_ty_scheme`,PULL_EXISTS,
      translate_pred_type_scheme_get_method_type] >>
    rw[translate_predicate_def] >>
    simp[ELIM_UNCURRY,SRULE[ELIM_UNCURRY] ALOOKUP_MAP_2] >>
    simp[tcons_to_type_def,cons_types_def] >>
    simp[specialises_def] >>
    qexists `GENLIST TypeVar (LENGTH meth_ks) ++
      [tshift (LENGTH meth_ks) inst'.type]` >>
    simp[LIST_REL_EL_EQN,EL_GENLIST,kind_ok,Functions_arg_EQ_IMP,
      LLOOKUP_THM,EL_APPEND_EQN,shift_db_Functions,subst_db_Functions,
      shift_db_def,subst_db_def] >>
    conj_tac
    >- (
      irule kind_ok_shift_db_APPEND >>
      simp[] >>
      irule_at (Pat `_ ++ _ = _ ++ _`) EQ_REFL >>
      simp[translate_ns_def] >>
      irule kind_ok_tdefs_APPEND >>
      simp[kind_ok_tdefs_to_tcexp_tdefs]
    ) >>
    irule EQ_TRANS >>
    irule_at Any tsubst_GENLIST_APPEND >>
    simp[arithmeticTheory.ADD1] >>
    qexists_tac `LENGTH meth_ks + LENGTH inst'.kinds` >>
    simp[unshift_db_shift_db] >>
    irule freetyvars_ok_shift_db_skip >>
    drule class_map_to_ns_EVERY_type_scheme_ok >>
    rw[EVERY_EL] >>
    gvs[FLOOKUP_to_cl_tyid_map,LLOOKUP_THM,EL_APPEND_EQN,
      translate_ns_def,LENGTH_tdefs_to_tcexp_tdefs] >>
    first_x_assum drule >>
    rw[] >>
    pop_assum $ qspec_then `LENGTH sup_tys + n` mp_tac >>
    rw[EL_APPEND_EQN,type_scheme_ok_def] >>
    drule kind_ok_IMP_freetyvars_ok >>
    simp[]
  ) >>
  (* normal implementations *)
  strip_tac >>
  drule ALOOKUP_MEM >>
  rw[MEM_EL] >>
  pop_assum $ assume_tac o GSYM >>
  last_x_assum drule >>
  disch_then strip_assume_tac >>
  gvs[] >>
  rev_drule_then strip_assume_tac ALOOKUP_MEM >>
  drule_all_then assume_tac $
    ALL_DISTINCT_method_names_IMP_ALL_DISTINCT_methods >>
  drule ALOOKUP_ALL_DISTINCT_MEM >>
  rw[MEM_EL,PULL_EXISTS] >>
  first_x_assum drule >>
  rw[] >>
  (drule_then $ drule_then $ drule_then $ drule_then irule)
    impl_type_tcexp >>
  simp[SF ETA_ss] >>
  first_assum $ irule_at (Pat `translate_ie_alist _ _ = _`) >>
  first_assum $ irule_at (Pat `entailment_kind_ok _ _ _`) >>
  simp[MAP_REVERSE,MAP_MAP_o,ZIP_MAP,LAMBDA_PROD,combinTheory.o_DEF] >>
  gvs[ELIM_UNCURRY] >>
  drule_then irule DISJOINT_lambda_varsl_MEM >>
  simp[MEM_MAP,EXISTS_PROD,MEM_EL] >>
  first_x_assum $ irule_at (Pos hd) >>
  simp[]
QED

Theorem instance_list_type_tcexp:
  type_elaborate_instance_list ns cl_map ie st env
    inst_list inst_list' ∧
  instance_list_construct_dict ns cl_map ie_map env_vs defaults
    inst_list' trans_inst_list ∧
  translate_ie_alist cl_to_tyid (instance_list_to_ie inst_list') =
    SOME instance_type_schemes ∧
  (∀n. n < LENGTH inst_list' ⇒
    ALOOKUP ie_env (EL n inst_list').dict_name =
      SOME $ SND $ EL n instance_type_schemes) ∧

  defaults_env_rel cl_to_tyid cl_map defaults trans_env ∧
  translate_env cl_to_tyid env = SOME trans_env ∧
  translate_ie_alist cl_to_tyid ie_alist = SOME ie_env ∧
  namespace_ok ns ∧
  translate_ns_and_class_datatypes ns cl_map new_ns ∧
  EVERY (type_ok tds []) st ∧
  EVERY (λ(v,scheme). pred_type_kind_scheme_ok clk tds [] scheme) env ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  DISJOINT (set $ MAP FST ie_alist) (set (MAP FST env)) ∧
  DISJOINT (set $ MAP FST ie_alist)
    (lambda_varsl (MAP SND (LIST_BIND inst_list' (λx. x.impls)))) ∧
  (∀ent. ent ∈ ie ⇒ entailment_kind_ok tds clk ent) ∧
  instance_list_kind_ok tds clk inst_list' ∧
  class_map_kind_ok tds cl_map ∧
  ALL_DISTINCT (MAP FST ie_alist) ∧
  ALL_DISTINCT (method_names cl_map) ∧

  cl_to_tyid = to_cl_tyid_map tds cl_map ∧
  tds = SND ns ∧
  clk = class_map_to_clk cl_map ∧
  ie_map = alist_to_fmap ie_alist ∧
  ie = FRANGE ie_map ∧
  env_vs = set (MAP FST env) ∧
  new_env = trans_env ++ ie_env ∧
  type_list = MAP SND instance_type_schemes ∧
  typed = (λ(fname,func) (ks,ty).
      type_tcexp new_ns ks (MAP (tshift (LENGTH ks)) st)
      (tshift_env (LENGTH ks) new_env) (tcexp_of func) ty)
  ⇒
  LIST_REL typed trans_inst_list type_list
Proof
  rw[type_elaborate_instance_list_def,
    instance_list_construct_dict_def,
    OPT_MMAP_SOME_LIST_REL] >>
  gvs[LIST_REL_EL_EQN] >>
  conj_asm1_tac
  >- gvs[translate_ie_alist_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,
      EVERY2_MAP,instance_list_to_ie_def,LIST_REL_EL_EQN] >>
  rw[EL_MAP,oneline SND] >>
  CASE_TAC >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `!n. _ ⇒ type_elaborate_instance _ _ _ _ _ _ _`
    drule >>
  qpat_x_assum `!n. _ ⇒ instance_construct_dict _ _ _ _ _ _ _`
    drule >>
  rpt strip_tac >>
  drule_then (drule_then irule) instance_type_tcexp >>
  simp[] >>
  first_assum $ irule_at (Pat `translate_ie_alist _ _ = _`) >>
  rw[]
  >- (
    gvs[translate_ie_alist_OPT_MMAP,OPT_MMAP_SOME_LIST_REL,
      LIST_REL_EL_EQN,instance_list_to_ie_def,EL_MAP] >>
    last_x_assum drule >>
    rw[]
  )
  >- (
    gvs[lambda_varsl_def,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,
      PULL_EXISTS] >>
    rw[] >>
    first_x_assum irule >>
    simp[LIST_BIND_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
    first_assum $ irule_at (Pat `MEM _ _.impls`) >>
    simp[MEM_EL] >>
    irule_at Any EQ_REFL >> simp[]
  )
  >- gvs[instance_list_kind_ok_def,EVERY_EL]
QED

Theorem EVERY_SOME_IMP_EXISTS_OPT_MMAP_SOME:
  EVERY (λx. ∃y. f x = SOME y) l ⇒ ∃r. OPT_MMAP f l = SOME r
Proof
  Induct_on `l` >> rw[] >> simp[]
QED

Theorem entailment_kind_ok_IMP_translate_entailment_SOME:
  ALL_DISTINCT (MAP FST cl_map) ∧
  entailment_kind_ok tds (class_map_to_clk cl_map) ent ⇒
  ∃t. translate_entailment (to_cl_tyid_map tds cl_map) ent = SOME t
Proof
  Cases_on `ent` >>
  rw[entailment_kind_ok_def,translate_entailment_def,PULL_EXISTS] >>
  gvs[translate_predicates_OPT_MMAP,translate_predicate_def,
    FLOOKUP_to_cl_tyid_map,PULL_EXISTS] >>
  PairCases_on `p` >>
  gvs[class_map_to_clk_def] >>
  drule miscTheory.ALOOKUP_find_index_SOME >>
  rw[] >> simp[] >>
  irule EVERY_SOME_IMP_EXISTS_OPT_MMAP_SOME >>
  drule_at_then (Pos last) irule MONO_EVERY >>
  simp[FORALL_PROD,PULL_EXISTS] >>
  rw[translate_predicate_def,FLOOKUP_to_cl_tyid_map] >>
  drule miscTheory.ALOOKUP_find_index_SOME >>
  rw[] >> simp[]
QED

(* main theorem *)
Theorem prog_construct_dict_type_tcexp:
  namespace_ok ns ∧
  EVERY (type_ok (SND ns) db) st ∧
  ALL_DISTINCT (MAP FST cl_map) ∧
  translate_ns_and_class_datatypes ns cl_map trans_ns ∧
  type_elaborate_prog ns st cl_map defaults inst_list fns main
    main_t defaults' inst_list' fns' main' ∧
  prog_construct_dict ns cl_map defaults' inst_list' fns' main'
    output ⇒
  type_tcexp trans_ns [] st [] (tcexp_of output) main_t
Proof
  rw[type_elaborate_prog_def,prog_construct_dict_def] >>
  simp[tcexp_of_def] >>
  irule type_tcexp_Letrec >>
  conj_tac
  >- (
    dxrule $ iffLR $ cj 2 texp_construct_dict_cases >>
    simp[] >>
    dxrule $ iffLR $ cj 2 type_elaborate_texp_cases >>
    rw[] >>
    fs[LIST_REL_EL_EQN]
  ) >>
  simp[] >>
  qabbrev_tac `cl_to_tyid = to_cl_tyid_map (SND ns) cl_map` >>
  `∃instance_type_schemes.
    translate_ie_alist cl_to_tyid (instance_list_to_ie inst_list') =
    SOME instance_type_schemes`
  by (
    simp[translate_ie_alist_OPT_MMAP] >>
    irule EVERY_SOME_IMP_EXISTS_OPT_MMAP_SOME >>
    rw[EVERY_MEM,instance_list_to_ie_def,MEM_MAP] >>
    simp[Abbr`cl_to_tyid`] >>
    irule entailment_kind_ok_IMP_translate_entailment_SOME >>
    gvs[instance_list_kind_ok_def,EVERY_MEM,instance_kind_ok_def]
  ) >>

  `cl_to_tyid_cl_map_rel (SND ns) cl_to_tyid cl_map`
  by (
  )


  dxrule $ iffLR $ cj 2 texp_construct_dict_cases >>
  simp[] >>
  dxrule $ iffLR $ cj 2 type_elaborate_texp_cases >>
  rw[] >>

  irule_at Any $ cj 1 $ iffLR LIST_REL_APPEND >>
  irule_at (Pos hd) $ cj 1 $ iffLR LIST_REL_APPEND >>
  irule_at (Pos hd) $ cj 1 $ iffLR LIST_REL_APPEND >>
  simp[EVERY2_MAP,LAMBDA_PROD] >>

QED

val _ = export_theory();
