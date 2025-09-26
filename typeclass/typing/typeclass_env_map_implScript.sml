(* concrete data structures for implementing
* instance map and type class map *)
Theory typeclass_env_map_impl
Ancestors
  relation set_relation pair option list pred_set finite_map
  mlmap mlstring balanced_map alist topological_sort misc
  typeclass_types typeclass_kindCheck typeclass_typesProps
  typeclass_texp typeclass_typing typeclass_typingProps
Libs
  dep_rewrite BasicProvers monadsyntax

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"


(* Since we only support single-param typeclass, we only need to keep
* track of the names of the super classes *)
Datatype:
  classinfo_impl =
    <| supers : mlstring list
     ; kind : Kind option
     ; methodsig : (cvname, 'a # PredType) mlmap$map
     ; defaults : (cvname, 'a texp) mlmap$map |>
End

(* We only support the form where there is only one constructor on the
* right, and every constraint in the context can only refer to a type
* variabale *)
Datatype:
  instinfo_impl =
    <| cstr : (mlstring # num) list (* list of classes and type vars *)
     ; impls : (cvname, 'a texp) mlmap$map |>
     (* method name and its implementation *)
End

(* class name to class info *)
Type class_map_impl = ``:(mlstring, 'a classinfo_impl) map``;

(* NOTE: We don't actually need to record the number of
 * type arguments as it can be inferred from the
 * kind, but it should make things simpler *)
(* class name, the constructor and
* the number of type arguments to instance info *)
Type inst_map_impl = ``:((mlstring # ty_cons # num), 'a instinfo_impl) map``;

Definition built_in_ty_num_def:
  built_in_ty_num (PrimT Bool) = 0 ∧
  built_in_ty_num (PrimT Integer) = 1 ∧
  built_in_ty_num (PrimT String) = 2 ∧
  built_in_ty_num (PrimT Message) = 3 ∧
  built_in_ty_num (CompPrimT Function) = 4 ∧
  built_in_ty_num (CompPrimT M) = 5 ∧
  built_in_ty_num (CompPrimT Array) = 6 ∧
  built_in_ty_num (CompPrimT $ Tuple n) = n + 7
End

Definition built_in_tyOrd_def:
  built_in_tyOrd = imageOrd built_in_ty_num numOrd
End

Theorem TO_built_in_tyOrd:
  TotOrd built_in_tyOrd
Proof
  DEP_REWRITE_TAC[totoTheory.TO_injection,built_in_tyOrd_def] >>
  rw[totoTheory.TO_numOrd,ONE_ONE_THM] >>
  gvs[oneline built_in_ty_num_def,AllCaseEqs()]
QED

Definition ty_consOrd_def:
  ty_consOrd (INL x) (INR y) = Less ∧
  ty_consOrd (INR x) (INL y) = Greater ∧
  ty_consOrd (INL x) (INL y) = numOrd x y ∧
  ty_consOrd (INR x) (INR y) = built_in_tyOrd x y
End

Theorem TO_ty_consOrd:
  TotOrd ty_consOrd
Proof
  rw[totoTheory.TotOrd,oneline ty_consOrd_def,EQ_IMP_THM,
    PULL_EXISTS,AllCaseEqs()]
  >~ [`_ ∨ _`] >- (
    Cases_on `x` >>
    simp[] >>
    metis_tac[totoTheory.TotOrd,totoTheory.TO_numOrd,TO_built_in_tyOrd]
  ) >>
  metis_tac[totoTheory.TotOrd,totoTheory.TO_numOrd,TO_built_in_tyOrd]
QED

Definition inst_map_cmp_def:
  inst_map_cmp = mlstring$compare lexTO ty_consOrd lexTO numOrd
End

(* The ordering for instance map *)
Theorem TO_inst_map_cmp:
  TotOrd inst_map_cmp
Proof
  metis_tac[inst_map_cmp_def,totoTheory.TO_lexTO,
    TotOrd_compare,TO_ty_consOrd,totoTheory.TO_numOrd]
QED

Definition init_inst_map_def:
  init_inst_map = empty inst_map_cmp
End

Theorem map_ok_init_inst_map:
  map_ok init_inst_map
Proof
  simp[init_inst_map_def,mlmapTheory.empty_thm,TO_inst_map_cmp]
QED

Theorem to_fmap_init_inst_map:
  to_fmap init_inst_map = FEMPTY
Proof
  simp[init_inst_map_def,mlmapTheory.empty_thm]
QED

Theorem cmp_of_init_inst_map:
  cmp_of init_inst_map = inst_map_cmp
Proof
  simp[cmp_of_empty,init_inst_map_def]
QED

Definition class_super_abs_rel_def:
  class_super_abs_rel (cl_impl: 'a classinfo_impl) (abs:Class) =
    (set (cl_impl.supers) = set (MAP FST abs.supers))
End

(* relating the concrete class and its abstraction *)
Definition class_abs_rel_def:
  class_abs_rel (cl_impl:Kind list classinfo_impl) (abs:Class) =
    (class_super_abs_rel cl_impl abs ∧
    cl_impl.kind = SOME abs.kind ∧
    lookup cl_impl.methodsig = ALOOKUP abs.methods)
End

(* relating the class map and its abstraction *)
Definition class_map_abs_rel_def:
  class_map_abs_rel (cl_map_impl:Kind list class_map_impl) (abs:class_map) =
  (∀c. OPTREL class_abs_rel (mlmap$lookup cl_map_impl c) (ALOOKUP abs c))
End

Definition class_map_super_abs_rel_def:
  class_map_super_abs_rel (cl_map_impl: 'a class_map_impl) (abs:class_map) =
  (∀c. OPTREL class_super_abs_rel (lookup cl_map_impl c) (ALOOKUP abs c))
End

Theorem class_map_abs_rel_IMP_class_map_super_abs_rel:
  class_map_abs_rel cl_map_impl abs ⇒
  class_map_super_abs_rel cl_map_impl abs
Proof
  rw[class_map_abs_rel_def,class_map_super_abs_rel_def] >>
  last_x_assum $ qspec_then `c` assume_tac >>
  drule_at_then (Pos last) irule OPTREL_MONO >>
  simp[class_abs_rel_def]
QED

(* every class in the super list must be a valid key of the map *)
Definition super_keys_ok_def:
  super_keys_ok (cl_map: 'a class_map_impl) =
  (∀c clinfo c'.
    mlmap$lookup cl_map c = SOME clinfo ∧ MEM c' clinfo.supers ⇒
    ∃x. mlmap$lookup cl_map c' = SOME x)
End

(* relating a concrete instance with its abstraction *)
Definition inst_abs_rel_def:
  inst_abs_rel class tycons ntargs (inst_impl:Kind list instinfo_impl)
    (abs:Kind list Instance) =
  (abs.context = MAP (λ(cl,v). (cl,TypeVar v)) inst_impl.cstr ∧
   ALOOKUP abs.impls = lookup inst_impl.impls ∧
   abs.class = class ∧
   abs.type = tcons_to_type tycons (GENLIST TypeVar ntargs) ∧
   LENGTH abs.kinds = ntargs)
End

(* relating a concrete instance map with its abstraction *)
Definition inst_map_abs_rel_def:
  inst_map_abs_rel
    (inst_map_impl:Kind list inst_map_impl)
    (abs_map:Kind list instance_list) ⇔
  (∀cl tycons ntargs instinfo.
    lookup inst_map_impl (cl,tycons,ntargs) = SOME instinfo ⇒
      ∃abs. MEM abs abs_map ∧
        inst_abs_rel cl tycons ntargs instinfo abs) ∧
  (∀abs. MEM abs abs_map ⇒
    ∃cl tycons ntargs instinfo.
      lookup inst_map_impl (cl,tycons,ntargs) = SOME instinfo ∧
      inst_abs_rel cl tycons ntargs instinfo abs)
End

(* return NONE if duplicated *)
Definition add_instance_def:
  add_instance (inst_map:'a inst_map_impl) cl ty n info =
    case lookup inst_map (cl,ty,n) of
    | NONE => SOME $ insert inst_map (cl,ty,n) info
    | SOME _ => NONE
End

(* `super_reachable_abs cl_map c s`
* checks if `s` is a parent of the class `c` *)
Definition super_reachable_abs_def:
  super_reachable_abs (cl_map: class_map) =
  TC (λclname supername.
    ∃cl. ALOOKUP cl_map clname = SOME cl ∧
      MEM supername (MAP FST cl.supers))
End

(* implementation of super_reachable_abs *)
Definition super_reachable_def:
  super_reachable (cl_map:'a class_map_impl) =
  TC (λclname supername.
    ∃cl. lookup cl_map clname = SOME cl ∧ MEM supername cl.supers)
End

(* RTC version of super_reachable *)
Definition super_reachable_RTC_def:
  super_reachable_RTC (cl_map:'a class_map_impl) =
  RTC (λclname supername.
    ∃cl. lookup cl_map clname = SOME cl ∧ MEM supername cl.supers)
End

Theorem super_reachable_RTC_CASES_super_reachable:
  super_reachable_RTC cl_map c s =
  (c = s ∨ super_reachable cl_map c s)
Proof
  simp[super_reachable_RTC_def,super_reachable_def,
    RTC_CASES_TC]
QED

Theorem class_map_super_abs_rel_super_reachable:
  class_map_super_abs_rel cl_map_impl cl_map ⇒
  super_reachable cl_map_impl = super_reachable_abs cl_map
Proof
  rw[class_map_super_abs_rel_def,super_reachable_def,
    super_reachable_abs_def] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum $ qspec_then `clname` mp_tac >>
  rw[OPTREL_def] >>
  gvs[class_super_abs_rel_def]
QED

Definition super_no_cycles_abs_def:
  super_no_cycles_abs cl_map =
    ∀clname. ¬super_reachable_abs cl_map clname clname
End

Definition super_no_cycles_def:
  super_no_cycles cl_map = ∀clname. ¬super_reachable cl_map clname clname
End

Theorem class_map_super_abs_rel_super_no_cycles:
  class_map_super_abs_rel cl_map_impl cl_map ⇒
  super_no_cycles cl_map_impl = super_no_cycles_abs cl_map
Proof
  rw[super_no_cycles_def,super_no_cycles_abs_def] >>
  drule class_map_super_abs_rel_super_reachable >>
  simp[]
QED

Definition superAList_def:
  superAList cl_map =
    MAP (λ(k,v). (k, v.supers)) $ toAscList cl_map
End

Theorem mlmap_ALOOKUP_toAscList:
  map_ok m ⇒
  ALOOKUP (mlmap$toAscList m) = mlmap$lookup m
Proof
  Cases_on `m` >>
  rw[FUN_EQ_THM,mlmapTheory.toAscList_def,map_ok_def,
    mlmapTheory.lookup_def] >>
  irule ALOOKUP_toAscList >>
  simp[] >>
  drule_then (irule_at Any) comparisonTheory.TotOrder_imp_good_cmp >>
  gvs[totoTheory.TotOrd]
QED

Theorem super_reachable_TC_depends_on_weak:
  map_ok cl_map ⇒
  super_reachable cl_map = TC_depends_on_weak (superAList cl_map)
Proof
  simp[TC_depends_on_weak_def,super_reachable_def,superAList_def,
    ALOOKUP_MAP,PULL_EXISTS] >>
  strip_tac >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM,mlmap_ALOOKUP_toAscList]
QED

Theorem ALL_DISTINCT_superAList:
  map_ok cl_map ⇒
  ALL_DISTINCT (MAP FST $ superAList cl_map)
Proof
  rw[superAList_def,map_fst] >>
  simp[mlmapTheory.MAP_FST_toAscList]
QED

(* algorithm for checking acyclic superclass relation *)
Definition check_cl_map_no_cycles_def:
  check_cl_map_no_cycles cl_map =
    ¬has_cycle (superAList cl_map)
End

Theorem check_cl_map_no_cycles_IMP_super_no_cycles:
  map_ok cl_map ∧
  check_cl_map_no_cycles cl_map ⇒
  super_no_cycles cl_map
Proof
  rw[super_no_cycles_def,super_reachable_TC_depends_on_weak] >>
  drule_then assume_tac ALL_DISTINCT_superAList >>
  strip_tac >>
  drule_then drule $ SRULE[PULL_EXISTS] $ iffRL has_cycle_correct2 >>
  gvs[check_cl_map_no_cycles_def]
QED

(* Similar to how it is implemented in
 * "Typing Haskell in Haskell" by Mark P. Jones *)

Theorem mlmap_domain_FINITE:
  map_ok m ⇒
  FINITE {s | ∃v. mlmap$lookup m s = SOME v}
Proof
  simp[mlmapTheory.lookup_thm,flookup_thm]
QED

Theorem super_reachable_FDOM_cl_map:
  ∀c s. super_reachable cl_map c s ⇒
  ∃x cl. lookup cl_map x = SOME cl ∧ MEM s cl.supers
Proof
  simp[super_reachable_def] >>
  ho_match_mp_tac TC_INDUCT >>
  simp[] >>
  metis_tac[]
QED

Theorem super_reachable_FINITE:
  map_ok cl_map ⇒
  FINITE (super_reachable cl_map c)
Proof
  rw[] >>
  irule SUBSET_FINITE >>
  qexists `BIGUNION (IMAGE (λcl. set cl.supers) $
    {v | ∃s. mlmap$lookup cl_map s = SOME v})` >>
  rw[SUBSET_DEF]
  >- (
    irule IMAGE_FINITE >>
    simp[mlmapTheory.lookup_thm,GSYM TO_FLOOKUP]
  )
  >- simp[] >>
  gvs[IN_DEF] >>
  drule super_reachable_FDOM_cl_map >>
  rw[] >>
  first_assum $ irule_at (Pos last) >>
  gvs[IN_DEF]
QED

Triviality GSPEC_super_reachable_or:
  {s | super_reachable cl_map c s ∨ c = s} =
    super_reachable cl_map c ∪ {c}
Proof
  rw[EXTENSION] >>
  metis_tac[IN_DEF]
QED

Theorem super_reachable_list_FINITE:
  map_ok cl_map ⇒
  FINITE {s | ∃c. MEM c cs ∧
    (super_reachable cl_map c s ∨ c = s)}
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `FINITE X` >>
  `X = BIGUNION (set $ (MAP (λc. {s | super_reachable cl_map c s ∨ c =
  s}) cs))`
  by (
    simp[Abbr`X`,BIGUNION,MEM_MAP,EXTENSION] >>
    rw[EQ_IMP_THM,PULL_EXISTS]
    >- (
      qexists_tac `\x. super_reachable cl_map c x ∨ c = x` >>
      simp[IN_DEF] >>
      qexists_tac`c` >>
      fs[SUBSET_DEF,IN_DEF]
    )
    >- (
      qexists_tac `\x. super_reachable cl_map c x ∨ c = x` >>
      simp[IN_DEF] >>
      qexists_tac`c` >>
      fs[SUBSET_DEF,IN_DEF]
    ) >>
    metis_tac[]
  ) >>
  rw[MEM_MAP,GSPEC_super_reachable_or] >>
  simp[] >>
  metis_tac[super_reachable_FINITE]
QED

Triviality INTER_PRESERVE_SUBSET:
  s ⊆ s' ∧ x ⊆ x' ⇒ (s ∩ x) ⊆ (s' ∩ x')
Proof
  simp[INTER_DEF,SUBSET_DEF,EXTENSION,IN_DEF]
QED

Triviality COMPL_SUBSET:
  s ⊆ s' ⇒ COMPL s' ⊆ COMPL s
Proof
  rw[COMPL_DEF,SUBSET_DEF] >>
  metis_tac[]
QED

Definition fix_visited_def:
  fix_visited s s' = if (∀x t. lookup s x = SOME t ⇒ lookup s' x = SOME t) then
    s' else s
End

Definition by_super_aux_def:
  (by_super_aux cl_map visited c t =
   if map_ok cl_map ∧ map_ok visited
   then
    case lookup visited c of
    | SOME _ => SOME visited
    | NONE =>
      case mlmap$lookup cl_map c of
      | NONE => NONE
      | SOME clinfo =>
          by_super_aux_list cl_map (insert visited c t) clinfo.supers t
   else NONE) ∧
  by_super_aux_list cl_map ret [] t = SOME ret ∧
  by_super_aux_list cl_map visited (sup::xs) t =
    if map_ok cl_map ∧ map_ok visited
    then
      case OPTION_MAP (fix_visited visited) (by_super_aux cl_map visited sup t) of
      | SOME visited' => by_super_aux_list cl_map visited' xs t
      | NONE => NONE
    else NONE
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (\x.
    ((case x of
    | INR (cl_map,(visited:(mlstring,'a)map),cs,t:'a) =>
      CARD ({s | ∃c. MEM c cs ∧ (super_reachable cl_map c s ∨ c = s)}
        DIFF {s | ∃v.  lookup visited s = SOME v})
    | INL (cl_map,visited,c,t) =>
       CARD ({s | super_reachable cl_map c s ∨ c = s}
        DIFF {s | ∃v. lookup visited s = SOME v})),
    (case x of
    | INR (cl_map,visited,cs,t) => LENGTH cs
    | INL (cl_map,visited,c,t) => 0)))` >>
  rw[]
  >- (
    irule CARD_PSUBSET >>
    conj_tac
    >- (
      irule FINITE_DIFF >>
      simp[GSPEC_super_reachable_or] >>
      drule_then irule super_reachable_FINITE
    ) >>
    rw[PSUBSET_MEMBER,SUBSET_DEF,DIFF_DEF,
      mlmapTheory.lookup_insert,AllCaseEqs()]
    >- (
      fs[super_reachable_def] >>
      disj1_tac >>
      irule TC_LEFT1_I >>
      first_assum $ irule_at (Pos last) >>
      fs[GSYM mlmapTheory.lookup_thm]
    )
    >- (Cases_on `c=x` >> fs[])
    >- (
      fs[super_reachable_def] >>
      Cases_on `c=c'` >>
      fs[GSYM mlmapTheory.lookup_thm] >>
      irule $ cj 1 TC_RULES >>
      simp[]
    )
    >- (Cases_on `c=c'` >> fs[]) >>
    qexists_tac `c` >>
    simp[]
  )
  >- (
    simp[GSYM arithmeticTheory.LE_LT] >>
    irule CARD_SUBSET >>
    conj_tac
    >- (
      irule FINITE_DIFF >>
      drule_then (qspec_then `sup'::xs` assume_tac)
        super_reachable_list_FINITE >>
      fs[]
    ) >>
    PURE_REWRITE_TAC[DIFF_INTER_COMPL] >>
    irule INTER_PRESERVE_SUBSET >>
    conj_tac
    >- (
      rw[SUBSET_DEF] >>
      qexists_tac `c` >>
      simp[]
    ) >>
    irule COMPL_SUBSET >>
    simp[SUBSET_DEF,PULL_EXISTS] >>
    simp[fix_visited_def] >>
    IF_CASES_TAC >>
    rw[] >>
    first_x_assum $ drule_then $ irule_at (Pos hd)
  ) >>
  simp[GSYM arithmeticTheory.LE_LT] >>
  irule CARD_SUBSET >>
  conj_tac
  >- (
    irule FINITE_DIFF >>
    drule_then (qspec_then `sup'::xs` assume_tac)
      super_reachable_list_FINITE >>
    fs[]
  ) >>
  PURE_REWRITE_TAC[DIFF_INTER_COMPL] >>
  irule INTER_PRESERVE_SUBSET >>
  simp[SUBSET_DEF] >> metis_tac[]
End

Theorem by_super_aux_monotone:
  (∀(cl_map:'b class_map_impl) visited c (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux cl_map visited c t = SOME new_visited ⇒
      map_ok new_visited ∧
    (∀c' t. lookup visited c' = SOME t ⇒
      lookup new_visited c' = SOME t)) ∧

  (∀(cl_map:'b class_map_impl) visited cs (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux_list cl_map visited cs t = SOME new_visited ⇒
      map_ok new_visited ∧
    (∀c' t. lookup visited c' = SOME t ⇒
        lookup new_visited c' = SOME t))
Proof
  ho_match_mp_tac by_super_aux_ind >>
  reverse $ rpt conj_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >>
  pop_assum $ mp_tac o SRULE[Once by_super_aux_def]
  >- (
    TOP_CASE_TAC >>
    rpt strip_tac >>
    fs[] >>
    gvs[fix_visited_def]
  ) >>
  rw[AllCaseEqs()] >>
  fs[mlmapTheory.lookup_insert,mlmapTheory.insert_thm,
    AllCaseEqs(),SF DNF_ss] >>
  Cases_on `c = c'` >>
  fs[]
QED

Theorem fix_visited_by_super_aux_OPTION_MAP:
  map_ok visited ⇒
  OPTION_MAP (fix_visited visited) (by_super_aux cl_map visited s t) =
  by_super_aux cl_map visited s t
Proof
  simp[oneline OPTION_MAP_DEF] >>
  TOP_CASE_TAC >>
  simp[fix_visited_def] >>
  rw[] >>
  gvs[] >>
  drule_all $ cj 1 by_super_aux_monotone >>
  rw[] >>
  metis_tac[]
QED

Theorem fix_visited_by_super_aux:
  map_ok visited ⇒
  by_super_aux cl_map visited s t = SOME z ⇒
    fix_visited visited z = z
Proof
  rpt strip_tac >>
  drule_then (qspecl_then [`t`,`s`,`cl_map`] mp_tac)
    fix_visited_by_super_aux_OPTION_MAP >>
  simp[oneline OPTION_MAP_DEF]
QED

Theorem full_by_super_aux_def =
  SRULE[fix_visited_by_super_aux_OPTION_MAP]
    by_super_aux_def;

Theorem full_by_super_aux_ind:
  ∀P0 P1.
  (∀cl_map visited c t.
     (∀clinfo.
         map_ok cl_map ∧ map_ok visited ∧ mlmap$lookup visited c = NONE ∧
         mlmap$lookup cl_map c = SOME clinfo ⇒
         P1 cl_map (insert visited c t) clinfo.supers t) ⇒
      P0 cl_map visited c t) ∧
  (∀cl_map ret t. P1 cl_map ret [] t) ∧
  (∀cl_map visited sup xs t.
    (∀visited'.
       map_ok cl_map ∧ map_ok visited ∧
       by_super_aux cl_map visited sup t = SOME visited' ⇒
       P1 cl_map visited' xs t) ∧
    (map_ok cl_map ∧ map_ok visited ⇒ P0 cl_map visited sup t) ⇒
     P1 cl_map visited (sup::xs) t) ⇒
  (∀(v0:'b class_map_impl) v1 v2 (v3:'a). P0 v0 v1 v2 v3) ∧
   ∀(v0:'b class_map_impl) v1 v2 (v3:'a). P1 v0 v1 v2 v3
Proof
  rpt gen_tac >>
  strip_tac >>
  irule by_super_aux_ind >>
  rw[] >>
  metis_tac[fix_visited_by_super_aux]
QED

Theorem by_super_aux_lookup_preserve_type:
  (∀(cl_map:'b class_map_impl) visited c (t:'a) new_visited.
  map_ok visited ∧
  by_super_aux cl_map visited c t = SOME new_visited ∧
  (∀c' v. lookup visited c' = SOME v ⇒ v = t) ⇒
  (∀c v. lookup new_visited c = SOME v ⇒ v = t)) ∧

  (∀(cl_map:'b class_map_impl) visited cs (t:'a) new_visited.
  map_ok visited ∧
  by_super_aux_list cl_map visited cs t = SOME new_visited ∧
  (∀c' v. lookup visited c' = SOME v ⇒ v = t) ⇒
  (∀c' v. lookup new_visited c' = SOME v ⇒ v = t))
Proof
  ho_match_mp_tac full_by_super_aux_ind >>
  rpt conj_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac
  >- (
    qpat_x_assum `by_super_aux _ _ _ _ = _` $
      mp_tac o SRULE[full_by_super_aux_def] >>
    rpt TOP_CASE_TAC
    >- (
      strip_tac >>
      first_x_assum $ qspec_then `x` mp_tac >>
      simp[] >>
      impl_tac
      >- (
        rw[mlmapTheory.insert_thm,mlmapTheory.lookup_insert] >>
        metis_tac[]
      ) >> rw[]
    ) >>
    strip_tac >> fs[]
  )
  >- (gvs[by_super_aux_def] >> metis_tac[]) >>
  qpat_x_assum `by_super_aux_list _ _ _ _ = _` $
    mp_tac o SRULE[Once full_by_super_aux_def] >>
  TOP_CASE_TAC >>
  strip_tac >>
  qpat_x_assum `!visited. _ ⇒
    ∀new_visited. _ ∧ by_super_aux_list _ _ _ _ = _ ∧
    _ ==> _` $ mp_tac o SRULE[] >>
  impl_tac >- simp[] >>
  pop_assum SUBST_ALL_TAC >>
  disch_then $ qspec_then `new_visited` $
    ho_match_mp_tac o SRULE[] >>
  conj_tac >- metis_tac[by_super_aux_monotone] >>
  metis_tac[]
QED

Theorem by_super_aux_visited:
  (∀(cl_map:'b class_map_impl) visited c (t:'a) new_visited.
    by_super_aux cl_map visited c t = SOME new_visited  ⇒
    ∃v. lookup new_visited c = SOME v) ∧
  (∀(cl_map:'b class_map_impl) visited cs (t:'a) new_visited c.
    by_super_aux_list cl_map visited cs t = SOME new_visited ∧
    MEM c cs ⇒
    ∃v. lookup new_visited c = SOME v)
Proof
  conj_asm1_tac
  >- (
    rw[Once full_by_super_aux_def,AllCaseEqs()]
    >- (
      drule_at (Pos last) $ cj 2 by_super_aux_monotone >>
      rw[mlmapTheory.insert_thm,mlmapTheory.lookup_insert] >>
      first_assum $ irule_at (Pos hd) >>
      simp[]) >>
    metis_tac[]
  ) >>
  Induct_on `cs` >>
  simp[Once full_by_super_aux_def] >>
  rw[AllCaseEqs()]
  >- (
    drule_at (Pos last) $ cj 2 by_super_aux_monotone >>
    reverse $ impl_tac >- metis_tac[] >>
    metis_tac[by_super_aux_monotone]
  ) >>
  first_x_assum $ drule_then $ drule_at (Pos last) >>
  metis_tac[by_super_aux_monotone]
QED

Theorem by_super_aux_IMP_reachable:
  (∀(cl_map:'b class_map_impl) visited c (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux cl_map visited c t = SOME new_visited ⇒
    (∀c' v. lookup new_visited c' = SOME v ⇒
      RTC
        (λsrc dst. ∃v. lookup cl_map src = SOME v ∧
        MEM dst v.supers ∧ lookup visited dst = NONE) c c' ∨
      lookup visited c' = SOME v)) ∧

  (∀(cl_map:'b class_map_impl) visited cs (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux_list cl_map visited cs t = SOME new_visited ⇒
    (∀c' v. lookup new_visited c' = SOME v ⇒
      (∃c. MEM c cs ∧ lookup visited c = NONE ∧
        RTC
          (λsrc dst. ∃v. lookup cl_map src = SOME v ∧
          MEM dst v.supers ∧ lookup visited dst = NONE) c c') ∨
       lookup visited c' = SOME v))
Proof
  ho_match_mp_tac full_by_super_aux_ind >>
  rpt conj_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac
  >- (
    last_x_assum $ markerLib.ASSUME_NAMED_TAC "ind_hyp" >>
    rw[] >>
    qpat_x_assum `by_super_aux _ _ _ _ = _` $ mp_tac o
      SRULE[Once by_super_aux_def] >>
    rpt TOP_CASE_TAC
    >- (
      strip_tac >>
      markerLib.LABEL_X_ASSUM "ind_hyp" $
        qspec_then `x` $ mp_tac o SRULE[] >>
      impl_tac >- simp[] >>
      simp[mlmapTheory.insert_thm] >>
      disch_then drule >>
      Cases_on `c = c'` >- simp[] >>
      rw[]
      >- (
        gvs[mlmapTheory.lookup_insert,AllCaseEqs()] >>
        disj1_tac >>
        irule $ cj 2 RTC_RULES >>
        qexists `c''` >>
        fs[] >>
        drule_at_then (Pos last) irule RTC_MONOTONE >>
        rw[mlmapTheory.lookup_insert] >>
        fs[]
      )
      >- (
        disj2_tac >>
        rev_drule_then strip_assume_tac $
          GEN_ALL mlmapTheory.lookup_insert >>
        gvs[AllCaseEqs()]
      )
    ) >>
    gvs[]
  )
  >- fs[full_by_super_aux_def]
  >- (
    rw[] >>
    qpat_x_assum `by_super_aux_list _ _ _ _ = _` $
      mp_tac o SRULE[Once full_by_super_aux_def] >>
    rw[AllCaseEqs()] >>
    `map_ok visited'` by metis_tac[by_super_aux_monotone] >>
    gvs[] >>
    reverse $ Cases_on `lookup visited c'`
    >- (
      disj2_tac >>
      drule_all $ cj 1 by_super_aux_monotone >>
      drule_all $ cj 2 by_super_aux_monotone >>
      metis_tac[]
    ) >>
    simp[] >>
    reverse $ Cases_on `lookup visited c`
    >- (
      qpat_x_assum `by_super_aux _ _ _ _ = _` $ mp_tac o
        SRULE[Once full_by_super_aux_def] >>
      rw[AllCaseEqs()] >>
      last_x_assum drule >>
      rw[] >>
      qexists `c''` >>
      simp[]
    ) >>
    reverse $ Cases_on `lookup visited' c'`
    >- (
      qexists `c` >>
      simp[] >>
      first_x_assum drule >>
      simp[]
    ) >>
    last_x_assum drule >>
    rw[] >>
    qexists `c''` >>
    simp[] >>
    conj_tac
    >- metis_tac[option_CASES,by_super_aux_monotone] >>
    drule_at_then (Pos $ el 2) irule RTC_MONOTONE >>
    rw[] >>
    metis_tac[option_CASES,by_super_aux_monotone]
  )
QED

Triviality PATH_IMP_RTC:
  ∀l x y.
    1 ≤ LENGTH l ∧ EL 0 l = x ∧ EL (LENGTH l - 1) l = y ∧
    (∀n. n < (LENGTH l -1) ⇒ R (EL n l) (EL (SUC n) l)) ⇒
    RTC R x y
Proof
  Induct_on `l` >>
  rw[] >>
  gvs[] >>
  Cases_on `LENGTH l` >>
  gvs[] >>
  irule $ cj 2 RTC_RULES >>
  last_x_assum $ irule_at (Pos last) >>
  rw[]
  >- (
    first_x_assum $ qspec_then `SUC n'` mp_tac >>
    simp[]
  ) >>
  first_x_assum $ qspec_then `0` mp_tac >>
  simp[]
QED

Triviality RTC_PATH:
  RTC R x y ⇔ (∃l. 1 ≤ LENGTH l ∧ ALL_DISTINCT l ∧
    EL 0 l = x ∧ EL (LENGTH l - 1) l = y ∧
    ∀n. n < (LENGTH l -1) ⇒ R (EL n l) (EL (SUC n) l))
Proof
  simp[EQ_IMP_THM] >>
  conj_tac
  >- (
    qid_spec_tac `y` >>
    qid_spec_tac `x` >>
    ho_match_mp_tac RTC_INDUCT >>
    rw[]
    >- (qexists `[x]` >> simp[]) >>
    Cases_on `MEM x l`
    >- (
      fs[MEM_EL] >>
      qexists `DROP n l` >>
      rw[EL_DROP,HD_DROP,ALL_DISTINCT_DROP] >>
      `n + n' < LENGTH l - 1` by DECIDE_TAC >>
      metis_tac[arithmeticTheory.ADD_SUC]
    ) >>
    qexists `x::l` >>
    rw[rich_listTheory.EL_CONS,arithmeticTheory.PRE_SUB1] >>
    Cases_on `n` >>
    simp[rich_listTheory.EL_CONS]
  ) >>
  simp[PULL_EXISTS] >>
  metis_tac[PATH_IMP_RTC,EL]
QED

Triviality HD_TL:
  1 < LENGTH l ⇒ HD (TL l) = EL 1 l
Proof
  Cases_on `l` >>
  simp[]
QED

Triviality DROP1_EQ_TL:
  DROP 1 l = TL l
Proof
  Cases_on `l` >>
  simp[]
QED

Theorem super_reachable_IMP_by_super_aux:
  (∀(cl_map:'b class_map_impl) visited c (t:'a) new_visited s.
    map_ok visited ∧
    by_super_aux cl_map visited c t = SOME new_visited ∧
    lookup visited c = NONE ∧
    RTC (λsrc dst. ∃v. mlmap$lookup cl_map src = SOME v ∧
      MEM dst v.supers ∧ mlmap$lookup visited dst = NONE) c s ⇒
    ∃v. mlmap$lookup new_visited s = SOME v) ∧

  (∀(cl_map:'b class_map_impl) visited cs (t:'a) new_visited c s.
    map_ok visited ∧
    by_super_aux_list cl_map visited cs t = SOME new_visited ∧
    MEM c cs ∧ lookup visited c = NONE ∧
    RTC (λsrc dst. ∃v. mlmap$lookup cl_map src = SOME v ∧
      MEM dst v.supers ∧ mlmap$lookup visited dst = NONE) c s ⇒
    ∃v. mlmap$lookup new_visited s = SOME v)
Proof
  ho_match_mp_tac full_by_super_aux_ind >>
  rpt conj_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac
  >- (
    fs[] >>
    qpat_x_assum `by_super_aux _ _ _ _ = _` $
      mp_tac o SRULE[Once full_by_super_aux_def] >>
    rw[AllCaseEqs()] >>
    gvs[mlmapTheory.insert_thm,RTC_PATH,PULL_EXISTS] >>
    Cases_on `LENGTH l = 1`
    >- (
      gvs[] >>
      drule_at (Pos last) $ cj 2 by_super_aux_monotone >>
      simp[mlmapTheory.insert_thm,mlmapTheory.lookup_insert] >>
      metis_tac[]) >>
    `1 < LENGTH l` by DECIDE_TAC >>
    gvs[] >>
    last_x_assum $ qspec_then `TL l` mp_tac >>
    simp[LENGTH_TL,GSYM $ cj 2 EL,arithmeticTheory.ADD1] >>
    disch_then ho_match_mp_tac >>
    simp[HD_TL] >>
    simp[GSYM DROP1_EQ_TL,ALL_DISTINCT_DROP] >>
    rw[mlmapTheory.lookup_insert]
    >- (
      first_x_assum $ qspec_then `0` mp_tac >>
      simp[]
    )
    >- (
      fs[EL_ALL_DISTINCT_EL_EQ] >>
      last_x_assum $ qspecl_then [`0`,`1`] mp_tac >>
      simp[]
    )
    >- (
      last_x_assum $ qspec_then `0` mp_tac >>
      rw[arithmeticTheory.ADD1]
    )
    >- (
      fs[EL_ALL_DISTINCT_EL_EQ] >>
      last_x_assum $ qspecl_then [`0`,`n + 2`] mp_tac >>
      simp[] >>
      last_x_assum $ qspec_then `n+1` mp_tac >>
      simp[arithmeticTheory.ADD1]
    )
  ) >>
  gvs[] >>
  qpat_x_assum `by_super_aux_list _ _ _ _ = _` $
      mp_tac o SRULE[Once full_by_super_aux_def]
  >- (
    rw[AllCaseEqs()] >>
    `map_ok visited'` by metis_tac[by_super_aux_monotone] >>
    gvs[RTC_PATH,PULL_EXISTS] >>
    first_x_assum $ qspec_then `l` mp_tac >>
    rw[] >>
    drule_then drule $ cj 2 by_super_aux_monotone >>
    metis_tac[]
  ) >>
  rw[AllCaseEqs()] >>
  Cases_on `lookup visited c`
  >- (
    `map_ok visited'` by metis_tac[cj 1 by_super_aux_monotone] >>
    gvs[PULL_EXISTS] >>
    qpat_assum `RTC _ c' s` $ strip_assume_tac o SRULE[RTC_PATH] >>
    Cases_on `!x. MEM x l ⇒ lookup visited' x = NONE` >>
    gvs[]
    >- (
      last_x_assum $ drule_then irule >>
      conj_tac
      >- (
        `0 < LENGTH l` by DECIDE_TAC >>
        `MEM (HD l) l` by (
          PURE_REWRITE_TAC[Once $ GSYM EL] >>
          metis_tac[MEM_EL]) >>
        metis_tac[]
      ) >>
      simp[RTC_PATH] >>
      first_assum $ irule_at (Pos hd) >>
      rw[] >>
      first_x_assum drule >>
      rw[] >>
      first_x_assum $ irule_at (Pos hd) >>
      simp[] >>
      first_x_assum irule >>
      simp[MEM_EL] >>
      irule_at (Pos last) EQ_REFL >>
      DECIDE_TAC
    ) >>
    `∃v. lookup visited' x = SOME v`
      by (Cases_on `lookup visited' x` >> fs[]) >>
    gvs[] >>
    qpat_x_assum `MEM x l` $ strip_assume_tac o SRULE[MEM_EL] >>
    gvs[] >>
    drule_then drule $ cj 2 $ cj 2 by_super_aux_monotone >>
    disch_then $ irule_at (Pos hd) >>
    first_assum irule >>
    simp[Once RTC_CASES_RTC_TWICE] >>
    qexists `EL n l` >>
    conj_tac
    >- (
      drule_then drule $ cj 1 by_super_aux_IMP_reachable >>
      disch_then $ qspec_then `EL n l` mp_tac >>
      rw[] >>
      Cases_on `n` >>
      gvs[] >>
      first_x_assum $ qspec_then `n'` mp_tac >>
      simp[]
    ) >>
    irule PATH_IMP_RTC >>
    qexists `DROP n l` >>
    simp[EL_DROP] >>
    rpt strip_tac >>
    PURE_REWRITE_TAC[GSYM arithmeticTheory.ADD_SUC] >>
    first_x_assum irule >>
    DECIDE_TAC
  ) >>
  gvs[] >>
  qpat_x_assum `by_super_aux _ _ _ _ = _` $ mp_tac o
    SRULE[Once full_by_super_aux_def] >>
  rw[AllCaseEqs()] >>
  metis_tac[]
QED

(* everything in the super list must be in the map *)
Theorem well_formed_by_super_aux:
  (∀(cl_map:'b class_map_impl) visited c (t:'a) clinfo.
    map_ok cl_map ∧ map_ok visited ∧
    super_keys_ok cl_map ⇒
    ((∃clinfo. mlmap$lookup cl_map c = SOME clinfo ∨
      (∃m. lookup visited c = SOME m)) ⇔
    (∃m. by_super_aux cl_map visited c t = SOME m))) ∧

  ∀(cl_map:'b class_map_impl) visited cs (t:'a).
    map_ok cl_map ∧ map_ok visited ∧
    super_keys_ok cl_map ⇒
    ((∀c. MEM c cs ⇒
      (∃clinfo. mlmap$lookup cl_map c = SOME clinfo ∨
      (∃m. lookup visited c = SOME m))) ⇔
    (∃m. by_super_aux_list cl_map visited cs t = SOME m))
Proof
  ho_match_mp_tac full_by_super_aux_ind >>
  rpt strip_tac
  >- (
    gvs[mlmapTheory.insert_thm] >>
    reverse $ rw[EQ_IMP_THM,Once full_by_super_aux_def]
    >- (
      qpat_x_assum `by_super_aux _ _ _ _ = _` $ mp_tac o
        SRULE[Once full_by_super_aux_def] >>
      rpt TOP_CASE_TAC
    ) >>
    rpt TOP_CASE_TAC >> gvs[] >>
    metis_tac[super_keys_ok_def]
  ) >>
  rw[Once full_by_super_aux_def] >>
  TOP_CASE_TAC >>
  gvs[super_keys_ok_def] >- metis_tac[] >>
  rename1`by_super_aux cl_map visited c t = SOME x` >>
  `map_ok x` by metis_tac[cj 1 $ cj 1 by_super_aux_monotone] >>
  iff_tac
  >- (
    strip_tac >>
    gvs[] >>
    first_x_assum $ irule o iffLR >>
    rw[]
    >- metis_tac[] >>
    first_x_assum $ qspec_then `c'` mp_tac >>
    rw[] >- metis_tac[] >>
    qexists `ARB` >>
    disj2_tac >>
    drule_then drule $ cj 1 by_super_aux_monotone >>
    metis_tac[]
  ) >>
  rpt strip_tac >- metis_tac[] >>
  gvs[] >>
  first_x_assum drule_all >>
  rw[] >- metis_tac[] >>
  drule_then drule $ cj 1 by_super_aux_IMP_reachable >>
  disch_then drule >>
  rw[GSYM mlmapTheory.lookup_thm]
  >- (
    pop_assum $ mp_tac o SRULE[Once RTC_CASES2] >>
    rw[] >>
    metis_tac[]
  ) >>
  metis_tac[]
QED

Definition by_super_def:
  by_super cl_map (c,t) =
    by_super_aux cl_map (empty mlstring$compare) c t
End

Theorem lookup_empty:
  map_ok (empty cmp: ('a,'b) mlmap$map) ⇒
  lookup (empty cmp: ('a,'b) mlmap$map) k = NONE
Proof
  simp[mlmapTheory.lookup_thm,mlmapTheory.empty_thm]
QED

Theorem by_super_thm:
  by_super cl_map (c,t) = SOME visited ⇒
  (∀s v. (mlmap$lookup visited s = SOME v) ⇔
    (v = t ∧ super_reachable_RTC cl_map c s))
Proof
  simp[super_reachable_RTC_def,by_super_def] >>
  strip_tac >>
  `map_ok (empty mlstring$compare)` by
    simp[mlmapTheory.empty_thm,mlstringTheory.TotOrd_compare] >>
  simp[EQ_IMP_THM,FORALL_AND_THM] >>
  conj_asm1_tac
  >- (
    rw[]
    >- (
      (drule_then $ drule_then irule) $
        cj 1 by_super_aux_lookup_preserve_type >>
      simp[lookup_empty] >>
      metis_tac[]
    ) >>
    drule_all $ cj 1 by_super_aux_IMP_reachable >>
    simp[lookup_empty]
  ) >>
  drule_then drule $ cj 1 super_reachable_IMP_by_super_aux >>
  simp[lookup_empty] >>
  rw[] >>
  first_x_assum drule >>
  metis_tac[]
QED

Theorem well_formed_by_super:
  ∀cl_map c (t:'a) clinfo.
    map_ok cl_map ∧ super_keys_ok cl_map ⇒
    ((∃clinfo. mlmap$lookup cl_map c = SOME clinfo) ⇔
    (∃m. by_super cl_map (c,t) = SOME m))
Proof
  rw[by_super_def] >>
  (drule_then $ drule_at_then (Pos last) $
    qspecl_then [`empty mlstring$compare`,`c`,`t`] mp_tac) $
    cj 1 well_formed_by_super_aux >>
  rw[mlmapTheory.lookup_thm,mlmapTheory.empty_thm,
    mlstringTheory.TotOrd_compare]
QED

Definition lookup_inst_map_def:
  lookup_inst_map inst_map c t =
  do
    (tcons,targs) <- split_ty_cons t;
    inst_info <- lookup inst_map (c,tcons,LENGTH targs);
    return (inst_info.impls, MAP (I ## flip EL targs) inst_info.cstr)
  od
End

Definition by_inst_def:
  by_inst inst_map c t = OPTION_MAP SND $ lookup_inst_map inst_map c t
End

Theorem lookup_inst_map_tcons_to_type:
  lookup_inst_map inst_map c t = SOME (impl,cstr) ⇔
  (∃tcons targs inst_info.
    t = tcons_to_type tcons targs ∧
    lookup inst_map (c,tcons,LENGTH targs) =
      SOME inst_info ∧
    impl = inst_info.impls ∧
    cstr = MAP (I ## (λv. EL v $ ty_args t)) inst_info.cstr)
Proof
  rw[lookup_inst_map_def,EQ_IMP_THM,EXISTS_PROD]
  >- (
    drule_then (assume_tac o GSYM) tcons_to_type_split_ty_cons >>
    first_assum $ irule_at (Pos hd) >>
    simp[MAP_EQ_f,ty_args_cons_types,tcons_to_type_def,
      FORALL_PROD,ty_args_alt]
  ) >>
  irule_at (Pos hd) split_ty_cons_tcons_to_type >>
  simp[MAP_EQ_f,ty_args_cons_types,tcons_to_type_def,
    FORALL_PROD,ty_args_alt]
QED

Theorem lookup_inst_map_thm:
  lookup_inst_map inst_map c t = SOME (impl,cstr) ⇔
  (∃tcons inst_info.
    head_ty_cons t = SOME tcons ∧
    lookup inst_map (c,tcons,LENGTH $ ty_args t) =
      SOME inst_info ∧
    impl = inst_info.impls ∧
    cstr = MAP (I ## (λv. EL v $ ty_args t)) inst_info.cstr)
Proof
  rw[lookup_inst_map_def,EQ_IMP_THM,
    split_ty_cons_thm,EXISTS_PROD] >>
  gvs[combinTheory.C_DEF]
QED

Theorem by_inst_lem:
  ∀inst_map c t cstr.
  by_inst inst_map c t = SOME cstr ⇔
  (∃tcons inst_info.
    head_ty_cons t = SOME tcons ∧
    lookup inst_map (c,tcons,LENGTH $ ty_args t) =
      SOME inst_info ∧
    cstr = MAP (I ## (λv. EL v $ ty_args t)) inst_info.cstr)
Proof
  rw[by_inst_def,EQ_IMP_THM,EXISTS_PROD] >>
  gvs[lookup_inst_map_thm]
QED

(* Every type variable in the context is in the rhs *)
Definition well_scoped_inst_map_def:
  well_scoped_inst_map (inst_map:'a inst_map_impl) =
  (∀class tycons n inst_info c v.
    lookup inst_map (class,tycons,n) = SOME inst_info ∧
    MEM (c,v) inst_info.cstr ⇒
    v < n)
End

Theorem inst_map_abs_rel_IMP_well_scoped_inst_map:
  inst_map_abs_rel inst_map_impl inst_map_abs ∧
  instance_list_kind_ok tds clk inst_map_abs ⇒
  well_scoped_inst_map inst_map_impl
Proof
  rw[inst_map_abs_rel_def,well_scoped_inst_map_def] >>
  last_x_assum drule >>
  rw[inst_abs_rel_def] >>
  drule $ SRULE[EVERY_MEM] $ iffLR instance_list_kind_ok_def >>
  disch_then drule >>
  rw[instance_kind_ok_def,entailment_kind_ok_def,
    instance_to_entailment_def] >>
  drule $ iffLR EVERY_MEM >>
  simp[MEM_MAP,PULL_EXISTS] >>
  disch_then drule >>
  rw[] >>
  drule kind_ok_IMP_freetyvars_ok >>
  simp[freetyvars_ok_def]
QED

Theorem by_inst_subst:
  well_scoped_inst_map inst_map ∧
  by_inst inst_map c t = SOME ps ⇒
  by_inst inst_map c (subst_db skip ts t) =
    SOME (MAP (λ(c,t). (c,subst_db skip ts t)) ps)
Proof
  simp[by_inst_def,lookup_inst_map_def,EXISTS_PROD] >>
  rw[split_ty_cons_thm,head_ty_cons_eq_head_ty] >>
  simp[subst_db_head_ty,subst_db_ty_args,MAP_MAP_o,
    combinTheory.o_DEF,lambdify PAIR_MAP,LAMBDA_PROD] >>
  rw[MAP_EQ_f] >>
  pairarg_tac >> gvs[] >>
  drule_all $ iffLR well_scoped_inst_map_def >>
  simp[EL_MAP]
QED

Inductive full_entail:
[~mem:]
  MEM p ps ⇒ full_entail cl_map inst_map ps p
[~super:]
  full_entail cl_map inst_map ps (c,t) ∧
  lookup cl_map c = SOME cl ∧
  MEM s cl.supers ⇒
  full_entail cl_map inst_map ps (s,t)
[~inst:]
  by_inst inst_map c t = SOME qs ∧
  (∀q. MEM q qs ⇒ full_entail cl_map inst_map ps q) ⇒
  full_entail cl_map inst_map ps (c,t)
End

Inductive entail:
[~super:]
  MEM (c,t) ps ∧
  super_reachable_RTC cl_map c s ⇒
  entail cl_map inst_map ps (s,t)
[~inst:]
  by_inst inst_map c t = SOME qs ∧
  (∀q. MEM q qs ⇒ entail cl_map inst_map ps q) ⇒
  entail cl_map inst_map ps (c,t)
End

Theorem entail_strong_ind:
  ∀cl_map inst_map ps entail'.
    (∀c s t.
      MEM (c,t) ps ∧ super_reachable_RTC cl_map c s ⇒ entail' (s,t)) ∧
    (∀c qs t.
      by_inst inst_map c t = SOME qs ∧ (∀q. MEM q qs ⇒
        entail cl_map inst_map ps q ∧ entail' q) ⇒
      entail' (c,t)) ⇒
  ∀a0. entail cl_map inst_map ps a0 ⇒ entail' a0
Proof
  rpt gen_tac >>
  strip_tac >>
  `∀a0. entail cl_map inst_map ps a0 ⇒
    entail' a0 ∧ entail cl_map inst_map ps a0` suffices_by rw[] >>
  ho_match_mp_tac entail_ind >>
  rw[]
  >- metis_tac[]
  >- drule_all_then irule entail_super >>
  irule entail_inst >>
  rw[]
QED

Theorem entail_tsubst:
  well_scoped_inst_map inst_map ⇒
  ∀p. entail cl_map inst_map ps p ⇒
  ∀c t ts. p = (c,t) ⇒
  entail cl_map inst_map (MAP (λ(c',t'). (c',tsubst ts t')) ps) (c,tsubst ts t)
Proof
  strip_tac >>
  ho_match_mp_tac entail_ind >>
  rw[]
  >- (
    irule entail_super >>
    simp[MEM_MAP,PULL_EXISTS] >>
    first_assum $ irule_at (Pos last) >>
    first_assum $ irule_at (Pos last) >>
    simp[]
  ) >>
  irule entail_inst >>
  qexists `MAP (λ(c',t'). (c',tsubst ts t')) qs` >>
  rw[MEM_MAP]
  >- (
    first_x_assum $ drule_then strip_assume_tac >>
    pairarg_tac >>
    gvs[]
  ) >>
  gvs[by_inst_subst]
QED

Theorem full_entail_tsubst:
  well_scoped_inst_map inst_map ⇒
  ∀p. full_entail cl_map inst_map ps p ⇒
  ∀c t ts. p = (c,t) ⇒
  full_entail cl_map inst_map (MAP (λ(c',t'). (c',tsubst ts t')) ps) (c,tsubst ts t)
Proof
  strip_tac >>
  ho_match_mp_tac full_entail_ind >>
  rw[]
  >- (
    irule full_entail_mem >>
    simp[MEM_MAP] >>
    first_x_assum $ irule_at (Pos last) >>
    simp[]
  )
  >- (
    irule full_entail_super >>
    first_assum $ irule_at (Pos last) >>
    first_assum $ irule_at (Pos last) >>
    simp[]
  ) >>
  irule full_entail_inst >>
  qexists `MAP (λ(c',t'). (c',tsubst ts t')) qs` >>
  rw[MEM_MAP]
  >- (
    first_x_assum $ drule_then strip_assume_tac >>
    pairarg_tac >>
    gvs[]
  ) >>
  gvs[by_inst_subst]
QED

(* `entail` is equivalent to `full_entail`
* if for every instance in inst_map,
* the constraint ps for the instance (c,t)
* `entail`s (s,t) for all super class s of c *)
Definition entail_wf_def:
  entail_wf cl_map inst_map ⇔
  ∀c tcons n inst clinfo s.
    lookup inst_map (c,tcons,n) = SOME inst ∧
    lookup cl_map c = SOME clinfo ∧ MEM s clinfo.supers ⇒
    ∃inst'. lookup inst_map (s,tcons,n) = SOME inst' ∧
      (∀cl v. MEM (cl,v) inst'.cstr ⇒
        ∃scl. MEM (scl,v) inst.cstr ∧
          super_reachable_RTC cl_map scl cl)
End

(* every class in the constraints is in cl_map *)
Definition inst_map_constraints_class_ok_def:
  inst_map_constraints_class_ok cl_map inst_map ⇔
  (∀k inst cl tyvar.
    lookup inst_map k = SOME inst ∧ MEM (cl,tyvar) inst.cstr ⇒
      ∃clinfo. lookup cl_map cl = SOME clinfo)
End

(* implementation to check if entail_wf is satified *)
Definition entail_wf_impl_def:
  entail_wf_impl cl_map inst_map ⇔
  all (λ(class,tycons,ntargs) inst.
    case lookup cl_map class of
    | NONE => T
    | SOME clinfo =>
        EVERY (λs.
          case lookup inst_map (s,tycons,ntargs) of
          | NONE => F
          | SOME inst' =>
              let supers = MAP (by_super cl_map) inst.cstr in
              EVERY (λclv.
                EXISTS (λx.
                  case x of
                  | NONE => F
                  | SOME visited =>
                      lookup visited (FST clv) = SOME (SND clv))
                supers) inst'.cstr) clinfo.supers) inst_map
End

Theorem entail_wf_impl_thm:
  map_ok cl_map ∧ map_ok inst_map ∧
  super_keys_ok cl_map ∧ inst_map_constraints_class_ok cl_map inst_map ⇒
  (entail_wf_impl cl_map inst_map ⇔
    entail_wf cl_map inst_map)
Proof
  rw[entail_wf_impl_def,all_thm,entail_wf_def,EQ_IMP_THM]
  >- (
    first_x_assum drule >>
    simp[] >>
    rw[EVERY_MEM] >>
    first_x_assum drule >>
    TOP_CASE_TAC >>
    rw[] >>
    first_x_assum drule >>
    rw[EXISTS_MEM,MEM_MAP,PULL_EXISTS] >>
    pop_assum mp_tac >>
    TOP_CASE_TAC >>
    strip_tac >>
    rename1`by_super cl_map ct = SOME _` >>
    Cases_on `ct` >>
    drule_all $ iffLR by_super_thm >>
    metis_tac[]
  ) >>
  pairarg_tac >>
  gvs[EVERY_MEM,PULL_EXISTS] >>
  TOP_CASE_TAC >>
  rpt strip_tac >>
  first_x_assum drule_all >>
  rpt strip_tac >>
  rw[EXISTS_MEM,MEM_MAP,PULL_EXISTS] >>
  rename1 `MEM clv inst'.cstr` >>
  Cases_on `clv` >>
  first_x_assum drule >>
  rw[] >>
  first_assum $ irule_at (Pos hd) >>
  rename1 `by_super cl_map (scl,t')` >>
  TOP_CASE_TAC
  >- (
    `∃x. by_super cl_map (scl,t') = SOME x`
      suffices_by gvs[] >>
    irule $ iffLR well_formed_by_super >>
    simp[] >>
    drule_then irule $
      iffLR inst_map_constraints_class_ok_def >>
    metis_tac[]
  ) >>
  drule_then irule $ iffRL by_super_thm >>
  rw[]
QED

Theorem entail_super_TypeVar:
  well_scoped_inst_map inst_map ∧
  lookup inst_map (c,tcons,ntargs) = SOME inst ∧
  lookup cl_map c = SOME clinfo ∧
  MEM s clinfo.supers ⇒
  (entail cl_map inst_map (MAP (I ## TypeVar) inst.cstr)
    (s,tcons_to_type tcons (GENLIST TypeVar ntargs)) ⇔
   ∃inst'.
    lookup inst_map (s,tcons,ntargs) = SOME inst' ∧
    ∀cl v. MEM (cl,v) inst'.cstr ⇒
      ∃scl. MEM (scl,v) inst.cstr ∧
        super_reachable_RTC cl_map scl cl)
Proof
  rw[EQ_IMP_THM]
  >- (
    reverse $ pop_assum $ strip_assume_tac o SRULE[Once entail_cases]
    >- (
      gvs[by_inst_def,lookup_inst_map_def,
        split_ty_cons_tcons_to_type,MEM_MAP,PULL_EXISTS] >>
      rw[] >>
      `v < ntargs` by (
        gvs[well_scoped_inst_map_def] >>
        last_x_assum irule >>
        metis_tac[MEM_EL]
      ) >>
      first_x_assum drule >>
      rw[Once entail_cases] >>
      gvs[MEM_MAP]
      >- (goal_assum drule >> simp[]) >>
      gvs[by_inst_def,lookup_inst_map_def] >>
      rename1 `split_ty_cons _ = SOME p` >>
      Cases_on `p` >>
      gvs[split_ty_cons_thm,head_ty_cons_def]
    ) >>
    gvs[MEM_MAP] >>
    rename1 `MEM p inst.cstr` >>
    Cases_on `p` >>
    gvs[tcons_to_type_NEQ_TypeVar]
  ) >>
  irule entail_inst >>
  rw[by_inst_def,lookup_inst_map_def,EXISTS_PROD,
    split_ty_cons_tcons_to_type,MEM_MAP,PULL_EXISTS] >>
  first_x_assum drule >>
  rw[] >>
  irule entail_super >>
  simp[MEM_MAP] >>
  first_assum $ irule_at (Pos last) >>
  first_assum $ irule_at (Pos last) >>
  simp[] >>
  DEP_REWRITE_TAC[EL_GENLIST] >>
  gvs[well_scoped_inst_map_def] >>
  last_x_assum irule >>
  metis_tac[MEM_EL]
QED

Theorem entail_wf_alt:
  well_scoped_inst_map inst_map ⇒
  (entail_wf cl_map inst_map ⇔
  ∀c tcons ntargs inst clinfo s.
    lookup inst_map (c,tcons,ntargs) = SOME inst ∧
    lookup cl_map c = SOME clinfo ∧ MEM s clinfo.supers ⇒
    entail cl_map inst_map (MAP (I ## TypeVar) inst.cstr)
      (s,tcons_to_type tcons (GENLIST TypeVar ntargs)))
Proof
  rw[entail_wf_def,EQ_IMP_THM]
  >- (
    first_x_assum $ drule_then $ drule_then drule >>
    rw[] >>
    metis_tac[entail_super_TypeVar]
  ) >>
  first_x_assum $ drule_then $ drule_then drule >>
  metis_tac[entail_super_TypeVar]
QED

Triviality entail_wf_lookup_super:
  entail_wf cl_map inst_map ∧
  lookup cl_map c = SOME c' ∧
  MEM s c'.supers ∧
  lookup inst_map (c,tcons,ntargs) = SOME inst ⇒
  ∃inst'. lookup inst_map (s,tcons,ntargs) = SOME inst' ∧
    ∀cl v. MEM (cl,v) inst'.cstr ⇒
      ∃scl. MEM (scl,v) inst.cstr ∧
        super_reachable_RTC cl_map scl cl
Proof
  rw[] >>
  gvs[entail_wf_def] >>
  ntac 2 (first_x_assum drule >> rw[]) >>
  gvs[]
QED

Theorem super_reachable_RTC_trans:
  super_reachable_RTC cl_map x y ∧
  super_reachable_RTC cl_map y z ⇒
  super_reachable_RTC cl_map x z
Proof
  rw[super_reachable_RTC_CASES_super_reachable] >>
  simp[] >>
  gvs[super_reachable_def] >>
  drule_all $ cj 2 TC_RULES >>
  simp[]
QED

Theorem entail_wf_lookup_super_reachable:
  entail_wf cl_map inst_map ⇒
  ∀c s. super_reachable_RTC cl_map c s ⇒
  ∀tcons ntargs inst.
    lookup inst_map (c,tcons,ntargs) = SOME inst ⇒
  ∃inst'. lookup inst_map (s,tcons,ntargs) = SOME inst' ∧
    ∀cl v. MEM (cl,v) inst'.cstr ⇒
      ∃scl. MEM (scl,v) inst.cstr ∧
        super_reachable_RTC cl_map scl cl
Proof
  strip_tac >>
  simp[super_reachable_RTC_def] >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[]
  >- metis_tac[RTC_REFL] >>
  drule_all entail_wf_lookup_super >>
  rw[] >>
  last_x_assum drule >> rw[] >>
  rw[] >>
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  gvs[GSYM super_reachable_RTC_def] >>
  metis_tac[super_reachable_RTC_trans]
QED

Triviality entail_wf_super_reachable_RTC_aux:
  entail_wf cl_map inst_map ⇒
  ∀p. entail cl_map inst_map ps p ⇒
    ∀c t clinfo s. p = (c,t) ∧
    super_reachable_RTC cl_map c s ⇒
    entail cl_map inst_map ps (s,t)
Proof
  strip_tac >>
  ho_match_mp_tac entail_strong_ind >>
  rw[]
  >- (
    irule entail_super >>
    first_assum $ irule_at (Pos hd) >>
    drule_all_then irule super_reachable_RTC_trans
  ) >>
  gvs[IMP_CONJ_THM,FORALL_AND_THM] >>
  gvs[PULL_FORALL,AND_IMP_INTRO] >>
  (* drule_all entail_inst >> *)
  gvs[by_inst_lem,MEM_MAP,PULL_EXISTS,LAMBDA_PROD,
    GSYM PFORALL_THM,GSYM PEXISTS_THM] >>
  irule entail_inst >>
  simp[by_inst_lem,MEM_MAP,
    PULL_EXISTS,EXISTS_PROD,GSYM PFORALL_THM] >>
  drule_all entail_wf_lookup_super_reachable >>
  rw[] >>
  rw[MEM_MAP,GSYM PEXISTS_THM]
QED

Theorem entail_wf_super_reachable_RTC:
  entail_wf cl_map inst_map ∧
  entail cl_map inst_map ps (c,t) ∧
  super_reachable_RTC cl_map c s ⇒
  entail cl_map inst_map ps (s,t)
Proof
  metis_tac[entail_wf_super_reachable_RTC_aux]
QED

Theorem entail_wf_super_reachable:
  entail_wf cl_map inst_map ∧
  entail cl_map inst_map ps (c,t) ∧
  super_reachable cl_map c s ⇒
  entail cl_map inst_map ps (s,t)
Proof
  rw[] >>
  (drule_then $ drule_then irule)
    entail_wf_super_reachable_RTC >>
  simp[super_reachable_RTC_CASES_super_reachable]
QED

Theorem super_reachable_IMP_full_entail:
  ∀c s. super_reachable cl_map c s ⇒
  MEM (c,t) ps ⇒
  full_entail cl_map inst_map ps (s,t)
Proof
  simp[super_reachable_def] >>
  ho_match_mp_tac TC_INDUCT_RIGHT1 >>
  rw[]
  >- (
    irule full_entail_super >>
    first_assum $ irule_at (Pos hd) >>
    simp[] >>
    drule_then irule full_entail_mem
  ) >>
  gvs[] >>
  irule full_entail_super >>
  first_assum $ irule_at (Pos hd) >>
  simp[]
QED

Theorem entail_EQ_full_entail:
  entail_wf cl_map inst_map ⇒
  ∀p. (entail cl_map inst_map ps p ⇔ full_entail cl_map inst_map ps p)
Proof
  strip_tac >>
  simp[EQ_IMP_THM,FORALL_AND_THM] >>
  conj_tac
  >- (
    ho_match_mp_tac entail_ind >>
    rw[super_reachable_RTC_CASES_super_reachable]
    >- drule_all_then irule full_entail_mem
    >- (
      drule_all_then irule
        super_reachable_IMP_full_entail
    )
    >- drule_all_then irule full_entail_inst
  ) >>
  ho_match_mp_tac full_entail_ind >>
  rw[]
  >- (
    Cases_on `p` >>
    irule entail_super >>
    metis_tac[super_reachable_RTC_def,RTC_REFL]
  )
  >- (
    drule_then irule entail_wf_super_reachable >>
    first_assum $ irule_at (Pat `entail _ _ _ _`) >>
    simp[super_reachable_def] >>
    irule $ cj 1 TC_RULES >>
    simp[]
  )
  >- drule_all_then irule entail_inst
QED

Theorem entail_monotone:
  ∀p. entail cl_map inst_map ps p ⇒
  (∀q. MEM q ps ⇒ MEM q qs) ⇒
  entail cl_map inst_map qs p
Proof
  ho_match_mp_tac entail_ind >>
  rw[]
  >- (irule entail_super >> metis_tac[]) >>
  irule entail_inst >> metis_tac[]
QED

Theorem full_entail_monotone:
  ∀p. full_entail cl_map inst_map ps p ⇒
  (∀q. MEM q ps ⇒ MEM q qs) ⇒
  full_entail cl_map inst_map qs p
Proof
  ho_match_mp_tac full_entail_ind >>
  rw[]
  >- (irule full_entail_mem >> metis_tac[])
  >- (irule full_entail_super >> metis_tac[]) >>
  irule full_entail_inst >> metis_tac[]
QED

Theorem full_entail_add_full_entail:
  ∀p. full_entail cl_map inst_map (q::ps) p ⇒
  full_entail cl_map inst_map ps q ⇒
  full_entail cl_map inst_map ps p
Proof
  ho_match_mp_tac full_entail_ind >>
  rw[]
  >- simp[]
  >- drule_then irule full_entail_mem
  >- (irule full_entail_super >> metis_tac[]) >>
  drule_then irule full_entail_inst >>
  rw[]
QED

(* entail_aux terminates if every q in qs is smaller than t *)
Definition entail_aux_def:
  (entail_aux supers inst_map (c,t) =
    if well_scoped_inst_map inst_map
    then
      (EXISTS (λvisited. lookup visited c = SOME t) supers ∨
      (case by_inst inst_map c t of
        | NONE => F
        | SOME qs => entail_aux_list supers inst_map qs))
    else F (* should not happen given the map is well formed *)) ∧

  (entail_aux_list supers inst_map [] = T) ∧
  (entail_aux_list supers inst_map (q::qs) =
    (entail_aux supers inst_map q ∧
     entail_aux_list supers inst_map qs))
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λx.
    (case x of
     | INR (_,_,qs) => list_max $ MAP (type_size o SND) qs
     | INL (_,_,_,t) => type_size t),
    (case x of
     | INR (_,_,qs) => LENGTH qs
     | INL _ => 0))` >>
  rw[]
  >- (
    gvs[by_inst_def,lookup_inst_map_def] >>
    pairarg_tac >> gvs[] >>
    PURE_REWRITE_TAC[Once $ GSYM arithmeticTheory.GREATER_DEF] >>
    irule list_max_intro >>
    simp[EVERY_MAP,arithmeticTheory.GREATER_DEF,type_size_GT_0] >>
    drule_then (assume_tac o GSYM) tcons_to_type_split_ty_cons >>
    gvs[EVERY_EL] >>
    rw[] >>
    gvs[well_scoped_inst_map_def] >>
    last_x_assum $ drule_then strip_assume_tac >>
    irule type_size_tcons_to_type >>
    Cases_on `EL n inst_info.cstr` >>
    gvs[] >>
    rename1 `EL n inst_info.cstr = (a,b)` >>
    first_x_assum $ qspecl_then [`a`,`b`] mp_tac >>
    metis_tac[MEM_EL]
  ) >>
  simp[GSYM arithmeticTheory.LE_LT,list_max_def]
End

Definition entail_impl_def:
  entail_impl cl_map inst_map ps (c,t) =
   case OPT_MMAP (by_super cl_map) ps of
   | NONE => F
   | SOME visiteds => entail_aux visiteds inst_map (c,t)
End

Theorem entail_aux_list_EVERY:
  entail_aux_list supers inst_map = EVERY (entail_aux supers inst_map)
Proof
  rw[FUN_EQ_THM] >>
  rename1 `entail_aux_list _ _ l` >>
  Induct_on `l` >>
  simp[entail_aux_def]
QED

Theorem entail_aux_induct_EVERY:
  ∀P.
  (∀(supers:(mlstring,type) map list) inst_map c t.
    (∀qs q.
      well_scoped_inst_map inst_map ∧
      by_inst inst_map c t = SOME qs ∧ MEM q qs ⇒
      P supers inst_map q) ⇒
    P supers inst_map (c,t)) ⇒
    (∀supers inst_map p. P supers inst_map p)
Proof
  ntac 2 strip_tac >>
  qspecl_then [`P`,`λv0 v1 v2. ∀q. MEM q v2 ⇒ P v0 v1 q`]
    mp_tac entail_aux_ind >>
  impl_tac >>
  rw[] >>
  metis_tac[]
QED

Theorem OPT_MMAP_SOME_EL:
  ∀l fl. OPT_MMAP f l = SOME fl ⇒
  LENGTH fl = LENGTH l ∧
  (∀n. n < LENGTH l ⇒ f (EL n l) = SOME (EL n fl))
Proof
  Induct_on `l` >>
  rw[OPT_MMAP_def] >>
  gvs[] >>
  Cases_on `n` >>
  simp[]
QED

Theorem OPT_MMAP_NONE:
  ∀l. OPT_MMAP f l = NONE ⇒
  ∃x. MEM x l ∧ f x = NONE
Proof
  Induct_on `l` >>
  rw[OPT_MMAP_def] >>
  metis_tac[]
QED

Theorem entail_aux_thm:
  ∀supers inst_map p cl_map ps.
  map_ok cl_map ∧ map_ok inst_map ∧
  well_scoped_inst_map inst_map ∧ super_keys_ok cl_map ∧
  (∀q. MEM q ps ⇒ ∃clinfo. lookup cl_map (FST q) = SOME clinfo) ∧
  (LENGTH supers = LENGTH ps) ∧
  (∀n. n < LENGTH ps ⇒
    by_super cl_map (EL n ps) = SOME (EL n supers)) ⇒
  (entail_aux supers inst_map p ⇔
    entail cl_map inst_map ps p)
Proof
  ho_match_mp_tac entail_aux_induct_EVERY >>
  rw[] >>
  gvs[AND_IMP_INTRO,cj 1 PULL_FORALL] >>
  last_x_assum $ drule_at (Pos last) >>
  rw[] >>
  simp[entail_aux_def] >>
  rw[EQ_IMP_THM]
  >- (
    gvs[EXISTS_MEM] >>
    qpat_x_assum `MEM visited supers` $
      strip_assume_tac o SRULE[MEM_EL] >>
    gvs[] >>
    first_x_assum $ drule_then assume_tac >>
    Cases_on `EL n ps` >>
    drule_all $ iffLR by_super_thm >>
    rw[] >>
    irule entail_super >>
    metis_tac[MEM_EL]
  )
  >- (
    pop_assum mp_tac >>
    TOP_CASE_TAC >>
    rw[entail_aux_list_EVERY,EVERY_MEM] >>
    irule entail_inst >>
    simp[]
  ) >>
  reverse $ pop_assum $ strip_assume_tac o SRULE[Once entail_cases]
  >- simp[entail_aux_list_EVERY,EVERY_MEM] >>
  qpat_x_assum `MEM _ ps` $
    strip_assume_tac o GSYM o SRULE[MEM_EL] >>
  first_x_assum $ drule_then assume_tac >>
  gvs[EXISTS_MEM] >>
  drule_then strip_assume_tac $
    SRULE[DISJ_IMP_THM,FORALL_AND_THM] $ iffRL by_super_thm >>
  metis_tac[MEM_EL]
QED

Theorem entail_impl_thm:
  map_ok cl_map ∧
  map_ok inst_map ∧
  well_scoped_inst_map inst_map ∧ super_keys_ok cl_map ∧
  (∀q. MEM q ps ⇒ ∃clinfo. lookup cl_map (FST q) = SOME clinfo) ⇒
  entail_impl cl_map inst_map ps p =
    entail cl_map inst_map ps p
Proof
  rw[oneline entail_impl_def] >>
  ntac 2 TOP_CASE_TAC
  >- (
    dxrule_then strip_assume_tac OPT_MMAP_NONE >>
    first_assum $ drule_then strip_assume_tac >>
    spose_not_then kall_tac >>
    `∃y. by_super cl_map x = SOME y`
      suffices_by gvs[] >>
    Cases_on `x` >>
    irule $ SRULE[PULL_EXISTS] $ iffLR well_formed_by_super >>
    gvs[]
  ) >>
  dxrule_then strip_assume_tac OPT_MMAP_SOME_EL >>
  irule entail_aux_thm >>
  rw[]
QED

Theorem entail_impl_full_entail:
  map_ok cl_map ∧ map_ok inst_map ∧
  well_scoped_inst_map inst_map ∧ super_keys_ok cl_map ∧
  entail_wf cl_map inst_map ∧
  (∀q. MEM q ps ⇒ ∃clinfo. lookup cl_map (FST q) = SOME clinfo) ⇒
  entail_impl cl_map inst_map ps p =
    full_entail cl_map inst_map ps p
Proof
  metis_tac[entail_impl_thm,entail_EQ_full_entail]
QED

(* full_entail is an implmentation of has_dict, when the ie is
* generated by the superclasses in cl_map_impl and
* instances in inst_map_impl *)
Theorem full_entail_IMP_has_dict:
  class_map_kind_ok tds cl_map_abs ∧
  instance_list_kind_ok tds clk inst_map_abs ∧
  class_map_super_abs_rel cl_map_impl cl_map_abs ∧
  inst_map_abs_rel inst_map_impl inst_map_abs ∧
  EVERY (λ(c,t). ∃k. clk c = SOME k ∧ kind_ok tds ks k t) lie ∧
  clk = class_map_to_clk cl_map_abs ∧
  ie = set (MAP SND (class_map_to_ie cl_map_abs)) ∪
    set (MAP SND (instance_list_to_ie inst_map_abs)) ∧
  lie_set = set lie
  ⇒
  ∀p. full_entail cl_map_impl inst_map_impl lie p ⇒
    ∀k. clk (FST p) = SOME k ∧ kind_ok tds ks k (SND p) ⇒
  has_dict tds ks ie lie_set p
Proof
  strip_tac >>
  ho_match_mp_tac full_entail_strongind >>
  rw[super_reachable_RTC_CASES_super_reachable]
  >- drule_then irule has_dict_lie
  >- (
    irule has_dict_ie >>
    irule_at (Pat `_ ∈ _`) $ cj 1 $
      PURE_REWRITE_RULE[SUBSET_DEF] SUBSET_UNION >>
    gvs[MEM_MAP,PULL_EXISTS,class_map_to_ie_def,
      LIST_BIND_def,MEM_FLAT] >>
    dxrule_then (qspec_then `c` mp_tac) $
      iffLR class_map_super_abs_rel_def >>
    rw[OPTREL_def,class_super_abs_rel_def,EXTENSION] >>
    drule_then assume_tac ALOOKUP_MEM >>
    first_assum $ irule_at (Pat `MEM _ cl_map_abs`) >>
    gvs[MEM_MAP,class_to_entailments_def,PULL_EXISTS,
      EXISTS_PROD] >>
    first_assum $ irule_at (Pat `MEM _ _.supers`) >>
    simp[specialises_inst_def,PULL_EXISTS,subst_db_def,
      EXISTS_PROD] >>
    conj_tac
    >- (
      gvs[class_map_kind_ok_def] >>
      last_x_assum drule >>
      simp[super_classes_def,EVERY_MAP] >>
      rw[EVERY_MEM] >>
      first_x_assum drule >>
      rw[] >> gvs[class_map_to_clk_def]
    ) >>
    irule has_dict_dicts >>
    rw[] >>
    first_x_assum irule >>
    gvs[class_map_to_clk_def] >>
    drule $ iffLR class_map_kind_ok_def >>
    rw[] >>
    pop_assum drule >>
    simp[super_classes_def,EVERY_MAP] >>
    rw[EVERY_MEM] >>
    first_x_assum drule >>
    rw[class_map_to_clk_def] >>
    gvs[]
  ) >>
  irule has_dict_ie >>
  irule_at (Pat `_ ∈ _`) $ cj 2 $
    PURE_REWRITE_RULE[SUBSET_DEF] SUBSET_UNION >>
  gvs[MEM_MAP,PULL_EXISTS,instance_list_to_ie_def] >>
  gvs[by_inst_def] >>
  rename1 `lookup_inst_map _ _ _ = SOME q` >>
  PairCases_on `q` >>
  gvs[lookup_inst_map_tcons_to_type,MEM_MAP,PULL_EXISTS] >>
  drule_then drule $ cj 1 $ iffLR inst_map_abs_rel_def >>
  rw[inst_abs_rel_def,instance_list_to_ie_def,MEM_MAP,
    PULL_EXISTS] >>
  first_assum $ irule_at (Pat `MEM _ inst_map_abs`) >>
  qexists_tac `MAP (I ## flip EL targs) inst_info.cstr` >>
  simp[instance_to_entailment_def,specialises_inst_def,
    PULL_EXISTS,EVERY2_MAP,LAMBDA_PROD] >>
  gvs[tcons_to_type_def,subst_db_cons_types,subst_db_def,
    cons_types_Atom_EQ] >>
  qexists `targs` >>
  gvs[kind_ok_cons_types] >>
  drule $ iffLR instance_list_kind_ok_def >>
  disch_then $ drule o SRULE[EVERY_MEM] >>
  simp[instance_kind_ok_def,instance_to_entailment_def,
    entailment_kind_ok_def,EVERY_MAP,kind_ok_cons_types] >>
  strip_tac >>
  `kind_arrows ks' k = kind_arrows ks'' k`
  by (
    Cases_on `tcons` >>
    gvs[kind_ok] >>
    rename1 `Atom (TypeCons (INR builtin_ty))` >>
    Cases_on `builtin_ty` >>
    gvs[kind_ok] >>
    rename1 `Atom (CompPrimTy comp)` >>
    Cases_on `comp` >>
    gvs[kind_ok]
  ) >>
  gvs[kind_arrows_ret_EQ] >>
  `abs.kinds = ks'`
  by (
    gvs[LIST_REL_EL_EQN] >>
    rw[LIST_EQ_REWRITE] >>
    first_x_assum drule >>
    simp[kind_ok,LLOOKUP_THM]
  ) >>
  rw[LIST_EQ_REWRITE,SF ETA_ss]
  >- simp[EL_MAP,subst_db_def]
  >- (
    irule EVERY2_refl >>
    simp[FORALL_PROD] >>
    rpt strip_tac >>
    rename1 `MEM (cstr_c,cstr_t) inst_info.cstr` >>
    `cstr_t < LENGTH targs` suffices_by simp[] >>
    drule $ iffLR instance_list_kind_ok_def >>
    rw[EVERY_MEM] >>
    first_x_assum drule >>
    simp[instance_kind_ok_def,entailment_kind_ok_def,
      instance_to_entailment_def] >>
    rw[EVERY_MAP] >>
    drule_then drule $ iffLR EVERY_MEM >>
    rw[] >>
    drule kind_ok_IMP_freetyvars_ok >>
    simp[freetyvars_ok_def]
  )
  >- (
    irule has_dict_dicts >>
    rw[MEM_MAP] >>
    last_x_assum drule >>
    rw[MAP_MAP_o,combinTheory.o_DEF,ty_args_alt,
      ty_args_cons_types,combinTheory.C_DEF] >>
    simp[GSYM instance_to_entailment_def] >>
    first_x_assum irule >>
    drule_then drule $ iffLR EVERY_MEM >>
    simp[LAMBDA_PROD] >>
    pairarg_tac >> simp[] >>
    pairarg_tac >> gvs[] >>
    rw[kind_ok,LLOOKUP_THM] >>
    gvs[LIST_REL_EL_EQN]
  )
QED

Theorem has_dict_IMP_full_entail:
  ALL_DISTINCT (MAP FST cl_map_abs) ∧
  class_map_kind_ok tds cl_map_abs ∧
  instance_list_kind_ok tds clk inst_map_abs ∧
  class_map_super_abs_rel cl_map_impl cl_map_abs ∧
  inst_map_abs_rel inst_map_impl inst_map_abs ∧
  EVERY (λ(c,t). ∃k. clk c = SOME k ∧ kind_ok tds ks k t) lie ∧
  clk = class_map_to_clk cl_map_abs ∧
  ie = set (MAP SND (class_map_to_ie cl_map_abs)) ∪
    set (MAP SND (instance_list_to_ie inst_map_abs)) ∧
  lie_set = set lie
  ⇒
  (∀p. has_dict tds ks ie lie_set p ⇒
    ∀k. clk (FST p) = SOME k ∧ kind_ok tds ks k (SND p) ⇒
  full_entail cl_map_impl inst_map_impl lie p) ∧
  (∀ps. has_dicts tds ks ie lie_set ps ⇒
    ∀p k. MEM p ps ∧
      clk (FST p) = SOME k ∧ kind_ok tds ks k (SND p) ⇒
    full_entail cl_map_impl inst_map_impl lie p)
Proof
  strip_tac >>
  ho_match_mp_tac has_dict_ind >>
  rw[]
  >- drule_then irule full_entail_mem
  >- ( (* super class *)
    gvs[MEM_MAP,PULL_EXISTS,class_map_to_ie_def,LIST_BIND_def,
      MEM_FLAT] >>
    drule $ iffLR class_map_kind_ok_def >>
    simp[] >>
    rename1 `MEM cl cl_map_abs` >>
    PairCases_on `cl` >>
    disch_then drule >>
    drule $ iffLR class_map_super_abs_rel_def >>
    drule_all_then strip_assume_tac ALOOKUP_ALL_DISTINCT_MEM >>
    disch_then $ qspec_then `cl0` mp_tac >>
    rw[OPTREL_def,super_classes_def,EVERY_MAP,EXTENSION,
      class_super_abs_rel_def] >>
    gvs[class_to_entailments_def,MEM_MAP,PULL_EXISTS,
      EXISTS_PROD,specialises_inst_def] >>
    qpat_x_assum `EVERY _ _.supers` $ drule o SRULE[EVERY_MEM] >>
    strip_tac >>
    PairCases_on `p` >>
    gvs[] >>
    irule full_entail_super >>
    first_assum $ irule_at (Pat `lookup _ _ = _`) >>
    gvs[subst_db_def] >>
    first_assum $ irule_at (Pos hd) >>
    first_x_assum irule >>
    gvs[class_map_to_clk_def]
  )
  >- ( (* instance *)
    Cases_on `p` >>
    gvs[MEM_MAP,PULL_EXISTS,instance_list_to_ie_def,
      instance_to_entailment_def,specialises_inst_def] >>
    irule full_entail_inst >>
    irule_at Any by_inst_subst >>
    drule_all inst_map_abs_rel_IMP_well_scoped_inst_map >>
    drule_then drule $ cj 2 $ iffLR inst_map_abs_rel_def >>
    rw[inst_abs_rel_def] >>
    simp[by_inst_def,lookup_inst_map_def,
      split_ty_cons_tcons_to_type] >>
    simp[MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
    rpt strip_tac >>
    drule_all_then assume_tac $ iffLR well_scoped_inst_map_def >>
    first_x_assum irule >>
    gvs[EXISTS_PROD,tcons_to_type_def,subst_db_cons_types,
      kind_ok_cons_types,EVERY2_MAP,LAMBDA_PROD,EL_GENLIST] >>
    strip_tac
    >- (
      drule_all LIST_REL_MEM_IMP >>
      simp[EXISTS_PROD]
    ) >>
    drule $ iffLR instance_list_kind_ok_def >>
    disch_then $ drule o SRULE[EVERY_MEM] >>
    simp[instance_kind_ok_def,entailment_kind_ok_def,
      instance_to_entailment_def] >>
    rw[EVERY_MAP,LAMBDA_PROD] >>
    drule_then drule $ iffLR EVERY_MEM >>
    rw[] >>
    simp[] >>
    irule kind_ok_subst_db >>
    simp[] >>
    first_assum $ irule_at (Pat `kind_ok _ _ _ _`) >>
    rw[]
    >- (
      gvs[LIST_REL_EL_EQN] >>
      last_x_assum drule >>
      gvs[LLOOKUP_THM]
    ) >>
    gvs[LIST_REL_EL_EQN,LLOOKUP_THM]
  )
QED

