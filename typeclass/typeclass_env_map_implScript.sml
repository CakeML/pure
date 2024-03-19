(* concrete data structures for implementing
* instance map and type class map *)
open HolKernel Parse boolLib bossLib dep_rewrite BasicProvers;
open relationTheory set_relationTheory;
open pairTheory optionTheory listTheory pred_setTheory finite_mapTheory
open mlmapTheory mlstringTheory balanced_mapTheory alistTheory;
open miscTheory typeclass_unificationTheory
typeclass_inference_commonTheory topological_sortTheory typeclass_tcexpTheory;

val _ = new_theory "typeclass_env_map_impl";

Datatype:
  classinfo_impl =
    <| super : mlstring list
     ; kind : Kind option
     ; methodsig : (cvname, PredType) mlmap$map
     ; minImp : minImplAST
     ; defaults : (cvname, tcexp) mlmap$map |>
End

Datatype:
  instinfo_impl =
    <| cstr : (mlstring # num) list (* class and type variable*)
     ; impl : (cvname, tcexp) mlmap$map |> (* function name and its expression *)
End

Type class_map_impl = ``:(mlstring, classinfo_impl) map``;
Type inst_map_impl = ``:(mlstring, (type # instinfo_impl) list) map``;

Definition to_class_map_def:
  to_class_map (m:class_map_impl) = FMAP_MAP2 (λ(k,x).
    <| super := x.super
     ; kind := x.kind
     ; methodsig := to_fmap x.methodsig
     ; minImp := x.minImp
     ; defaults := to_fmap x.defaults |>) (to_fmap m)
End

Definition to_inst_map_def:
  to_inst_map (m:inst_map_impl) =
    FMAP_MAP2 (λ(k1,l).
      MAP (λ(k2,x). (k2, <|cstr := x.cstr; impl := to_fmap x.impl|>)) l)
    (to_fmap m)
End

Definition lookup_inst_map_def:
  lookup_inst_map (m:inst_map_impl) cl ty =
    OPTION_BIND (lookup m cl) (λl. ALOOKUP l ty)
End

Definition add_instance_def:
  add_instance (inst_map:inst_map_impl) cl ty info =
    case lookup inst_map cl of
      | NONE => SOME $ insert inst_map cl [(ty,info)]
      | SOME l =>
        (case ALOOKUP l ty of
          | NONE => SOME $ insert inst_map cl ((ty,info)::l)
          | _ => NONE)
End

(* check if there is cyclic superclass relation *)
Definition superAList_def:
  superAList cl_map =
    MAP (λ(k,v). (k, v.super)) $ toAscList cl_map
End

Definition check_cl_map_no_cycles_def:
  check_cl_map_no_cycles cl_map =
    ¬has_cycle (superAList cl_map)
End

Theorem fmap_to_alist_MAP_KEYS:
  INJ f (FDOM m) UNIV ⇒
  set (fmap_to_alist (MAP_KEYS f m)) =
    set (MAP (λ(k,v). (f k,v)) $ fmap_to_alist m)
Proof
  Induct_on `m` >>
  rw[] >>
  `INJ f (FDOM m) UNIV`
  by (
    drule_then irule INJ_SUBSET >>
    simp[]
  ) >>
  drule_then (fn t => simp[t]) MAP_KEYS_FUPDATE >>
  fs[EXTENSION,LAMBDA_PROD,GSYM PFORALL_THM] >>
  rpt gen_tac >>
  simp[MEM_MAP,MEM_fmap_to_alist,
    LAMBDA_PROD,GSYM PEXISTS_THM,FLOOKUP_UPDATE] >>
  iff_tac
  >- (
    IF_CASES_TAC
    >- (
      rw[] >>
      irule_at (Pos hd) EQ_REFL >>
      simp[]) >>
    rw[MEM_MAP] >>
    pairarg_tac >>
    fs[] >>
    irule_at (Pos hd) EQ_REFL >>
    fs[FDOM_FLOOKUP,FAPPLY_FUPDATE_THM] >>
    IF_CASES_TAC >>
    fs[FLOOKUP_DEF]) >>
  fs[MEM_MAP,FAPPLY_FUPDATE_THM,LAMBDA_PROD,
    GSYM PEXISTS_THM] >>
  rw[]
  >- (
    IF_CASES_TAC >>
    fs[INJ_DEF] >>
    spose_not_then kall_tac >>
    pop_assum mp_tac >>
    simp[]) >>
  irule_at (Pos hd) EQ_REFL >>
  IF_CASES_TAC >>
  fs[FLOOKUP_DEF]
QED

Triviality set_MAP_SINGLE_FST_EQ:
  (∀x y. f x = f y ⇔ x = y) ∧
  set (MAP f x) = set (MAP f y) ⇒
  set x = set y
Proof
  simp[LIST_TO_SET_MAP] >>
  metis_tac[IMAGE_11]
QED

Triviality set_MAP_key_EQ:
  set (MAP (λ(k,v). ({k},v)) x) = set (MAP (λ(k,v). ({k},v)) y) ⇒
  set x = set y
Proof
  qpat_abbrev_tac `f=(λ(k,v). ({k},v))` >>
  strip_tac >>
  drule_at_then (Pos last) irule set_MAP_SINGLE_FST_EQ >>
  rw[Abbr`f`,EQ_IMP_THM] >>
  ntac 2 (pairarg_tac >> fs[])
QED

Theorem mlmap_toAscList:
  map_ok (m:('a,'b) map) ⇒
  SORTED (λ(x,y) (x',y'). (cmp_of m) x x' = Less) (toAscList m) ∧
  (set (toAscList m)) =
    set (fmap_to_alist (
      (to_fmap: ('a,'b) map -> ('a |-> 'b)) m))
Proof
  Cases_on `m` >>
  simp[map_ok_def,mlmapTheory.toAscList_def,cmp_of_def] >>
  strip_tac >>
  drule_then assume_tac comparisonTheory.TotOrder_imp_good_cmp >>
  drule_all balanced_mapTheory.toAscList_thm >>
  rw[] >>
  drule_then assume_tac to_fmap_thm >>
  drule_then assume_tac TotOrd_key_set >>
  fs[lift_key_def,GSYM LIST_TO_SET_MAP,MAP_KEYS_def] >>
  irule set_MAP_key_EQ >>
  qmatch_goalsub_abbrev_tac `MAP _ (fmap_to_alist m)` >>
  `INJ (λx. {x}) (FDOM m) UNIV` by simp[INJ_DEF] >>
  drule fmap_to_alist_MAP_KEYS >>
  rw[]
QED

Triviality ALL_DISTINCT_superAList:
  map_ok cl_map ⇒
  ALL_DISTINCT (MAP FST $ superAList cl_map)
Proof
  rw[superAList_def,map_fst] >>
  simp[mlmapTheory.MAP_FST_toAscList]
QED

Triviality super_reachable_EQ_TC_depends_on_weak:
  map_ok cl_map ⇒
  super_reachable (to_class_map cl_map) =
    TC_depends_on_weak (superAList cl_map)
Proof
  rw[super_reachable_def,TC_depends_on_weak_def] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM,superAList_def,map_fst,depends_on1_def] >>
  fs[to_class_map_def,FLOOKUP_FMAP_MAP2,FMAP_MAP2_THM,PULL_EXISTS] >>
  drule_then strip_assume_tac mlmap_toAscList >>
  gvs[ALOOKUP_MAP,PULL_EXISTS,EXTENSION] >>
  rw[EQ_IMP_THM]
  >- (
    drule_then assume_tac $
      cj 2 mlmapTheory.MAP_FST_toAscList >>
    drule_then assume_tac ALOOKUP_ALL_DISTINCT_MEM >>
    drule_then strip_assume_tac mlmap_toAscList >>
    fs[EXTENSION] >>
    metis_tac[]
  ) >>
  drule_then assume_tac ALOOKUP_MEM >>
  drule_then assume_tac $ cj 2 mlmap_toAscList >>
  fs[EXTENSION]
QED

Theorem check_cl_map_no_cycles_IMP_super_no_cycles:
  map_ok cl_map ∧
  check_cl_map_no_cycles cl_map ⇒
  super_no_cycles $ to_class_map cl_map
Proof
  rw[super_no_cycles_def] >>
  drule_all_then assume_tac
    super_reachable_EQ_TC_depends_on_weak >>
  drule_then assume_tac ALL_DISTINCT_superAList >>
  drule_then assume_tac has_cycle_correct2 >>
  fs[check_cl_map_no_cycles_def]
QED

(* Similar to how it is implemented in
 * "Typing Haskell in Haskell" by Mark P. Jones *)

Theorem mlmap_domain_FINITE:
  map_ok m ⇒
  FINITE {s | ∃v. mlmap$lookup m s = SOME v}
Proof
  simp[mlmapTheory.lookup_thm,flookup_thm]
QED

Triviality super_reachable_FDOM_cl_map:
  ∀c s. super_reachable m c s ⇒
  ∃x i. FLOOKUP m x = SOME i ∧ MEM s i.super 
Proof
  simp[super_reachable_def] >>
  ho_match_mp_tac TC_INDUCT >>
  simp[] >>
  metis_tac[]
QED

Theorem super_reachable_FINITE:
  map_ok cl_map ⇒
  FINITE {s | super_reachable (to_class_map cl_map) c s}
Proof
  rw[] >>
  irule SUBSET_FINITE >>
  qexists `BIGUNION (IMAGE (\info. set info.super) $
      {info | ?c. FLOOKUP (to_class_map cl_map) c = SOME info})` >>
  simp[] >>
  irule_at (Pos hd) IMAGE_FINITE >>
  rw[]
  >- (
    simp[super_reachable_def,to_class_map_def,
      FMAP_MAP2_THM,FLOOKUP_FMAP_MAP2,PULL_EXISTS] >>
    qmatch_goalsub_abbrev_tac `FINITE m` >>
    `m = IMAGE (\c. let v = to_fmap cl_map ' c in
        <|super := v.super; kind := v.kind;
          methodsig := to_fmap v.methodsig;
          minImp := v.minImp;
          defaults := to_fmap v.defaults|>)
         {c | ∃v. (FLOOKUP (to_fmap cl_map) c = SOME v)}`
      by (
        simp[Abbr`m`,IMAGE_DEF,EXTENSION,flookup_thm] >>
        metis_tac[]
      ) >>
     simp[] >>
     irule IMAGE_FINITE >>
     simp[flookup_thm]) >>
  rw[SUBSET_DEF] >>
  drule super_reachable_FDOM_cl_map >>
  rw[] >>
  metis_tac[SUBSET_DEF]
QED

Theorem super_reachable_list_FINITE:
  map_ok cl_map ⇒
  FINITE {s | ∃c. MEM c cs ∧
    (super_reachable (to_class_map cl_map) c s ∨
      c = s)}
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `FINITE X` >>
  `X = BIGUNION (set $ (MAP (λc. {s | super_reachable (to_class_map cl_map) c s ∨ c =
  s}) cs))`
    by (
      simp[Abbr`X`,BIGUNION,MEM_MAP,EXTENSION] >>
      rw[EQ_IMP_THM,PULL_EXISTS]
      >- (
        qexists_tac `\x. super_reachable (to_class_map cl_map) c x ∨ c = x` >>
        simp[IN_DEF] >>
        qexists_tac`c` >>
        fs[SUBSET_DEF,IN_DEF]
      )
      >- (
        qexists_tac `\x. super_reachable (to_class_map cl_map) c x ∨ c = x` >>
        simp[IN_DEF] >>
        qexists_tac`c` >>
        fs[SUBSET_DEF,IN_DEF]
      ) >>
      metis_tac[]
    ) >>
    rw[MEM_MAP] >>
    `{s | super_reachable (to_class_map cl_map) c s ∨ c = s} =
    {s | super_reachable (to_class_map cl_map) c s} ∪ {c}` 
      by (
        rw[EXTENSION] >>
        metis_tac[]
      ) >>
    pop_assum SUBST_ALL_TAC >>
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
    case mlmap$lookup cl_map c of
    | NONE => NONE
    | SOME clinfo =>
      case lookup visited c of
      | NONE => by_super_aux_list cl_map (insert visited c t) clinfo.super t
      | SOME _ => SOME visited
   else NONE) ∧ 
  by_super_aux_list cl_map ret [] t = SOME ret ∧
  by_super_aux_list cl_map visited (sup::xs) t =
    if map_ok cl_map ∧ map_ok visited
    then
     case lookup visited sup of
     | SOME _ => by_super_aux_list cl_map visited xs t
     | NONE =>
        case OPTION_MAP (fix_visited visited) (by_super_aux cl_map visited sup t) of
        | SOME visited' => by_super_aux_list cl_map visited' xs t
        | NONE => NONE
    else NONE
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (\x.
    ((case x of
    | INR (cl_map,(visited:(mlstring,'a)map),cs,t:'a) =>
      CARD ({s | ∃c. MEM c cs ∧ (super_reachable (to_class_map cl_map) c s ∨ c = s)}
        DIFF {s | ∃v.  lookup visited s = SOME v})
    | INL (cl_map,visited,c,t) =>
       CARD ({s | super_reachable (to_class_map cl_map) c s ∨ c = s}
        DIFF {s | ∃v. lookup visited s = SOME v})),
    (case x of
    | INR (cl_map,visited,cs,t) => LENGTH cs
    | INL (cl_map,visited,c,t) => 0)))` >>
  rw[]
  >- (
    Cases_on `?x. super_reachable (to_class_map cl_map) sup' x ∧ 
    lookup visited x = NONE ∧
    (∀c. MEM c xs ⇒
      ¬super_reachable (to_class_map cl_map) c x ∧
      c ≠ x)` >>
    rw[]
    >- (
      disj1_tac >>
      irule CARD_PSUBSET >>
      conj_tac >- (
        drule super_reachable_list_FINITE >>
        disch_then $ qspec_then `sup'::xs` assume_tac >>
        fs[]) >>
      rw[PSUBSET_DEF,SUBSET_DEF,DIFF_DEF,EXTENSION,
        PULL_EXISTS] >>
      qexists_tac`x` >>
      rw[] >>
      metis_tac[]) >>
    disj2_tac >>
    AP_TERM_TAC >>
    rw[EXTENSION,EQ_IMP_THM]
    >- metis_tac[]
    >- metis_tac[]
    >- (
      fs[] >>
      first_x_assum $ qspec_then `x` mp_tac >>
      simp[] >>
      impl_tac >- (
        Cases_on `lookup visited x` >>
        gvs[]) >>
      metis_tac[]
    ) >>
    metis_tac[]
  )
  >- (
    irule CARD_PSUBSET >>
    conj_tac
    >- (
      irule FINITE_DIFF >>
      drule super_reachable_FINITE >>
      disch_then $ qspec_then `c` assume_tac >>
      qmatch_asmsub_abbrev_tac `FINITE s` >>
      qmatch_goalsub_abbrev_tac `FINITE s'` >>
      `s' = s ∪ {c}`
      by (
        simp[Abbr`s`,Abbr`s'`,EXTENSION] >>
        metis_tac[]
      ) >>
      simp[]
    ) >>
    rw[PSUBSET_MEMBER,SUBSET_DEF,DIFF_DEF,
      mlmapTheory.lookup_insert,AllCaseEqs()]
    >- (
      fs[super_reachable_def,to_class_map_def,
        FMAP_MAP2_THM,FLOOKUP_FMAP_MAP2,PULL_EXISTS] >>
      disj1_tac >>
      irule TC_LEFT1_I >>
      first_assum $ irule_at (Pos last) >>
      fs[GSYM mlmapTheory.lookup_thm]
    )
    >- (Cases_on `c=x` >> fs[])
    >- (
      fs[super_reachable_def,to_class_map_def,
        FMAP_MAP2_THM,FLOOKUP_FMAP_MAP2,PULL_EXISTS] >>
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
      fs[]) >>
    PURE_REWRITE_TAC[DIFF_INTER_COMPL] >>
    irule INTER_PRESERVE_SUBSET >>
    conj_tac
    >- (
      rw[SUBSET_DEF] >>
      qexists_tac `c` >>
      simp[]) >>
    irule COMPL_SUBSET >>
    simp[SUBSET_DEF,PULL_EXISTS] >>
    simp[fix_visited_def] >>
    IF_CASES_TAC >>
    metis_tac[]
  ) >>
  simp[GSYM arithmeticTheory.LE_LT] >>
  irule CARD_SUBSET >>
  conj_tac
  >- (
    irule FINITE_DIFF >>
    drule_then (qspec_then `sup'::xs` assume_tac)
      super_reachable_list_FINITE >>
    fs[]) >>
  PURE_REWRITE_TAC[DIFF_INTER_COMPL] >>
  irule INTER_PRESERVE_SUBSET >>
  simp[SUBSET_DEF] >> metis_tac[]
End

Theorem by_super_aux_monotone:
  (∀cl_map visited c (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux cl_map visited c t = SOME new_visited ⇒
      map_ok new_visited ∧
    (∀c' t. lookup visited c' = SOME t ⇒
      lookup new_visited c' = SOME t)) ∧

  (∀cl_map visited cs (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux_list cl_map visited cs t = SOME new_visited ⇒
      map_ok new_visited ∧
    (∀c' t. lookup visited c' = SOME t ⇒
        lookup new_visited c' = SOME t))
Proof
  PURE_REWRITE_TAC[super_reachable_def] >>
  simp[to_class_map_def,FLOOKUP_FMAP_MAP2,FMAP_MAP2_THM,
    PULL_EXISTS,GSYM $ mlmapTheory.lookup_thm] >>
  ho_match_mp_tac by_super_aux_ind >>
  reverse $ rpt conj_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >>
  pop_assum $ mp_tac o SRULE[Once by_super_aux_def]
  >- (
    rpt TOP_CASE_TAC >>
    fs[] >>
    strip_tac >>
    fs[] >>
    gvs[] >>
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
         map_ok cl_map ∧ map_ok visited ∧
         lookup cl_map c = SOME clinfo ∧ lookup visited c = NONE ⇒
         P1 cl_map (insert visited c t) clinfo.super t) ⇒
      P0 cl_map visited c t) ∧ (∀cl_map ret t. P1 cl_map ret [] t) ∧
   (∀cl_map visited sup xs t.
     (∀v. map_ok cl_map ∧ map_ok visited ∧ lookup visited sup = SOME v ⇒
          P1 cl_map visited xs t) ∧
     (∀visited'.
        map_ok cl_map ∧ map_ok visited ∧ lookup visited sup = NONE ∧
        by_super_aux cl_map visited sup t = SOME visited' ⇒
        P1 cl_map visited' xs t) ∧
     (map_ok cl_map ∧ map_ok visited ∧ lookup visited sup = NONE ⇒
      P0 cl_map visited sup t) ⇒
      P1 cl_map visited (sup::xs) t) ⇒
  (∀v0 v1 v2 v3. P0 v0 v1 v2 v3) ∧
   ∀v0 v1 v2 v3. P1 v0 v1 v2 v3
Proof
  rpt gen_tac >>
  strip_tac >>
  irule by_super_aux_ind >>
  rw[] >>
  metis_tac[fix_visited_by_super_aux]
QED

Theorem by_super_aux_lookup_preserve_type:
  (∀cl_map visited c (t:'a) new_visited.
  map_ok visited ∧
  by_super_aux cl_map visited c t = SOME new_visited ∧
  (∀c' v. lookup visited c' = SOME v ⇒ v = t) ⇒
  (∀c v. lookup new_visited c = SOME v ⇒ v = t)) ∧

  (∀cl_map visited cs (t:'a) new_visited.
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
    ntac 2 TOP_CASE_TAC
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
  TOP_CASE_TAC
  >- (
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
  ) >>
  metis_tac[]
QED

Theorem by_super_aux_visited:
  (∀cl_map visited c (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux cl_map visited c t = SOME new_visited ⇒
    ∃v. lookup new_visited c = SOME v) ∧
  (∀cl_map visited cs (t:'a) new_visited c.
    map_ok visited ∧
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
  )
  >- (
    first_x_assum $ drule_at_then (Pos last) $
      drule_at (Pos last) >>
    metis_tac[by_super_aux_monotone]
  ) >>
  metis_tac[cj 2 by_super_aux_monotone]
QED

Theorem by_super_aux_IMP_reachable:
  (∀cl_map visited c (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux cl_map visited c t = SOME new_visited ⇒
    (∀c' v. lookup new_visited c' = SOME v ⇒
      super_reachable (to_class_map cl_map) c c' ∨
        c = c' ∨ lookup visited c' = SOME v)) ∧
  (∀cl_map visited cs (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux_list cl_map visited cs t = SOME new_visited ⇒
    (∀c' v. lookup new_visited c' = SOME v ⇒
      (∃c. MEM c cs ∧
        (super_reachable (to_class_map cl_map) c c' ∨
        c = c')) ∨
       lookup visited c' = SOME v))
Proof
  PURE_REWRITE_TAC[super_reachable_def] >>
  simp[to_class_map_def,FLOOKUP_FMAP_MAP2,FMAP_MAP2_THM,
    PULL_EXISTS,GSYM $ mlmapTheory.lookup_thm] >>
  ho_match_mp_tac full_by_super_aux_ind >>
  rpt conj_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac
  >- (
    last_x_assum $ markerLib.ASSUME_NAMED_TAC "ind_hyp" >>
    rw[] >>
    qpat_x_assum `by_super_aux _ _ _ _ = _` $ mp_tac o
      SRULE[Once by_super_aux_def] >>
    ntac 2 TOP_CASE_TAC
    >- (
      strip_tac >>
      markerLib.LABEL_X_ASSUM "ind_hyp" $
        qspec_then `x` $ mp_tac o SRULE[] >>
      impl_tac
      >- simp[] >>
      simp[mlmapTheory.insert_thm] >>
      disch_then drule >>
      rw[]
      >- (
        disj1_tac >>
        irule TC_LEFT1_I >>
        first_assum $ irule_at (Pos last) >>
        simp[GSYM mlmapTheory.lookup_thm]
      )
      >- (
        drule_at_then (Pos last) (drule_at (Pos last)) $
          cj 2 by_super_aux_visited >>
        simp[mlmapTheory.insert_thm] >>
        disj1_tac >>
        irule $ cj 1 TC_RULES >>
        simp[GSYM mlmapTheory.lookup_thm]
      )
      >- (
        Cases_on `c=c'` >> simp[] >>
        disj2_tac >>
        rev_drule_then strip_assume_tac $
          GEN_ALL mlmapTheory.lookup_insert >>
        fs[]
      )
    ) >>
    gvs[]
  )
  >- fs[full_by_super_aux_def]
  >- (
    rw[] >>
    qpat_x_assum `by_super_aux_list _ _ _ _ = _` $
      mp_tac o SRULE[Once full_by_super_aux_def] >>
    rw[AllCaseEqs()]
    >- (
      `map_ok visited'`
        by metis_tac[by_super_aux_monotone] >>
      fs[] >>
      metis_tac[]
    ) >>
    fs[] >>
    metis_tac[]
  )
QED


Theorem super_reachable_IMP_by_super_aux:
  ∀c s. super_reachable (to_class_map cl_map) c s ⇒
  ∀visited new_visited. by_super_aux cl_map visited c t = SOME new_visited ∧
  (∀c v. lookup visited c = SOME v ⇒ v = t) ⇒
  lookup new_visited s = SOME t
Proof
  simp[super_reachable_def,to_class_map_def,PULL_EXISTS,
    FMAP_MAP2_THM,FLOOKUP_FMAP_MAP2] >>
  ho_match_mp_tac TC_INDUCT_LEFT1 >>
  rw[] >>
  qpat_x_assum `by_super_aux _ _ _ _ = _` $ mp_tac o SRULE[by_super_aux_def] >>
  rpt TOP_CASE_TAC >>
  rw[] >>
  gvs[mlmapTheory.lookup_thm] >>
  qpat_x_assum `by_super_aux_list _ _ _ _ = _` $ mp_tac o SRULE[by_super_aux_def] >>

  cheat
QED

Theorem by_super_aux_super_reachable:
  (∀cl_map visited c (t:'a) new_visited. 
  map_ok visited ∧
  (* if something is visited,
   * its superclasses are also visited *)
  (∀c' v. lookup visited c' = SOME v ⇒ v = t) ∧
  (∀c' s. lookup visited c' = SOME t ∧
    super_reachable (to_class_map cl_map) c' s ⇒ 
      lookup visited s = SOME t) ∧
  by_super_aux cl_map visited c t = SOME new_visited ⇒
  map_ok new_visited ∧
  (∀c' v. lookup new_visited c' = SOME v ⇒ v = t) ∧
  (∀c' s. lookup new_visited c' = SOME t ∧
    super_reachable (to_class_map cl_map) c' s ⇒
      lookup new_visited s = SOME t) ∧
  (∀c'. lookup new_visited c' = SOME t ⇒
    super_reachable (to_class_map cl_map) c c' ∨
      c = c' ∨ lookup visited c' = SOME t) ∧
  (∀c'. lookup visited c' = SOME t ⇒
   lookup new_visited c' = SOME t) ∧
  (* c is inserted in the map *)
  (lookup new_visited c = SOME t)) ∧

  (∀cl_map visited cs (t:'a) new_visited.
  map_ok visited ∧
  (∀c' v. lookup visited c' = SOME v ⇒ v = t) ∧
  (∀c' s. lookup visited c' = SOME t ∧
  super_reachable (to_class_map cl_map) c' s ⇒ 
   lookup visited s = SOME t) ∧
  by_super_aux_list cl_map visited cs t = SOME new_visited ⇒
  map_ok new_visited ∧
  (∀c' v. lookup new_visited c' = SOME v ⇒ v = t) ∧
  (∀c' s. lookup new_visited c' = SOME t ∧
   super_reachable (to_class_map cl_map) c' s ⇒
     lookup new_visited s = SOME t) ∧
  (∀c'. lookup new_visited c' = SOME t ⇒
    (∃c. MEM c cs ∧
      (super_reachable (to_class_map cl_map) c c' ∨
      c = c')) ∨
   lookup visited c' = SOME t) ∧
  (∀c'. lookup visited c' = SOME t ⇒
   lookup new_visited c' = SOME t) ∧
  (* c is inserted in the map *)
  (∀c. MEM c cs ⇒ lookup new_visited c = SOME t))
Proof
  PURE_REWRITE_TAC[super_reachable_def] >>
  simp[to_class_map_def,FLOOKUP_FMAP_MAP2,FMAP_MAP2_THM,
    PULL_EXISTS,GSYM $ mlmapTheory.lookup_thm] >>
  ho_match_mp_tac by_super_aux_ind >>
  strip_tac >>
  rpt gen_tac >>
  rpt $ disch_then strip_assume_tac
  >- (
    pop_assum $ markerLib.ASSUME_NAMED_TAC "ind_hyp" >>
    rw[]
    >- (
      pop_assum $ mp_tac o SRULE[Once by_super_aux_def] >>
      simp[AllCaseEqs()] >>
      rw[] >>
      irule $ cj 1 mlmapTheory.insert_thm >>
      markerLib.LABEL_X_ASSUM "ind_hyp" $
        qspec_then `clinfo` mp_tac >>
      rw[] >>
      pop_assum $ drule_then drule >>
      simp[])
    >- (
      qpat_x_assum`by_super_aux _ _ _ _ = _` $
        mp_tac o SRULE[Once by_super_aux_def] >>
      rw[AllCaseEqs()] >>
      markerLib.LABEL_X_ASSUM "ind_hyp" $
        qspec_then `clinfo` mp_tac >>
      rw[] >>
      pop_assum $ drule_then drule >>
      strip_tac >>
      qpat_x_assum `lookup (insert _ _ _) _ = _` mp_tac >>
      simp[mlmapTheory.lookup_insert] >>
      IF_CASES_TAC >>
      simp[] >>
      metis_tac[]
    )
    >- (
      qpat_x_assum`by_super_aux _ _ _ _ = _` $
        mp_tac o SRULE[Once by_super_aux_def] >>
      rw[AllCaseEqs()] >>
      markerLib.LABEL_X_ASSUM "ind_hyp" $
        qspec_then `clinfo` mp_tac >>
      rw[] >>
      pop_assum $ drule_then drule >>
      strip_tac >>
      simp[mlmapTheory.lookup_insert] >>
      IF_CASES_TAC >>
      simp[] >>
      Cases_on `c' = c`
      >- (
        qpat_x_assum `TC _ c' s` $
          mp_tac o SRULE[Once TC_CASES1] >>
        rw[GSYM $ mlmapTheory.lookup_thm]
        >- metis_tac[] >>
        `lookup m dst = SOME t` by metis_tac[] >>
        metis_tac[mlmapTheory.lookup_thm]
      ) >>
      qpat_x_assum `lookup (insert _ _ _) _ = _` mp_tac >>
      simp[mlmapTheory.lookup_insert] >>
      metis_tac[mlmapTheory.lookup_thm]
    )
    >- (
      qpat_x_assum`by_super_aux _ _ _ _ = _` $
        mp_tac o SRULE[Once by_super_aux_def] >>
      rw[AllCaseEqs()] >>
      markerLib.LABEL_X_ASSUM "ind_hyp" $
        qspec_then `clinfo` mp_tac >>
      rw[] >>
      pop_assum $ drule_then drule >>
      strip_tac >>
      Cases_on`c'=c` >>
      simp[] >>
      qpat_x_assum `lookup (insert _ _ _) _ = _` $
        mp_tac >>
      simp[mlmapTheory.lookup_insert] >>
      strip_tac >>
      first_x_assum drule >>
      rw[]
      >- (
        disj1_tac >>
        irule TC_LEFT1_I >>
        first_assum $ irule_at (Pos last) >>
        simp[GSYM $ mlmapTheory.lookup_thm]
      )
      >- (
        disj1_tac >>
        irule $ cj 1 TC_RULES >>
        simp[GSYM $ mlmapTheory.lookup_thm]
      ) >>
      simp[]
    )
    >> (
      qpat_x_assum`by_super_aux _ _ _ _ = _` $
        mp_tac o SRULE[Once by_super_aux_def] >>
      rw[AllCaseEqs()] >>
      markerLib.LABEL_X_ASSUM "ind_hyp" $
        qspec_then `clinfo` mp_tac >>
      rw[] >>
      pop_assum $ drule_then drule >>
      simp[mlmapTheory.lookup_insert]
    )
  ) >>
  strip_tac >>
  rpt gen_tac >>
  rpt $ disch_then strip_assume_tac
  >- (
    fs[Once $ by_super_aux_def] >>
    metis_tac[]) >>
  qpat_x_assum`∀v. lookup visited c = SOME v ⇒ _` $
    markerLib.ASSUME_NAMED_TAC "ind_hyp_visited" >>
  qpat_x_assum`∀visited'. lookup visited c = NONE ∧ 
    by_super_aux _ _ _ _ = _ ⇒ _` $
    markerLib.ASSUME_NAMED_TAC "ind_hyp_by_super_aux" >>
  qpat_x_assum`lookup visited c = NONE ⇒ _` $
    markerLib.ASSUME_NAMED_TAC "ind_hyp_NONE" >>
  rw[] >>
  (qpat_x_assum`by_super_aux_list _ _ _ _ = _` $
    mp_tac o SRULE[Once by_super_aux_def] >>
  rw[AllCaseEqs()]
  >- (
    markerLib.LABEL_X_ASSUM "ind_hyp_NONE" $
      drule_then drule >>
    rw[] >>
    pop_assum $ drule_then drule >>
    rw[] >>
    markerLib.LABEL_X_ASSUM "ind_hyp_by_super_aux" $
      drule_then drule >>
    rpt (disch_then drule) >>
    metis_tac[]
  ) >>
  markerLib.LABEL_X_ASSUM "ind_hyp_visited" drule >>
  rpt (disch_then drule) >>
  metis_tac[])
QED

(* everything in the super list must be in the map *)
(* ∧ mlmap$lookup cl_map c ≠ NONE ∧
(∀cl info s.
  lookup cl_map cl = SOME info ∧
  MEM s info.super ⇒
  mlmap$lookup cl_map s ≠ NONE) *)
Theorem well_formed_by_super_aux:
  (∀cl_map visited c (t:'a).
    map_ok cl_map ∧ check_cl_map_no_cycles cl_map ∧
    (∀c clinfo c'.
      mlmap$lookup cl_map c = SOME clinfo ∧ MEM c' clinfo.super ⇒
      ∃x. mlmap$lookup cl_map c' = SOME x) ∧
    (∀c clinfo. mlmap$lookup visited c = SOME clinfo ⇒
      ∃x. mlmap$lookup cl_map c = SOME x)
    ⇒
    ((∃m. by_super_aux cl_map visited c t = SOME m) ⇔
      (∃x. mlmap$lookup cl_map c = SOME x)) ∧
    (∀m c clinfo. by_super_aux cl_map visited c t = SOME m ∧
      mlmap$lookup m c = SOME clinfo ⇒
      ∃x. mlmap$lookup cl_map c = SOME x)) ∧

  (∀cl_map visited cs (t:'a).
    map_ok cl_map ∧ check_cl_map_no_cycles cl_map ∧
    (∀c clinfo c'.
      mlmap$lookup cl_map c = SOME clinfo ∧ MEM c' clinfo.super ⇒
      ∃x. mlmap$lookup cl_map c' = SOME x) ∧
    (∀c clinfo. mlmap$lookup visited c = SOME clinfo ⇒
      ∃x. mlmap$lookup cl_map c = SOME x)
    ⇒
    ((∃m. by_super_aux_list cl_map visited cs t = SOME m) ⇔
      (∀c. MEM c cs ⇒ (∃x. mlmap$lookup cl_map c = SOME x))) ∧
     (∀m c m'. by_super_aux_list cl_map visited c t = SOME m ∧
      mlmap$lookup m c = SOME m' ⇒
      ∃x. mlmap$lookup cl_map c = SOME x))
Proof
  ho_match_mp_tac by_super_aux_ind >>
  rpt strip_tac
  >- (
    last_x_assum $ drule_then drule >>
    strip_tac >>
  )
  rw[] >>
  simp[Once by_super_aux_def]
  >- (
    CASE_TAC >>
    fs[] >>
    metis_tac[])
  >- (
    TOP_CASE_TAC >>
    fs[]
    >- (
      TOP_CASE_TAC >>
      gvs[]
      >- metis_tac[] >>
      last_x_assum drule >>
      first_x_assum drule >>
      rw[EQ_IMP_THM]>>
      metis_tac[]
    ) >>
    rw[EQ_IMP_THM] >>
    gvs[] >>
    metis_tac[]
  )
QED

Definition by_super_def:
  by_super cl_map (c,t) =
    by_super_aux cl_map (empty mlstring$compare) c t
End

Theorem by_super_thm:
  map_ok cl_map ∧ check_cl_map_no_cycles cl_map ⇒
  (mlmap$lookup (by_super cl_map (c,t)) s = SOME v) ⇔
    (v = t ∧
    (super_reachable (to_class_map cl_map) c s ∨ c = s))
Proof
  rw[by_super_def,super_reachable_def] >>
QED

(* return a list of goals that the type has to satisfy in order
* to satisfy c *)
Definition apply_pred:
  apply_pred m (cl,v) = OPTION_MAP (λt. (cl,t)) (FLOOKUP m v)
End

Definition by_inst_def:
  by_inst inst_map c t =
  OPTION_BIND (lookup inst_map c) (λinstl.
    let l  =
      FILTER (λ(m,inst_info). IS_SOME m) $
      MAP (λ(t',inst_info). (specialize_impl t t',inst_info)) instl
    in
      if LENGTH l = 1
      then
        case HD l of
         (SOME m,inst_info) =>
            OPT_MMAP (apply_pred m) inst_info.cstr
         | (NONE,_) => NONE (* should never happedn *)
      else NONE)
End

Triviality EL_FILTER_preserve_order:
  ∀i j. i < LENGTH l ∧
  j < i ∧
  P (EL i l) ∧
  P (EL j l) ⇒
  ∃i' j'.
  i' < LENGTH (FILTER P l) ∧
  j' < LENGTH (FILTER P l) ∧
  j' < i' ∧
  EL i' (FILTER P l) = EL i l ∧
  EL j' (FILTER P l) = EL j l
Proof
  Induct_on `l` >>
  rw[] >>
  Cases_on `j` >>
  fs[] >>
  `∃i'. i = SUC i'` by (
    `i ≠ 0` by fs[] >>
    metis_tac[num_CASES]) >>
  fs[]
  >- (
    `P (EL i' l)` by fs[] >>
    `MEM (EL i' l) (FILTER P l)` by
      (fs[MEM_FILTER,MEM_EL] >>
      metis_tac[]) >>
    fs[MEM_EL] >>
    qexistsl [`SUC n`,`0`] >>
    simp[]
  ) >>
  last_x_assum drule_all >>
  rw[] >>
  qexistsl [`SUC i''`,`SUC j'`] >>
  simp[]
QED

Triviality FILTER_EQ_NIL_EL:
  (∀i. i < LENGTH l ⇒ ¬P (EL i l)) ⇒
  FILTER P l = []
Proof
  simp[FILTER_EQ_NIL,EVERY_MEM,MEM_EL] >>
  metis_tac[]
QED

Triviality EXISTS_UNIQUE_IMP_FILTER_SINGLE:
  (∀i i'. i < LENGTH l ∧ P (EL i l) ∧
    i' < LENGTH l ∧ P (EL i' l) ⇒
    i = i') ⇒
  ((∃i. i < LENGTH l ∧ P (EL i l)) ⇒
    ∀i. i < LENGTH l ∧ P (EL i l) ⇒ FILTER P l = [EL i l]) ∧
  (¬(∃i. i < LENGTH l ∧ P (EL i l)) ⇒
    FILTER P l = [])
Proof
  Induct_on `l` >>
  fs[EXISTS_UNIQUE_THM,PULL_EXISTS] >>
  rpt gen_tac >>
  rpt $ disch_then strip_assume_tac >>
  last_x_assum mp_tac >>
  impl_tac
  >- (
    rw[] >>
    PURE_REWRITE_TAC[Once $ GSYM $ prim_recTheory.INV_SUC_EQ] >>
    last_x_assum irule >>
    simp[]) >>
  strip_tac >>
  fs[PULL_FORALL] >>
  rw[]
  >- (
    last_x_assum $ qspecl_then [`0`,`i'`]
      strip_assume_tac >>
    gvs[]
  )
  >- (
    last_x_assum irule >>
    rw[GSYM IMP_DISJ_THM] >>    
    last_x_assum $ qspecl_then [`SUC i''`,`0`] assume_tac >>
    gvs[]
  )
  >- (
    `∃j. i' = SUC j`
    by (
      Cases_on `i = 0` >>
      fs[] >>
      metis_tac[num_CASES]
    ) >>
    first_x_assum $ qspecl_then [`j`,`j`] assume_tac >>
    fs[]
  )
  >- (
    qexists `0` >>
    simp[]
  ) >>
  last_x_assum irule >>
  fs[GSYM IMP_DISJ_THM] >>
  rw[] >>
  first_x_assum $ qspec_then `SUC i` assume_tac >>
  fs[]
QED

Theorem by_inst_thm:
  (mlmap$lookup inst_map c = NONE ⇒
    by_inst inst_map c t = NONE) ∧
  (∀instl. lookup inst_map c = SOME instl ∧
    (∀i. i < LENGTH instl ⇒
       specialize_impl t (FST $ EL i instl) = NONE) ⇒
     by_inst inst_map c t = NONE) ∧
  (∀instl i j. lookup inst_map c = SOME instl ∧
     i < j ∧ i < LENGTH instl ∧ j < LENGTH instl ∧
     IS_SOME (specialize_impl t (FST $ EL i instl)) ∧ 
     IS_SOME (specialize_impl t (FST $ EL j instl)) ⇒
     by_inst inst_map c t = NONE) ∧
  (∀instl i m. lookup inst_map c = SOME instl ∧
    (∃!i. i < LENGTH instl ∧ IS_SOME (specialize_impl t (FST $ EL i instl))) ∧
    i < LENGTH instl ∧
    specialize_impl t (FST $ EL i instl) = SOME m ⇒
    by_inst inst_map c t =
      OPT_MMAP (apply_pred m) ((SND $ EL i instl).cstr))
Proof
  simp[by_inst_def] >>
  Cases_on `lookup inst_map c` >>
  rpt strip_tac >>
  fs[]
  >- (
    spose_not_then kall_tac >>
    fs[rich_listTheory.FILTER_MAP,combinTheory.o_DEF,
      LAMBDA_PROD] >>
    `(FILTER (λ(p1,p2). IS_SOME (specialize_impl t p1)) instl) = []` suffices_by
      (strip_tac >> gvs[]) >>
    irule FILTER_EQ_NIL_EL >>
    rw[] >>
    last_x_assum drule >>
    pairarg_tac >>
    simp[])
  >- (
    spose_not_then kall_tac >>
    fs[rich_listTheory.FILTER_MAP,combinTheory.o_DEF,
      LAMBDA_PROD] >>
    drule_then drule EL_FILTER_preserve_order >>
    disch_then $ qspec_then
      `\x. IS_SOME (specialize_impl t (FST x))`
      strip_assume_tac >>
    gvs[LAMBDA_PROD]) >>
  fs[EXISTS_UNIQUE_THM,LAMBDA_PROD,
    rich_listTheory.FILTER_MAP,combinTheory.o_DEF] >>
  qmatch_goalsub_abbrev_tac `LENGTH (FILTER P instl) = 1` >>
  `FILTER P instl = [EL i' instl]`
  by (
    qspecl_then [`instl`,`P`] mp_tac $ GEN_ALL $
      cj 1 EXISTS_UNIQUE_IMP_FILTER_SINGLE >>
    fs[Abbr`P`] >>
    impl_tac
    >- (
      rw[] >>
      ntac 2 (pairarg_tac >> fs[])) >>
    impl_tac
    >- (
      first_x_assum $ irule_at (Pos hd) >>
      pairarg_tac >> fs[]
    ) >>
    rw[] >>
    first_x_assum $ qspec_then `i'` mp_tac >>
    pairarg_tac >> fs[]
  ) >>
  simp[] >>
  pairarg_tac >>
  fs[] >>
  `i = i'` by (first_x_assum irule >> simp[]) >>
  fs[]
QED

Definition entail_def:
  entail cl_map inst_map ps (c,t) = ANY (MEM (c,t)) (MAP (by_super
  cl_map) ps) ∨
  case by_inst inst_map c t of
    | NONE => F
    | SOME qs => ALL (entail cl_map inst_map ps) qs
End


val _ = export_theory();
