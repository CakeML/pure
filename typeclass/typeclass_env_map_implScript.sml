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
Theorem TC_flip:
  ∀x y. TC R x y ⇒ TC (flip R) y x
Proof
  Induct_on `TC` >>
  rw[]
  >- 
    (irule $ cj 1 relationTheory.TC_RULES >>
    simp[]) >>
  irule $ cj 2 relationTheory.TC_RULES >>
  metis_tac[]
QED

Theorem WF_PULL_lift:
  ∀P f R g R'. 
  (!x. P (f x) ⇒ WF (R (f x))) ⇒
  (∀x y. R' x y ⇒ P (f x) ∧ f x = f y ∧ R (f x) (g x) (g y)) ⇒
  WF R'
Proof
  rw[WF_DEF] >>
  reverse $ Cases_on `∃w'. P (f w') ∧ B w'`
  >- (
    fs[] >>
    metis_tac[]) >>
  rw[] >>
  first_x_assum drule >>
  qpat_x_assum `B w` kall_tac >>
  rw[PULL_EXISTS] >>
  first_x_assum $ qspec_then
    `\x. ∃y. x = g y ∧ B y ∧ P (f y) ∧ f y = f w'` assume_tac >>
  fs[PULL_EXISTS] >>
  first_x_assum (dxrule_then dxrule) >>
  rw[] >>
  first_assum $ irule_at (Pos hd) >>
  rw[] >>
  last_x_assum drule >>
  rw[] >>
  gvs[]
QED

(* everything in the super list must be in the map *)
(* ∧ mlmap$lookup cl_map c ≠ NONE ∧
(∀cl info s.
  lookup cl_map cl = SOME info ∧
  MEM s info.super ⇒
  mlmap$lookup cl_map s ≠ NONE) *)

Theorem by_super_aux_terminate:
  ∃R. WF R ∧
       ∀visited t c cl_map clinfo sup visited'.
         (map_ok cl_map ∧ check_cl_map_no_cycles cl_map) ∧
         lookup cl_map c = SOME clinfo ∧ MEM sup clinfo.super ∧
         lookup visited' sup = NONE ⇒
         R (cl_map,visited',sup,t) (cl_map,visited,c,t)
Proof
  qexists
  `(λ(cl_map,visited,sup,t) (cl_map',visited',c,t').
    cl_map = cl_map' ∧ map_ok cl_map ∧
    check_cl_map_no_cycles cl_map ∧
    ∃info. lookup cl_map c = SOME info ∧
      MEM sup info.super)` >>
   rw[] >>
   qspecl_then [
     `\x. map_ok x ∧ check_cl_map_no_cycles x`,
     `FST`,
     `\x sup c. ∃info. lookup x c = SOME info ∧
       MEM sup info.super`,
       `λ(cl_map,visited,c,t). c`]
     irule WF_PULL_lift >>
   reverse $ rw[]
   >- (
    PairCases_on `x` >>
    fs[] >>
    rename1 `lookup cl_map` >>
    `WF (reln_to_rel (rel_to_reln
      (λsup c. ∃info. lookup cl_map c = SOME info ∧
        MEM sup info.super)))`
    suffices_by (
      PURE_REWRITE_TAC[reln_rel_conv_thms] >>
      simp[]) >>
    irule acyclic_WF >>
    simp[acyclic_def,rel_to_reln_def] >>
    simp[reln_rel_conv_thms,reln_to_rel_def,
      rel_to_reln_def] >>
    conj_tac
    >- (
      rpt strip_tac >>
      drule_all
        check_cl_map_no_cycles_IMP_super_no_cycles >>
      simp[super_no_cycles_def] >>
      simp[super_reachable_def,to_class_map_def,
        PULL_EXISTS,FLOOKUP_FMAP_MAP2] >>
      drule TC_flip >>
      simp[combinTheory.C_DEF,
        GSYM mlmapTheory.lookup_thm] >>
      metis_tac[]
    ) >>
    qexists
      `{c | ∃x. lookup cl_map c = SOME x} ∪
      BIGUNION (IMAGE (\info. set info.super) $
      {info | ?c. lookup cl_map c = SOME info})` >>
    rw[]
    >- simp[mlmapTheory.lookup_thm,flookup_thm]
    >- (
      irule IMAGE_FINITE >>
      `{info | ?c. mlmap$lookup cl_map c = SOME info} =
        FRANGE (to_fmap cl_map)`
      by simp[mlmapTheory.lookup_thm,EXTENSION,
        IN_FRANGE,flookup_thm] >>
      simp[])
    >- simp[FINITE_LIST_TO_SET]
    >- (
      irule SUBSET_TRANS >>
      irule_at (Pos last) $ cj 2 SUBSET_UNION >>
      simp[mlmapTheory.lookup_thm,BIGUNION,
        RDOM_DEF,SUBSET_DEF,IN_DEF] >>
      metis_tac[]
    )
    >- (
      irule SUBSET_TRANS >>
      irule_at (Pos last) $ cj 1 SUBSET_UNION >>
      rw[RRANGE,SUBSET_DEF,IN_DEF] >>
      metis_tac[])
   ) >>
   ntac 2 (pairarg_tac >> fs[]) >>
   metis_tac[]
QED

(* use map to store what super classes have been visited *)
Definition by_super_aux_def:
  by_super_aux cl_map visited c t =
  if map_ok cl_map ∧ check_cl_map_no_cycles cl_map
  then
    case mlmap$lookup cl_map c of
      | NONE => visited
      | SOME clinfo =>
        FOLDL  (λvisited sup.
        case lookup visited sup of
          | SOME _ => visited
          | NONE => by_super_aux cl_map visited sup t)
          (mlmap$insert visited c t)
        clinfo.super
  else visited (* should never happen *)
Termination
  metis_tac[by_super_aux_terminate]
End

Definition by_super_def:
  by_super cl_map (c,t) =
    by_super_aux cl_map (empty mlstring$compare) c t
End

Theorem by_super_thm:
  map_ok cl_map ∧ check_cl_map_no_cycles cl_map ⇒
  (mlmap$lookup (by_super cl_map (c,t)) s = SOME v ⇔
    (v = t ∧ super_reachable (to_class_map cl_map) c s))
Proof
  rw[by_super_def] >>

QED


(* return a list of goals that the type has to satisfy in order
* to satisfy c *)
Definition apply_pred:
  apply_pred m (cl,v) = OPTION_MAP (λt. (cl,t)) (FLOOKUP m v)
End

Definition by_inst_def:
  byInst inst_map c t =
  OPTION_BIND (lookup inst_map c) (λinstl.
    let l  =
      FILTER (λ(m,inst_info). IS_SOME m) $
      MAP (λ(t',inst_info). (specialize t t',inst_info)) instl
    in
      if LENGTH l = 1
      then
        (case HD l of
          (SOME m,inst_info) =>
            OPT_MMAP (apply_pred m) inst_info.cstr)
      else NONE)
End

Definition entail_def:
  entail cl_map inst_map ps (c,t) = ANY (MEM (c,t)) (MAP (by_super
  cl_map) ps) ∨
  case by_inst inst_map c t of
    | NONE => F
    | SOME qs => ALL (entail cl_map inst_map ps) qs
End


val _ = export_theory();
