open HolKernel Parse boolLib bossLib dep_rewrite BasicProvers;
open pairTheory optionTheory listTheory pred_setTheory;
open finite_mapTheory alistTheory;
open balanced_mapTheory mlmapTheory miscTheory;
open cycle_detectionTheory typeclass_tcexpTheory
typeclass_env_map_implTheory;

val _ = new_theory "typeclass_well_formed_check";

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
  simp[map_ok_def,toAscList_def,cmp_of_def] >>
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

Triviality super_reachable_EQ_TC_depends_on:
  map_ok cl_map ∧
  (∀c d. FLOOKUP (to_fmap cl_map) c = SOME d ⇒
    set d.super ⊆ FDOM (to_fmap cl_map)) ⇒
  super_reachable (to_class_map cl_map) =
    TC_depends_on (superAList cl_map)
Proof
  rw[super_reachable_def,TC_depends_on_def] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM,superAList_def,map_fst] >>
  fs[to_class_map_def,FLOOKUP_FMAP_MAP2,FMAP_MAP2_THM,PULL_EXISTS] >>
  drule_then strip_assume_tac mlmap_toAscList >>
  gvs[ALOOKUP_MAP,PULL_EXISTS,EXTENSION] >>
  rw[EQ_IMP_THM]
  >- (
    drule_then assume_tac $ cj 2 MAP_FST_toAscList >>
    drule_then assume_tac ALOOKUP_ALL_DISTINCT_MEM >>
    drule_then strip_assume_tac mlmap_toAscList >>
    gvs[EXTENSION] >>
    qpat_assum `∀v k. FLOOKUP _ _ = _ ⇒ ALOOKUP _ _ = _` $
      drule_then $ irule_at (Pos hd) >>
    drule_then assume_tac $ cj 3 MAP_FST_toAscList >>
    fs[SUBSET_DEF] >>
    metis_tac[]
  ) >>
  drule_then assume_tac ALOOKUP_MEM >>
  drule_then assume_tac $ cj 2 mlmap_toAscList >>
  fs[EXTENSION,SUBSET_DEF]
QED

(*
Theorem check_cl_map_no_cycles_IMP_super_no_cycles:
  map_ok cl_map ∧
  (∀c d. FLOOKUP (to_fmap cl_map) c = SOME d ⇒
    set d.super ⊆ FDOM (to_fmap cl_map)) ∧
  check_cl_map_no_cycles cl_map ⇒
  super_no_cycles $ to_class_map cl_map
Proof
  rw[super_no_cycles_def] >>
  drule_all_then assume_tac
    super_reachable_EQ_TC_depends_on >>
  drule_then assume_tac ALL_DISTINCT_superAList >>
  drule_then assume_tac has_cycle_correct >>
  fs[check_cl_map_no_cycles_def]
QED
*)

Triviality super_reachable_EQ_TC_depends_on_weak:
  map_ok cl_map ⇒
  super_reachable (to_class_map cl_map) =
    TC_depends_on_weak (superAList cl_map)
Proof
  rw[super_reachable_def,TC_depends_on_weak_def] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM,superAList_def,map_fst] >>
  fs[to_class_map_def,FLOOKUP_FMAP_MAP2,FMAP_MAP2_THM,PULL_EXISTS] >>
  drule_then strip_assume_tac mlmap_toAscList >>
  gvs[ALOOKUP_MAP,PULL_EXISTS,EXTENSION] >>
  rw[EQ_IMP_THM]
  >- (
    drule_then assume_tac $ cj 2 MAP_FST_toAscList >>
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


(*
Definition check_cl_map_def:
  check_cl_map cl_map =
  (all (\cl cl_info.
    EVERY (\c. lookup cl_map c ≠ NONE) cl_info.super ∧
    all (\name impl. lookup cl_info.methodsig name ≠ NONE) cl_info.defaults ∧
    EVERY (\names. EVERY (\name. lookup cl_info.methodsig name ≠ NONE) names)
    cl_info.minImp
    ) cl_map ∧
  check_cl_map_no_cycles cl_map)
End

Definition EVERY_instance_def:
  EVERY_instance f inst_map =
    all (\cl_name l. EVERY (\(ty,instinfo). f cl_name ty instinfo) l) inst_map
End

Definition has_instance_def:
  has_instance inst_map cstr ty cl =
    case lookup inst_map cl of
       | NONE => F
       | SOME l => ARB l
End

(* check if every instance satisfy the class requirements *)
Definition check_inst_map_sat_cl_req_def:
  check_inst_map_sat_cl_req inst_map cl_map = EVERY_instance
    (\cl_name ty instinfo.
      (case lookup cl_map cl_name of
      | NONE => F
      | SOME cl_info =>
        (* implemented minImpl *)
        EXISTS (\names. EVERY (\name. lookup instinfo.impl name ≠ NONE) names) cl_info.minImp ∧
        (* implemented every method without function definitions *)
        EVERY (\name sig. lookup cl_info.defaults name ≠ NONE ∨ lookup instinfo.impl name ≠ NONE) cl_info.methodsig ∧
        (* TODO: implemented super classes *)
        EVERY (has_instance inst_map instinfo.cstr ty) cl_map.super
      ) ∧
      (* check if constraints is valid *)
      EVERY (λ(cl,v). lookup cl_map cl ≠ NONE ∧
        TypeVar v ≠ ty (* v must be a variable in ty,
          so we only need to test there
          size are not equal to show its size is smaller than ty *)
        ) instinfo.cstr
     ) inst_map
End

(* the constraints must be scoped if the parser does not produce an error *)
Theorem inst_cstr_scoped_type_var:
Proof
QED

(* inst_map produced after the parsing does not contain
* type that are alpha equivalent *)
Theorem inst_map_no_alpha_equiv:
Proof
QED
*)

val _ = export_theory();
