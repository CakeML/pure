(* concrete data structures for implementing
* instance map and type class map *)
open HolKernel Parse boolLib bossLib dep_rewrite BasicProvers;
open relationTheory set_relationTheory;
open pairTheory optionTheory listTheory pred_setTheory finite_mapTheory;
open miscTheory typeclass_typesTheory typeclass_tcexpTheory
typeclass_typingTheory;
open monadsyntax;

val _ = new_theory "typeclass_env_map";

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "option";

Type minImplAST = ``:(mlstring list) list``; (* DNF of function names*)

Datatype:
  classinfo =
    <| super : mlstring list
     ; kind : Kind option
     ; methodsig : cvname |-> PredType
     ; minImp : minImplAST
     ; defaults : cvname |-> 'a tcexp |>
End

Definition super_reachable_def:
  super_reachable cdb =
    TC (\src dst.
      ∃c. FLOOKUP cdb src = SOME (c:'a classinfo) ∧
      MEM dst c.super)
End

Theorem super_reachable_RULES:
  (∀x y c. FLOOKUP cdb x = SOME c ∧ MEM y c.super ⇒
    super_reachable cdb x y) ∧
  (∀x y z. super_reachable cdb x y ∧ super_reachable cdb y z ⇒
    super_reachable cdb x z)
Proof
  rw[super_reachable_def,relationTheory.TC_RULES] >>
  metis_tac[cj 2 relationTheory.TC_RULES]
QED

Theorem super_reachable_SUBSET = cj 1 super_reachable_RULES;
Theorem super_reachable_trans = cj 2 super_reachable_RULES;

Theorem super_reachable_LEFT1_I:
  ∀x y z c.
    FLOOKUP cdb x = SOME c ∧ MEM y c.super ∧
    super_reachable cdb y z ⇒
    super_reachable cdb x z
Proof
  rw[] >> irule super_reachable_trans >>
  first_x_assum $ irule_at Any >>
  drule_all_then irule super_reachable_SUBSET
QED

Theorem super_reachable_RIGHT1_I:
  ∀x y z c.
    super_reachable cdb x y ∧
    FLOOKUP cdb y = SOME c ∧ MEM z c.super ⇒
    super_reachable cdb x z
Proof
  rw[] >> irule super_reachable_trans >>
  first_x_assum $ irule_at Any >>
  drule_all_then irule super_reachable_SUBSET
QED

Definition super_no_cycles_def:
  super_no_cycles cdb =
    ∀x. ¬(super_reachable cdb x x)
End

Datatype:
  instinfo =
    <| cstr : (mlstring # 'b) list (* class and type variable *)
     ; nargs : num (* number of arguments to the type constructor *)
     ; impl : cvname |-> 'a tcexp |> (* function name and its expression *)
End

Definition instinfo_well_scoped_def:
  instinfo_well_scoped inf ⇔
    (∀c v. MEM (c,v) inf.cstr ⇒ v < inf.nargs)
End

Definition instinfo_impl_ok:
  instinfo_impl_ok cdb inst class <=>
  ∃c. FLOOKUP cdb class = SOME c ∧
    (∀meth ty. FLOOKUP c.methodsig meth = SOME ty ⇒
     ∃exp.
       FLOOKUP inst.impl meth = SOME exp ∨
       FLOOKUP c.defaults meth = SOME exp) ∧
    (∃minimpl. ∀m.
      MEM minimpl c.minImp ∧ MEM m minimpl ⇒
        ∃exp. FLOOKUP inst.impl m = SOME exp)
End

Type class_map = ``:mlstring |-> 'a classinfo``;
Type inst_map = ``: (mlstring # typeclass_types$ty_cons) |-> ('a ,num) instinfo``;

Definition add_instance_def:
  add_instance (inst_map:'a inst_map) cl ty info =
    case FLOOKUP inst_map (cl,ty) of
    | NONE => SOME $ inst_map |+ ((cl,ty), info)
    | SOME _ => NONE
End

Definition super_keys_ok_def:
  super_keys_ok (cl_map:'a class_map) =
  (∀c clinfo c'.
    FLOOKUP cl_map c = SOME clinfo ∧ MEM c' clinfo.super ⇒
    ∃x. FLOOKUP cl_map c' = SOME x)
End

Definition FLOOKUP_inst_map_def:
  FLOOKUP_inst_map inst_map c t =
  do
    tcons <- head_ty_cons t;
    FLOOKUP inst_map (c,tcons)
  od
End

(*
Definition inst_to_types_def:
  inst_to_PredType_scheme (inst:inst_info) =
  (inst.nargs, (MAP (I ## TypeVar) inst.cstr),
    (c,tcons_to_type tcons (GENLIST TypeVar inst.nargs)))
End

Definition by_inst_def:
  by_inst inst_map c cstr t =
    ∃tcons targs inst ts.
      t = tcons_to_type tcons targs ∧
      FLOOKUP inst_map (c,tcons) = SOME inst ∧
      tsubst_inst ts (_ inst) = _ cstr (c,t)
End

Definition by_inst_def:
  by_inst inst_map c t = OPTION_MAP SND $ lookup_inst_map inst_map c t
End

Theorem lookup_inst_map_lem:
  ∀inst_map c t impl cstr.
    lookup_inst_map inst_map c t = SOME (impl,cstr)
    ⇔
    (∃tcons targs inst_info.
      split_ty_head t = SOME (tcons,targs) ∧
      lookup inst_map (c,tcons) = SOME inst_info ∧
      LENGTH targs = inst_info.nargs ∧
      impl = inst_info.impl ∧
      cstr = MAP (I ## (λv. EL v targs)) inst_info.cstr)
Proof
  reverse $ rw[lookup_inst_map_def,EQ_IMP_THM]
  >- simp[combinTheory.C_DEF] >>
  pairarg_tac >>
  gvs[combinTheory.C_DEF]
QED

Theorem by_inst_lem:
  ∀inst_map c t cstr.
  by_inst inst_map c t = SOME cstr ⇔
  (∃tcons targs inst_info.
    split_ty_head t = SOME (tcons,targs) ∧
    lookup inst_map (c,tcons) = SOME inst_info ∧
    LENGTH targs = inst_info.nargs ∧
      cstr = MAP (I ## (λv. EL v targs)) inst_info.cstr)
Proof
  simp[by_inst_def,LAMBDA_PROD,GSYM PEXISTS_THM,lookup_inst_map_lem]
QED

Theorem lookup_inst_map_thm:
  ∀inst_map c t impl cstr.
    lookup_inst_map inst_map c t = SOME (impl,cstr)
    ⇔
    (∃tcons targs inst_info.
      split_ty_head t = SOME (tcons,targs) ∧
      lookup inst_map (c,tcons) = SOME inst_info ∧
      LENGTH targs = inst_info.nargs ∧
      impl = inst_info.impl ∧
      LENGTH cstr = LENGTH inst_info.cstr ∧
      (∀n. n < LENGTH inst_info.cstr ⇒
        let (cl,v) = EL n inst_info.cstr in
          EL n cstr = (cl,EL v targs)))
Proof
  reverse $ rw[lookup_inst_map_lem,EQ_IMP_THM]
  >- (
    simp[] >>
    irule LIST_EQ >>
    rw[EL_MAP,oneline PAIR_MAP_THM] >>
    CASE_TAC >>
    first_x_assum drule >>
    simp[]
  ) >>
  rw[] >>
  pairarg_tac >>
  gvs[EL_MAP,oneline PAIR_MAP_THM]
QED

Theorem by_inst_thm:
  ∀inst_map c t cstr.
    by_inst inst_map c t = SOME cstr ⇔
    (∃tcons targs inst_info.
      split_ty_head t = SOME (tcons,targs) ∧
      lookup inst_map (c,tcons) = SOME inst_info ∧
      LENGTH targs = inst_info.nargs ∧
      LENGTH cstr = LENGTH inst_info.cstr ∧
      (∀n. n < LENGTH inst_info.cstr ⇒
        let (cl,v) = EL n inst_info.cstr in
          EL n cstr = (cl,EL v targs)))
Proof
  simp[by_inst_def,LAMBDA_PROD,GSYM PEXISTS_THM,lookup_inst_map_thm]
QED

Inductive full_entail:
[~mem]
  MEM p ps ⇒ full_entail cl_map inst_map ps p
[~super]
  full_entail cl_map inst_map ps (c,t) ∧
  super_reachable cl_map c s ⇒
  full_entail cl_map inst_map ps (s,t)
[~inst]
  by_inst inst_map c t = SOME qs ∧
  (∀q. MEM q qs ⇒ full_entail cl_map inst_map ps q) ⇒
  full_entail cl_map inst_map ps (c,t)
End

Inductive entail:
[~mem]
  MEM p ps ⇒ entail cl_map inst_map ps p
[~super]
  MEM (c,t) ps ∧
  super_reachable cl_map c s ⇒
  entail cl_map inst_map ps (s,t)
[~inst]
  by_inst inst_map c t = SOME qs ∧
  (∀q. MEM q qs ⇒ entail cl_map inst_map ps q) ⇒
  entail cl_map inst_map ps (c,t)
End

Theorem split_ty_head_tsubst:
  ∀t tcons targs ts.
    split_ty_head t = SOME (tcons,targs) ⇒
    split_ty_head (tsubst ts t) = SOME (tcons, MAP (tsubst ts) targs)
Proof
  ho_match_mp_tac head_ty_cons_ind >>
  rw[] >>
  gvs[subst_db_def,split_ty_head_thm,head_ty_cons_def,ty_args_alt]
QED

Definition well_scoped_inst_map_def:
  well_scoped_inst_map inst_map =
  (∀k inst_info c v.
    lookup inst_map k = SOME inst_info ∧
    MEM (c,v) inst_info.cstr ⇒
    v < inst_info.nargs)
End

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
    irule entail_mem >>
    simp[MEM_MAP] >>
    first_x_assum $ irule_at (Pos last) >>
    simp[]
  )
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
  gvs[by_inst_thm] >>
  drule_then (irule_at (Pos hd)) split_ty_head_tsubst >>
  rw[] >>
  first_x_assum drule >>
  pairarg_tac >> gvs[EL_MAP] >>
  DEP_REWRITE_TAC[EL_MAP] >>
  gvs[well_scoped_inst_map_def] >>
  last_x_assum irule >>
  simp[MEM_EL] >>
  metis_tac[]
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
    simp[MEM_MAP,PULL_EXISTS] >>
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
  gvs[by_inst_thm] >>
  drule_then (irule_at (Pos hd)) split_ty_head_tsubst >>
  rw[] >>
  first_x_assum drule >>
  pairarg_tac >> gvs[EL_MAP] >>
  DEP_REWRITE_TAC[EL_MAP] >>
  gvs[well_scoped_inst_map_def] >>
  last_x_assum irule >>
  simp[MEM_EL] >>
  metis_tac[]
QED

Theorem head_ty_cons_cons_types:
  ∀t targs. head_ty_cons (cons_types t targs) = head_ty_cons t
Proof
  Induct_on `targs` >>
  rw[head_ty_cons_def,cons_types_def]
QED

Theorem ty_args_cons_types:
  ∀t targs. ty_args (cons_types t targs) = ty_args t ++ targs
Proof
  Induct_on `targs` >>
  rw[cons_types_def,ty_args_alt]
QED

Theorem split_ty_head_tcons_to_type:
  split_ty_head (tcons_to_type tcons targs) = SOME (tcons, targs)
Proof
  Induct_on `targs` using SNOC_INDUCT >>
  gvs[tcons_to_type_def,split_ty_head_thm] >>
  rw[cons_types_def,ty_args_alt,head_ty_cons_def] >>
  gvs[head_ty_cons_cons_types,ty_args_cons_types]
QED

Theorem tcons_to_type_split_ty_head:
  ∀t tcons targs.
    split_ty_head t = SOME (tcons,targs) ⇒
    tcons_to_type tcons targs = t
Proof
  ho_match_mp_tac head_ty_cons_ind >>
  rw[] >>
  gvs[split_ty_head_thm,head_ty_cons_def,
    ty_args_alt,tcons_to_type_alt] >>
  gvs[tcons_to_type_def,cons_types_SNOC]
QED

Theorem tcons_to_type_NEQ_TypeVar:
  ∀v. tcons_to_type tcons targs ≠ TypeVar v
Proof
  rpt strip_tac >>
  pop_assum $ mp_tac o Q.AP_TERM `split_ty_head` >>
  simp[split_ty_head_tcons_to_type,split_ty_head_thm,head_ty_cons_def]
QED

Triviality tcons_to_type_tsubst_TypeVar:
  tcons_to_type tcons targs =
    tsubst targs $ tcons_to_type tcons $ GENLIST TypeVar (LENGTH targs)
Proof
  simp[tsubst_tcons_to_type,MAP_GENLIST] >>
  AP_TERM_TAC >>
  PURE_REWRITE_TAC[Once $ GSYM GENLIST_ID] >>
  irule GENLIST_CONG >>
  simp[subst_db_def]
QED

(* `entail` is equivalent to `full_entail`
* if for every instance in inst_map,
* the constraint ps for the instance (c,t)
* `entail`s (s,t) for all super class s of c *)
Definition entail_wf_def:
  entail_wf cl_map inst_map ⇔
  ∀c tcons inst clinfo s.
    FLOOKUP inst_map (c,tcons) = SOME inst ∧
    FLOOKUP cl_map c = SOME clinfo ∧ MEM s clinfo.super ⇒
    ∃inst'. FLOOKUP inst_map (s,tcons) = SOME inst' ∧
    inst'.nargs = inst.nargs ∧
    ∀cl v. MEM (cl,v) inst'.cstr ⇒
      MEM (cl,v) inst.cstr ∨
      ∃scl. MEM (scl,v) inst.cstr ∧ super_reachable cl_map scl cl
End

Definition inst_map_constraints_ok_def:
  inst_map_constraints_ok cl_map inst_map ⇔
  (∀k inst x.
    FLOOKUP inst_map k = SOME inst ∧ MEM x inst.cstr ⇒
      ∃clinfo. FLOOKKUP cl_map (FST x) = SOME clinfo)
End

Theorem entail_super_TypeVar:
  well_scoped_inst_map inst_map ∧
  lookup inst_map (c,tcons) = SOME inst ∧
  FLOOKUP cl_map c = SOME clinfo ∧
  MEM s clinfo.super ⇒
  (entail cl_map inst_map (MAP (I ## TypeVar) inst.cstr)
    (s,tcons_to_type tcons (GENLIST TypeVar inst.nargs)) ⇔
   ∃inst'. lookup inst_map (s,tcons) = SOME inst' ∧
    inst'.nargs = inst.nargs ∧
    ∀cl v. MEM (cl,v) inst'.cstr ⇒
      MEM (cl,v) inst.cstr ∨
      ∃scl. MEM (scl,v) inst.cstr ∧ super_reachable cl_map scl cl)
Proof
  rw[EQ_IMP_THM]
  >- (
    reverse $ pop_assum $ strip_assume_tac o SRULE[Once entail_cases]
    >- (
      gvs[by_inst_lem,split_ty_head_tcons_to_type,MEM_MAP,PULL_EXISTS] >>
      rw[] >>
      `v < inst_info.nargs` by (
        gvs[well_scoped_inst_map_def] >>
        last_x_assum irule >>
        metis_tac[MEM_EL]) >>
      first_x_assum drule >>
      rw[Once entail_cases] >>
      gvs[MEM_MAP]
      >- (
        rename1 `MEM p inst.cstr` >>
        Cases_on `p` >>
        gvs[]
      )
      >- (
        rename1 `MEM p inst.cstr` >>
        Cases_on `p` >>
        gvs[] >>
        disj2_tac >>
        metis_tac[]
      ) >>
      gvs[by_inst_lem,split_ty_head_thm,head_ty_cons_def]
    ) >>
    gvs[MEM_MAP] >>
    rename1 `MEM p inst.cstr` >>
    Cases_on `p` >>
    gvs[tcons_to_type_NEQ_TypeVar]
  ) >>
  irule entail_inst >>
  rw[by_inst_lem,split_ty_head_tcons_to_type,MEM_MAP,PULL_EXISTS] >>
  rename1 `entail _ _ _ (_ p)` >>
  Cases_on `p` >>
  first_x_assum drule >>
  rw[]
  >- (
    irule entail_mem >>
    simp[MEM_MAP] >>
    first_assum $ irule_at (Pos last) >>
    DEP_REWRITE_TAC[EL_GENLIST] >>
    gvs[well_scoped_inst_map_def] >>
    last_x_assum irule >>
    metis_tac[MEM_EL]
  ) >>
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
  ∀c tcons inst clinfo s.
    lookup inst_map (c,tcons) = SOME inst ∧
    FLOOKUP cl_map c = SOME clinfo ∧ MEM s clinfo.super ⇒
    entail cl_map inst_map (MAP (I ## TypeVar) inst.cstr)
      (s,tcons_to_type tcons (GENLIST TypeVar inst.nargs)))
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
  FLOOKUP cl_map c = SOME c' ∧
  MEM s c'.super ∧
  lookup inst_map (c,tcons) = SOME inst ⇒
  ∃inst'. lookup inst_map (s,tcons) = SOME inst' ∧
    inst'.nargs = inst.nargs ∧
    ∀cl v. MEM (cl,v) inst'.cstr ⇒
      MEM (cl,v) inst.cstr ∨
      ∃scl. MEM (scl,v) inst.cstr ∧ super_reachable cl_map scl cl
Proof
  rw[] >>
  gvs[entail_wf_def] >>
  ntac 2 (first_x_assum drule >> rw[]) >>
  gvs[]
QED

Theorem entail_wf_lookup_super_reachable:
  entail_wf cl_map inst_map ⇒
  ∀c s. super_reachable cl_map c s ⇒
  ∀tcons inst. lookup inst_map (c,tcons) = SOME inst ⇒
  ∃inst'. lookup inst_map (s,tcons) = SOME inst' ∧
    inst'.nargs = inst.nargs ∧
    ∀cl v. MEM (cl,v) inst'.cstr ⇒
      MEM (cl,v) inst.cstr ∨
      ∃scl. MEM (scl,v) inst.cstr ∧ super_reachable cl_map scl cl
Proof
  strip_tac >>
  simp[Once super_reachable_def] >>
  ho_match_mp_tac TC_INDUCT_LEFT1 >>
  rw[]
  >- metis_tac[entail_wf_lookup_super] >>
  drule_all entail_wf_lookup_super >>
  rw[] >>
  last_x_assum drule >> rw[] >>
  rw[] >>
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[]
  >- metis_tac[] >>
  disj2_tac >>
  irule_at (Pos last) super_reachable_trans >>
  metis_tac[]
QED

Theorem entail_strong_ind:
  ∀cl_map inst_map ps entail'.
    (∀p. MEM p ps ⇒ entail' p) ∧
    (∀c s t.
      MEM (c,t) ps ∧ super_reachable cl_map c s ⇒ entail' (s,t)) ∧
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
  >- drule_all_then irule entail_mem
  >- metis_tac[]
  >- drule_all_then irule entail_super >>
  irule entail_inst >>
  rw[]
QED

Triviality entail_wf_super_reachable':
  entail_wf cl_map inst_map ⇒
  ∀p. entail cl_map inst_map ps p ⇒
    ∀c t clinfo s. p = (c,t) ∧
    (c = s ∨
    super_reachable cl_map c s) ⇒
    entail cl_map inst_map ps (s,t)
Proof
  strip_tac >>
  ho_match_mp_tac entail_strong_ind >>
  rw[]
  >- drule_then irule entail_mem
  >- drule_all_then irule entail_super
  >- drule_all_then irule entail_super
  >- (
    irule entail_super >>
    first_assum $ irule_at (Pos hd) >>
    drule_all_then irule super_reachable_trans) >>
  gvs[IMP_CONJ_THM,FORALL_AND_THM] >>
  gvs[PULL_FORALL,AND_IMP_INTRO]
  >- drule_all_then irule entail_inst >>
  gvs[by_inst_lem,MEM_MAP,PULL_EXISTS,LAMBDA_PROD,
    GSYM PFORALL_THM,GSYM PEXISTS_THM] >>
  irule entail_inst >>
  simp[by_inst_lem,MEM_MAP,
    PULL_EXISTS,LAMBDA_PROD,GSYM PFORALL_THM] >>
  drule_all entail_wf_lookup_super_reachable >>
  rw[] >>
  rw[MEM_MAP,GSYM PEXISTS_THM] >>
  first_x_assum drule >>
  rw[] >>
  first_x_assum drule >> rw[]
QED

Theorem entail_wf_super_reachable:
  ∀cl_map inst_map ps c t s.
    entail_wf cl_map inst_map ∧
    entail cl_map inst_map ps (c,t) ∧
    super_reachable cl_map c s ⇒
    entail cl_map inst_map ps (s,t)
Proof
  metis_tac[entail_wf_super_reachable']
QED

Theorem entail_eq_full_entail:
  entail_wf cl_map inst_map ⇒
  ∀p. (entail cl_map inst_map ps p ⇔ full_entail cl_map inst_map ps p)
Proof
  strip_tac >>
  simp[EQ_IMP_THM,FORALL_AND_THM] >>
  conj_tac
  >- (
    ho_match_mp_tac entail_ind >>
    rw[]
    >- drule_all_then irule full_entail_mem
    >- (
      drule_at_then (Pos last) irule full_entail_super >>
      drule_then irule full_entail_mem
    )
    >- drule_all_then irule full_entail_inst
  ) >>
  ho_match_mp_tac full_entail_ind >>
  rw[]
  >- drule_all_then irule entail_mem
  >- drule_all_then irule entail_wf_super_reachable
  >- drule_all_then irule entail_inst
QED

Theorem entail_monotone:
  ∀p. entail cl_map inst_map ps p ⇒
  (∀q. MEM q ps ⇒ MEM q qs) ⇒
  entail cl_map inst_map qs p
Proof
  ho_match_mp_tac entail_ind >>
  rw[]
  >- (irule entail_mem >> metis_tac[])
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

Triviality type_size_GT_0:
  ∀t. 0 < type_size t
Proof
  Cases_on `t` >>
  simp[type_size_def]
QED

Theorem type_size_tcons_to_type:
  ∀t targs.
  MEM t targs ⇒
  type_size t < type_size (tcons_to_type tcons targs)
Proof
  Induct_on `targs` using SNOC_INDUCT >>
  rw[tcons_to_type_SNOC,type_size_def]
  >- rw[] >>
  irule arithmeticTheory.LESS_TRANS >>
  first_x_assum $ drule_then $ irule_at (Pos hd) >>
  DECIDE_TAC
QED

(* entail_aux terminates if every q in qs is smaller than t *)
Definition entail_aux_def:
  (entail_aux supers inst_map (c,t) =
    if well_scoped_inst_map inst_map
    then
      (EXISTS (\visited. lookup visited c = SOME t) supers ∨
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
    gvs[by_inst_lem] >>
    PURE_REWRITE_TAC[Once $ GSYM arithmeticTheory.GREATER_DEF] >>
    irule list_max_intro >>
    simp[EVERY_MAP,arithmeticTheory.GREATER_DEF,type_size_GT_0] >>
    drule_then (assume_tac o GSYM) tcons_to_type_split_ty_head >>
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
    entail (to_class_map cl_map) inst_map ps p)
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
    rw[]
    >- (irule entail_mem >> metis_tac[MEM_EL]) >>
    irule entail_super >> metis_tac[MEM_EL]
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
  map_ok cl_map ∧ map_ok inst_map ∧
  well_scoped_inst_map inst_map ∧ super_keys_ok cl_map ∧
  (∀q. MEM q ps ⇒ ∃clinfo. lookup cl_map (FST q) = SOME clinfo) ⇒
  entail_impl cl_map inst_map ps p =
    entail (to_class_map cl_map) inst_map ps p
Proof
  rw[oneline entail_impl_def] >>
  ntac 2 TOP_CASE_TAC
  >- (
    dxrule_then strip_assume_tac OPT_MMAP_NONE >>
    first_assum $ drule_then strip_assume_tac >>
    drule_all_then (qspec_then `SND x` mp_tac) $
      SRULE[PULL_EXISTS] $ iffLR well_formed_by_super >>
    rw[]
  ) >>
  dxrule_then strip_assume_tac OPT_MMAP_SOME_EL >>
  irule entail_aux_thm >>
  rw[]
QED

Theorem entail_impl_full_entail:
  map_ok cl_map ∧ map_ok inst_map ∧
  well_scoped_inst_map inst_map ∧ super_keys_ok cl_map ∧
  entail_wf (to_class_map cl_map) inst_map ∧
  (∀q. MEM q ps ⇒ ∃clinfo. lookup cl_map (FST q) = SOME clinfo) ⇒
  entail_impl cl_map inst_map ps p =
    full_entail (to_class_map cl_map) inst_map ps p
Proof
  metis_tac[entail_impl_thm,entail_eq_full_entail]
QED
*)

val _ = export_theory();
