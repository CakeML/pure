(* concrete data structures for implementing
* instance map and type class map *)
open HolKernel Parse boolLib bossLib dep_rewrite BasicProvers;
open relationTheory set_relationTheory;
open pairTheory optionTheory listTheory pred_setTheory finite_mapTheory;
open mlmapTheory mlstringTheory balanced_mapTheory alistTheory topological_sortTheory;
open miscTheory typeclass_unificationTheory
  typeclass_inference_commonTheory typeclass_tcexpTheory
  typeclass_specializeTheory;

val _ = new_theory "typeclass_env_map_impl";

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

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
    <| cstr : (mlstring # num) list (* class and type variable *)
     ; nargs : num (* number of arguments to the type constructor *)
     ; impl : (cvname, tcexp) mlmap$map |> (* function name and its expression *)
End

Type class_map_impl = ``:(mlstring, classinfo_impl) map``;
Type inst_map_impl = ``:((mlstring # ty_cons), instinfo_impl) map``;

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
  inst_map_cmp = mlstring$compare lexTO ty_consOrd
End

Theorem TO_inst_map_cmp:
  TotOrd inst_map_cmp
Proof
  metis_tac[inst_map_cmp_def,totoTheory.TO_lexTO,TotOrd_compare,TO_ty_consOrd]
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
    FMAP_MAP2 (λ(k,inf).
      <|cstr := inf.cstr
       ;nargs := inf.nargs
       ;impl := to_fmap inf.impl|>)
    (to_fmap m)
End

Definition head_ty_cons_def:
  head_ty_cons (Cons t1 t2) = head_ty_cons t1 ∧
  head_ty_cons (Atom $ TypeCons tc) = SOME tc ∧
  head_ty_cons (Atom _) = NONE
End

Definition ty_args_aux_def:
  ty_args_aux (Cons t1 t2) l = ty_args_aux t1 (t2::l) ∧
  ty_args_aux (Atom _) l = l
End

Definition ty_args_def:
  ty_args t = ty_args_aux t []
End

Triviality ty_args_aux_SNOC:
  ∀t t1 t2 l. t = Cons t1 t2 ⇒ ty_args_aux t l = ty_args_aux t1 [] ++ (t2::l)
Proof
  Induct_on `t` >>
  rw[] >>
  Cases_on `t` >>
  gvs[ty_args_aux_def]
QED

Theorem ty_args_SNOC:
  ty_args (Cons t1 t2) = SNOC t2 (ty_args t1)
Proof
  simp[ty_args_def,ty_args_aux_SNOC]
QED

Definition split_ty_head_aux_def:
  split_ty_head_aux (Cons t1 t2) l = split_ty_head_aux t1 (t2::l) ∧
  split_ty_head_aux (Atom $ TypeCons tc) l = SOME (tc,l) ∧
  split_ty_head_aux (Atom _) l = NONE
End

Triviality split_ty_head_aux_thm:
  ∀t l tc targs.
    split_ty_head_aux t l = SOME (tc,targs) ⇔
    (head_ty_cons t = SOME tc ∧ ty_args_aux t l = targs)
Proof
  ho_match_mp_tac head_ty_cons_ind >>
  rw[head_ty_cons_def,split_ty_head_aux_def,ty_args_aux_def]
QED

Definition split_ty_head_def:
  split_ty_head t = split_ty_head_aux t []
End

Theorem split_ty_head_thm:
  ∀t tc targs. 
    split_ty_head t = SOME (tc,targs) ⇔
    (head_ty_cons t = SOME tc ∧ ty_args t = targs)
Proof
  simp[split_ty_head_def,ty_args_def,split_ty_head_aux_thm]
QED

Definition add_instance_def:
  add_instance (inst_map:inst_map_impl) cl ty info =
    case lookup inst_map (cl,ty) of
    | NONE => SOME $ insert inst_map (cl,ty) info
    | SOME _ => NONE
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
    case lookup visited c of
    | SOME _ => SOME visited
    | NONE =>
      case mlmap$lookup cl_map c of
      | NONE => NONE
      | SOME clinfo =>
          by_super_aux_list cl_map (insert visited c t) clinfo.super t
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
         map_ok cl_map ∧ map_ok visited ∧ lookup visited c = NONE ∧
         lookup cl_map c = SOME clinfo ⇒
         P1 cl_map (insert visited c t) clinfo.super t) ⇒
      P0 cl_map visited c t) ∧
  (∀cl_map ret t. P1 cl_map ret [] t) ∧
  (∀cl_map visited sup xs t.
    (∀visited'.
       map_ok cl_map ∧ map_ok visited ∧
       by_super_aux cl_map visited sup t = SOME visited' ⇒
       P1 cl_map visited' xs t) ∧
    (map_ok cl_map ∧ map_ok visited ⇒ P0 cl_map visited sup t) ⇒
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
  (∀cl_map visited c (t:'a) new_visited.
    by_super_aux cl_map visited c t = SOME new_visited ∧
    map_ok visited ⇒
    ∃v. lookup new_visited c = SOME v) ∧
  (∀cl_map visited cs (t:'a) new_visited c.
    by_super_aux_list cl_map visited cs t = SOME new_visited ∧
    map_ok visited ∧
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
  (∀cl_map visited c (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux cl_map visited c t = SOME new_visited ⇒
    (∀c' v. lookup new_visited c' = SOME v ⇒
      RTC
        (λsrc dst. ∃v. FLOOKUP (to_fmap cl_map) src = SOME v ∧
        MEM dst v.super ∧ lookup visited dst = NONE) c c' ∨
      lookup visited c' = SOME v)) ∧

  (∀cl_map visited cs (t:'a) new_visited.
    map_ok visited ∧
    by_super_aux_list cl_map visited cs t = SOME new_visited ⇒
    (∀c' v. lookup new_visited c' = SOME v ⇒
      (∃c. MEM c cs ∧ lookup visited c = NONE ∧
        RTC
          (λsrc dst. ∃v. FLOOKUP (to_fmap cl_map) src = SOME v ∧
          MEM dst v.super ∧ lookup visited dst = NONE) c c') ∨
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
        gvs[GSYM mlmapTheory.lookup_thm,
          mlmapTheory.lookup_insert,AllCaseEqs()] >>
        disj1_tac >>
        irule $ cj 2 RTC_RULES >>
        qexists `c''` >>
        fs[GSYM mlmapTheory.lookup_thm] >>
        drule_at_then (Pos last) irule RTC_MONOTONE >>
        rw[GSYM mlmapTheory.lookup_thm,mlmapTheory.lookup_insert] >>
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
    gvs[GSYM mlmapTheory.lookup_thm] >>
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
      qexists `c'''` >>
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
    qexists `c'''` >>
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
  (∀cl_map visited c (t:'a) new_visited s.
    map_ok visited ∧
    by_super_aux cl_map visited c t = SOME new_visited ∧
    lookup visited c = NONE ∧
    RTC (λsrc dst. ∃v. FLOOKUP (to_fmap cl_map) src = SOME v ∧
      MEM dst v.super ∧ lookup visited dst = NONE) c s ⇒
    ∃v. lookup new_visited s = SOME v) ∧

  (∀cl_map visited cs (t:'a) new_visited c s.
    map_ok visited ∧
    by_super_aux_list cl_map visited cs t = SOME new_visited ∧
    MEM c cs ∧ lookup visited c = NONE ∧
    RTC (λsrc dst. ∃v. FLOOKUP (to_fmap cl_map) src = SOME v ∧
      MEM dst v.super ∧ lookup visited dst = NONE) c s ⇒
    ∃v. lookup new_visited s = SOME v)
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
      simp[GSYM mlmapTheory.lookup_thm]
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
      strip_tac >>
      last_x_assum $ qspecl_then [`0`,`n + 2`] mp_tac >>
      simp[]
    )
    >- (
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
    gvs[PULL_EXISTS,GSYM mlmapTheory.lookup_thm] >>
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
      rw[GSYM mlmapTheory.lookup_thm] >>
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
  (∀cl_map visited c (t:'a) clinfo.
    map_ok cl_map ∧ map_ok visited ∧
    (∀c clinfo c'.
      mlmap$lookup cl_map c = SOME clinfo ∧ MEM c' clinfo.super ⇒
      ∃x. mlmap$lookup cl_map c' = SOME x) ⇒
    ((∃clinfo. mlmap$lookup cl_map c = SOME clinfo ∨
      (∃m. lookup visited c = SOME m)) ⇔
    (∃m. by_super_aux cl_map visited c t = SOME m))) ∧

  ∀cl_map visited cs (t:'a).
    map_ok cl_map ∧ map_ok visited ∧
    (∀c clinfo c'.
      mlmap$lookup cl_map c = SOME clinfo ∧ MEM c' clinfo.super ⇒
      ∃x. mlmap$lookup cl_map c' = SOME x) ⇒
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
    metis_tac[]
  ) >>
  rw[Once full_by_super_aux_def] >>
  TOP_CASE_TAC >>
  gvs[] >- metis_tac[] >>
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

Theorem by_super_thm:
  by_super cl_map (c,t) = SOME visited ⇒
  (∀s v. (mlmap$lookup visited s = SOME v) ⇔
    (v = t ∧
      (c = s ∨ super_reachable (to_class_map cl_map) c s)))
Proof
  simp[super_reachable_def,to_class_map_def,by_super_def,
    FMAP_MAP2_THM,FLOOKUP_FMAP_MAP2,PULL_EXISTS,
    GSYM RTC_CASES_TC] >>
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
      simp[mlmapTheory.lookup_thm,mlmapTheory.empty_thm] >>
      metis_tac[]
    ) >>
    drule_all $ cj 1 by_super_aux_IMP_reachable >>
    simp[mlmapTheory.lookup_thm,mlmapTheory.empty_thm]
  ) >>
  drule_then drule $ cj 1 super_reachable_IMP_by_super_aux >>
  simp[mlmapTheory.lookup_thm,mlmapTheory.empty_thm] >>
  rw[] >>
  first_x_assum drule >>
  metis_tac[]
QED

Theorem well_formed_by_super:
  ∀cl_map c (t:'a) clinfo.
    map_ok cl_map ∧
    (∀c clinfo c'.
      mlmap$lookup cl_map c = SOME clinfo ∧ MEM c' clinfo.super ⇒
      ∃x. mlmap$lookup cl_map c' = SOME x) ⇒
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
    OPTION_BIND (split_ty_head t) (λ(tcons,targs).
      OPTION_BIND (lookup inst_map (c,tcons)) (λinst_info.
      if LENGTH targs = inst_info.nargs
      then
        SOME $ (inst_info.impl, MAP (I ## flip EL targs) inst_info.cstr)
      else NONE))
End

Definition by_inst_def:
  by_inst inst_map c t = OPTION_MAP SND $ lookup_inst_map inst_map c t
End

Theorem lookup_inst_map_thm:
  ∀inst_map c t impl cstr.
    (∃tcons targs inst_info.
      split_ty_head t = SOME (tcons,targs) ∧
      lookup inst_map (c,tcons) = SOME inst_info ∧
      LENGTH targs = inst_info.nargs ∧
      impl = inst_info.impl ∧
      LENGTH cstr = LENGTH inst_info.cstr ∧
      (∀n. n < LENGTH inst_info.cstr ⇒
        let (cl,v) = EL n inst_info.cstr in
          EL n cstr = (cl,EL v targs)))
    ⇔
    lookup_inst_map inst_map c t = SOME (impl,cstr)
Proof
  rw[lookup_inst_map_def,EQ_IMP_THM]
  >- (
    simp[] >>
    irule LIST_EQ >>
    rw[EL_MAP,oneline PAIR_MAP_THM] >>
    CASE_TAC >>
    first_x_assum drule >>
    simp[]
  ) >>
  pairarg_tac >>
  gvs[] >>
  rw[] >>
  pairarg_tac >>
  gvs[EL_MAP,oneline PAIR_MAP_THM]
QED

Theorem by_inst_thm:
  ∀inst_map c t cstr.
    (∃tcons targs inst_info.
      split_ty_head t = SOME (tcons,targs) ∧
      lookup inst_map (c,tcons) = SOME inst_info ∧
      LENGTH targs = inst_info.nargs ∧
      LENGTH cstr = LENGTH inst_info.cstr ∧
      (∀n. n < LENGTH inst_info.cstr ⇒
        let (cl,v) = EL n inst_info.cstr in
          EL n cstr = (cl,EL v targs)))
    ⇔
    by_inst inst_map c t = SOME cstr
Proof
  simp[by_inst_def,LAMBDA_PROD,GSYM PEXISTS_THM,GSYM lookup_inst_map_thm]
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

(*
Theorem entail_tsubst:
  ∀p. entail cl_map inst_map ps p ⇒
  ∀c t ts. p = (c,t) ⇒
  entail cl_map inst_map (MAP (λ(c',t'). (c',tsubst ts t')) ps) (c,tsubst ts t)
Proof
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
  drule by_inst_SOME >>
  rw[] >>
  irule EQ_TRANS >>
  irule_at (Pos hd) $ cj 4 by_inst_thm >>
  simp[]
QED

(* `entail` is equivalent to `full_entail`
* if for every instance in inst_map,
* the constraint ps for the instance (c,t)
* `entail`s (s,t) for all super class s of c *)
Definition entail_wf_def:
  entail_wf cl_map inst_map ⇔
  ∀c inst instl t clinfo s.
    lookup inst_map c = SOME instl ∧ MEM (t,inst) instl ∧
    FLOOKUP cl_map c = SOME clinfo ∧ MEM s clinfo.super ⇒
    entail cl_map inst_map (MAP (I ## TypeVar) inst.cstr) (s,t)
End

Theorem entail_wf_super:
  entail_wf cl_map inst_map ⇒
  FLOOKUP cl_map c = SOME clinfo ∧
  MEM s clinfo.super ∧
  entail cl_map inst_map ps (c,t) ⇒
  entail cl_map inst_map ps (s,t)
Proof
  rw[] >>
  pop_assum $ strip_assume_tac o SRULE[Once entail_cases]
  >- (
    irule entail_super >>
    first_assum $ irule_at (Pos hd) >>
    simp[super_reachable_def] >>
    irule TC_SUBSET >>
    simp[]
  )
  >- (
    irule entail_super >>
    first_assum $ irule_at (Pos hd) >>
    fs[super_reachable_def] >>
    irule TC_RIGHT1_I >>
    first_assum $ irule_at (Pos last) >>
    simp[]
  )
  >- (
    drule by_inst_SOME >>
    rw[] >>
    fs[entail_wf_def] >>
    last_x_assum drule >>
    disch_then $ drule_at_then (Pos last) (drule_at (Pos last)) >>
    disch_then $ qspecl_then
      [`SND (EL i instl)`,`FST (EL i instl)`] mp_tac >>
    impl_tac
    >- (
      rw[MEM_EL]  >>
      metis_tac[]
    ) >>
    gvs[] >>
  )
QED

Theorem entail_wf_super_reachable:
  entail_wf cl_map inst_map ⇒
  ∀c s. super_reachable cl_map c s ⇒
    entail cl_map inst_map ps (c,t) ⇒
    entail cl_map inst_map ps (s,t)
Proof
  strip_tac >>
  simp[super_reachable_def] >>
  ho_match_mp_tac TC_INDUCT_LEFT1 >>
  rw[] >>
  metis_tac[entail_wf_super]
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

Definition entail_terminate_wf_def:
  entail_terminate_wf inst_map ⇔
  ∀c instl t inst.
    lookup inst_map c = SOME instl ∧
    MEM (t,inst) instl ∧
    (∀x. t ≠ TypeVar x)
End

Definition inst_map_scoped_def:
  inst_map_scoped inst_map ⇔
  ∀c instl t inst.
    lookup inst_map c = SOME instl ∧
    MEM (t,inst) instl ∧
    (∀c' v. MEM (c',v) inst.cstr ⇒ scoped c t)
End

(* entail_aux terminates if every q in qs is smaller than t *)
Definition entail_aux_def:
  (entail_aux supers inst_map (c,t) =
    if entail_terminate_wf inst_map
    then
      EXISTS (\visited. lookup visited c = SOME t) supers ∨
      (case by_inst inst_map c t of
        | NONE => F
        | SOME qs => entail_aux_list supers inst_map qs)
     else F (* should never happen *)) ∧
  ((entail_aux_list supers inst_map [] = T) ∧
  (entail_aux_list supers inst_map (q::qs) =
    (entail_aux supers inst_map q) ∧
     entail_aux_list supers inst_map qs))
Termination
  (* LENGTH LEX type_size *)
  WF_REL_TAC `_ LEX _` >>
  cheat
End

Definition entail_impl_def:
  entail_impl cl_map inst_map ps (c,t) =
   case OPT_MMAP (by_super cl_map) ps of
   | NONE => F
   | SOME visiteds => entail_aux visiteds inst_map (c,t)
End
*)

val _ = export_theory();
