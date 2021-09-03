
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory rich_listTheory finite_mapTheory pred_setTheory;
open pure_typingTheory pure_cexpTheory pure_configTheory pure_varsTheory
     pure_inference_commonTheory pure_inferenceTheory pure_unificationTheory
     pure_miscTheory;

val _ = new_theory "pure_inference_model";

Datatype:
  mconstraint = mUnify itype itype
             | mInstantiate itype (num # itype)
             | mImplicit itype (num set) itype
End

Type massumptions[pp] = ``:string |-> num set``;

Definition get_massumptions_def:
  get_massumptions (as : massumptions) x =
    case FLOOKUP as x of NONE => {} | SOME xas => xas
End

Definition maunion_def:
  maunion = FMERGE $UNION : massumptions -> massumptions -> massumptions
End

Definition massumptions_ok_def:
  massumptions_ok (asms : massumptions) ⇔
    ∀k v x. FLOOKUP asms k = SOME v ∧ x ∈ v (* if assumption k |-> x is present *)
    ⇒ x ∉ BIGUNION (FRANGE (asms \\ k)) (* then x is unique *)
End

Definition list_disjoint_def:
  list_disjoint l ⇔
    ∀left mid right.
      l = left ++ [mid] ++ right
    ⇒ DISJOINT mid (BIGUNION (set (left ++ right)))
End

Theorem list_disjoint_doubleton[simp]:
  list_disjoint [a;b] ⇔ DISJOINT a b
Proof
  rw[list_disjoint_def] >> eq_tac >> rw[]
  >- (first_x_assum irule >> qexistsl_tac [`[]`] >> simp[]) >>
  Cases_on `left` >> gvs[] >> Cases_on `t` >> gvs[] >> simp[DISJOINT_SYM]
QED

Theorem list_disjoint_append:
  ∀l1 l2. list_disjoint (l1 ++ l2) ⇔
    list_disjoint l1 ∧ list_disjoint l2 ∧
    DISJOINT (BIGUNION (set l1)) (BIGUNION (set l2))
Proof
  rw[list_disjoint_def] >> eq_tac >> rw[]
  >- (first_x_assum irule >> qexists_tac `left` >> simp[])
  >- (first_x_assum irule >> qexists_tac `left` >> simp[])
  >- (first_x_assum irule >> qexists_tac `l1 ++ left` >> simp[])
  >- (first_x_assum irule >> qexists_tac `l1 ++ left` >> simp[])
  >- (
    first_x_assum irule >> last_x_assum assume_tac >>
    drule_at Concl $ iffLR MEM_SING_APPEND >> simp[] >> strip_tac >> gvs[] >>
    qexists_tac `a` >> simp[]
    )
  >- (
    qpat_x_assum `_ ++ _ = _` mp_tac >>
    simp[APPEND_EQ_APPEND_MID] >> rw[] >> gvs[]
    >- (last_x_assum irule >> qexists_tac `left` >> simp[])
    >- (first_x_assum drule >> simp[Once DISJOINT_SYM])
    >- (last_x_assum kall_tac >> last_x_assum irule >> qexists_tac `l` >> simp[])
    )
  >- (
    qpat_x_assum `_ ++ _ = _` mp_tac >>
    simp[APPEND_EQ_APPEND_MID] >> rw[] >> gvs[]
    >- (last_x_assum irule >> qexists_tac `left` >> simp[])
    >- (last_x_assum kall_tac >> last_x_assum irule >> qexists_tac `l` >> simp[])
    )
QED

Theorem TAKE_EL_DROP:
  ∀n l. n < LENGTH l ⇒
    l = TAKE n l ++ [EL n l] ++ DROP (SUC n) l
Proof
  rw[] >>
  qspecl_then [`1`,`n`,`l`] assume_tac TAKE_SEG_DROP >> gvs[SEG1, ADD1]
QED

Theorem list_disjoint_ALL_DISTINCT:
  ∀l. EVERY FINITE l ⇒
    (list_disjoint l ⇔ ALL_DISTINCT (FLAT $ MAP SET_TO_LIST l))
Proof
  rw[list_disjoint_def, miscTheory.ALL_DISTINCT_FLAT] >>
  eq_tac >> rw[]
  >- (gvs[MEM_MAP, EVERY_MEM])
  >- (
    gvs[EL_MAP] >>
    `∃a b c. l = a ++ [EL i l] ++ b ++ [EL j l] ++ c` by (
      qexistsl_tac [`TAKE i l`,`SEG (j - SUC i) (SUC i) l`,`DROP (SUC j) l`] >>
      `∃k. j = i + k ∧ 0 < k` by (
        qpat_x_assum `_ < _` kall_tac >>
        drule LESS_STRONG_ADD >> rw[] >> simp[]) >>
      gvs[] >>
      qspecl_then [`i`,`l`] assume_tac TAKE_EL_DROP >> gvs[] >>
      first_assum $ (fn th => rewrite_tac[Once th, SimpLHS]) >> simp[] >>
      once_rewrite_tac[GSYM APPEND_ASSOC] >> rewrite_tac[GSYM CONS_APPEND] >>
      DEP_REWRITE_TAC[GSYM DROP_CONS_EL] >> simp[SEG_TAKE_DROP, ADD1] >>
      qspecl_then [`DROP i l`,`1`,`k`] assume_tac $ GSYM DROP_TAKE >>
      gvs[DROP_DROP_T] >>
      qspecl_then [`1`,`TAKE k (DROP i l)`,`DROP k (DROP i l)`] assume_tac $
        GSYM DROP_APPEND >>
      gvs[] >> `1 - k = 0` by DECIDE_TAC >> pop_assum $ SUBST_ALL_TAC >>
      gvs[DROP_DROP_T]) >>
    rename1 `_ ++ [ii] ++ _ ++ [jj] ++ _` >>
    pop_assum $ SUBST_ALL_TAC >> gvs[] >>
    first_x_assum $ qspec_then `a` assume_tac >> gvs[] >>
    pop_assum $ qspec_then `jj` assume_tac >> gvs[DISJOINT_ALT]
    )
  >- (
    gvs[EL_MAP] >> pop_assum mp_tac >> rw[MEM_EL, DISJOINT_ALT] >>
    first_x_assum $ qspecl_then [`n`,`LENGTH left`] assume_tac >>
    gvs[EL_APPEND_EQN, EVERY_EL, MEM_SET_TO_LIST] >> CCONTR_TAC >> gvs[]
    )
  >- (
    gvs[EL_MAP] >> pop_assum mp_tac >> rw[MEM_EL, DISJOINT_ALT] >>
    first_x_assum $ qspecl_then [`LENGTH left`,`LENGTH left + n + 1`] assume_tac >>
    gvs[EL_APPEND_EQN, EVERY_EL, MEM_SET_TO_LIST] >> CCONTR_TAC >> gvs[]
    )
QED

Definition used_vars_constraint_def:
  used_vars_constraint (mUnify t1 t2) = pure_vars t1 ∪ pure_vars t2 ∧
  used_vars_constraint (mImplicit t1 vars t2) = vars ∪ pure_vars t1 ∪ pure_vars t2 ∧
  used_vars_constraint (mInstantiate t (vars, scheme)) = pure_vars t ∪ pure_vars scheme
End

Definition used_vars_def:
  used_vars (asms : massumptions) cs ts =
    BIGUNION (FRANGE asms) ∪
    BIGUNION (IMAGE used_vars_constraint cs) ∪
    BIGUNION (IMAGE pure_vars ts)
End

Theorem massumptions_ok_maunion:
  ∀as bs.
    massumptions_ok as ∧ massumptions_ok bs ∧
    DISJOINT (BIGUNION (FRANGE as)) (BIGUNION (FRANGE bs))
  ⇒ massumptions_ok (maunion as bs)
Proof
  rw[massumptions_ok_def, DISJ_EQ_IMP] >>
  gvs[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM, PULL_EXISTS,
      maunion_def, FLOOKUP_FMERGE] >> rw[] >>
  every_case_tac >> gvs[] >> metis_tac[DISJOINT_ALT]
QED

Theorem BIGUNION_FRANGE_maunion:
  ∀as bs.
    BIGUNION (FRANGE (maunion as bs)) =
    BIGUNION (FRANGE as) ∪ BIGUNION (FRANGE bs)
Proof
  rw[] >> once_rewrite_tac[EXTENSION] >>
  rw[] >> eq_tac >> rw[] >>
  gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, maunion_def, FLOOKUP_FMERGE]
  >- (every_case_tac >> gvs[] >> metis_tac[])
  >- (
    Cases_on `FLOOKUP bs k` >> gvs[]
    >- (goal_assum drule >> qexists_tac `k` >> simp[])
    >- (qexistsl_tac [`s ∪ x'`,`k`] >> simp[])
    )
  >- (
    Cases_on `FLOOKUP as k` >> gvs[]
    >- (goal_assum drule >> qexists_tac `k` >> simp[])
    >- (qexistsl_tac [`s ∪ x'`,`k`] >> simp[UNION_COMM])
    )
QED

Definition cvars_disjoint_def:
  cvars_disjoint l ⇔ list_disjoint (MAP (λ(as,cs,t). used_vars as cs {t}) l)
End

(* TODO delete
Definition massumptions_list_ok_def:
  massumptions_list_ok (asms : massumptions list) ⇔
    EVERY massumptions_ok asms ∧
    (* each assumption k |-> x has x unique within the list *)
    ∀left mid right x.
      asms = left ++ [mid] ++ right ∧
      x ∈ BIGUNION (FRANGE mid)
    ⇒ x ∉ BIGUNION $ set (MAP (BIGUNION o FRANGE) (left ++ right))
End

Theorem massumptions_list_ok_remove:
  ∀al a ar.
    massumptions_list_ok (al ++ [a] ++ ar) ⇒ massumptions_list_ok (al ++ ar)
Proof
  rw[massumptions_list_ok_def, DISJ_EQ_IMP] >>
  gvs[combinTheory.o_DEF, MEM_MAP] >> rw[] >>
  gvs[PULL_EXISTS, PULL_FORALL, AND_IMP_INTRO, IMP_CONJ_THM] >>
  gvs[FORALL_AND_THM, PULL_EXISTS, GSYM CONJ_ASSOC] >>
  qpat_x_assum `_ ++ _ = _` mp_tac >>
  simp[APPEND_EQ_APPEND_MID] >> rw[] >> gvs[]
  >- (
    first_x_assum $ qspec_then `left` mp_tac >> gvs[] >>
    rpt $ disch_then $ drule_at $ Pos last >> simp[]
    )
  >- (
    first_x_assum $ qspec_then `al ++ [a] ++ l` mp_tac >> gvs[] >>
    rpt $ disch_then $ drule_at $ Pos last >> simp[]
    )
  >- (
    last_x_assum $ qspec_then `left` mp_tac >> gvs[] >>
    rpt $ disch_then $ drule_at $ Pos last >> simp[]
    )
  >- (
    last_x_assum $ qspec_then `al ++ [a] ++ l` mp_tac >> gvs[] >>
    rpt $ disch_then $ drule_at $ Pos last >> simp[]
    )
QED
*)

Inductive minfer:
[~Var:]
  (fresh ∉ mset
    ⇒ minfer (ns : exndef # typedefs) mset (pure_cexp$Var d x)
        (FEMPTY |+ (x, {fresh})) {} (CVar fresh)) ∧

[~Tuple:]
  (LENGTH es = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ(e,ty) (a,c). minfer ns mset e a c ty)
      (ZIP (es,tys)) (ZIP (ass,css)) ∧
   cvars_disjoint (ZIP (ass, ZIP (css, tys)))
    ⇒ minfer ns mset (Prim d (Cons "") es)
        (FOLDR maunion FEMPTY ass) (BIGUNION (set css)) (Tuple tys)) ∧

[~Ret:]
  (minfer ns mset e as cs ty
    ⇒ minfer ns mset (Prim d (Cons "Ret") [e])
        as cs (M ty)) ∧

[~Bind:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f1 ∉ mset ∪ used_vars (maunion as1 as2) (cs1 ∪ cs2) {ty1;ty2} ∧
   f2 ∉ mset ∪ used_vars (maunion as1 as2) (cs1 ∪ cs2) {ty1;ty2}
    ⇒ minfer ns mset (Prim d (Cons "Bind") [e1;e2])
        (maunion as1 as2)
        ({mUnify ty1 (M $ CVar f1); mUnify ty2 (Function (CVar f1) (M $ CVar f2))}
          ∪ cs1 ∪ cs2)
        (M $ CVar f2)) ∧

[~Raise:]
  (minfer ns mset e as cs ty ∧
   f ∉ mset ∪ used_vars as cs {ty}
    ⇒ minfer ns mset (Prim d (Cons "Raise") [e])
        as (mUnify ty Exception INSERT cs) (M $ CVar f)) ∧

[~Handle:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f1 ∉ mset ∪ used_vars (maunion as1 as2) (cs1 ∪ cs2) {ty1; ty2} ∧
   f2 ∉ mset ∪ used_vars (maunion as1 as2) (cs1 ∪ cs2) {ty1; ty2}
    ⇒ minfer ns mset (Prim d (Cons "Handle") [e1;e2])
        (maunion as1 as2)
        ({mUnify ty1 (M $ CVar f1); mUnify ty2 (Function Exception (M $ CVar f2))}
          ∪ cs1 ∪ cs2)
        (M $ CVar f2)) ∧

[~Act:]
  (minfer ns mset e as cs ty
    ⇒ minfer ns mset (Prim d (Cons "Act") [e])
        as (mUnify ty (PrimTy Message) INSERT cs) (M StrTy)) ∧

[~Alloc:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)]
    ⇒ minfer ns mset (Prim d (Cons "Alloc") [e1;e2])
        (maunion as1 as2)
        (mUnify ty1 IntTy INSERT cs1 ∪ cs2)
        (M $ Array ty2)) ∧

[~Length:]
  (minfer ns mset e as cs ty ∧
   f ∉ mset ∪ used_vars as cs {ty}
    ⇒ minfer ns mset (Prim d (Cons "Length") [e])
        as (mUnify ty (Array $ CVar fresh) INSERT cs) (M IntTy)) ∧

[~Deref:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f ∉ mset ∪ used_vars (maunion as1 as2) (cs1 ∪ cs2) {ty1;ty2}
    ⇒ minfer ns mset (Prim d (Cons "Deref") [e1;e2])
        (maunion as1 as2)
        ({mUnify ty2 IntTy; mUnify ty1 (Array $ CVar f)} ∪ cs1 ∪ cs2)
        (M $ CVar f)) ∧

[~Update:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   minfer ns mset e3 as3 cs3 ty3 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2);(as3,cs3,ty3)] ∧
   f ∉ mset ∪ used_vars as (cs1 ∪ cs2 ∪ cs3) {ty1;ty2;ty3}
    ⇒ minfer ns mset (Prim d (Cons "Update") [e1;e2;e3])
        as
        ({mUnify ty3 (CVar f); mUnify ty2 IntTy; mUnify ty1 (Array $ CVar f)}
          ∪ cs1 ∪ cs2 ∪ cs3)
        (M Unit)) ∧

[~True:]
  (minfer ns mset (Prim d (Cons "True") []) FEMPTY {} BoolTy) ∧
[~False:]
  (minfer ns mset (Prim d (Cons "False") []) FEMPTY {} BoolTy) ∧
[~Subscript:]
  (minfer ns mset (Prim d (Cons "Subscript") []) FEMPTY {} Exception) ∧

[~Exception:]
  (LENGTH es = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ(e,ty) (a,c). minfer ns mset e a c ty)
      (ZIP (es,tys)) (ZIP (ass,css)) ∧
   cvars_disjoint (ZIP (ass, ZIP (css, tys))) ∧
   ALOOKUP (FST ns) s = SOME arg_tys ∧
   LENGTH arg_tys = LENGTH tys ∧
   s ∉ reserved_cns
    ⇒ minfer ns mset (Prim d (Cons s) es)
        (FOLDR maunion FEMPTY ass)
        (set (list$MAP2 (λt a. mUnify t (itype_of a)) tys arg_tys) ∪ BIGUNION (set css))
        Exception) ∧

[~Cons:]
  (LENGTH es = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ(e,ty) (a,c). minfer ns mset e a c ty)
      (ZIP (es,tys)) (ZIP (ass,css)) ∧
   cvars_disjoint (ZIP (ass, ZIP (css, tys))) ∧
   id < LENGTH (SND ns) ∧
   EL id (SND ns) = (ar,cns) ∧
   ALOOKUP cns cname = SOME arg_tys ∧
   LENGTH arg_tys = LENGTH tys ∧
   LENGTH freshes = ar ∧
   EVERY (λf.
    f ∉ mset ∪ used_vars (FOLDR maunion FEMPTY ass) (BIGUNION (set css)) (set tys))
      freshes ∧
   s ∉ reserved_cns
    ⇒ minfer ns mset (Prim d (Cons s) es)
        (FOLDR maunion FEMPTY ass)
        (set (list$MAP2 (λt a. mUnify t (isubst cfreshes $ itype_of a)) tys arg_tys) ∪
          BIGUNION (set css))
        (TypeCons id (MAP CVar freshes))) ∧

[~AtomOp:]
  (infer_atom_op (LENGTH es) aop = SOME (parg_tys, pret_ty) ∧
   LENGTH es = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ(e,ty) (a,c). minfer ns mset e a c ty)
      (ZIP (es,tys)) (ZIP (ass,css)) ∧
   cvars_disjoint (ZIP (ass, ZIP (css, tys)))
    ⇒ minfer ns mset (Prim d (AtomOp aop) es)
        (FOLDR maunion FEMPTY ass)
        (set (list$MAP2 (λt a. mUnify t (PrimTy a)) tys parg_tys) ∪ BIGUNION (set css))
        (PrimTy pret_ty)) ∧

[~Seq:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)]
    ⇒ minfer ns mset (Prim d Seq [e1;e2])
        (maunion as1 as2) (cs1 ∪ cs2) ty2) ∧

[~App:]
  (LENGTH es = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ(e,ty) (a,c). minfer ns mset e a c ty)
      (ZIP (es,tys)) (ZIP (ass,css)) ∧
   minfer ns mset e fas fcs fty ∧
   cvars_disjoint ((fas,fcs,fty)::ZIP (ass, ZIP (css, tys))) ∧
   as = FOLDR maunion FEMPTY (fas::ass) ∧
   cs = fcs ∪ BIGUNION (set css) ∧
   f ∉ mset ∪ used_vars as cs (fty INSERT set tys)
    ⇒ minfer ns mset (App d e es)
        as (mUnify fty (iFunctions tys (CVar f)) INSERT cs) (CVar f)) ∧

[~Lam:]
  (¬NULL xs ∧
   minfer ns (set freshes ∪ mset) e as cs ty ∧
   LENGTH freshes = LENGTH xs ∧
   EVERY (λf. f ∉ mset ∪ used_vars as cs {ty}) freshes
    ⇒ minfer ns mset (Lam d xs e)
        (FDIFF as (set xs))
        (cs ∪ (BIGUNION $ set $ list$MAP2 (λf x.
          IMAGE (λn. mUnify (CVar f) (CVar n)) (get_massumptions as x)) freshes xs))
        (iFunctions (MAP CVar freshes) ty)) ∧

[~Let:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)]
    ⇒ minfer ns mset (Let d x e1 e2)
        (maunion as1 (as2 \\ x))
        (IMAGE (λn. mImplicit (CVar n) mset ty1) (get_massumptions as2 x) ∪ cs1 ∪ cs2)
        ty2) ∧

[~Letrec:]
  (LENGTH fns = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ((fn,e),ty) (a,c). minfer ns mset e a c ty)
      (ZIP (fns,tys)) (ZIP (ass,css)) ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint ((eas,ecs,ety)::ZIP (ass, ZIP (css, tys))) ∧
   as = FOLDR maunion FEMPTY (eas::ass) ∧
   cs = ecs ∪ BIGUNION (set css)
    ⇒ minfer ns mset (Letrec d fns e)
        (FDIFF as (set $ MAP FST fns))
        (cs ∪ (BIGUNION $ set $ list$MAP2 (λ(x,b) tyfn.
          IMAGE (λn. mImplicit (CVar n) mset tyfn) (get_massumptions as x)) fns tys))
        ety) ∧

[~TupleCase:]
  (¬MEM v pvars ∧
   minfer ns (f INSERT set freshes ∪ mset) rest asrest csrest tyrest ∧
   minfer ns mset rest eas ecs ety ∧
   f ∉ mset ∪ used_vars (maunion eas asrest) (ecs ∪ csrest) {ety; tyrest} ∧
   EVERY (λf.
    f ∉ mset ∪ used_vars (maunion eas asrest) (ecs ∪ csrest) {ety; tyrest})
    freshes ∧
   pvar_cs =
    list$MAP2
      (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions asrest v))
      (v::pvars) (MAP CVar $ f::freshes)
    ⇒ minfer ns mset (Case d e v [("",pvars,rest)])
        (maunion as (FDIFF asrest (set (v::pvars))))
        (mUnify (CVar f) tye INSERT mUnify tye (Tuple $ MAP CVar freshes) INSERT
          BIGUNION (set pvar_cs) ∪ cs)
        tyrest) ∧

[~Case:]
  (¬MEM v (FLAT (MAP (FST o SND) cases)) ∧
   get_typedef 0 (SND ns)
    (MAP (λ(cn,pvs,_). (cn, LENGTH pvs)) cases) = SOME (id, ar, cdefs) ∧
   expected_arg_tys =
    MAP (λ(cn,ts). (cn, MAP (isubst (MAP CVar freshes) o itype_of) ts)) cdefs ∧
   LENGTH cases = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ((cname,pvars,rest),ty) (a,c).
      ∃asrest csrest.
        minfer ns (f INSERT set freshes ∪ mset) rest asrest csrest ty ∧
        ALOOKUP expected_arg_tys cname = SOME expected_cname_arg_tys ∧
        let pvar_cs = list$MAP2
          (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions asrest v))
          (v::pvars) (CVar f :: expected_cname_arg_tys) in
        a = FDIFF asrest (v INSERT set pvars) ∧
        c = BIGUNION (set pvar_cs) ∪ csrest)
      (ZIP (cases,tys)) (ZIP (ass,css)) ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint ((eas,ecs,ety)::ZIP (ass, ZIP (css, tys))) ∧
   as = FOLDR maunion FEMPTY (eas::ass) ∧
   cs = ecs ∪ BIGUNION (set css) ∧
   f ∉ mset ∪ used_vars as cs (ety INSERT set tys) ∧
   EVERY (λf.  f ∉ mset ∪ used_vars as cs (ety INSERT set tys)) freshes
    ⇒ minfer ns mset (Case d e v cases)
        as
        (mUnify (CVar f) tye INSERT mUnify tye (TypeCons id (MAP CVar freshes)) INSERT
          set (MAP (λt. mUnify (HD tys) t) (TL tys)) ∪ cs)
        (HD tys))
End

val _ = export_theory();

