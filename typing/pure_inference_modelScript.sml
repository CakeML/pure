
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory rich_listTheory finite_mapTheory pred_setTheory
     sptreeTheory;
open mlmapTheory;
open pure_typingTheory pure_typingPropsTheory
     pure_cexpTheory pure_configTheory pure_varsTheory pure_unificationTheory
     pure_inference_commonTheory pure_inferenceTheory pure_inferencePropsTheory
     pure_miscTheory;

val _ = new_theory "pure_inference_model";

(******************** Definitions ********************)

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

Definition new_vars_constraint_def[simp]:
  new_vars_constraint (mUnify t1 t2) = pure_vars t1 ∪ pure_vars t2 ∧
  new_vars_constraint (mImplicit t1 vars t2) = pure_vars t1 ∪ pure_vars t2 ∧
  new_vars_constraint (mInstantiate t (vars, scheme)) = pure_vars t ∪ pure_vars scheme
End

Definition new_vars_def:
  new_vars (asms : massumptions) cs t =
    BIGUNION (FRANGE asms) ∪
    BIGUNION (IMAGE new_vars_constraint cs) ∪
    pure_vars t
End

Definition cvars_disjoint_def:
  cvars_disjoint l ⇔ list_disjoint (MAP (λ(as,cs,t). new_vars as cs t) l)
End

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
   f1 ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2 ∧
   f2 ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2
    ⇒ minfer ns mset (Prim d (Cons "Bind") [e1;e2])
        (maunion as1 as2)
        ({mUnify ty1 (M $ CVar f1); mUnify ty2 (Function (CVar f1) (M $ CVar f2))}
          ∪ cs1 ∪ cs2)
        (M $ CVar f2)) ∧

[~Raise:]
  (minfer ns mset e as cs ty ∧
   f ∉ mset ∪ new_vars as cs ty
    ⇒ minfer ns mset (Prim d (Cons "Raise") [e])
        as (mUnify ty Exception INSERT cs) (M $ CVar f)) ∧

[~Handle:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2
    ⇒ minfer ns mset (Prim d (Cons "Handle") [e1;e2])
        (maunion as1 as2)
        ({mUnify ty1 (M $ CVar f); mUnify ty2 (Function Exception (M $ CVar f))}
          ∪ cs1 ∪ cs2)
        (M $ CVar f)) ∧

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
   fresh ∉ mset ∪ new_vars as cs ty
    ⇒ minfer ns mset (Prim d (Cons "Length") [e])
        as (mUnify ty (Array $ CVar fresh) INSERT cs) (M IntTy)) ∧

[~Deref:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2
    ⇒ minfer ns mset (Prim d (Cons "Deref") [e1;e2])
        (maunion as1 as2)
        ({mUnify ty2 IntTy; mUnify ty1 (Array $ CVar f)} ∪ cs1 ∪ cs2)
        (M $ CVar f)) ∧

[~Update:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   minfer ns mset e3 as3 cs3 ty3 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2);(as3,cs3,ty3)] ∧
   f ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2 ∪ new_vars as3 cs3 ty3
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
   EVERY (λf. f ∉ mset ∧
    EVERY (λ(as,cs,ty). f ∉ new_vars as cs ty) (ZIP (ass,ZIP(css,tys)))) freshes ∧
   s ∉ reserved_cns
    ⇒ minfer ns mset (Prim d (Cons s) es)
        (FOLDR maunion FEMPTY ass)
        (set (list$MAP2
              (λt a. mUnify t (isubst (MAP CVar freshes) $ itype_of a)) tys arg_tys) ∪
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
   f ∉ mset ∧
   EVERY (λ(as,cs,ty). f ∉ new_vars as cs ty) (ZIP (fas::ass,ZIP(fcs::css,fty::tys))) ∧
   as = FOLDR maunion FEMPTY (fas::ass) ∧
   cs = fcs ∪ BIGUNION (set css)
    ⇒ minfer ns mset (App d e es)
        as (mUnify fty (iFunctions tys (CVar f)) INSERT cs) (CVar f)) ∧

[~Lam:]
  (¬NULL xs ∧
   minfer ns (set freshes ∪ mset) e as cs ty ∧
   LENGTH freshes = LENGTH xs ∧
   EVERY (λf. f ∉ mset ∪ new_vars as cs ty) freshes
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

[~BoolCase:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint [(eas,ecs,ety);(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f ∉ mset ∪ new_vars eas ecs ety ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2 ∧
   {cn1; cn2} = {"True";"False"}
    ⇒ minfer ns mset (Case d e v [(cn1,[],e1);(cn2,[],e2)])
        ((maunion eas (maunion as1 as2)) \\ v)
        (mUnify (CVar f) ety INSERT mUnify ety BoolTy INSERT mUnify ty1 ty2 INSERT
          ecs ∪ cs1 ∪ cs2)
        ty1) ∧

[~TupleCase:]
  (¬MEM v pvars ∧
   minfer ns (f INSERT set freshes ∪ mset) rest asrest csrest tyrest ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint [(eas,ecs,ety);(asrest,csrest,tyrest)] ∧
   EVERY (λf.
    f ∉ mset ∪ new_vars eas ecs ety ∪ new_vars asrest csrest tyrest)
    (f::freshes) ∧
   pvar_cs =
    list$MAP2
      (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions asrest v))
      (v::pvars) (MAP CVar $ f::freshes)
    ⇒ minfer ns mset (Case d e v [("",pvars,rest)])
        (maunion as (FDIFF asrest (set (v::pvars))))
        (mUnify (CVar f) ety INSERT mUnify ety (Tuple $ MAP CVar freshes) INSERT
          BIGUNION (set pvar_cs) ∪ cs)
        tyrest) ∧

[~ExceptionCase:]
  (¬MEM v (FLAT (MAP (FST o SND) cases)) ∧
   PERM (MAP (λ(cn,ts). (cn, LENGTH ts)) (FST ns))
    (MAP (λ(cn,pvars,rest). (cn, LENGTH pvars)) cases) ∧
   LENGTH cases = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ((cname,pvars,rest),ty) (a,c).
      minfer ns (f INSERT mset) rest a c ty)
      (ZIP (cases,tys)) (ZIP (ass,css)) ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint ((eas,ecs,ety)::ZIP (ass, ZIP (css, tys))) ∧
   f ∉ mset ∧
   EVERY (λ(as,cs,ty). f ∉ new_vars as cs ty)
    (ZIP (eas::ass,ZIP(ecs::css,ety::tys))) ∧
   LENGTH final_as = LENGTH final_cs ∧
   LIST_REL (λ((cn,pvars,rest),as,cs) (as',cs').
    ∃schemes.
      ALOOKUP (FST ns) cn = SOME schemes ∧
      let pvar_cs = list$MAP2
        (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions as v))
          (v::pvars) (CVar f :: MAP itype_of schemes) in
      as' = FDIFF as (v INSERT set pvars) ∧
      cs' = BIGUNION (set pvar_cs) ∪ cs)
    (ZIP (cases,ZIP (ass,css))) (ZIP (final_as,final_cs))
    ⇒ minfer ns mset (Case d e v cases)
        (FOLDR maunion FEMPTY (eas::final_as))
        (mUnify (CVar f) ety INSERT mUnify ety Exception INSERT
          set (MAP (λt. mUnify (HD tys) t) (TL tys)) ∪ ecs ∪ BIGUNION (set final_cs))
        (HD tys)) ∧

[~Case:]
  (¬MEM v (FLAT (MAP (FST o SND) cases)) ∧
   oEL id (SND ns) = SOME (ar, cdefs) ∧
   PERM (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)
    (MAP (λ(cn,pvars,rest). (cn, LENGTH pvars)) cases) ∧
   LENGTH cases = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ((cname,pvars,rest),ty) (a,c).
      minfer ns (f INSERT set freshes ∪ mset) rest a c ty)
      (ZIP (cases,tys)) (ZIP (ass,css)) ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint ((eas,ecs,ety)::ZIP (ass, ZIP (css, tys))) ∧
   EVERY (λf. f ∉ mset ∧
    EVERY (λ(as,cs,ty). f ∉ new_vars as cs ty)
      (ZIP (eas::ass,ZIP(ecs::css,ety::tys)))) (f::freshes) ∧
   LENGTH final_as = LENGTH final_cs ∧
   LIST_REL (λ((cn,pvars,rest),as,cs) (as',cs').
    ∃schemes.
      ALOOKUP cdefs cn = SOME schemes ∧
      let pvar_cs = list$MAP2
        (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions as v))
        (v::pvars) (CVar f :: MAP (isubst (MAP CVar freshes) o itype_of) schemes) in
      as' = FDIFF as (v INSERT set pvars) ∧
      cs' = BIGUNION (set pvar_cs) ∪ cs)
    (ZIP (cases,ZIP (ass,css))) (ZIP (final_as,final_cs))
    ⇒ minfer ns mset (Case d e v cases)
        (FOLDR maunion FEMPTY (eas::final_as))
        (mUnify (CVar f) ety INSERT mUnify ety (TypeCons id (MAP CVar freshes)) INSERT
          set (MAP (λt. mUnify (HD tys) t) (TL tys)) ∪ ecs ∪ BIGUNION (set final_cs))
        (HD tys))
End


(******************** Proof apparatus ********************)

Definition to_mconstraint_def[simp]:
  to_mconstraint (Unify d t1 t2) = mUnify t1 t2 ∧
  to_mconstraint (Instantiate d t sch) = mInstantiate t sch ∧
  to_mconstraint (Implicit d t1 mono t2) = mImplicit t1 (domain mono) t2
End

Definition assumptions_rel_def:
  assumptions_rel asms masms ⇔
    map_ok asms ∧ cmp_of asms = var_cmp ∧
    (∀s. FLOOKUP masms s = OPTION_MAP domain (lookup asms s)) ∧
    (∀s aset. lookup asms s = SOME aset ⇒ wf aset)
End


(******************** Lemmas ********************)

Triviality maunion_comm:
  ∀x y. maunion x y = maunion y x
Proof
  rw[maunion_def] >>
  irule $ iffRL $ SIMP_RULE (srw_ss()) [combinTheory.COMM_DEF] FMERGE_COMM >>
  rw[UNION_COMM]
QED

Theorem list_disjoint_alt_def:
  list_disjoint l ⇔
    ∀left right. l = left ++ right ⇒
      DISJOINT (BIGUNION (set left)) (BIGUNION (set right))
Proof
  rw[list_disjoint_def] >> eq_tac >> rw[]
  >- (
    first_x_assum irule >>
    qspecl_then [`left`,`s'`] assume_tac $ GEN_ALL MEM_SING_APPEND >> gvs[] >>
    qexists_tac `a` >> simp[]
    )
  >- (
    once_rewrite_tac[DISJOINT_SYM] >>
    first_x_assum irule >> qexists_tac `left` >> simp[]
    )
  >- (first_x_assum irule >> qexists_tac `left ++ [mid]` >> simp[])
QED

Theorem list_disjoint_singleton[simp]:
  list_disjoint [a]
Proof
  rw[list_disjoint_alt_def] >> Cases_on `left` >> gvs[]
QED

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
  rw[list_disjoint_alt_def] >> eq_tac >> rw[]
  >- (first_x_assum irule >> qexists_tac `left` >> simp[])
  >- (first_x_assum irule >> qexists_tac `l1 ++ left` >> simp[])
  >- (first_x_assum irule >> qexists_tac `l1` >> simp[]) >>
  gvs[APPEND_EQ_APPEND]
  >- (last_x_assum irule >> ntac 2 $ goal_assum drule >> simp[])
  >- (
    last_x_assum kall_tac >> last_x_assum irule >>
    ntac 2 $ goal_assum drule >> simp[]
    )
QED

Theorem list_disjoint_ALL_DISTINCT:
  ∀l. EVERY FINITE l ⇒
    (list_disjoint l ⇔ ALL_DISTINCT (FLAT $ MAP SET_TO_LIST l))
Proof
  rw[list_disjoint_alt_def, miscTheory.ALL_DISTINCT_FLAT] >>
  eq_tac >> rw[]
  >- (gvs[MEM_MAP, EVERY_MEM])
  >- (
    gvs[EL_MAP] >> pop_assum mp_tac >>
    DEP_REWRITE_TAC[MEM_SET_TO_LIST] >> conj_tac >- gvs[EVERY_EL] >>
    qid_spec_tac `e` >> simp[GSYM DISJOINT_ALT] >>
    first_x_assum irule >>
    qexistsl_tac [`TAKE (SUC i) l`,`DROP (SUC i) l`] >> rw[MEM_EL]
    >- (qexists_tac `i` >> simp[EL_TAKE])
    >- (qexists_tac `j - SUC i` >> simp[EL_DROP])
    )
  >- (
    gvs[EL_MAP] >> ntac 2 $ pop_assum mp_tac >> rw[MEM_EL] >>
    first_x_assum $ qspecl_then [`n`,`LENGTH left + n'`] assume_tac >> gvs[] >>
    rw[DISJOINT_ALT] >> first_x_assum $ qspec_then `x` mp_tac >>
    simp[EL_APPEND_EQN] >>
    DEP_REWRITE_TAC[MEM_SET_TO_LIST] >> simp[] >> gvs[EVERY_EL]
    )
QED

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

Theorem LIST_TO_SET_get_assumptions:
  ∀as mas. assumptions_rel as mas ⇒
    ∀x. set (get_assumptions x as) = get_massumptions mas x
Proof
  rw[EXTENSION, get_assumptions_def, get_massumptions_def] >>
  gvs[assumptions_rel_def] >> CASE_TAC >> gvs[] >>
  simp[miscTheory.toAList_domain]
QED

Triviality domain_list_insert_alt:
  domain (list_insert xs t) = set xs ∪ domain t
Proof
  rw[EXTENSION, domain_list_insert]
QED

Theorem FLOOKUP_FOLDR_maunion:
  ∀ms base k.
    FLOOKUP (FOLDR maunion base ms) k =
      if k ∉ FDOM base ∧ ∀m. MEM m ms ⇒ k ∉ FDOM m then NONE
      else  SOME $
        BIGUNION {s | FLOOKUP base k = SOME s ∨ ∃m. MEM m ms ∧ FLOOKUP m k = SOME s}
Proof
  Induct >> rw[]
  >- simp[FLOOKUP_DEF]
  >- simp[FLOOKUP_DEF]
  >- (gvs[maunion_def, FLOOKUP_FMERGE] >> gvs[FLOOKUP_DEF]) >>
  gvs[maunion_def, FLOOKUP_FMERGE] >> gvs[FLOOKUP_DEF] >>
  every_case_tac >> gvs[] >> rw[EXTENSION] >> metis_tac[]
QED

Triviality infer_bind_alt_def:
  ∀g f.
    infer_bind g f = λs. case g s of NONE => NONE | SOME ((a,b,c),s') => f (a,b,c) s'
Proof
  rw[FUN_EQ_THM, infer_bind_def] >> rpt (CASE_TAC >> simp[])
QED

val inferM_ss = simpLib.named_rewrites "inferM_ss"
  [infer_bind_alt_def, infer_bind_def, infer_ignore_bind_def, fail_def,
   return_def, fresh_var_def, fresh_vars_def, oreturn_def];

val _ = simpLib.register_frag inferM_ss;

val inferM_rws = SF inferM_ss;

Theorem infer_minfer:
  ∀ns mset e n ty as cs m.
    infer ns mset e n = SOME ((ty,as,cs),m) ∧
    namespace_ok ns ∧
    (∀mvar. mvar ∈ domain mset ⇒ mvar < n) ⇒
    ∃mas.
      assumptions_rel as mas ∧
      minfer ns (domain mset) e mas (set (MAP to_mconstraint cs)) ty ∧
      n ≤ m ∧
      (new_vars mas (set (MAP to_mconstraint cs)) ty ⊆ { v | n ≤ v ∧ v < m})
Proof
  recInduct infer_ind >> rw[infer_def]
  >- ( (* Var *)
    last_x_assum mp_tac >> rw[inferM_rws] >>
    qexists_tac `FEMPTY |+ (x, {n})` >> simp[assumptions_rel_def] >>
    simp[lookup_singleton, FLOOKUP_UPDATE] >> rw[]
    >- simp[wf_insert]
    >- (
      simp[Once minfer_cases] >> CCONTR_TAC >> gvs[] >>
      last_x_assum drule >> simp[]
      )
    >- gvs[new_vars_def, pure_vars]
    )
  >- ( (* Tuple *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    ntac 2 $ pop_assum mp_tac >>
    map_every qid_spec_tac [`m`,`n`,`tys`,`as`,`cs`] >>
    Induct_on `es` >> rw[] >> simp[]
    >- (
      qexists_tac `FEMPTY` >> simp[assumptions_rel_def] >>
      simp[Once minfer_cases, PULL_EXISTS] >>
      qexistsl_tac [`[]`,`[]`] >> simp[cvars_disjoint_def, new_vars_def] >>
      simp[list_disjoint_def, pure_vars]
      ) >>
    every_case_tac >> gvs[] >>
    last_x_assum drule >> strip_tac >> gvs[] >>
    last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
    disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
    strip_tac >> gvs[] >> qexists_tac `maunion mas' mas` >> rw[]
    >- (
      gvs[assumptions_rel_def, aunion_def, PULL_FORALL] >> rpt gen_tac >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm, lookup_unionWith] >>
      simp[maunion_def, FLOOKUP_FMERGE] >>
      every_case_tac >> gvs[] >> rw[] >>
      once_rewrite_tac[UNION_COMM] >> metis_tac[wf_union, domain_union]
      )
    >- (
      qpat_x_assum `minfer _ _ _ _ _ (Tuple _)` mp_tac >>
      once_rewrite_tac[minfer_cases] >> simp[] >> strip_tac >> gvs[] >>
      rename1 `set (_ cs) ∪ _` >>
      qexistsl_tac [`mas'::ass`, `(set (MAP to_mconstraint cs)) :: css`] >>
      gvs[cvars_disjoint_def] >>
      once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
      DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
      pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
      irule SUBSET_DISJOINT >>
      qexistsl_tac [`{v | r ≤ v ∧ v < m}`,`{v | n ≤ v ∧ v < r}`] >>
      conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
      irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
      simp[new_vars_def, BIGUNION_SUBSET, pure_vars, PULL_EXISTS] >> rw[]
      >- (
        simp[SUBSET_DEF] >> rw[] >> ntac 2 disj1_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            GSYM CONJ_ASSOC, FLOOKUP_DEF] >>
        rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj2_tac >>
        simp[PULL_EXISTS] >> rpt $ goal_assum drule >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj2_tac >> simp[MEM_MAP, PULL_EXISTS] >>
        goal_assum drule >> simp[EL_MEM]
        )
      )
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC, pure_vars] >> rw[] >>
      rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
      )
    )
  >- ( (* Ret *)
    gvs[inferM_rws] >> Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[inferM_rws] >>
    every_case_tac >> gvs[] >>
    last_x_assum drule_all >> strip_tac >> simp[] >>
    goal_assum drule >> simp[Once minfer_cases] >>
    gvs[new_vars_def, pure_vars]
    )
  >- ( (* Bind *)
    gvs[inferM_rws] >>
    Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >>
    Cases_on `t'` >> gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    last_x_assum drule >> impl_tac
    >- (rw[] >> last_x_assum drule >> simp[]) >>
    strip_tac >> gvs[] >>
    simp[Once minfer_cases, PULL_EXISTS] >>
    ntac 2 $ goal_assum $ drule_at Any >> qexists_tac `r'` >> rw[]
    >- (
      gvs[assumptions_rel_def] >> simp[PULL_FORALL, aunion_def] >>
      rpt gen_tac >> DEP_REWRITE_TAC[lookup_unionWith] >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
      simp[maunion_def, FLOOKUP_FMERGE] >>
      every_case_tac >> gvs[] >> rw[] >>
      metis_tac[wf_union, domain_union]
      )
    >- (rw[EXTENSION] >> eq_tac >> rw[] >> simp[])
    >- (
      simp[cvars_disjoint_def, DISJOINT_ALT] >> rw[] >> CCONTR_TAC >> gvs[SUBSET_DEF] >>
      first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      )
    >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC] >>
      simp[new_vars_constraint_def, pure_vars] >>
      rw[] >> rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >>
      first_x_assum drule >> rw[]
      )
    )
  >- ( (* Raise *)
    gvs[inferM_rws] >>
    Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    goal_assum drule >> simp[Once minfer_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
    goal_assum $ drule_at Any >> simp[] >> rw[]
    >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[]) >>
    gvs[new_vars_def, new_vars_constraint_def, pure_vars] >>
    rw[] >> rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >>
    first_x_assum drule >> rw[]
    )
  >- ( (* Handle *)
    gvs[inferM_rws] >>
    Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >>
    Cases_on `t'` >> gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    last_x_assum drule >> impl_tac
    >- (rw[] >> last_x_assum drule >> simp[]) >>
    strip_tac >> gvs[] >>
    simp[Once minfer_cases, PULL_EXISTS] >>
    ntac 2 $ goal_assum $ drule_at Any >> rw[]
    >- (
      gvs[assumptions_rel_def] >> simp[PULL_FORALL, aunion_def] >>
      rpt gen_tac >> DEP_REWRITE_TAC[lookup_unionWith] >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
      simp[maunion_def, FLOOKUP_FMERGE] >>
      every_case_tac >> gvs[] >> rw[] >>
      metis_tac[wf_union, domain_union]
      )
    >- (rw[EXTENSION] >> eq_tac >> rw[] >> simp[])
    >- (
      simp[cvars_disjoint_def, DISJOINT_ALT] >> rw[] >> CCONTR_TAC >> gvs[SUBSET_DEF] >>
      first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      )
    >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC] >>
      simp[new_vars_constraint_def, pure_vars] >>
      rw[] >> rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >>
      first_x_assum drule >> rw[]
      )
    )
  >- ( (* Act *)
    gvs[inferM_rws] >>
    Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    goal_assum drule >> simp[Once minfer_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
    goal_assum $ drule_at Any >> simp[] >> rw[] >>
    gvs[new_vars_def, new_vars_constraint_def, pure_vars]
    )
  >- ( (* Alloc *)
    gvs[inferM_rws] >>
    Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >>
    Cases_on `t'` >> gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    last_x_assum drule >> impl_tac
    >- (rw[] >> last_x_assum drule >> simp[]) >>
    strip_tac >> gvs[] >>
    simp[Once minfer_cases, PULL_EXISTS] >>
    ntac 2 $ goal_assum $ drule_at Any >> rw[]
    >- (
      gvs[assumptions_rel_def] >> simp[PULL_FORALL, aunion_def] >>
      rpt gen_tac >> DEP_REWRITE_TAC[lookup_unionWith] >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
      simp[maunion_def, FLOOKUP_FMERGE] >>
      every_case_tac >> gvs[] >> rw[] >>
      metis_tac[wf_union, domain_union]
      )
    >- (
      simp[cvars_disjoint_def, DISJOINT_ALT] >> rw[] >> CCONTR_TAC >> gvs[SUBSET_DEF] >>
      first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      )
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC] >>
      simp[new_vars_constraint_def, pure_vars] >>
      rw[] >> rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >>
      first_x_assum drule >> rw[]
      )
    )
  >- ( (* Length *)
    gvs[inferM_rws] >>
    Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    goal_assum drule >> simp[Once minfer_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
    goal_assum $ drule_at Any >> irule_at Any EQ_REFL >> rw[]
    >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC] >>
      simp[new_vars_constraint_def, pure_vars] >>
      rw[] >> rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >>
      first_x_assum drule >> rw[]
      )
    )
  >- ( (* Deref *)
    gvs[inferM_rws] >>
    Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >>
    Cases_on `t'` >> gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    last_x_assum drule >> impl_tac
    >- (rw[] >> last_x_assum drule >> simp[]) >>
    strip_tac >> gvs[] >>
    simp[Once minfer_cases, PULL_EXISTS] >>
    ntac 2 $ goal_assum $ drule_at Any >> rw[]
    >- (
      gvs[assumptions_rel_def] >> simp[PULL_FORALL, aunion_def] >>
      rpt gen_tac >> DEP_REWRITE_TAC[lookup_unionWith] >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
      simp[maunion_def, FLOOKUP_FMERGE] >>
      every_case_tac >> gvs[] >> rw[] >>
      metis_tac[wf_union, domain_union]
      )
    >- (rw[EXTENSION] >> eq_tac >> rw[] >> simp[])
    >- (
      simp[cvars_disjoint_def, DISJOINT_ALT] >> rw[] >> CCONTR_TAC >> gvs[SUBSET_DEF] >>
      first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      )
    >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC] >>
      simp[new_vars_constraint_def, pure_vars] >>
      rw[] >> rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >>
      first_x_assum drule >> rw[]
      )
    )
  >- ( (* Update *)
    gvs[inferM_rws] >>
    Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >>
    Cases_on `t'` >> gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    first_x_assum drule >> impl_tac
    >- (rw[] >> last_x_assum drule >> simp[]) >>
    strip_tac >> gvs[] >>
    first_x_assum drule >> impl_tac
    >- (rw[] >> last_x_assum drule >> simp[]) >>
    strip_tac >> gvs[] >>
    simp[Once minfer_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
    ntac 3 $ goal_assum $ drule_at Any >> simp[] >>
    qexistsl_tac [`maunion (maunion mas' mas) mas''`,`r''`] >> rw[]
    >- (
      gvs[assumptions_rel_def] >> simp[PULL_FORALL, aunion_def] >>
      rpt gen_tac >> DEP_REWRITE_TAC[lookup_unionWith] >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
      simp[maunion_def, FLOOKUP_FMERGE] >>
      every_case_tac >> gvs[] >> rw[] >>
      DEP_REWRITE_TAC[wf_union] >>
      simp[domain_union, AC UNION_ASSOC UNION_COMM] >> metis_tac[]
      )
    >- (rw[EXTENSION] >> eq_tac >> rw[] >> simp[])
    >- (
      simp[cvars_disjoint_def, list_disjoint_alt_def, DISJOINT_ALT] >> rw[] >>
      CCONTR_TAC >> gvs[SUBSET_DEF] >>
      Cases_on `left` >> gvs[] >> Cases_on `t` >> gvs[]
      >- (ntac 2 (first_x_assum drule >> strip_tac) >> gvs[])
      >- (ntac 2 (first_x_assum drule >> strip_tac) >> gvs[]) >>
      Cases_on `t'` >> gvs[] >>
      first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      )
    >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC] >>
      simp[new_vars_constraint_def, pure_vars] >>
      rw[] >> rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >>
      first_x_assum drule >> rw[]
      )
    )
  >- ( (* True *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    simp[Once minfer_cases, new_vars_def, pure_vars, assumptions_rel_def]
    )
  >- ( (* False *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    simp[Once minfer_cases, new_vars_def, pure_vars, assumptions_rel_def]
    )
  >- ( (* Subscript *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    simp[Once minfer_cases] >> irule_at Any OR_INTRO_THM1 >>
    simp[new_vars_def, pure_vars, assumptions_rel_def]
    )
  >- ( (* Cons and Exception *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    every_case_tac >> gvs[]
    >- ( (* Exception *)
      rename1 `_ = SOME ((_,_,cs),_)` >>
      qsuff_tac
        `∃ass css.
          LIST_REL (λ(e,ty) (a,c). minfer ns (domain mset) e a c ty)
            (ZIP (es,tys)) (ZIP (ass,css)) ∧
          assumptions_rel as (FOLDR maunion FEMPTY ass) ∧
          BIGUNION (set css) = set (MAP to_mconstraint cs) ∧
          cvars_disjoint (ZIP (ass, ZIP (css, tys))) ∧
          new_vars (FOLDR maunion FEMPTY ass)
            (BIGUNION (set css)) (iFunctions tys Exception) ⊆ {v | n ≤ v ∧ v < m} ∧
          LENGTH es = LENGTH tys ∧ LENGTH ass = LENGTH css ∧
          n ≤ m`
      >- (
        rw[] >> gvs[] >>
        simp[Once minfer_cases, PULL_EXISTS] >>
        rpt $ goal_assum $ drule_at Any >>
        simp[MAP2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[reserved_cns_def] >>
        gvs[new_vars_def, LIST_TO_SET_MAP, IMAGE_IMAGE,
            combinTheory.o_DEF, LAMBDA_PROD, pure_vars] >>
        simp[BIGUNION_SUBSET, PULL_EXISTS] >>
        gen_tac >> DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >> strip_tac >> gvs[] >>
        gvs[pure_vars_iFunctions, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
        last_x_assum irule >> simp[EL_MEM]
        ) >>
      qpat_x_assum `FOLDR _ _ _ _ = _` mp_tac >>
      ntac 3 $ pop_assum kall_tac >> pop_assum mp_tac >>
      ntac 13 $ last_x_assum kall_tac >>
      map_every qid_spec_tac [`m`,`n`,`tys`,`as`,`cs`] >>
      Induct_on `es` >> rw[] >> simp[]
      >- (
        qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
        simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
        ) >>
      every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
      rename1 `FOLDR _ _ _ _ = SOME ((tysrest,asrest,csrest),r)` >>
      rename1 `infer _ _ _ _ = SOME ((ty,as,cs),m)` >>
      last_x_assum drule >> strip_tac >> gvs[] >>
      last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
      disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
      strip_tac >> gvs[] >> ntac 2 $ goal_assum $ drule_at Any >>
      once_rewrite_tac[GSYM ZIP] >> irule_at Any EQ_REFL >> simp[] >> rw[]
      >- (
        gvs[assumptions_rel_def, aunion_def, PULL_FORALL] >> rpt gen_tac >>
        DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm, lookup_unionWith] >>
        gvs[maunion_def, FLOOKUP_FMERGE] >>
        ntac 2 $ first_x_assum $ qspecl_then [`s`,`s'`] assume_tac >>
        every_case_tac >> gvs[] >> rw[] >>
        metis_tac[wf_union, domain_union, UNION_COMM]
        )
      >- (
        gvs[cvars_disjoint_def] >>
        once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
        DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
        pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
        irule SUBSET_DISJOINT >> goal_assum $ drule_at Any >>
        qexists_tac `{v | n ≤ v ∧ v < r}` >>
        conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
        irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
        gvs[new_vars_def, BIGUNION_SUBSET, pure_vars, PULL_EXISTS] >> rw[]
        >- (
          simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj1_tac >>
          gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
              GSYM CONJ_ASSOC, FLOOKUP_DEF, BIGUNION_SUBSET] >>
          rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj2_tac >>
          simp[PULL_EXISTS] >> goal_assum drule >>
          qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
          disch_then $ irule o iffLR >> goal_assum drule >> simp[EL_MEM]
          )
        >- (
          simp[SUBSET_DEF] >> rw[] >> disj2_tac >> simp[MEM_MAP, PULL_EXISTS] >>
          simp[pure_vars_iFunctions, pure_vars] >>
          simp[MEM_MAP, PULL_EXISTS] >> goal_assum drule >> simp[EL_MEM]
          )
        )
      >- (
        gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC,
            pure_vars, pure_vars_iFunctions] >> rw[] >>
        rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
        )
      )
    >- (
      gvs[inferM_rws] >> rename1 `_ = SOME ((_,_,cs),m)` >>
      qsuff_tac
        `∃ass css.
          LIST_REL (λ(e,ty) (a,c). minfer ns (domain mset) e a c ty)
            (ZIP (es,tys)) (ZIP (ass,css)) ∧
          assumptions_rel as (FOLDR maunion FEMPTY ass) ∧
          BIGUNION (set css) = set (MAP to_mconstraint cs) ∧
          cvars_disjoint (ZIP (ass, ZIP (css, tys))) ∧
          new_vars (FOLDR maunion FEMPTY ass)
            (BIGUNION (set css)) (iFunctions tys Exception) ⊆ {v | n ≤ v ∧ v < m} ∧
          LENGTH es = LENGTH tys ∧ LENGTH ass = LENGTH css ∧
          n ≤ m`
      >- (
        rw[] >> gvs[] >>
        drule infer_cons_SOME >>
        disch_then $ qspec_then `FST ns` assume_tac >> gvs[] >>
        rename [`ALOOKUP _ _ = SOME schemes`,`oEL tyid _ = SOME (arity,_)`] >>
        simp[Once minfer_cases, PULL_EXISTS] >>
        rpt $ goal_assum $ drule_at Any >> simp[] >> irule_at Any EQ_REFL >>
        DEP_REWRITE_TAC[MAP2_MAP] >> gvs[oEL_THM] >>
        simp[MAP2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[reserved_cns_def] >> conj_tac
        >- (
          drule LIST_REL_LENGTH >>
          DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >> rw[] >> gvs[] >>
          simp[EVERY_GENLIST, EVERY_MEM, FORALL_PROD] >> rw[]
          >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[]) >>
          pop_assum mp_tac >> DEP_REWRITE_TAC[MEM_ZIP] >> simp[MIN_DEF] >>
          strip_tac >> gvs[] >>
          pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >>
          strip_tac >> gvs[] >>
          qsuff_tac
            `new_vars (EL n'' ass) (EL n'' css) (EL n'' tys) ⊆ {v | n ≤ v ∧ v < m}`
          >- (rw[SUBSET_DEF] >> CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[]) >>
          irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
          gvs[new_vars_def, BIGUNION_SUBSET, pure_vars, PULL_EXISTS] >> rw[]
          >- (
            simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj1_tac >>
            gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
                GSYM CONJ_ASSOC, FLOOKUP_DEF, BIGUNION_SUBSET] >>
            rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
            )
          >- (
            simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj2_tac >>
            simp[PULL_EXISTS] >> goal_assum drule >>
            qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
            disch_then $ irule o iffLR >> goal_assum drule >> simp[EL_MEM]
            )
          >- (
            simp[SUBSET_DEF] >> rw[] >> disj2_tac >> simp[MEM_MAP, PULL_EXISTS] >>
            simp[pure_vars_iFunctions, pure_vars] >>
            simp[MEM_MAP, PULL_EXISTS] >> goal_assum drule >> simp[EL_MEM]
            )
          )
        >- (
          gvs[new_vars_def, BIGUNION_SUBSET, pure_vars, pure_vars_iFunctions,
              PULL_EXISTS, IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, GSYM CONJ_ASSOC,
              MEM_MAP, EXISTS_PROD, MEM_GENLIST, FLOOKUP_DEF, MEM_ZIP] >> rw[]
          >- (
            first_x_assum drule_all >> rw[SUBSET_DEF] >>
            first_x_assum drule >> simp[]
            )
          >- (
            last_x_assum $ qspec_then `EL n' tys` mp_tac >> simp[EL_MEM] >>
            rw[SUBSET_DEF] >> first_x_assum drule >> simp[]
            )
          >- (
            irule SUBSET_TRANS >> irule_at Any pure_vars_isubst_SUBSET >>
            simp[BIGUNION_SUBSET, MAP_MAP_o, combinTheory.o_DEF, pure_vars] >>
            simp[MEM_MAP, MEM_GENLIST, PULL_EXISTS]
            )
          >- (
            first_x_assum drule >> rw[SUBSET_DEF] >> first_x_assum drule >> simp[]
            )
          )
        ) >>
      qpat_x_assum `FOLDR _ _ _ _ = _` mp_tac >>
      ntac 3 $ pop_assum kall_tac >> pop_assum mp_tac >>
      ntac 13 $ last_x_assum kall_tac >>
      map_every qid_spec_tac [`m`,`n`,`tys`,`as`,`cs`] >>
      Induct_on `es` >> rw[] >> simp[]
      >- (
        qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
        simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
        ) >>
      every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
      rename1 `FOLDR _ _ _ _ = SOME ((tysrest,asrest,csrest),r)` >>
      rename1 `infer _ _ _ _ = SOME ((ty,as,cs),m)` >>
      last_x_assum drule >> strip_tac >> gvs[] >>
      last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
      disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
      strip_tac >> gvs[] >> ntac 2 $ goal_assum $ drule_at Any >>
      once_rewrite_tac[GSYM ZIP] >> irule_at Any EQ_REFL >> simp[] >> rw[]
      >- (
        gvs[assumptions_rel_def, aunion_def, PULL_FORALL] >> rpt gen_tac >>
        DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm, lookup_unionWith] >>
        gvs[maunion_def, FLOOKUP_FMERGE] >>
        ntac 2 $ first_x_assum $ qspecl_then [`s`,`s'`] assume_tac >>
        every_case_tac >> gvs[] >> rw[] >>
        metis_tac[wf_union, domain_union, UNION_COMM]
        )
      >- (
        gvs[cvars_disjoint_def] >>
        once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
        DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
        pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
        irule SUBSET_DISJOINT >> goal_assum $ drule_at Any >>
        qexists_tac `{v | n ≤ v ∧ v < r}` >>
        conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
        irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
        gvs[new_vars_def, BIGUNION_SUBSET, pure_vars, PULL_EXISTS] >> rw[]
        >- (
          simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj1_tac >>
          gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
              GSYM CONJ_ASSOC, FLOOKUP_DEF, BIGUNION_SUBSET] >>
          rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj2_tac >>
          simp[PULL_EXISTS] >> goal_assum drule >>
          qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
          disch_then $ irule o iffLR >> goal_assum drule >> simp[EL_MEM]
          )
        >- (
          simp[SUBSET_DEF] >> rw[] >> disj2_tac >> simp[MEM_MAP, PULL_EXISTS] >>
          simp[pure_vars_iFunctions, pure_vars] >>
          simp[MEM_MAP, PULL_EXISTS] >> goal_assum drule >> simp[EL_MEM]
          )
        )
      >- (
        gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC,
            pure_vars, pure_vars_iFunctions] >> rw[] >>
        rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
        )
      )
    >- (
      gvs[inferM_rws] >> rename1 `_ = SOME ((_,_,cs),m)` >>
      qsuff_tac
        `∃ass css.
          LIST_REL (λ(e,ty) (a,c). minfer ns (domain mset) e a c ty)
            (ZIP (es,tys)) (ZIP (ass,css)) ∧
          assumptions_rel as (FOLDR maunion FEMPTY ass) ∧
          BIGUNION (set css) = set (MAP to_mconstraint cs) ∧
          cvars_disjoint (ZIP (ass, ZIP (css, tys))) ∧
          new_vars (FOLDR maunion FEMPTY ass)
            (BIGUNION (set css)) (iFunctions tys Exception) ⊆ {v | n ≤ v ∧ v < m} ∧
          LENGTH es = LENGTH tys ∧ LENGTH ass = LENGTH css ∧
          n ≤ m`
      >- (
        rw[] >> gvs[] >>
        drule infer_cons_SOME >>
        disch_then $ qspec_then `FST ns` assume_tac >> gvs[] >>
        rename [`ALOOKUP _ _ = SOME schemes`,`oEL tyid _ = SOME (arity,_)`] >>
        simp[Once minfer_cases, PULL_EXISTS] >>
        rpt $ goal_assum $ drule_at Any >> simp[] >>
        DEP_REWRITE_TAC[MAP2_MAP] >> gvs[oEL_THM] >>
        simp[MAP2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[reserved_cns_def] >>
        gvs[new_vars_def, pure_vars, LIST_TO_SET_MAP, IMAGE_IMAGE,
            combinTheory.o_DEF, BIGUNION_SUBSET, PULL_EXISTS, FORALL_PROD,
            MEM_ZIP, pure_vars_iFunctions] >>
        rw[] >> last_x_assum irule >> simp[EL_MEM]
        ) >>
      qpat_x_assum `FOLDR _ _ _ _ = _` mp_tac >>
      ntac 3 $ pop_assum kall_tac >> pop_assum mp_tac >>
      ntac 13 $ last_x_assum kall_tac >>
      rename1 `FOLDR _ _ _ _ = SOME (_,m)` >>
      map_every qid_spec_tac [`m`,`n`,`tys`,`as`,`cs`] >>
      Induct_on `es` >> rw[] >> simp[]
      >- (
        qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
        simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
        ) >>
      every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
      rename1 `FOLDR _ _ _ _ = SOME ((tysrest,asrest,csrest),r)` >>
      rename1 `infer _ _ _ _ = SOME ((ty,as,cs),m)` >>
      last_x_assum drule >> strip_tac >> gvs[] >>
      last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
      disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
      strip_tac >> gvs[] >> ntac 2 $ goal_assum $ drule_at Any >>
      once_rewrite_tac[GSYM ZIP] >> irule_at Any EQ_REFL >> simp[] >> rw[]
      >- (
        gvs[assumptions_rel_def, aunion_def, PULL_FORALL] >> rpt gen_tac >>
        DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm, lookup_unionWith] >>
        gvs[maunion_def, FLOOKUP_FMERGE] >>
        ntac 2 $ first_x_assum $ qspecl_then [`s`,`s'`] assume_tac >>
        every_case_tac >> gvs[] >> rw[] >>
        metis_tac[wf_union, domain_union, UNION_COMM]
        )
      >- (
        gvs[cvars_disjoint_def] >>
        once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
        DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
        pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
        irule SUBSET_DISJOINT >> goal_assum $ drule_at Any >>
        qexists_tac `{v | n ≤ v ∧ v < r}` >>
        conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
        irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
        gvs[new_vars_def, BIGUNION_SUBSET, pure_vars, PULL_EXISTS] >> rw[]
        >- (
          simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj1_tac >>
          gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
              GSYM CONJ_ASSOC, FLOOKUP_DEF, BIGUNION_SUBSET] >>
          rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj2_tac >>
          simp[PULL_EXISTS] >> goal_assum drule >>
          qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
          disch_then $ irule o iffLR >> goal_assum drule >> simp[EL_MEM]
          )
        >- (
          simp[SUBSET_DEF] >> rw[] >> disj2_tac >> simp[MEM_MAP, PULL_EXISTS] >>
          simp[pure_vars_iFunctions, pure_vars] >>
          simp[MEM_MAP, PULL_EXISTS] >> goal_assum drule >> simp[EL_MEM]
          )
        )
      >- (
        gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC,
            pure_vars, pure_vars_iFunctions] >> rw[] >>
        rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
        )
      )
    )
  >- ( (* AtomOp *)
    Cases_on `infer_atom_op (LENGTH es) aop` >> gvs[inferM_rws] >>
    pairarg_tac >> gvs[] >>
    every_case_tac >> gvs[] >> rename1 `FOLDR _ _ _ _ = SOME ((tys,as,cs),m)` >>
    qsuff_tac
      `∃ass css.
        LIST_REL (λ(e,ty) (a,c). minfer ns (domain mset) e a c ty)
          (ZIP (es,tys)) (ZIP (ass,css)) ∧
        assumptions_rel as (FOLDR maunion FEMPTY ass) ∧
        BIGUNION (set css) = set (MAP to_mconstraint cs) ∧
        cvars_disjoint (ZIP (ass, ZIP (css, tys))) ∧
        new_vars (FOLDR maunion FEMPTY ass)
          (BIGUNION (set css)) (iFunctions tys Exception) ⊆ {v | n ≤ v ∧ v < m} ∧
        LENGTH es = LENGTH tys ∧ LENGTH ass = LENGTH css ∧
        n ≤ m`
    >- (
      rw[] >> gvs[] >>
      simp[Once minfer_cases, PULL_EXISTS] >>
      rpt $ goal_assum $ drule_at Any >> simp[] >>
      DEP_REWRITE_TAC[MAP2_MAP] >> gvs[oEL_THM] >>
      simp[MAP2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      imp_res_tac infer_atom_op_LENGTH >> gvs[] >>
      gvs[new_vars_def, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF,
          BIGUNION_SUBSET, PULL_EXISTS, MEM_ZIP, pure_vars, pure_vars_iFunctions] >>
      rw[] >> last_x_assum irule >> simp[EL_MEM]
      ) >>
    qpat_x_assum `FOLDR _ _ _ _ = _` mp_tac >>
    pop_assum kall_tac >> pop_assum mp_tac >> last_x_assum mp_tac >>
    map_every qid_spec_tac [`m`,`n`,`tys`,`as`,`cs`] >>
    Induct_on `es` >> rw[] >> simp[]
    >- (
      qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
      simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
      ) >>
    every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
    rename1 `FOLDR _ _ _ _ = SOME ((tysrest,asrest,csrest),r)` >>
    rename1 `infer _ _ _ _ = SOME ((ty,as,cs),m)` >>
    last_x_assum drule >> strip_tac >> gvs[] >>
    last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
    disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
    strip_tac >> gvs[] >> ntac 2 $ goal_assum $ drule_at Any >>
    once_rewrite_tac[GSYM ZIP] >> irule_at Any EQ_REFL >> simp[] >> rw[]
    >- (
      gvs[assumptions_rel_def, aunion_def, PULL_FORALL] >> rpt gen_tac >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm, lookup_unionWith] >>
      gvs[maunion_def, FLOOKUP_FMERGE] >>
      ntac 2 $ first_x_assum $ qspecl_then [`s`,`s'`] assume_tac >>
      every_case_tac >> gvs[] >> rw[] >>
      metis_tac[wf_union, domain_union, UNION_COMM]
      )
    >- (
      gvs[cvars_disjoint_def] >>
      once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
      DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
      pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
      irule SUBSET_DISJOINT >> goal_assum $ drule_at Any >>
      qexists_tac `{v | n ≤ v ∧ v < r}` >>
      conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
      irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
      gvs[new_vars_def, BIGUNION_SUBSET, pure_vars, PULL_EXISTS] >> rw[]
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj1_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            GSYM CONJ_ASSOC, FLOOKUP_DEF, BIGUNION_SUBSET] >>
        rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj2_tac >>
        simp[PULL_EXISTS] >> goal_assum drule >>
        qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
        disch_then $ irule o iffLR >> goal_assum drule >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj2_tac >> simp[MEM_MAP, PULL_EXISTS] >>
        simp[pure_vars_iFunctions, pure_vars] >>
        simp[MEM_MAP, PULL_EXISTS] >> goal_assum drule >> simp[EL_MEM]
        )
      )
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC,
          pure_vars, pure_vars_iFunctions] >> rw[] >>
      rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
      )
    )
  >- ( (* Seq *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    pairarg_tac >> gvs[] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    last_x_assum drule >> impl_tac
    >- (rw[] >> last_x_assum drule >> simp[]) >>
    strip_tac >> gvs[] >>
    simp[Once minfer_cases, PULL_EXISTS] >>
    ntac 2 $ goal_assum $ drule_at Any >> rw[]
    >- (
      gvs[assumptions_rel_def] >> simp[PULL_FORALL, aunion_def] >>
      rpt gen_tac >> DEP_REWRITE_TAC[lookup_unionWith] >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
      simp[maunion_def, FLOOKUP_FMERGE] >>
      every_case_tac >> gvs[] >> rw[] >>
      metis_tac[wf_union, domain_union]
      )
    >- (
      simp[cvars_disjoint_def, DISJOINT_ALT] >> rw[] >> CCONTR_TAC >> gvs[SUBSET_DEF] >>
      first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      )
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC] >>
      simp[new_vars_constraint_def, pure_vars] >>
      rw[] >> rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >>
      first_x_assum drule >> rw[]
      )
    )
  >- gvs[fail_def] (* App empty case *)
  >- ( (* App non-empty case *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    pairarg_tac >> gvs[] >> every_case_tac >> gvs[] >>
    rename [
      `FOLDR _ _ _ _ = SOME ((tys,as,cs),m)`,
      `infer _ _ _ _ = SOME ((ety,eas,ecs),l)`] >>
    qsuff_tac
      `∃ass css.
        LIST_REL (λ(e,ty) (a,c). minfer ns (domain mset) e a c ty)
          (ZIP (es,tys)) (ZIP (ass,css)) ∧
        assumptions_rel as (FOLDR maunion FEMPTY ass) ∧
        BIGUNION (set css) = set (MAP to_mconstraint cs) ∧
        cvars_disjoint (ZIP (ass, ZIP (css, tys))) ∧
        new_vars (FOLDR maunion FEMPTY ass)
          (BIGUNION (set css)) (iFunctions tys Exception) ⊆ {v | n ≤ v ∧ v < m} ∧
        LENGTH es = LENGTH tys ∧ LENGTH ass = LENGTH css ∧
        n ≤ m`
    >- (
      rw[] >> gvs[] >>
      first_x_assum drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
      strip_tac >> gvs[] >>
      simp[Once minfer_cases, PULL_EXISTS] >>
      rpt $ goal_assum $ drule_at Any >> simp[] >>
      gvs[new_vars_def, LIST_TO_SET_MAP, IMAGE_IMAGE, combinTheory.o_DEF,
          BIGUNION_SUBSET, PULL_EXISTS, MEM_ZIP, pure_vars, pure_vars_iFunctions] >>
      rw[]
      >- (
        once_rewrite_tac[maunion_comm] >>
        gvs[assumptions_rel_def, aunion_def] >>
        simp[PULL_FORALL] >> rpt gen_tac >>
        DEP_REWRITE_TAC[lookup_unionWith] >>
        DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
        gvs[maunion_def, FLOOKUP_FMERGE, IN_FRANGE_FLOOKUP] >>
        every_case_tac >> gvs[] >> rw[] >> metis_tac[wf_union, domain_union]
        )
      >- (
        gvs[cvars_disjoint_def] >>
        once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
        DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
        pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
        irule SUBSET_DISJOINT >>
        qexistsl_tac [`{v | m ≤ v ∧ v < l}`,`{v | n ≤ v ∧ v < m}`] >>
        conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
        simp[new_vars_def, BIGUNION_SUBSET, IMAGE_IMAGE, PULL_EXISTS] >> rw[]
        >- (
          gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
              FLOOKUP_DEF, BIGUNION_SUBSET] >>
          first_x_assum irule >> simp[EL_MEM] >>
          goal_assum $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
          disch_then $ mp_tac o iffLR >> simp[PULL_EXISTS] >>
          disch_then drule >> simp[EL_MEM] >> strip_tac >> gvs[]
          )
        >- (last_x_assum irule >> simp[EL_MEM])
        )
      >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> rw[])
      >- (
        rw[Once DISJ_COMM] >> rw[DISJ_EQ_IMP] >>
        first_x_assum drule >> rw[SUBSET_DEF] >>
        CCONTR_TAC >> gvs[] >> first_x_assum drule >> rw[]
        )
      >- (
        rw[Once DISJ_COMM] >> rw[DISJ_EQ_IMP] >>
        first_x_assum drule >> rw[SUBSET_DEF] >>
        CCONTR_TAC >> gvs[] >> first_x_assum drule >> rw[]
        )
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> rw[])
      >- (
        simp[EVERY_MEM] >> gen_tac >>
        DEP_REWRITE_TAC[MEM_ZIP] >> simp[LENGTH_ZIP] >>
        drule LIST_REL_LENGTH >> simp[] >> rw[] >>
        DEP_REWRITE_TAC[EL_ZIP] >> simp[] >>
        simp[Once DISJ_COMM] >> rw[DISJ_EQ_IMP]
        >- (
          gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
              BIGUNION_SUBSET, FLOOKUP_DEF] >>
          first_x_assum $ drule_at Any >> simp[EL_MEM] >>
          disch_then $ drule_at Any >> simp[EL_MEM] >>
          rw[SUBSET_DEF] >> CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[]
          )
        >- (
          qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
          disch_then $ mp_tac o iffLR >> simp[PULL_EXISTS] >>
          strip_tac >> CCONTR_TAC >> gvs[] >>
          first_x_assum drule >> simp[EL_MEM] >> rw[] >>
          CCONTR_TAC >> gvs[] >> last_x_assum drule >> simp[SUBSET_DEF] >>
          goal_assum drule >> simp[]
          )
        >- (
          last_x_assum $ qspec_then `EL n' tys` mp_tac >> rw[EL_MEM, SUBSET_DEF] >>
          CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[]
          )
        )
      >- (
        gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
        pop_assum mp_tac >> simp[Once maunion_def, FLOOKUP_FMERGE] >>
        every_case_tac >> gvs[] >> rw[]
        >- (
          first_x_assum drule >> rw[SUBSET_DEF] >>
          first_x_assum drule >> simp[]
          )
        >- (
          first_x_assum drule >> rw[SUBSET_DEF] >>
          first_x_assum drule >> simp[]
          )
        >- (
          first_x_assum drule >> first_x_assum drule >>
          rw[SUBSET_DEF] >> first_x_assum drule >> simp[]
          )
        )
      >- (gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> simp[])
      >- (last_x_assum drule >> rw[SUBSET_DEF] >> first_x_assum drule >> simp[])
      >- (first_x_assum drule >> rw[SUBSET_DEF] >> first_x_assum drule >> simp[])
      >- (first_x_assum drule >> rw[SUBSET_DEF] >> first_x_assum drule >> simp[])
      ) >>
    qpat_x_assum `FOLDR _ _ _ _ = _` mp_tac >>
    pop_assum kall_tac >> pop_assum mp_tac >> last_x_assum kall_tac >>
    last_x_assum mp_tac >> last_x_assum kall_tac >>
    map_every qid_spec_tac [`m`,`n`,`tys`,`as`,`cs`] >>
    Induct_on `es` >> rw[] >> simp[]
    >- (
      qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
      simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
      ) >>
    every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
    rename1 `FOLDR _ _ _ _ = SOME ((tysrest,asrest,csrest),r)` >>
    rename1 `infer _ _ _ _ = SOME ((ty,as,cs),m)` >>
    last_x_assum drule >> strip_tac >> gvs[] >>
    last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
    disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
    strip_tac >> gvs[] >> ntac 2 $ goal_assum $ drule_at Any >>
    once_rewrite_tac[GSYM ZIP] >> irule_at Any EQ_REFL >> simp[] >> rw[]
    >- (
      gvs[assumptions_rel_def, aunion_def, PULL_FORALL] >> rpt gen_tac >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm, lookup_unionWith] >>
      gvs[maunion_def, FLOOKUP_FMERGE] >>
      ntac 2 $ first_x_assum $ qspecl_then [`s`,`s'`] assume_tac >>
      every_case_tac >> gvs[] >> rw[] >>
      metis_tac[wf_union, domain_union, UNION_COMM]
      )
    >- (
      gvs[cvars_disjoint_def] >>
      once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
      DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
      pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
      irule SUBSET_DISJOINT >> goal_assum $ drule_at Any >>
      qexists_tac `{v | n ≤ v ∧ v < r}` >>
      conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
      irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
      gvs[new_vars_def, BIGUNION_SUBSET, pure_vars, PULL_EXISTS] >> rw[]
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj1_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            GSYM CONJ_ASSOC, FLOOKUP_DEF, BIGUNION_SUBSET] >>
        rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj2_tac >>
        simp[PULL_EXISTS] >> goal_assum drule >>
        qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
        disch_then $ irule o iffLR >> goal_assum drule >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj2_tac >> simp[MEM_MAP, PULL_EXISTS] >>
        simp[pure_vars_iFunctions, pure_vars] >>
        simp[MEM_MAP, PULL_EXISTS] >> goal_assum drule >> simp[EL_MEM]
        )
      )
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC,
          pure_vars, pure_vars_iFunctions] >> rw[] >>
      rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
      )
    )
  >- gvs[fail_def] (* Lam empty case *)
  >- ( (* Lam non-empty case *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    pairarg_tac >> gvs[] >>
    qpat_abbrev_tac `gens = GENLIST _ _` >>
    last_x_assum drule >> simp[domain_list_insert] >> impl_tac
    >- (
      reverse $ rw[] >- (last_x_assum drule >> simp[]) >>
      unabbrev_all_tac >> gvs[MEM_GENLIST]
      ) >>
    strip_tac >> gvs[] >> qexists_tac `FDIFF mas (set xs)` >> rw[]
    >- (
      gvs[assumptions_rel_def, PULL_FORALL] >> rpt gen_tac >>
      DEP_REWRITE_TAC[cj 1 map_ok_list_delete, cj 2 map_ok_list_delete] >>
      DEP_REWRITE_TAC[lookup_list_delete] >> simp[FLOOKUP_FDIFF] >>
      IF_CASES_TAC >> simp[] >> metis_tac[]
      )
    >- (
      simp[Once minfer_cases] >> irule_at Any EQ_REFL >>
      gvs[domain_list_insert_alt] >> goal_assum $ drule_at Any >>
      gvs[Abbr `gens`] >> reverse $ rw[]
      >- (
        gvs[EVERY_MEM, MEM_GENLIST] >> ntac 2 strip_tac >> gvs[] >> conj_tac >>
        CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[]
        ) >>
      DEP_REWRITE_TAC[MAP2_MAP] >>
      simp[LIST_TO_SET_MAP, LIST_TO_SET_FLAT] >>
      simp[Once UNION_COMM] >> AP_TERM_TAC >>
      simp[IMAGE_BIGUNION, IMAGE_IMAGE, LIST_TO_SET_MAP,
           combinTheory.o_DEF, LAMBDA_PROD] >>
      rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> ntac 2 $ rw[Once FUN_EQ_THM] >>
      DEP_REWRITE_TAC[LIST_TO_SET_get_assumptions] >> simp[]
      ) >>
    gvs[new_vars_def, new_vars_constraint_def, pure_vars, pure_vars_iFunctions] >>
    DEP_REWRITE_TAC[MAP2_MAP] >> simp[Abbr `gens`] >>
    gvs[LIST_TO_SET_MAP, LIST_TO_SET_FLAT,
         IMAGE_BIGUNION, IMAGE_IMAGE, LIST_TO_SET_MAP,
         combinTheory.o_DEF, LAMBDA_PROD, MAP_GENLIST, GSYM CONJ_ASSOC] >>
    rw[]
    >- (
      irule SUBSET_TRANS >> qexists_tac `BIGUNION (FRANGE mas)` >> conj_tac
      >- (irule SUBSET_BIGUNION >> simp[FRANGE_FDIFF_SUBSET]) >>
      rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
      )
    >- (
      simp[pure_vars, BIGUNION_SUBSET, PULL_EXISTS] >> rpt gen_tac >>
      PairCases_on `x` >> once_rewrite_tac[UNCURRY] >> BETA_TAC >>
      DEP_REWRITE_TAC[LIST_TO_SET_get_assumptions] >> simp[] >> strip_tac >> gvs[] >>
      gvs[MEM_ZIP, get_massumptions_def] >> every_case_tac >> gvs[] >>
      gvs[BIGUNION_SUBSET, IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
      first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
      )
    >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
    >- (
      simp[LIST_TO_SET_GENLIST, IMAGE_IMAGE, combinTheory.o_DEF, pure_vars] >>
      rw[SUBSET_DEF] >> gvs[]
      )
    >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
    )
  >- ( (* Let *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    pairarg_tac >> gvs[] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    last_x_assum drule >> impl_tac
    >- (rw[] >> last_x_assum drule >> simp[]) >>
    strip_tac >> gvs[] >>
    simp[Once minfer_cases, PULL_EXISTS] >>
    ntac 2 $ goal_assum $ drule_at Any >> rw[]
    >- (
      gvs[assumptions_rel_def] >> simp[PULL_FORALL, aunion_def] >>
      rpt gen_tac >> DEP_REWRITE_TAC[lookup_unionWith, lookup_delete] >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
      DEP_REWRITE_TAC[cj 1 delete_thm, cj 2 delete_thm] >> simp[] >>
      simp[maunion_def, FLOOKUP_FMERGE, DOMSUB_FLOOKUP_THM] >>
      every_case_tac >> gvs[] >> rw[] >>
      metis_tac[wf_union, domain_union]
      )
    >- (
      simp[MAP_MAP_o, combinTheory.o_DEF] >> simp[LIST_TO_SET_MAP] >>
      imp_res_tac LIST_TO_SET_get_assumptions >> simp[]
      )
    >- (
      simp[cvars_disjoint_def, DISJOINT_ALT] >> rw[] >> CCONTR_TAC >> gvs[SUBSET_DEF] >>
      first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      ) >>
    gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC] >>
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
    simp[new_vars_constraint_def, pure_vars] >> rw[]
    >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
    >- (
      irule SUBSET_TRANS >> qexists_tac `BIGUNION (FRANGE mas)` >> conj_tac
      >- (irule SUBSET_BIGUNION >> simp[FRANGE_DOMSUB_SUBSET]) >>
      rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
      )
    >- (
      simp[GSYM LIST_TO_SET_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
      simp[LIST_TO_SET_MAP] >>
      DEP_REWRITE_TAC[LIST_TO_SET_get_assumptions] >>
      gvs[BIGUNION_SUBSET, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP] >>
      simp[get_massumptions_def] >> gen_tac >> CASE_TAC >> simp[] >>
      strip_tac >> gvs[] >>
      first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >>
      simp[] >> strip_tac >> gen_tac >> strip_tac >> gvs[SUBSET_DEF] >>
      first_x_assum drule >> simp[]
      )
    >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
    >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
    >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
    )
  >- ( (* Letrec *)
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    pairarg_tac >> gvs[] >> every_case_tac >> gvs[] >>
    rename [
      `FOLDR _ _ _ _ = SOME ((tys,as,cs),m)`,
      `infer _ _ _ _ = SOME ((ety,eas,ecs),l)`] >>
    qsuff_tac
      `∃ass css.
        LIST_REL (λ((fn,e),ty) (a,c). minfer ns (domain mset) e a c ty)
          (ZIP (fns,tys)) (ZIP (ass,css)) ∧
        assumptions_rel as (FOLDR maunion FEMPTY ass) ∧
        BIGUNION (set css) = set (MAP to_mconstraint cs) ∧
        cvars_disjoint (ZIP (ass, ZIP (css, tys))) ∧
        new_vars (FOLDR maunion FEMPTY ass)
          (BIGUNION (set css)) (iFunctions tys Exception) ⊆ {v | l ≤ v ∧ v < m} ∧
        LENGTH fns = LENGTH tys ∧ LENGTH ass = LENGTH css ∧
        l ≤ m`
    >- (
      rw[] >> gvs[] >>
      first_x_assum drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
      strip_tac >> gvs[] >>
      simp[Once minfer_cases, PULL_EXISTS] >>
      rpt $ goal_assum $ drule_at Any >> simp[] >>
      DEP_REWRITE_TAC[MAP2_MAP] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      gvs[new_vars_def, LIST_TO_SET_MAP, IMAGE_IMAGE,
          combinTheory.o_DEF, LAMBDA_PROD, pure_vars] >>
      gvs[pure_vars_iFunctions, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS,
          LAMBDA_PROD, MEM_FLAT, pure_vars, EXISTS_PROD] >>
      simp[PULL_FORALL] >> rpt gen_tac >>
      DEP_REWRITE_TAC[MEM_ZIP] >> simp[PULL_EXISTS] >> rw[]
      >- (
        gvs[assumptions_rel_def, aunion_def] >>
        simp[PULL_FORALL] >> rpt gen_tac >>
        DEP_REWRITE_TAC[lookup_list_delete, lookup_unionWith] >>
        DEP_REWRITE_TAC[cj 1 map_ok_list_delete, cj 2 map_ok_list_delete] >>
        DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
        gvs[maunion_def, FLOOKUP_FDIFF, FLOOKUP_FMERGE, IN_FRANGE_FLOOKUP] >>
        simp[MEM_MAP, EXISTS_PROD] >> gvs[PULL_EXISTS] >>
        IF_CASES_TAC >> gvs[]
        >- (rw[] >> every_case_tac >> gvs[] >> metis_tac[wf_union]) >>
        rw[] >> every_case_tac >> gvs[] >> metis_tac[wf_union, domain_union]
        )
      >- (
        simp[AC UNION_ASSOC UNION_COMM] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        simp[LIST_TO_SET_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
             IMAGE_BIGUNION, LIST_TO_SET_MAP, IMAGE_IMAGE] >>
        rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        rewrite_tac[FUN_EQ_THM] >> rpt gen_tac >> BETA_TAC >>
        rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        irule LIST_TO_SET_get_assumptions >>
        gvs[assumptions_rel_def, aunion_def] >>
        simp[PULL_FORALL] >> rpt gen_tac >>
        DEP_REWRITE_TAC[lookup_unionWith] >>
        DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
        gvs[maunion_def, FLOOKUP_FMERGE, IN_FRANGE_FLOOKUP] >>
        rw[] >> every_case_tac >> gvs[] >> metis_tac[wf_union, domain_union]
        )
      >- (
        gvs[cvars_disjoint_def] >>
        once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
        DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
        pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
        irule SUBSET_DISJOINT >>
        qexistsl_tac [`{v | n ≤ v ∧ v < l}`,`{v | l ≤ v ∧ v < m}`] >>
        conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
        simp[new_vars_def, BIGUNION_SUBSET, IMAGE_IMAGE, PULL_EXISTS] >> rw[]
        >- (
          gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
              FLOOKUP_DEF, BIGUNION_SUBSET] >>
          first_x_assum irule >> simp[EL_MEM] >>
          goal_assum $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
          disch_then $ mp_tac o iffLR >> simp[PULL_EXISTS] >>
          disch_then drule >> simp[EL_MEM] >> strip_tac >> gvs[]
          )
        >- (last_x_assum irule >> simp[EL_MEM])
        )
      >- (
        drule $ SIMP_RULE std_ss [SUBSET_DEF] FRANGE_FDIFF_SUBSET >>
        simp[Once maunion_def] >> gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FMERGE] >> rw[] >>
        every_case_tac >> gvs[PULL_EXISTS]
        >- (first_x_assum drule >> rw[SUBSET_DEF] >> first_x_assum drule >> simp[])
        >- (first_x_assum drule >> rw[SUBSET_DEF] >> first_x_assum drule >> simp[])
        >- (
          first_x_assum drule >> first_x_assum drule >>
          rw[SUBSET_DEF] >> first_x_assum drule >> simp[]
          )
        )
      >- (
        gvs[get_assumptions_def, assumptions_rel_def] >> every_case_tac >> gvs[] >>
        gvs[miscTheory.toAList_domain] >>
        qpat_x_assum `lookup _ _ = _` mp_tac >> simp[aunion_def] >>
        DEP_REWRITE_TAC[lookup_unionWith] >> simp[] >>
        ntac 3 $ first_x_assum $ qspec_then `p_1` assume_tac >>
        rw[] >> every_case_tac >> gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS]
        >- (first_x_assum drule >> simp[SUBSET_DEF])
        >- (first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[])
        >- (
          gvs[domain_union] >>
          first_x_assum drule >> first_x_assum drule >> simp[SUBSET_DEF] >>
          rw[] >> first_x_assum drule >> simp[]
          )
        )
      >- (
        gvs[get_assumptions_def, assumptions_rel_def] >> every_case_tac >> gvs[] >>
        gvs[miscTheory.toAList_domain] >>
        qpat_x_assum `lookup _ _ = _` mp_tac >> simp[aunion_def] >>
        DEP_REWRITE_TAC[lookup_unionWith] >> simp[] >>
        ntac 3 $ first_x_assum $ qspec_then `p_1` assume_tac >>
        rw[] >> every_case_tac >> gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS]
        >- (first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[])
        >- (first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[])
        >- (
          gvs[domain_union] >>
          first_x_assum drule >> first_x_assum drule >> simp[SUBSET_DEF] >>
          rw[] >> first_x_assum drule >> simp[]
          )
        )
      >- (
        last_x_assum $ qspec_then `EL n'' tys` mp_tac >> simp[EL_MEM, SUBSET_DEF] >>
        rw[] >> first_x_assum drule >> simp[]
        )
      >- (
        last_x_assum drule >> simp[SUBSET_DEF] >> rw[] >> first_x_assum drule >> simp[]
        )
      >- (
        last_x_assum drule >> simp[SUBSET_DEF] >> rw[] >> first_x_assum drule >> simp[]
        )
      >- (gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> simp[])
      ) >>
    qpat_x_assum `FOLDR _ _ _ _ = _` mp_tac >>
    `∀mvar. mvar ∈ domain mset ⇒ mvar < l` by (
      first_x_assum drule_all >> strip_tac >> gvs[] >> rw[] >>
      first_x_assum drule >> simp[]) >>
    pop_assum mp_tac >> ntac 2 $ pop_assum kall_tac >>
    last_x_assum mp_tac >> last_x_assum kall_tac >>
    rename1 `n ≤ m` >>
    map_every qid_spec_tac [`m`,`l`,`tys`,`as`,`cs`] >>
    Induct_on `fns` >> rw[] >> simp[]
    >- (
      qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
      simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
      ) >>
    every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
    pairarg_tac >> gvs[] >> every_case_tac >> gvs[] >> simp[PULL_EXISTS] >>
    rename1 `FOLDR _ _ _ _ = SOME ((tysrest,asrest,csrest),r)` >>
    rename1 `infer _ _ _ _ = SOME ((ty,as,cs),m)` >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    first_x_assum drule >> strip_tac >> gvs[] >>
    last_x_assum drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
    strip_tac >> gvs[] >>
    qexistsl_tac [`mas::ass`,`set (MAP to_mconstraint cs)::css`] >> rw[]
    >- (
      gvs[assumptions_rel_def, aunion_def, PULL_FORALL] >> rpt gen_tac >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm, lookup_unionWith] >>
      gvs[maunion_def, FLOOKUP_FMERGE] >>
      rw[] >> every_case_tac >> gvs[] >> metis_tac[wf_union, domain_union, UNION_COMM]
      )
    >- (
      gvs[cvars_disjoint_def] >>
      once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
      DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
      pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
      irule SUBSET_DISJOINT >> goal_assum $ drule_at Any >>
      qexists_tac `{v | n ≤ v ∧ v < r}` >>
      conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
      irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
      gvs[new_vars_def, BIGUNION_SUBSET, pure_vars, PULL_EXISTS] >> rw[]
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj1_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            GSYM CONJ_ASSOC, FLOOKUP_DEF, BIGUNION_SUBSET] >>
        rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj2_tac >>
        simp[PULL_EXISTS] >> goal_assum drule >>
        qpat_x_assum `BIGUNION _ = _` mp_tac >> simp[EXTENSION] >>
        disch_then $ irule o iffLR >> goal_assum drule >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj2_tac >> simp[MEM_MAP, PULL_EXISTS] >>
        simp[pure_vars_iFunctions, pure_vars] >>
        simp[MEM_MAP, PULL_EXISTS] >> goal_assum drule >> simp[EL_MEM]
        )
      )
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC,
          pure_vars, pure_vars_iFunctions] >> rw[] >>
      rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
      )
    )
  >- gvs[fail_def] (* Case empty case *)
  >- ( (* Case non-empty case *)
    Cases_on `css` >- gvs[inferM_rws] >>
    Cases_on `∃pvars rest. h::t = [("",pvars,rest)]`
    >- ( (* TupleCase *)
      gvs[] >> gvs[inferM_rws] >> every_case_tac >> gvs[] >>
      pairarg_tac >> gvs[] >> every_case_tac >> gvs[] >>
      rename1 `infer _ _ _ _ = SOME ((ety,eas,ecs),m)` >>
      rename1 `SOME ((tyrest,_,_),r)` >>
      first_x_assum drule >> impl_tac
      >- (
        simp[domain_list_insert] >> rw[] >> gvs[MEM_GENLIST] >>
        first_x_assum drule >> simp[]
        ) >>
      strip_tac >> gvs[] >> first_x_assum drule >> impl_tac
      >- (rw[] >> first_x_assum drule >> simp[]) >>
      strip_tac >> gvs[] >>
      simp[Once minfer_cases] >> irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS] >>
      DEP_REWRITE_TAC[MAP2_MAP] >>
      simp[MAP2_MAP, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
           LIST_TO_SET_MAP, LIST_TO_SET_FLAT, IMAGE_IMAGE, IMAGE_BIGUNION] >>
      qexistsl_tac [
        `mas'`,`mas`,`IMAGE to_mconstraint (set ecs ∪ set csrest)`,
        `IMAGE to_mconstraint (set csrest)`, `mas'`,
        `IMAGE to_mconstraint (set ecs)`,`ety`,`n`,
        `GENLIST (λn'. n' + SUC n) (LENGTH pvars)`] >>
      rw[] >> gvs[LIST_TO_SET_MAP]
      >- (
        simp[AC UNION_ASSOC UNION_COMM] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        imp_res_tac LIST_TO_SET_get_assumptions >> simp[] >>
        rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> simp[MAP2_MAP, LIST_TO_SET_MAP]
        )
      >- gvs[domain_list_insert_alt, INSERT_UNION_EQ]
      >- (
        gvs[cvars_disjoint_def] >>
        irule SUBSET_DISJOINT >> ntac 2 $ goal_assum $ drule_at Any >>
        simp[DISJOINT_ALT]
        )
      >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
      >- (
        simp[EVERY_MEM, MEM_GENLIST, PULL_EXISTS] >> rw[] >> gvs[SUBSET_DEF] >>
        CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[]
        )
      >- (
        gvs[assumptions_rel_def, aunion_def] >> simp[PULL_FORALL] >> rpt gen_tac >>
        DEP_REWRITE_TAC[lookup_unionWith, lookup_list_delete] >>
        DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >>
        DEP_REWRITE_TAC[cj 1 map_ok_list_delete, cj 2 map_ok_list_delete] >>
        simp[maunion_def, FLOOKUP_FMERGE, FLOOKUP_FDIFF] >>
        rw[] >> every_case_tac >> gvs[] >> metis_tac[domain_union, wf_union]
        ) >>
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC,
          pure_vars, MAP_MAP_o, combinTheory.o_DEF, MAP_GENLIST,
          LIST_TO_SET_GENLIST, IMAGE_IMAGE, GSYM INSERT_SING_UNION,
          IMAGE_BIGUNION, LAMBDA_PROD] >> rw[]
      >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
      >- (
        gvs[BIGUNION_SUBSET] >> rw[] >>
        drule $ SIMP_RULE std_ss [SUBSET_DEF] FRANGE_FDIFF_SUBSET >> strip_tac >>
        first_x_assum drule >> simp[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
        )
      >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
      >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
      >- simp[BIGUNION_SUBSET, PULL_EXISTS]
      >- (
        gvs[BIGUNION_SUBSET, IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
        gvs[get_assumptions_def, assumptions_rel_def, PULL_EXISTS] >>
        gen_tac >> strip_tac >> every_case_tac >> gvs[] >>
        gvs[miscTheory.toAList_domain] >>
        first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
        )
      >- (
        gvs[BIGUNION_SUBSET, EXISTS_PROD, PULL_EXISTS, MEM_ZIP, pure_vars] >>
        gvs[IN_FRANGE_FLOOKUP, get_assumptions_def, assumptions_rel_def, PULL_EXISTS] >>
        ntac 2 gen_tac >> strip_tac >> every_case_tac >> gvs[] >>
        gvs[miscTheory.toAList_domain] >>
        first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
        )
      >- (
        gvs[BIGUNION_SUBSET, PULL_EXISTS, SUBSET_DEF] >> rw[] >>
        first_x_assum drule_all >> simp[]
        )
      >- (
        gvs[BIGUNION_SUBSET, PULL_EXISTS, SUBSET_DEF] >> rw[] >>
        first_x_assum drule_all >> simp[]
        )
      >- (gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule_all >> simp[])
      ) >>
    qpat_abbrev_tac `cases = h::t` >>
    qmatch_asmsub_abbrev_tac `list_CASE _ _ (λv1 v2. foo)` >>
    `foo n = SOME ((ty,as,cs),m)` by (PairCases_on `h` >> gvs[Abbr `cases`] >>
      Cases_on `h0` >> gvs[] >> Cases_on `t` >> gvs[]) >>
    qpat_x_assum `(list_CASE _ _ _) _ = _` kall_tac >> gvs[Abbr `foo`] >>
    `∀n' ty' as' cs' m'.
      infer ns mset e n' = SOME ((ty',as',cs'),m') ∧
      (∀mvar. mvar ∈ domain mset ⇒ mvar < n') ⇒
      ∃mas.
        assumptions_rel as' mas ∧
        minfer ns (domain mset) e mas (set (MAP to_mconstraint cs'))
          ty' ∧ n' ≤ m' ∧
        new_vars mas (set (MAP to_mconstraint cs')) ty' ⊆
        {v | n' ≤ v ∧ v < m'}` by (
        unabbrev_all_tac >> PairCases_on `h` >> gvs[] >>
        Cases_on `h0` >> gvs[] >> Cases_on `t` >> gvs[]) >>
    `∀fresh_v fresh_tyargs cname pvars rest.
      MEM (cname,pvars,rest) cases ⇒
        ∀n' ty' as' cs' m'.
          infer ns (list_insert (fresh_v::fresh_tyargs) mset) rest n' =
          SOME ((ty',as',cs'),m') ∧
          (∀mvar.
             mvar ∈ domain (list_insert (fresh_v::fresh_tyargs) mset) ⇒
             mvar < n') ⇒
          ∃mas.
            assumptions_rel as' mas ∧
            minfer ns (domain (list_insert (fresh_v::fresh_tyargs) mset))
              rest mas (set (MAP to_mconstraint cs')) ty' ∧ n' ≤ m' ∧
            new_vars mas (set (MAP to_mconstraint cs')) ty' ⊆
            {v | n' ≤ v ∧ v < m'}` by (
        unabbrev_all_tac >> PairCases_on `h` >> gvs[] >>
        Cases_on `h0` >> gvs[] >> Cases_on `t` >> gvs[] >>
        rw[] >> first_x_assum irule >> simp[] >> metis_tac[]) >>
    last_x_assum assume_tac >> ntac 4 $ last_x_assum kall_tac >>
    qpat_x_assum `_ = SOME _` assume_tac >> gvs[inferM_rws] >>
    qmatch_asmsub_abbrev_tac `oreturn foo` >>
    Cases_on `foo` >> gvs[inferM_rws] >> rename1 `SOME tdef` >>
    pairarg_tac >> gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    gvs[ALOOKUP_MAP, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
    qmatch_asmsub_abbrev_tac `FOLDR f` >>
    rename [
      `infer _ _ _ _ = SOME ((ety,eas,ecs),m)`,
      `FOLDR _ _ _ _ = SOME ((tyrest,asrest,csrest),l)`] >>
    drule get_typedef_SOME >>
    disch_then $ qspec_then `FST ns` assume_tac >> gvs[] >>
    `EVERY (λ(cn,pvs,_).
      MEM (cn, LENGTH pvs) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)) cases` by (
      rw[EVERY_MEM] >> pairarg_tac >> simp[] >>
      drule $ iffRL sortingTheory.PERM_MEM_EQ >>
      simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> rw[] >>
      first_x_assum drule >> simp[]) >>
    `ALL_DISTINCT (MAP FST cdefs)` by (
      qpat_x_assum `namespace_ok _` assume_tac >> PairCases_on `ns` >>
      gvs[namespace_ok_def] >> gvs[ALL_DISTINCT_APPEND, MAP_FLAT] >>
      drule miscTheory.ALL_DISTINCT_FLAT_EVERY >>
      simp[EVERY_EL, EL_MAP] >> gvs[oEL_THM] >>
      disch_then drule >> simp[]) >>
    qsuff_tac
      `∃ass css final_as final_cs.
        LIST_REL (λ((cname,pvars,rest),ty) (a,c).
          minfer ns (n INSERT set (GENLIST (λn'. n' + SUC n) ar) ∪ domain mset)
            rest a c ty)
          (ZIP (cases,tyrest)) (ZIP (ass,css)) ∧
        LIST_REL
         (λ((cn,pvars,rest),as,cs) (as',cs').
              ∃schemes.
                ALOOKUP cdefs cn = SOME schemes ∧
                (let pvar_cs =
                  MAP2 (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions as v))
                    (v::pvars)
                    (CVar n::
                      MAP (isubst (MAP CVar (GENLIST (λn'. n' + SUC n) ar)) ∘ itype_of)
                        schemes)
                 in
                   as' = FDIFF as (v INSERT set pvars) ∧
                   cs' = BIGUNION (set pvar_cs) ∪ cs))
         (ZIP (cases,ZIP (ass,css))) (ZIP (final_as,final_cs)) ∧
        assumptions_rel asrest (FOLDR maunion FEMPTY final_as) ∧
        BIGUNION (set final_cs) = set (MAP to_mconstraint csrest) ∧
        cvars_disjoint (ZIP (ass, ZIP (css, tyrest))) ∧
        new_vars (FOLDR maunion FEMPTY ass)
          (BIGUNION (set css)) (iFunctions tyrest Exception) ⊆
            {v | ar + SUC n ≤ v ∧ v < l} ∧
        LENGTH cases = LENGTH tyrest ∧ LENGTH ass = LENGTH css ∧
        LENGTH final_as = LENGTH final_cs ∧ ar + SUC n ≤ l`
    >- (
      rw[] >> gvs[] >>
      last_x_assum drule >> impl_tac >- (rw[] >> first_x_assum drule >> simp[]) >>
      strip_tac >> gvs[] >>
      simp[Once minfer_cases] >> ntac 2 $ irule_at Any $ OR_INTRO_THM2 >>
      simp[PULL_EXISTS, GSYM CONJ_ASSOC] >>
      goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
      gvs[domain_list_insert_alt, INSERT_UNION_EQ] >>
      goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
      rpt $ goal_assum $ drule_at Any >> simp[SF ETA_ss, combinTheory.o_DEF] >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, new_vars_def,
          LIST_TO_SET_MAP, IMAGE_IMAGE, pure_vars, pure_vars_iFunctions,
          BIGUNION_SUBSET, PULL_EXISTS, MEM_GENLIST, EXISTS_PROD] >>
      rw[]
      >- (
        gvs[cvars_disjoint_def] >>
        once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
        DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
        pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
        irule SUBSET_DISJOINT >>
        qexistsl_tac [`{v | l ≤ v ∧ v < m}`,`{v | n ≤ v ∧ v < l}`] >>
        conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
        simp[new_vars_def, BIGUNION_SUBSET, IMAGE_IMAGE, PULL_EXISTS] >> rw[]
        >- (
          gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
              FLOOKUP_DEF, BIGUNION_SUBSET] >>
          first_x_assum $ drule_at Any >> disch_then $ drule_at Any >>
          simp[EL_MEM, SUBSET_DEF] >> rw[] >>
          first_x_assum drule >> simp[]
          )
        >- (
          first_x_assum drule >> simp[EL_MEM, SUBSET_DEF] >> rw[] >>
          first_x_assum drule >> simp[]
          )
        >- (
          gvs[SUBSET_DEF, PULL_FORALL] >> gen_tac >> strip_tac >>
          qpat_x_assum `∀a b. MEM _ tyrest ⇒ _` $ drule_at Any >> simp[EL_MEM]
          )
        )
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule_all >> simp[])
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule_all >> simp[])
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule_all >> simp[])
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule_all >> simp[])
      >- (
        simp[EVERY_MEM, FORALL_PROD] >> rpt gen_tac >>
        DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[LENGTH_ZIP] >> simp[PULL_EXISTS] >>
        gen_tac >> strip_tac >>
        pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >>
        strip_tac >> gvs[] >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            BIGUNION_SUBSET, FLOOKUP_DEF, GSYM CONJ_ASSOC] >>
        rw[]
        >- (
          CCONTR_TAC >> gvs[] >>
          first_x_assum $ drule_at Any >> disch_then $ drule_at Any >>
          simp[EL_MEM, SUBSET_DEF] >> goal_assum drule >> simp[]
          )
        >- (
          CCONTR_TAC >> gvs[] >> first_x_assum $ drule_at Any >>
          simp[EL_MEM, SUBSET_DEF] >> goal_assum drule >> simp[]
          )
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF] >>
          first_x_assum $ drule_at Any >> simp[EL_MEM]
          )
        )
      >- (
        simp[EVERY_MEM, FORALL_PROD, MEM_GENLIST] >> rpt gen_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            BIGUNION_SUBSET, FLOOKUP_DEF, GSYM CONJ_ASSOC] >>
        gen_tac >> strip_tac >> gvs[] >> rpt conj_tac
        >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
        >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum $ drule_at Any >> simp[])
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF, PULL_FORALL] >>
          first_x_assum drule_all >> simp[]
          )
        >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum $ drule_at Any >> simp[]) >>
        rpt gen_tac >> DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> strip_tac >> gvs[] >>
        pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >>
        strip_tac >> gvs[SUBSET_DEF, PULL_FORALL, GSYM CONJ_ASSOC, AND_IMP_INTRO] >>
        rw[]
        >- (
          CCONTR_TAC >> gvs[] >>
          first_x_assum $ drule_at Any >> disch_then $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          CCONTR_TAC >> gvs[] >>
          first_x_assum $ drule_at Any >> disch_then $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF] >>
          first_x_assum $ drule_at Any >> simp[EL_MEM]
          )
        )
      >- (
        gvs[assumptions_rel_def, aunion_def] >> simp[PULL_FORALL] >> rpt gen_tac >>
        DEP_REWRITE_TAC[lookup_unionWith] >>
        DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
        simp[Once maunion_def, FLOOKUP_FMERGE] >>
        rw[] >> every_case_tac >> gvs[] >> metis_tac[wf_union, domain_union]
        )
      >- (
        gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, BIGUNION_SUBSET] >>
        pop_assum mp_tac >> simp[Once maunion_def, FLOOKUP_FMERGE] >>
        rw[] >> every_case_tac >> gvs[SUBSET_DEF, PULL_FORALL]
        >- (first_x_assum drule >> rw[] >> first_x_assum drule >> simp[])
        >- (
          gen_tac >> strip_tac >> gvs[FLOOKUP_FOLDR_maunion] >>
          qpat_x_assum `MEM _ _` mp_tac >> simp[MEM_EL] >> strip_tac >>
          gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[EL_ZIP] >>
          pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
          gvs[FLOOKUP_FDIFF, PULL_EXISTS, FLOOKUP_DEF, GSYM CONJ_ASSOC] >>
          first_x_assum $ drule_at Any >> simp[EL_MEM] >>
          disch_then $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          rpt gen_tac >> first_x_assum drule >> strip_tac >> conj_tac
          >- (strip_tac >> first_x_assum drule >> simp[]) >>
          gvs[FLOOKUP_FOLDR_maunion] >> strip_tac >> gvs[] >>
          qpat_x_assum `MEM _ _` mp_tac >> simp[MEM_EL] >> strip_tac >>
          gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[EL_ZIP] >>
          pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
          gvs[FLOOKUP_FDIFF, PULL_EXISTS, FLOOKUP_DEF, GSYM CONJ_ASSOC] >>
          first_x_assum $ drule_at Any >> simp[EL_MEM] >>
          disch_then $ drule_at Any >> simp[EL_MEM] >>
          disch_then drule >> simp[]
          )
        )
      >- (gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> simp[])
      >- (gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> simp[])
      >- (
        gvs[SUBSET_DEF] >> gen_tac >> strip_tac >>
        Cases_on `tyrest` >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
        first_x_assum drule >> simp[]
        )
      >- (
        gvs[SUBSET_DEF] >> gen_tac >> strip_tac >>
        Cases_on `tyrest` >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
        first_x_assum drule_all >> simp[]
        )
      >- (gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule_all >> simp[])
      >- (
        qpat_assum `BIGUNION _ = _` mp_tac >> rewrite_tac[EXTENSION] >> simp[] >>
        disch_then $ mp_tac o iffRL >> simp[PULL_EXISTS] >>
        disch_then drule >> strip_tac >> gvs[] >>
        qpat_x_assum `MEM _ _` mp_tac >> simp[MEM_EL] >> strip_tac >> gvs[] >>
        qpat_x_assum `LIST_REL _ _ _` assume_tac >> gvs[LIST_REL_EL_EQN] >>
        first_x_assum drule >> simp[EL_ZIP] >> pairarg_tac >> gvs[] >>
        strip_tac >> gvs[pure_vars]
        >- (
          gvs[get_massumptions_def] >> every_case_tac >> gvs[] >>
          gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_FOLDR_maunion, FLOOKUP_DEF] >>
          first_x_assum $ drule_at Any >>
          simp[EL_MEM, BIGUNION_SUBSET, PULL_EXISTS] >>
          disch_then $ drule_at Any >> simp[EL_MEM, SUBSET_DEF] >>
          disch_then drule >> simp[]
          )
        >- (
          qpat_x_assum `MEM _ (MAP2 _ _ _)` mp_tac >>
          DEP_REWRITE_TAC[MAP2_MAP] >> simp[] >>
          gvs[EVERY_EL] >> last_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
          drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[] >> strip_tac >> gvs[] >>
          simp[MEM_MAP, EXISTS_PROD, MEM_ZIP, PULL_EXISTS] >> rw[] >>
          gvs[pure_vars, EL_MAP] >> conj_tac
          >- (
            qpat_x_assum `_ ∈ get_massumptions _ _` mp_tac >>
            simp[get_massumptions_def] >> CASE_TAC >> gvs[] >> strip_tac >>
            gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
                BIGUNION_SUBSET, FLOOKUP_DEF] >>
            first_x_assum $ drule_at Any >> disch_then $ drule_at Any >>
            simp[EL_MEM, SUBSET_DEF] >> disch_then drule >> simp[]
            )
          >- (
            irule SUBSET_TRANS >>
            irule_at Any pure_vars_isubst_SUBSET >> simp[] >>
            simp[BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, MEM_GENLIST, pure_vars]
            )
          )
        >- (
          first_x_assum drule >> simp[EL_MEM, SUBSET_DEF] >> rw[] >>
          first_x_assum drule >> simp[]
          )
        )
      >- (
        gvs[SUBSET_DEF] >> gen_tac >> strip_tac >>
        Cases_on `tyrest` >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
        first_x_assum drule >> simp[]
        )
      ) >>
    qpat_x_assum `get_typedef _ _ _ = _` kall_tac >>
    qpat_x_assum `PERM _ _` kall_tac >>
    qpat_x_assum `infer _ _ _ _ = _` kall_tac >>
    `∀mvar. mvar ∈ domain mset ⇒ mvar < ar + SUC n` by (
      rw[] >> last_x_assum drule >> simp[]) >>
    last_x_assum assume_tac >>
    ntac 4 $ last_x_assum kall_tac >>
    rpt $ pop_assum mp_tac >>
    map_every qid_spec_tac [`n`,`l`,`tyrest`,`asrest`,`csrest`] >>
    Induct_on `cases` >> rw[] >> simp[]
    >- (
      qexistsl_tac [`[]`,`[]`,`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
      simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
      ) >>
    gvs[Abbr `f`] >> pairarg_tac >> gvs[] >>
    every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
    qmatch_asmsub_abbrev_tac `FOLDR f` >>
    rename1 `FOLDR _ _ _ _ = SOME ((tysrest,asrest,csrest),r)` >>
    rename1 `infer _ _ _ _ = SOME ((ty,as,cs),m)` >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    last_x_assum drule >> disch_then drule >> simp[] >>
    strip_tac >> gvs[] >>
    first_x_assum drule >> impl_tac
    >- (rw[domain_list_insert, MEM_GENLIST] >> gvs[] >> first_x_assum drule >> simp[]) >>
    strip_tac >> gvs[] >>
    gvs[domain_list_insert_alt, GSYM CONJ_ASSOC, INSERT_UNION_EQ] >>
    goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
    goal_assum $ drule_at $ Pat `minfer _ _ _ _ _` >>
    qexistsl_tac [`mas::ass`,`set (MAP to_mconstraint cs) :: css`] >> simp[] >>
    simp[PULL_EXISTS, GSYM CONJ_ASSOC, EXISTS_PROD] >>
    goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
    Cases_on `ALOOKUP cdefs cn` >> gvs[inferM_rws] >> rw[] >>
    rewrite_tac[Once $ GSYM ZIP] >> irule_at Any EQ_REFL >> simp[] >> rw[]
    >- (
      gvs[assumptions_rel_def, aunion_def] >> simp[PULL_FORALL] >> rpt gen_tac >>
      DEP_REWRITE_TAC[lookup_unionWith, lookup_list_delete] >>
      DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >>
      DEP_REWRITE_TAC[cj 1 map_ok_list_delete, cj 2 map_ok_list_delete] >> simp[] >>
      simp[Once maunion_def, FLOOKUP_FMERGE, FLOOKUP_FDIFF] >>
      rw[] >> every_case_tac >> gvs[] >> metis_tac[wf_union, domain_union]
      )
    >- (
      DEP_REWRITE_TAC[MAP2_MAP] >>
      simp[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LIST_TO_SET_MAP, IMAGE_IMAGE,
           LIST_TO_SET_FLAT, LAMBDA_PROD, IMAGE_BIGUNION] >>
      drule LIST_TO_SET_get_assumptions >> rw[] >>
      qpat_x_assum `MEM _ (MAP _ _)` mp_tac >> rw[MEM_MAP] >> pairarg_tac >> gvs[] >>
      drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[]
      )
    >- (
      gvs[cvars_disjoint_def] >>
      once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rpt gen_tac >>
      DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
      pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
      irule SUBSET_DISJOINT >> goal_assum $ drule_at Any >>
      qexists_tac `{v | ar + SUC n ≤ v ∧ v < r}` >>
      conj_tac >- rw[DISJOINT_ALT] >> gvs[] >> rw[] >>
      irule SUBSET_TRANS >> goal_assum $ drule_at Any >>
      gvs[new_vars_def, BIGUNION_SUBSET, pure_vars, PULL_EXISTS] >> rw[]
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj1_tac >>
        gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
            GSYM CONJ_ASSOC, FLOOKUP_DEF, BIGUNION_SUBSET] >>
        rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj1_tac >> disj2_tac >>
        simp[PULL_EXISTS] >> ntac 2 $ goal_assum drule >> simp[EL_MEM]
        )
      >- (
        simp[SUBSET_DEF] >> rw[] >> disj2_tac >> simp[MEM_MAP, PULL_EXISTS] >>
        simp[pure_vars_iFunctions, pure_vars] >>
        simp[MEM_MAP, PULL_EXISTS] >> goal_assum drule >> simp[EL_MEM]
        )
      )
    >- (
      gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC,
          pure_vars, pure_vars_iFunctions] >> rw[] >>
      rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[]
      )
    )
  >- gvs[fail_def] (* Seq empty case *)
  >- gvs[fail_def] (* Seq singleton case *)
  >- gvs[fail_def] (* Seq too many args case *)
QED

val _ = export_theory();

