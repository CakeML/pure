
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite goalStack;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory rich_listTheory finite_mapTheory pred_setTheory
     sptreeTheory;
open mlmapTheory;
open pure_typingTheory pure_typingPropsTheory
     pure_cexpTheory pure_configTheory pure_varsTheory pure_unificationTheory
     pure_inference_commonTheory pure_inferenceTheory pure_inferencePropsTheory
     pure_miscTheory pure_barendregtTheory;

val _ = new_theory "pure_inference_model";

(******************** Definitions ********************)

Datatype:
  mconstraint = mUnify itype itype
             | mInstantiate itype (num # itype)
             | mImplicit itype (num set) itype
End

Type massumptions[pp] = ``:mlstring |-> num set``;

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
        (FEMPTY |+ (x, {fresh})) {} (CVar fresh))

[~Tuple:]
  (LENGTH es = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ(e,ty) (a,c). minfer ns mset e a c ty)
      (ZIP (es,tys)) (ZIP (ass,css)) ∧
   cvars_disjoint (ZIP (ass, ZIP (css, tys)))
    ⇒ minfer ns mset (Prim d (Cons «») es)
        (FOLDR maunion FEMPTY ass) (BIGUNION (set css)) (Tuple tys))

[~Ret:]
  (minfer ns mset e as cs ty
    ⇒ minfer ns mset (Prim d (Cons «Ret») [e])
        as cs (M ty))

[~Bind:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f1 ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2 ∧
   f2 ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2
    ⇒ minfer ns mset (Prim d (Cons «Bind») [e1;e2])
        (maunion as1 as2)
        ({mUnify ty1 (M $ CVar f1); mUnify ty2 (Function (CVar f1) (M $ CVar f2))}
          ∪ cs1 ∪ cs2)
        (M $ CVar f2))

[~Raise:]
  (minfer ns mset e as cs ty ∧
   f ∉ mset ∪ new_vars as cs ty
    ⇒ minfer ns mset (Prim d (Cons «Raise») [e])
        as (mUnify (CVar f) (CVar f) INSERT mUnify ty Exception INSERT cs)
        (M $ CVar f))

[~Handle:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2
    ⇒ minfer ns mset (Prim d (Cons «Handle») [e1;e2])
        (maunion as1 as2)
        ({mUnify ty1 (M $ CVar f); mUnify ty2 (Function Exception (M $ CVar f))}
          ∪ cs1 ∪ cs2)
        (M $ CVar f))

[~Act:]
  (minfer ns mset e as cs ty
    ⇒ minfer ns mset (Prim d (Cons «Act») [e])
        as (mUnify ty (PrimTy Message) INSERT cs) (M StrTy))

[~Alloc:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)]
    ⇒ minfer ns mset (Prim d (Cons «Alloc») [e1;e2])
        (maunion as1 as2)
        (mUnify ty1 IntTy INSERT cs1 ∪ cs2)
        (M $ Array ty2))

[~Length:]
  (minfer ns mset e as cs ty ∧
   fresh ∉ mset ∪ new_vars as cs ty
    ⇒ minfer ns mset (Prim d (Cons «Length») [e])
        as (mUnify ty (Array $ CVar fresh) INSERT cs) (M IntTy))

[~Deref:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2
    ⇒ minfer ns mset (Prim d (Cons «Deref») [e1;e2])
        (maunion as1 as2)
        ({mUnify ty2 IntTy; mUnify ty1 (Array $ CVar f)} ∪ cs1 ∪ cs2)
        (M $ CVar f))

[~Update:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   minfer ns mset e3 as3 cs3 ty3 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2);(as3,cs3,ty3)] ∧
   f ∉ mset ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2 ∪ new_vars as3 cs3 ty3
    ⇒ minfer ns mset (Prim d (Cons «Update») [e1;e2;e3])
        (maunion as1 (maunion as2 as3))
        ({mUnify ty3 (CVar f); mUnify ty2 IntTy; mUnify ty1 (Array $ CVar f)}
          ∪ cs1 ∪ cs2 ∪ cs3)
        (M Unit))

[~True:]
  (minfer ns mset (Prim d (Cons «True») []) FEMPTY {} BoolTy)
[~False:]
  (minfer ns mset (Prim d (Cons «False») []) FEMPTY {} BoolTy)

[~Exception:]
  (LENGTH es = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ(e,ty) (a,c). minfer ns mset e a c ty)
      (ZIP (es,tys)) (ZIP (ass,css)) ∧
   cvars_disjoint (ZIP (ass, ZIP (css, tys))) ∧
   ALOOKUP (FST ns) s = SOME arg_tys ∧
   LENGTH arg_tys = LENGTH tys ∧
   explode s ∉ monad_cns
    ⇒ minfer ns mset (Prim d (Cons s) es)
        (FOLDR maunion FEMPTY ass)
        (set (list$MAP2 (λt a. mUnify t (itype_of a)) tys arg_tys) ∪ BIGUNION (set css))
        Exception)

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
   explode cname ∉ monad_cns
    ⇒ minfer ns mset (Prim d (Cons cname) es)
        (FOLDR maunion FEMPTY ass)
        (set (MAP (λf. mUnify (CVar f) (CVar f)) freshes) ∪
         set (list$MAP2
              (λt a. mUnify t (isubst (MAP CVar freshes) $ itype_of a)) tys arg_tys) ∪
          BIGUNION (set css))
        (TypeCons id (MAP CVar freshes)))

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
        (PrimTy pret_ty))

[~Seq:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)]
    ⇒ minfer ns mset (Prim d Seq [e1;e2])
        (maunion as1 as2) (cs1 ∪ cs2) ty2)

[~App:]
  (¬NULL es ∧
   LENGTH es = LENGTH tys ∧
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
        as (mUnify fty (iFunctions tys (CVar f)) INSERT cs) (CVar f))

[~Lam:]
  (¬NULL xs ∧
   minfer ns (set freshes ∪ mset) e as cs ty ∧
   LENGTH freshes = LENGTH xs ∧
   EVERY (λf. f ∉ mset ∪ new_vars as cs ty) freshes
    ⇒ minfer ns mset (Lam d xs e)
        (FDIFF as (set xs))
        (cs ∪ set (MAP (λf. mUnify (CVar f) (CVar f)) freshes) ∪
         (BIGUNION $ set $ list$MAP2 (λf x.
          IMAGE (λn. mUnify (CVar f) (CVar n)) (get_massumptions as x)) freshes xs))
        (iFunctions (MAP CVar freshes) ty))

[~Let:]
  (minfer ns mset e1 as1 cs1 ty1 ∧
   minfer ns mset e2 as2 cs2 ty2 ∧
   cvars_disjoint [(as1,cs1,ty1);(as2,cs2,ty2)]
    ⇒ minfer ns mset (Let d x e1 e2)
        (maunion as1 (as2 \\ x))
        (IMAGE (λn. mImplicit (CVar n) mset ty1) (get_massumptions as2 x) ∪ cs1 ∪ cs2)
        ty2)

[~Letrec:]
  (¬NULL fns ∧
   LENGTH fns = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ((fn,e),ty) (a,c). minfer ns mset e a c ty)
      (ZIP (fns,tys)) (ZIP (ass,css)) ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint ((eas,ecs,ety)::ZIP (ass, ZIP (css, tys))) ∧
   as = FOLDR maunion FEMPTY ass ∧
   cs = ecs ∪ BIGUNION (set css)
    ⇒ minfer ns mset (Letrec d fns e)
        (FDIFF (maunion eas as) (set $ MAP FST fns))
        (set (MAP (λt. mUnify t t) tys) ∪ cs ∪
          (BIGUNION $ set $ list$MAP2 (λ(x,b) tyfn.
            IMAGE (λn. mUnify (CVar n) tyfn) (get_massumptions as x)) fns tys) ∪
          (BIGUNION $ set $ list$MAP2 (λ(x,b) tyfn.
            IMAGE (λn. mImplicit (CVar n) mset tyfn) (get_massumptions eas x)) fns tys))
        ety)

[~BoolCase:]
  (minfer ns (f INSERT mset) e1 as1 cs1 ty1 ∧
   minfer ns (f INSERT mset) e2 as2 cs2 ty2 ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint [(eas,ecs,ety);(as1,cs1,ty1);(as2,cs2,ty2)] ∧
   f ∉ mset ∪ new_vars eas ecs ety ∪ new_vars as1 cs1 ty1 ∪ new_vars as2 cs2 ty2 ∧
   {cn1; cn2} = {«True»;«False»}
    ⇒ minfer ns mset (Case d e v [(cn1,[],e1);(cn2,[],e2)] NONE)
        (maunion eas (maunion as1 as2 \\ v))
        (mUnify (CVar f) ety INSERT mUnify ety BoolTy INSERT mUnify ty1 ty2 INSERT
          IMAGE (λn. mUnify (CVar n) (CVar f))
            (get_massumptions as1 v ∪ get_massumptions as2 v) ∪
          ecs ∪ cs1 ∪ cs2)
        ty1)

[~TupleCase:]
  (¬MEM v pvars ∧ ALL_DISTINCT pvars ∧
   minfer ns (f INSERT set freshes ∪ mset) rest asrest csrest tyrest ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint [(eas,ecs,ety);(asrest,csrest,tyrest)] ∧
   EVERY (λf.
    f ∉ mset ∪ new_vars eas ecs ety ∪ new_vars asrest csrest tyrest)
    (f::freshes) ∧
   LENGTH pvars = LENGTH freshes ∧
   pvar_cs =
    list$MAP2
      (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions asrest v))
      (v::pvars) (MAP CVar $ f::freshes)
    ⇒ minfer ns mset (Case d e v [(«»,pvars,rest)] NONE)
        (maunion eas (FDIFF asrest (set (v::pvars))))
        (mUnify (CVar f) ety INSERT mUnify ety (Tuple $ MAP CVar freshes) INSERT
          BIGUNION (set pvar_cs) ∪ ecs ∪ csrest)
        tyrest)

[~ExceptionCase:]
  (¬MEM v (FLAT (MAP (FST o SND) cases)) ∧
   PERM (MAP (λ(cn,ts). (cn, LENGTH ts)) (FST ns))
    (MAP (λ(cn,pvars,rest). (cn, LENGTH pvars)) cases) ∧
   LENGTH cases = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   LIST_REL (λ((cname,pvars,rest),ty) (a,c).
      minfer ns (f INSERT mset) rest a c ty)
      (ZIP (cases,tys)) (ZIP (ass,css)) ∧
   EVERY (λ(cname,pvars,rest). ALL_DISTINCT pvars) cases ∧
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
    ⇒ minfer ns mset (Case d e v cases NONE)
        (FOLDR maunion FEMPTY (eas::final_as))
        (mUnify (CVar f) ety INSERT mUnify ety Exception INSERT
          set (MAP (λt. mUnify (HD tys) t) (TL tys)) ∪ ecs ∪ BIGUNION (set final_cs))
        (HD tys))

[~CaseExhaustive:]
  (¬MEM v (FLAT (MAP (FST o SND) cases)) ∧
   oEL id (SND ns) = SOME (ar, cdefs) ∧
   PERM (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)
    (MAP (λ(cn,pvars,rest). (cn, LENGTH pvars)) cases) ∧
   LENGTH cases = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   ar = LENGTH freshes ∧
   LIST_REL (λ((cname,pvars,rest),ty) (a,c).
               minfer ns (f INSERT set freshes ∪ mset) rest a c ty)
            (ZIP (cases,tys))
            (ZIP (ass,css)) ∧
   EVERY (λ(cname,pvars,rest). ALL_DISTINCT pvars) cases ∧
   minfer ns mset e eas ecs ety ∧
   cvars_disjoint ((eas,ecs,ety)::ZIP (ass, ZIP (css, tys))) ∧
   EVERY (λf. f ∉ mset ∧
              EVERY (λ(as,cs,ty). f ∉ new_vars as cs ty)
                    (ZIP (eas::ass,ZIP(ecs::css,ety::tys))))
         (f::freshes) ∧
   LENGTH final_as = LENGTH final_cs ∧
   LIST_REL (λ((cn,pvars,rest),as,cs) (as',cs').
               ∃schemes.
              ALOOKUP cdefs cn = SOME schemes ∧
              let pvar_cs =
                  list$MAP2
                  (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions as v))
                  (v::pvars)
                  (CVar f :: MAP (isubst (MAP CVar freshes) o itype_of) schemes)
              in
                as' = FDIFF as (v INSERT set pvars) ∧
                cs' = BIGUNION (set pvar_cs) ∪ cs)
            (ZIP (cases,ZIP (ass,css)))
            (ZIP (final_as,final_cs))
    ⇒ minfer ns mset (Case d e v cases NONE)
        (FOLDR maunion FEMPTY (eas::final_as))
        (mUnify (CVar f) ety INSERT
         mUnify ety (TypeCons id (MAP CVar freshes)) INSERT
         set (MAP (λt. mUnify (HD tys) t) (TL tys)) ∪ ecs ∪
         BIGUNION (set final_cs))
        (HD tys))

[~CaseNonexhaustive:]
  (¬MEM v (FLAT (MAP (FST o SND) cases)) ∧
   oEL id (SND ns) = SOME (ar, cdefs) ∧
   cases ≠ [] ∧ us_cn_ars ≠ [] ∧
   PERM (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)
    (MAP (λ(cn,pvars,rest). (cn, LENGTH pvars)) cases ++ us_cn_ars) ∧
   LENGTH cases = LENGTH tys ∧
   LENGTH ass = LENGTH css ∧
   ar = LENGTH freshes ∧
   LIST_REL (λ((cname,pvars,rest),ty) (a,c).
               minfer ns (f INSERT set freshes ∪ mset) rest a c ty)
            (ZIP (cases,tys))
            (ZIP (ass,css)) ∧
   EVERY (λ(cname,pvars,rest). ALL_DISTINCT pvars) cases ∧
   minfer ns mset e eas ecs ety ∧
   minfer ns (f INSERT set freshes ∪ mset) usrest usas uscs usty ∧
   cvars_disjoint ((eas,ecs,ety)::(usas,uscs,usty)::ZIP (ass, ZIP (css, tys))) ∧
   EVERY (λf. f ∉ mset ∧
              EVERY (λ(as,cs,ty). f ∉ new_vars as cs ty)
                    (ZIP (eas::usas::ass,ZIP(ecs::uscs::css,ety::usty::tys))))
         (f::freshes) ∧
   LENGTH final_as = LENGTH final_cs ∧
   LIST_REL (λ((cn,pvars,rest),as,cs) (as',cs').
               ∃schemes.
              ALOOKUP cdefs cn = SOME schemes ∧
              let pvar_cs =
                  list$MAP2
                  (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions as v))
                  (v::pvars)
                  (CVar f :: MAP (isubst (MAP CVar freshes) o itype_of) schemes)
              in
                as' = FDIFF as (v INSERT set pvars) ∧
                cs' = BIGUNION (set pvar_cs) ∪ cs)
            (ZIP (cases,ZIP (ass,css)))
            (ZIP (final_as,final_cs)) ∧
    final_usas = usas \\ v ∧
    final_uscs = IMAGE (λn. mUnify (CVar n) (CVar f)) (get_massumptions usas v) ∪ uscs
    ⇒ minfer ns mset (Case d e v cases (SOME (us_cn_ars, usrest)))
        (FOLDR maunion FEMPTY (eas::final_usas::final_as))
        (mUnify (CVar f) ety INSERT
         mUnify ety (TypeCons id (MAP CVar freshes)) INSERT
         set (MAP (λt. mUnify usty t) tys) ∪ ecs ∪
         final_uscs ∪ BIGUNION (set final_cs))
        usty)

[~Annot:]
  (minfer ns mset e as cs ty ⇒ minfer ns mset (Annot d annot e) as cs ty)
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

Definition msubst_vars_def:
  msubst_vars s vars = BIGUNION (IMAGE (pure_vars o pure_walkstar s o CVar) vars)
End

Definition mactivevars_def:
  mactivevars (mUnify t1 t2) = pure_vars t1 ∪ pure_vars t2 ∧
  mactivevars (mInstantiate t1 (vs,sch)) = pure_vars t1 ∪ pure_vars sch ∧
  mactivevars (mImplicit t1 vs t2) = pure_vars t1 ∪ (vs ∩ pure_vars t2)
End

Definition mis_solveable_def:
  mis_solveable (mUnify t1 t2) cs = T ∧
  mis_solveable (mInstantiate t1 sch) cs = T ∧
  mis_solveable (mImplicit t1 vs t2) cs = (
    pure_vars t2 ∩ (BIGUNION $ IMAGE mactivevars ({mImplicit t1 vs t2} ∪ cs)) ⊆ vs)
End

Definition constraint_vars_def:
  constraint_vars (mUnify t1 t2) = pure_vars t1 ∪ pure_vars t2 ∧
  constraint_vars (mInstantiate t (vs,sch)) = pure_vars t ∪ pure_vars sch ∧
  constraint_vars (mImplicit t1 vs t2) = pure_vars t1 ∪ vs ∪ pure_vars t2
End

Definition constraints_ok_def:
  constraints_ok tds cs ⇔
  ∀c. c ∈ cs ⇒
    (∀t1 t2. c = mUnify t1 t2 ⇒
      itype_ok tds 0 t1 ∧ itype_ok tds 0 t2) ∧
    (∀t1 vs t2. c = mInstantiate t1 (vs,t2) ⇒
      itype_ok tds 0 t1 ∧ itype_ok tds vs t2) ∧
    (∀t1 vs t2. c = mImplicit t1 vs t2 ⇒
      itype_ok tds 0 t1 ∧ itype_ok tds 0 t2 ∧ FINITE vs)
End


(******************** Lemmas ********************)

Triviality maunion_comm:
  ∀x y. maunion x y = maunion y x
Proof
  rw[maunion_def] >>
  irule $ iffRL $ SIMP_RULE (srw_ss()) [combinTheory.COMM_DEF] FMERGE_COMM >>
  rw[UNION_COMM]
QED

Theorem FDIFF_maunion:
  FDIFF (maunion a b) s = maunion (FDIFF a s) (FDIFF b s)
Proof
  rw[maunion_def, FDIFF_FMERGE]
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

Theorem FLOOKUP_maunion:
  ∀a b k.
    FLOOKUP (maunion a b) k =
      case FLOOKUP a k of
      | NONE => FLOOKUP b k
      | SOME av => SOME (case FLOOKUP b k of NONE => av | SOME bv => av ∪ bv)
Proof
  rw[maunion_def, FLOOKUP_FMERGE] >> rpt CASE_TAC >> simp[]
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

Theorem BIGUNION_FRANGE_FOLDR_maunion:
  ∀as ass a. MEM as ass ⇒ BIGUNION (FRANGE as) ⊆ BIGUNION (FRANGE (FOLDR maunion a ass))
Proof
  rw[BIGUNION_SUBSET] >> rw[SUBSET_DEF] >>
  gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_FOLDR_maunion, GSYM CONJ_ASSOC] >>
  goal_assum drule >> qexists_tac `k` >> simp[] >>
  gvs[FLOOKUP_DEF] >> metis_tac[]
QED

Triviality infer_bind_alt_def:
  ∀g f.
    infer_bind g f = λs. case g s of Err e => Err e | OK ((a,b,c),s') => f (a,b,c) s'
Proof
  rw[FUN_EQ_THM, infer_bind_def] >> rpt (CASE_TAC >> simp[])
QED

Theorem subst_vars_msubst_vars:
  ∀s vs. pure_wfs s ⇒
    domain (subst_vars s vs) = msubst_vars s (domain vs)
Proof
  rw[subst_vars_def, msubst_vars_def] >>
  qsuff_tac
    `∀m b.
      domain (
        foldi (λn u acc. union acc (freecvars (pure_walkstar s (CVar n)))) m b vs) =
      BIGUNION (IMAGE
        (pure_vars o pure_walkstar s o CVar o (λi. m + sptree$lrnext m * i))
        (domain vs))
        ∪ domain b`
  >- rw[Once lrnext_def, combinTheory.o_DEF] >>
  qid_spec_tac `vs` >> Induct >> rw[foldi_def] >>
  simp[pure_walkstar_alt, freecvars_def, domain_union]
  >- (CASE_TAC >> simp[freecvars_pure_vars, domain_union, Once UNION_COMM]) >>
  simp[IMAGE_IMAGE, combinTheory.o_DEF] >>
  simp[lrnext_lrnext, lrnext_lrnext_2, LEFT_ADD_DISTRIB]
  >- simp[AC UNION_ASSOC UNION_COMM] >>
  qmatch_goalsub_abbrev_tac `BIGUNION A ∪ (BIGUNION B ∪ _ ∪ C) = C' ∪ _ ∪ _ ∪ _` >>
  qsuff_tac `C = C'` >> rw[] >- simp[AC UNION_ASSOC UNION_COMM] >>
  unabbrev_all_tac >> CASE_TAC >> simp[freecvars_pure_vars]
QED

Theorem msubst_vars_UNION:
  msubst_vars s (a ∪ b) = msubst_vars s a ∪ msubst_vars s b
Proof
  simp[msubst_vars_def]
QED

Theorem domain_activevars:
  ∀c. domain (activevars c) = mactivevars (to_mconstraint c)
Proof
  Cases >> rw[activevars_def, mactivevars_def] >>
  simp[domain_union, freecvars_pure_vars, domain_inter] >>
  Cases_on `p` >> rw[activevars_def, mactivevars_def] >>
  simp[domain_union, freecvars_pure_vars]
QED

Theorem is_solveable_mis_solveable:
  ∀c cs.
    is_solveable c cs ⇔ mis_solveable (to_mconstraint c) (set $ MAP to_mconstraint cs)
Proof
  Cases >> rw[is_solveable_def, mis_solveable_def] >>
  DEP_REWRITE_TAC[domain_empty] >> rw[] >- (irule wf_difference >> simp[]) >>
  simp[domain_difference, domain_inter, freecvars_pure_vars, SUBSET_DIFF_EMPTY] >>
  qmatch_goalsub_abbrev_tac `FOLDL _ imp _` >>
  qmatch_goalsub_abbrev_tac `mimp ∪ _` >>
  qsuff_tac `domain (FOLDL (λacc c. union (activevars c) acc) imp cs) =
    mimp ∪ (BIGUNION $ IMAGE mactivevars $ set $ MAP to_mconstraint cs)` >> simp[] >>
  Induct_on `cs` using SNOC_INDUCT >> rw[FOLDL_SNOC, MAP_SNOC]
  >- (unabbrev_all_tac >> gvs[domain_activevars]) >>
  simp[domain_union, domain_activevars, LIST_TO_SET_SNOC, AC UNION_ASSOC UNION_COMM]
QED

Theorem constraints_ok_UNION:
  constraints_ok ns (cs1 ∪ cs2) ⇔ constraints_ok ns cs1 ∧ constraints_ok ns cs2
Proof
  simp[constraints_ok_def] >> eq_tac >> rw[] >> metis_tac[]
QED

val inferM_ss = simpLib.named_rewrites "inferM_ss"
  [infer_bind_alt_def, infer_bind_def, infer_ignore_bind_def, fail_def,
   return_def, fresh_var_def, fresh_vars_def, oreturn_def];

val _ = simpLib.register_frag inferM_ss;

val inferM_rws = SF inferM_ss;

Triviality infer_ignore_bind_simps[simp]:
  (do _ <- ( λs. Err e) ; foo od = \s. Err e) ∧
  (do _ <- ( λs. OK ((),s)) ; foo od = foo)
Proof
  rw[FUN_EQ_THM, inferM_rws]
QED

fun print_tac s gs = (print (s ^ "\n"); ALL_TAC gs)

Theorem infer_minfer:
  ∀ns mset e n ty as cs m.
    infer ns mset e n = OK ((ty,as,cs),m) ∧
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
    print_tac "Var" >>
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
    print_tac "Tuple" >>
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
      simp[AC UNION_ASSOC UNION_COMM] >> metis_tac[wf_union, domain_union]
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
    print_tac "Ret" >>
    gvs[inferM_rws] >> Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[inferM_rws] >>
    every_case_tac >> gvs[] >>
    last_x_assum drule_all >> strip_tac >> simp[] >>
    goal_assum drule >> simp[Once minfer_cases] >>
    gvs[new_vars_def, pure_vars]
    )
  >- ( (* Bind *)
    print_tac "Bind" >>
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
    print_tac "Raise" >>
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
    print_tac "Handle" >>
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
    print_tac "Act" >>
    gvs[inferM_rws] >>
    Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >> every_case_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    goal_assum drule >> simp[Once minfer_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
    goal_assum $ drule_at Any >> simp[] >> rw[] >>
    gvs[new_vars_def, new_vars_constraint_def, pure_vars]
    )
  >- ( (* Alloc *)
    print_tac "Alloc" >>
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
    print_tac "Length" >>
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
    print_tac "Deref" >>
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
    print_tac "Update" >>
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
    qexists_tac `r''` >> rw[]
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
    print_tac "True" >>
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    simp[Once minfer_cases, new_vars_def, pure_vars, assumptions_rel_def]
    )
  >- ( (* False *)
    print_tac "False" >>
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    simp[Once minfer_cases, new_vars_def, pure_vars, assumptions_rel_def]
    )
  >- ( (* Cons and Exception *)
    print_tac "Cons/Exception" >>
    gvs[inferM_rws] >> every_case_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    every_case_tac >> gvs[]
    >- ( (* Exception *)
      print_tac "Exception" >>
      rename1 `_ = OK ((_,_,cs),_)` >>
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
        simp[monad_cns_def] >>
        gvs[new_vars_def, LIST_TO_SET_MAP, IMAGE_IMAGE,
            combinTheory.o_DEF, LAMBDA_PROD, pure_vars] >>
        simp[BIGUNION_SUBSET, PULL_EXISTS, GSYM implodeEQ,
             mlstringTheory.implode_def] >>
        gen_tac >> DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >> strip_tac >> gvs[] >>
        gvs[pure_vars_iFunctions, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS] >>
        first_x_assum irule >> simp[EL_MEM]
        ) >>
      qpat_x_assum `FOLDR _ _ _ _ = _` mp_tac >>
      ntac 3 $ pop_assum kall_tac >> pop_assum mp_tac >>
      ntac 12 $ last_x_assum kall_tac >>
      map_every qid_spec_tac [`m`,`n`,`tys`,`as`,`cs`] >>
      Induct_on `es` >> rw[] >> simp[]
      >- (
        qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
        simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
        ) >>
      every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
      rename1 `FOLDR _ _ _ _ = OK ((tysrest,asrest,csrest),r)` >>
      rename1 `infer _ _ _ _ = OK ((ty,as,cs),m)` >>
      last_x_assum drule >> strip_tac >> gvs[] >>
      last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
      disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
      strip_tac >> gvs[] >> goal_assum $ drule_at Any >>
      goal_assum $ rev_drule_at Any >>
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
      ) >>
    print_tac "Cons"
    >- (
      gvs[inferM_rws] >> rename1 `_ = OK ((_,_,cs),m)` >>
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
        simp[monad_cns_def] >> conj_tac
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
              MEM_MAP, EXISTS_PROD, MEM_GENLIST, FLOOKUP_DEF, MEM_ZIP] >>
          rw[GSYM implodeEQ, mlstringTheory.implode_def]
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
      ntac 12 $ last_x_assum kall_tac >>
      map_every qid_spec_tac [`m`,`n`,`tys`,`as`,`cs`] >>
      Induct_on `es` >> rw[] >> simp[]
      >- (
        qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
        simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
        ) >>
      every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
      rename1 `FOLDR _ _ _ _ = OK ((tysrest,asrest,csrest),r)` >>
      rename1 `infer _ _ _ _ = OK ((ty,as,cs),m)` >>
      last_x_assum drule >> strip_tac >> gvs[] >>
      last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
      disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
      strip_tac >> gvs[] >> goal_assum $ drule_at Any >>
      goal_assum $ rev_drule_at Any >>
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
      gvs[inferM_rws] >> rename1 `_ = OK ((_,_,cs),m)` >>
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
        simp[monad_cns_def] >>
        gvs[new_vars_def, pure_vars, LIST_TO_SET_MAP, IMAGE_IMAGE,
            combinTheory.o_DEF, BIGUNION_SUBSET, PULL_EXISTS, FORALL_PROD,
            MEM_ZIP, pure_vars_iFunctions] >>
        simp[GSYM implodeEQ, mlstringTheory.implode_def] >>
        rw[] >> first_x_assum irule >> simp[EL_MEM]
        ) >>
      qpat_x_assum `FOLDR _ _ _ _ = _` mp_tac >>
      ntac 3 $ pop_assum kall_tac >> pop_assum mp_tac >>
      ntac 12 $ last_x_assum kall_tac >>
      rename1 `FOLDR _ _ _ _ = OK (_,m)` >>
      map_every qid_spec_tac [`m`,`n`,`tys`,`as`,`cs`] >>
      Induct_on `es` >> rw[] >> simp[]
      >- (
        qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
        simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
        ) >>
      every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
      rename1 `FOLDR _ _ _ _ = OK ((tysrest,asrest,csrest),r)` >>
      rename1 `infer _ _ _ _ = OK ((ty,as,cs),m)` >>
      last_x_assum drule >> strip_tac >> gvs[] >>
      last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
      disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
      strip_tac >> gvs[] >> goal_assum $ drule_at Any >>
      goal_assum $ rev_drule_at Any >>
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
    print_tac "AtomOp" >>
    Cases_on `infer_atom_op (LENGTH es) aop` >> gvs[inferM_rws] >>
    pairarg_tac >> gvs[] >>
    every_case_tac >> gvs[] >> rename1 `FOLDR _ _ _ _ = OK ((tys,as,cs),m)` >>
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
      rw[] >> first_x_assum irule >> simp[EL_MEM]
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
    rename1 `FOLDR _ _ _ _ = OK ((tysrest,asrest,csrest),r)` >>
    rename1 `infer _ _ _ _ = OK ((ty,as,cs),m)` >>
    last_x_assum drule >> strip_tac >> gvs[] >>
    last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
    disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
    strip_tac >> gvs[] >> goal_assum $ drule_at Any >>
    goal_assum $ rev_drule_at Any >>
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
    print_tac "Seq" >>
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
  >- gvs[fail_def] (* Seq empty case *)
  >- gvs[fail_def] (* Seq singleton case *)
  >- gvs[fail_def] (* Seq too many args case *)
  >- gvs[fail_def] (* App empty case *)
  >- ( (* App non-empty case *)
    print_tac "App" >>
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    pairarg_tac >> gvs[] >> every_case_tac >> gvs[] >>
    rename [
      `FOLDR _ _ _ _ = OK ((tys,as,cs),m)`,
      `infer _ _ _ _ = OK ((ety,eas,ecs),l)`] >>
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
        >- (first_x_assum irule >> simp[EL_MEM])
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
    rename1 `FOLDR _ _ _ _ = OK ((tysrest,asrest,csrest),r)` >>
    rename1 `infer _ _ _ _ = OK ((ty,as,cs),m)` >>
    last_x_assum drule >> strip_tac >> gvs[] >>
    last_x_assum $ qspec_then `h` mp_tac >> simp[] >>
    disch_then drule >> impl_tac >- (rw[] >> first_x_assum drule >> rw[]) >>
    strip_tac >> gvs[] >> goal_assum $ drule_at Any >>
    goal_assum $ rev_drule_at Any >>
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
    print_tac "Lam" >>
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
      simp[LIST_TO_SET_MAP, LIST_TO_SET_FLAT, IMAGE_IMAGE, combinTheory.o_DEF] >>
      simp[AC UNION_ASSOC UNION_COMM] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
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
    >- simp[pure_vars, BIGUNION_SUBSET, PULL_EXISTS, MEM_GENLIST]
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
    print_tac "Let" >>
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
  >- gvs[inferM_rws] (* Letrec empty case *)
  >- ( (* Letrec non-empty case *)
    print_tac "Letrec" >>
    gvs[inferM_rws] >> every_case_tac >> gvs[] >>
    pairarg_tac >> gvs[] >> every_case_tac >> gvs[] >>
    rename [
      `FOLDR _ _ _ _ = OK ((tys,as,cs),m)`,
      `infer _ _ _ _ = OK ((ety,eas,ecs),l)`] >>
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
        simp[Once UNION_COMM] >> MK_COMB_TAC >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
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
        >- (first_x_assum irule >> simp[EL_MEM])
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
      >- (first_x_assum drule >> rw[SUBSET_DEF] >> first_x_assum drule >> simp[])
      >- (
        rename1 `fst,snd` >>
        gvs[get_assumptions_def, assumptions_rel_def] >> every_case_tac >> gvs[] >>
        gvs[miscTheory.toAList_domain] >>
        qpat_x_assum `lookup _ _ = _` mp_tac >> simp[aunion_def] >>
        DEP_REWRITE_TAC[lookup_unionWith] >> simp[] >>
        ntac 3 $ first_x_assum $ qspec_then `fst` assume_tac >>
        rw[] >> every_case_tac >> gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
        first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
        )
      >- (
        rename1 `fst,snd` >>
        gvs[get_assumptions_def, assumptions_rel_def] >> every_case_tac >> gvs[] >>
        gvs[miscTheory.toAList_domain] >>
        qpat_x_assum `lookup _ _ = _` mp_tac >> simp[aunion_def] >>
        DEP_REWRITE_TAC[lookup_unionWith] >> simp[] >>
        ntac 3 $ first_x_assum $ qspec_then `fst` assume_tac >>
        rw[] >> every_case_tac >> gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
        first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
        )
      >- (
        last_x_assum $ qspec_then `EL n' tys` mp_tac >> simp[EL_MEM, SUBSET_DEF] >>
        rw[] >> first_x_assum drule >> simp[]
        )
      >- (
        rename1 `fst,snd` >>
        gvs[get_assumptions_def, assumptions_rel_def] >> every_case_tac >> gvs[] >>
        gvs[miscTheory.toAList_domain] >>
        qpat_x_assum `lookup _ _ = _` mp_tac >> simp[aunion_def] >>
        DEP_REWRITE_TAC[lookup_unionWith] >> simp[] >>
        ntac 3 $ first_x_assum $ qspec_then `fst` assume_tac >>
        rw[] >> every_case_tac >> gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
        first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
        )
      >- (
        rename1 `fst,snd` >>
        gvs[get_assumptions_def, assumptions_rel_def] >> every_case_tac >> gvs[] >>
        gvs[miscTheory.toAList_domain] >>
        qpat_x_assum `lookup _ _ = _` mp_tac >> simp[aunion_def] >>
        DEP_REWRITE_TAC[lookup_unionWith] >> simp[] >>
        ntac 3 $ first_x_assum $ qspec_then `fst` assume_tac >>
        rw[] >> every_case_tac >> gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
        first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
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
    last_x_assum kall_tac >> last_x_assum mp_tac >> last_x_assum kall_tac >>
    rename1 `n ≤ m` >>
    map_every qid_spec_tac [`m`,`l`,`tys`,`as`,`cs`] >>
    Induct_on `fns` >> rw[] >> simp[]
    >- (
      qexistsl_tac [`[]`,`[]`] >> simp[assumptions_rel_def, iFunctions_def] >>
      simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
      ) >>
    every_case_tac >> gvs[PULL_EXISTS, EXISTS_PROD] >>
    pairarg_tac >> gvs[] >> every_case_tac >> gvs[] >> simp[PULL_EXISTS] >>
    rename1 `FOLDR _ _ _ _ = OK ((tysrest,asrest,csrest),r)` >>
    rename1 `infer _ _ _ _ = OK ((ty,as,cs),m)` >>
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
    print_tac "Case cases" >>
    Cases_on `css` >- gvs[inferM_rws] >>
    Cases_on `∃pvars rest. h::t = [(«»,pvars,rest)]`
    >- ( (* TupleCase *)
      print_tac "TupleCase" >>
      gvs[] >> gvs[inferM_rws, get_case_type_def] >>
      `eopt = NONE` by (
        every_case_tac >> gvs[] >> every_case_tac >> gvs[] >>
        gvs[DefnBase.one_line_ify NONE oreturn_def] >>
        every_case_tac >> gvs[inferM_rws] >>
        PairCases_on `ns` >> gvs[] >>
        drule_all get_typedef_SOME >> strip_tac >> gvs[] >>
        rename1 `oEL tyid _ = SOME (ar,cdefs)` >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >> strip_tac >> gvs[SF DNF_ss] >>
        qpat_x_assum `MEM _ _` mp_tac >> simp[MEM_MAP, FORALL_PROD] >> rw[] >>
        gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        qpat_x_assum `∀e. _ ⇒ ¬MEM _ (MAP _ (FLAT _))` $
          qspec_then `«»` mp_tac >>
        simp[Once MEM_MAP] >> simp[reserved_cns_def, implodeEQ] >>
        simp[MEM_MAP, MEM_FLAT, FORALL_PROD] >> simp[Once MEM_EL, PULL_FORALL] >>
        simp[DISJ_EQ_IMP] >> disch_then irule >> gvs[oEL_THM] >>
        goal_assum $ drule_at Any >> simp[]) >>
      gvs[] >> gvs[inferM_rws, get_case_type_def] >>
      every_case_tac >> gvs[] >>
      rename1 `infer _ _ _ _ = OK ((ety,eas,ecs),m)` >>
      rename1 `infer _ _ _ (_ + _) = OK ((tyrest,asrest,csrest),r)` >>
      last_x_assum drule >> impl_tac
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
      goal_assum $ drule_at Any >>
      qexistsl_tac [
        `mas`, `IMAGE to_mconstraint (set csrest)`,`n`,
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
      >- (gvs[SUBSET_DEF, PULL_EXISTS] >> rw[] >> first_x_assum drule_all >> simp[])
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
      ) >>
    qpat_abbrev_tac `cases = h::t` >>
    qmatch_asmsub_abbrev_tac `list_CASE _ _ (λv1 v2. foo)` >>
    `foo n = OK ((ty,as,cs),m)` by (PairCases_on `h` >> gvs[Abbr `cases`] >>
      Cases_on `h0` >> gvs[] >> Cases_on `t` >> gvs[]) >>
    qpat_x_assum `(list_CASE _ _ _) _ = _` kall_tac >> gvs[Abbr `foo`] >>
    `∀n' ty' as' cs' m'.
      infer ns mset e n' = OK ((ty',as',cs'),m') ∧
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
          OK ((ty',as',cs'),m') ∧
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
    `∀us_cn_ars rest. eopt = SOME (us_cn_ars, rest) ⇒
      ∀fresh_v fresh_tyargs n' ty' as' cs' m'.
        infer ns (list_insert (fresh_v::fresh_tyargs) mset) rest n' =
        OK ((ty',as',cs'),m') ∧
        (∀mvar.
           mvar ∈ domain (list_insert (fresh_v::fresh_tyargs) mset) ⇒
           mvar < n') ⇒
        ∃mas.
          assumptions_rel as' mas ∧
          minfer ns (domain (list_insert (fresh_v::fresh_tyargs) mset))
            rest mas (set (MAP to_mconstraint cs')) ty' ∧ n' ≤ m' ∧
          new_vars mas (set (MAP to_mconstraint cs')) ty' ⊆
          {v | n' ≤ v ∧ v < m'}` by (
        Cases_on `eopt` >> gvs[] >>
        unabbrev_all_tac >> PairCases_on `h` >> gvs[]) >>
    last_x_assum assume_tac >> ntac 3 $ last_x_assum kall_tac >>
    qpat_x_assum `_ = OK _` assume_tac >> gvs[inferM_rws] >>
    gvs[get_case_type_def] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
    >- (PairCases_on `h` >> gvs[]) >>
    IF_CASES_TAC >> gvs[]
    >- ( (* Bool case *)
      print_tac "BoolCase" >> strip_tac >>
      `eopt = NONE` by (
        Cases_on `eopt` >> gvs[] >> PairCases_on `x` >> gvs[inferM_rws] >>
        every_case_tac >> gvs[] >> every_case_tac >> gvs[] >> pop_assum kall_tac >>
        gvs[DefnBase.one_line_ify NONE oreturn_def] >>
        every_case_tac >> gvs[inferM_rws] >>
        PairCases_on `ns` >> gvs[] >>
        drule_all get_typedef_SOME >> strip_tac >> gvs[] >>
        rename1 `oEL tyid _ = SOME (ar,cdefs)` >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        disch_then $ qspec_then `«True»,0` assume_tac >> gvs[] >>
        qpat_x_assum `MEM _ _` mp_tac >> simp[MEM_MAP, FORALL_PROD] >> rw[] >>
        gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        qpat_x_assum `∀e. _ ⇒ ¬MEM _ (MAP _ (FLAT _))` $
          qspec_then `«True»` mp_tac >>
        simp[Once MEM_MAP] >> simp[reserved_cns_def, implodeEQ] >>
        simp[MEM_MAP, MEM_FLAT, FORALL_PROD] >> simp[Once MEM_EL, PULL_FORALL] >>
        simp[DISJ_EQ_IMP] >> disch_then irule >> gvs[oEL_THM] >>
        goal_assum $ drule_at Any >> simp[]) >>
      gvs[inferM_rws] >>
      `∃c1 e1 c2 e2. cases = [(c1,[],e1);(c2,[],e2)]` by (
        gvs[LENGTH_EQ_NUM_compute] >>
        PairCases_on `h` >> PairCases_on `h''` >> gvs[]) >>
      gvs[inferM_rws, AllCaseEqs()] >>
      (
        qmatch_goalsub_abbrev_tac `[(cn1,_,_);(cn2,_,_)]` >>
        `{cn1;cn2} = {cn2;cn1}` by (rw[EXTENSION] >> eq_tac >> rw[]) >>
        rename1 `infer _ _ e2 _ = OK ((ty2,as2,cs2),n2)` >>
        rename1 `infer _ _ e1 _ = OK ((ty1,as1,cs1),n1)` >>
        rename1 `infer _ _ e _ = OK ((tye,ase,cse),ne)` >>
        gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
        first_x_assum drule >> impl_tac
        >- (
          rw[list_insert_def, domain_insert] >> simp[] >>
          last_x_assum drule >> rw[]
          ) >>
        strip_tac >> gvs[] >> first_x_assum drule >> impl_tac
        >- (
          rw[list_insert_def, domain_insert] >> simp[] >>
          last_x_assum drule >> rw[]
          ) >>
        strip_tac >> gvs[] >> first_x_assum drule >> impl_tac
        >- (rw[] >> last_x_assum drule >> rw[]) >>
        strip_tac >> gvs[] >>
        simp[Once minfer_cases] >> irule_at Any OR_INTRO_THM1 >>
        simp[PULL_EXISTS] >> goal_assum $ drule_at Any >>
        gvs[domain_list_insert_alt, GSYM INSERT_SING_UNION] >>
        ntac 2 (goal_assum $ drule_at Any) >> rw[] >> gvs[LIST_TO_SET_MAP]
        >- (
          simp[AC UNION_ASSOC UNION_COMM] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
          imp_res_tac LIST_TO_SET_get_assumptions >> simp[] >>
          simp[IMAGE_IMAGE, combinTheory.o_DEF, AC UNION_ASSOC UNION_COMM]
          )
        >- (
          gvs[cvars_disjoint_def, list_disjoint_def] >>
          simp[APPEND_EQ_CONS] >> rw[] >> gvs[] >>
          irule_at Any SUBSET_DISJOINT >> ntac 2 $ goal_assum $ drule_at Any >>
          simp[DISJOINT_ALT]
          )
        >- (CCONTR_TAC >> gvs[] >> first_x_assum drule >> simp[])
        >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
        >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
        >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule >> simp[])
        >- (
          gvs[assumptions_rel_def, aunion_def] >> simp[PULL_FORALL] >> rpt gen_tac >>
          DEP_REWRITE_TAC[lookup_unionWith, lookup_list_delete] >>
          DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >>
          DEP_REWRITE_TAC[cj 1 map_ok_list_delete, cj 2 map_ok_list_delete] >>
          simp[maunion_def, FLOOKUP_FMERGE, DOMSUB_FLOOKUP_THM] >>
          rpt (IF_CASES_TAC >> gvs[]) >>
          rw[] >> every_case_tac >> gvs[] >> metis_tac[domain_union, wf_union]
          ) >>
        gvs[new_vars_def, BIGUNION_FRANGE_maunion, GSYM CONJ_ASSOC,
            pure_vars, MAP_MAP_o, combinTheory.o_DEF, MAP_GENLIST,
            LIST_TO_SET_GENLIST, IMAGE_IMAGE, GSYM INSERT_SING_UNION,
            IMAGE_BIGUNION, LAMBDA_PROD] >> rw[]
        >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
        >- (
          gvs[BIGUNION_SUBSET] >> rw[] >>
          drule $ SIMP_RULE std_ss [SUBSET_DEF] FRANGE_DOMSUB_SUBSET >>
          pop_assum kall_tac >> strip_tac >>
          gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_maunion] >>
          every_case_tac >> gvs[] >> res_tac >>
          gvs[SUBSET_DEF] >> rw[] >> res_tac >> simp[]
          )
        >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
        >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
        >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
        >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
        >- (gvs[SUBSET_DEF, PULL_EXISTS] >> rw[] >> first_x_assum drule_all >> simp[])
        >- (
          gvs[BIGUNION_SUBSET, IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
          gvs[get_assumptions_def, assumptions_rel_def, PULL_EXISTS] >>
          gen_tac >> strip_tac >> every_case_tac >> gvs[] >>
          gvs[miscTheory.toAList_domain] >>
          first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
          )
        >- (
          gvs[BIGUNION_SUBSET, PULL_EXISTS, SUBSET_DEF] >> rw[] >>
          first_x_assum drule_all >> simp[]
          )
        >- (
          gvs[BIGUNION_SUBSET, IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
          gvs[get_assumptions_def, assumptions_rel_def, PULL_EXISTS] >>
          gen_tac >> strip_tac >> every_case_tac >> gvs[] >>
          gvs[miscTheory.toAList_domain] >>
          first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
          )
        >- (
          gvs[BIGUNION_SUBSET, PULL_EXISTS, SUBSET_DEF] >> rw[] >>
          first_x_assum drule_all >> simp[]
          )
        >- (rename1 `foo ⊆ _` >> gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[])
        )
      ) >>
    IF_CASES_TAC >> gvs[]
    >- ( (* Exception case *)
      print_tac "ExceptionCase" >> strip_tac >>
      `eopt = NONE` by (
        Cases_on `eopt` >> gvs[] >> PairCases_on `x` >> gvs[inferM_rws] >>
        every_case_tac >> gvs[] >> every_case_tac >> gvs[] >> pop_assum kall_tac >>
        gvs[DefnBase.one_line_ify NONE oreturn_def] >>
        every_case_tac >> gvs[inferM_rws] >>
        PairCases_on `ns` >> gvs[] >>
        drule_all get_typedef_SOME >> strip_tac >> gvs[] >>
        rename1 `oEL tyid _ = SOME (ar,cdefs)` >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        disch_then $ qspec_then `«Subscript»,0` mp_tac >> simp[] >> conj_tac
        >- (
          disj1_tac >> gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD, FORALL_PROD] >>
          first_x_assum $ qspecl_then [`«Subscript»`,`[]`] mp_tac >>
          gvs[namespace_ok_def]
          ) >>
        simp[MEM_MAP, FORALL_PROD] >> rw[] >>
        gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        qpat_x_assum `∀e. _ ⇒ ¬MEM _ (MAP _ (FLAT _))` $
          qspec_then `«Subscript»` mp_tac >> impl_tac
        >- (
          disj2_tac >> simp[MEM_MAP, EXISTS_PROD] >> gvs[namespace_ok_def, SF SFY_ss]
          ) >>
        simp[MEM_MAP, MEM_FLAT, FORALL_PROD] >> simp[Once MEM_EL, PULL_FORALL] >>
        simp[DISJ_EQ_IMP] >> disch_then irule >> gvs[oEL_THM] >>
        goal_assum $ drule_at Any >> simp[]) >>
      gvs[inferM_rws] >> every_case_tac >> gvs[] >>
      gvs[COND_RAND, COND_RATOR, inferM_rws] >>
      qmatch_asmsub_abbrev_tac `FOLDR f` >>
      rename [
        `infer _ _ _ _ = OK ((ety,eas,ecs),m)`,
        `FOLDR _ _ _ _ = OK ((tyrest,asrest,csrest),l)`] >>
      `ALL_DISTINCT (MAP FST (FST ns))` by (
        PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND]) >>
      `PERM (MAP (λ(cn,ts). (cn,LENGTH ts)) (FST ns))
        (MAP (λ(cn,pvars,rest). (cn,LENGTH pvars)) cases)` by (
        irule PERM_ALL_DISTINCT_LENGTH >>
        PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND, EVERY_MEM] >>
        gvs[MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >> rw[] >> simp[SF SFY_ss] >>
        irule ALL_DISTINCT_MAP_INJ >> imp_res_tac ALL_DISTINCT_MAP >> gvs[] >>
        simp[FORALL_PROD] >> rw[] >> qpat_x_assum `ALL_DISTINCT (_ ns0)` mp_tac >>
        simp[EL_ALL_DISTINCT_EL_EQ, MEM_EL, EL_MAP] >> gvs[MEM_EL] >>
        ntac 2 (disch_then dxrule) >>
        ntac 2 $ qpat_x_assum `_ = EL _ _` $ assume_tac o GSYM >> rw[] >> gvs[]) >>
      `EVERY (λ(cn,pvs,_).
        MEM (cn, LENGTH pvs) (MAP (λ(cn,ts). (cn, LENGTH ts)) (FST ns))) cases` by (
        rw[EVERY_MEM] >> pairarg_tac >> simp[] >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> rw[] >>
        first_x_assum drule >> rw[] >> gvs[]) >>
      qsuff_tac
        `∃ass css final_as final_cs.
          LIST_REL (λ((cname,pvars,rest),ty) (a,c).
            minfer ns (n INSERT domain mset) rest a c ty)
            (ZIP (cases,tyrest)) (ZIP (ass,css)) ∧
          EVERY (λ(cn,pvars,rest). ALL_DISTINCT pvars) cases ∧
          LIST_REL
           (λ((cn,pvars,rest),as,cs) (as',cs').
                ∃schemes.
                  ALOOKUP (FST ns) cn = SOME schemes ∧
                  (let pvar_cs =
                    MAP2 (λv t. IMAGE (λn. mUnify (CVar n) t) (get_massumptions as v))
                      (v::pvars) (CVar n:: MAP itype_of schemes)
                   in
                     as' = FDIFF as (v INSERT set pvars) ∧
                     cs' = BIGUNION (set pvar_cs) ∪ cs))
           (ZIP (cases,ZIP (ass,css))) (ZIP (final_as,final_cs)) ∧
          assumptions_rel asrest (FOLDR maunion FEMPTY final_as) ∧
          BIGUNION (set final_cs) = set (MAP to_mconstraint csrest) ∧
          cvars_disjoint (ZIP (ass, ZIP (css, tyrest))) ∧
          new_vars (FOLDR maunion FEMPTY ass)
            (BIGUNION (set css)) (iFunctions tyrest Exception) ⊆
              {v | SUC n ≤ v ∧ v < l} ∧
          LENGTH cases = LENGTH tyrest ∧ LENGTH ass = LENGTH css ∧
          LENGTH final_as = LENGTH final_cs ∧ SUC n ≤ l`
      >- (
        rw[] >> gvs[] >>
        last_x_assum drule >> impl_tac >- (rw[] >> first_x_assum drule >> simp[]) >>
        strip_tac >> gvs[] >>
        simp[Once minfer_cases] >>
        irule_at Any $ OR_INTRO_THM2 >>
        irule_at Any $ OR_INTRO_THM1 >>
        simp[PULL_EXISTS, GSYM CONJ_ASSOC] >>
        goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
        gvs[domain_list_insert_alt, INSERT_UNION_EQ] >>
        goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
        rpt $ goal_assum $ drule_at Any >> simp[SF ETA_ss, combinTheory.o_DEF] >>
        gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, new_vars_def,
            LIST_TO_SET_MAP, IMAGE_IMAGE, pure_vars, pure_vars_iFunctions,
            BIGUNION_SUBSET, PULL_EXISTS, MEM_GENLIST, EXISTS_PROD] >>
        rw[SF ETA_ss]
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
            disch_then $ drule_at Any >> simp[EL_MEM] >>
            disch_then drule >> simp[]
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
          last_x_assum drule >> simp[]
          )
        >- (
          gvs[SUBSET_DEF] >> gen_tac >> strip_tac >>
          Cases_on `tyrest` >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
          first_x_assum drule_all >> simp[]
          )
        >- (gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule_all >> simp[])
        >- (
          qpat_x_assum `EVERY _ cases` kall_tac >>
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
            DEP_REWRITE_TAC[MAP2_MAP] >> simp[] >> conj_asm1_tac
            >- (
              qpat_x_assum `EVERY _ cases` mp_tac >> simp[EVERY_EL] >>
              disch_then drule >> simp[] >> strip_tac >> gvs[] >>
              drule_all ALOOKUP_ALL_DISTINCT_MEM >> strip_tac >> gvs[]
              ) >>
            simp[MEM_MAP, EXISTS_PROD, MEM_ZIP, PULL_EXISTS] >> rw[] >>
            gvs[pure_vars, EL_MAP] >>
            qpat_x_assum `_ ∈ get_massumptions _ _` mp_tac >>
            simp[get_massumptions_def] >> CASE_TAC >> gvs[] >> strip_tac >>
            gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, PULL_EXISTS,
                BIGUNION_SUBSET, FLOOKUP_DEF] >>
            first_x_assum $ drule_at Any >> disch_then $ drule_at Any >>
            simp[EL_MEM, SUBSET_DEF] >> disch_then drule >> simp[]
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
      qpat_x_assum `PERM _ _` kall_tac >>
      qpat_x_assum `infer _ _ _ _ = _` kall_tac >>
      `∀mvar. mvar ∈ domain mset ⇒ mvar < SUC n` by (
        rw[] >> last_x_assum drule >> simp[]) >>
      last_x_assum assume_tac >>
      ntac 4 $ last_x_assum kall_tac >>
      ntac 6 $ pop_assum mp_tac >> ntac 5 $ pop_assum kall_tac >>
      rpt $ pop_assum mp_tac >>
      map_every qid_spec_tac [`n`,`l`,`tyrest`,`asrest`,`csrest`] >>
      Induct_on `cases` >> rw[] >> simp[]
      >- (
        qexistsl_tac [`[]`,`[]`,`[]`,`[]`] >>
        simp[assumptions_rel_def, iFunctions_def] >>
        simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
        ) >>
      gvs[Abbr `f`] >> pairarg_tac >> gvs[] >>
      reverse $ Cases_on `ALL_DISTINCT pvars` >> gvs[inferM_rws] >>
      qpat_x_assum `_ = OK ((_,_,_),_)` mp_tac >> rpt (TOP_CASE_TAC >> gvs[]) >>
      pairarg_tac >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[]) >>
      strip_tac >> gvs[inferM_rws, PULL_EXISTS, EXISTS_PROD] >>
      qmatch_asmsub_abbrev_tac `FOLDR f` >>
      rename1 `FOLDR _ _ _ _ = OK ((tysrest,asrest,csrest),r)` >>
      rename1 `infer _ _ _ _ = OK ((ty,as,cs),m)` >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      last_x_assum drule >> disch_then drule >> simp[] >>
      strip_tac >> gvs[] >>
      first_x_assum drule >> impl_tac
      >- (
        rw[domain_list_insert, MEM_GENLIST] >> gvs[] >>
        first_x_assum drule >> simp[]
        ) >>
      strip_tac >> gvs[] >>
      gvs[domain_list_insert_alt, GSYM CONJ_ASSOC, INSERT_UNION_EQ] >>
      goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
      goal_assum $ drule_at $ Pat `minfer _ _ _ _ _` >>
      qexistsl_tac [`mas::ass`,`set (MAP to_mconstraint cs) :: css`] >> simp[] >>
      simp[PULL_EXISTS, GSYM CONJ_ASSOC, EXISTS_PROD] >>
      goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
      gvs[ALOOKUP_MAP] >> Cases_on `ALOOKUP (FST ns) cn` >> gvs[inferM_rws] >> rw[] >>
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
        qexists_tac `{v | SUC n ≤ v ∧ v < r}` >>
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
      ) >>
    print_tac "DataCase" >>
    ntac 3 $ pop_assum kall_tac >> strip_tac >>
    Cases_on `eopt` >> gvs[inferM_rws, COND_RATOR, COND_RAND]
    >- (
      print_tac "Case case - exhaustive" >>
      every_case_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `oreturn _ foo` >>
      Cases_on `foo` >> gvs[inferM_rws] >> rename1 `SOME (tyid,ar,cdefs)` >>
      gvs[inferM_rws] >> every_case_tac >> gvs[] >>
      gvs[ALOOKUP_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
      qmatch_asmsub_abbrev_tac `FOLDR f` >>
      rename [
        `infer _ _ _ _ = OK ((ety,eas,ecs),m)`,
        `FOLDR _ _ _ _ = OK ((tyrest,asrest,csrest),l)`] >>
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
      `∃ass css final_as final_cs.
      LIST_REL (λ((cname,pvars,rest),ty) (a,c).
        minfer ns (n INSERT set (GENLIST (λn'. n' + SUC n) ar) ∪ domain mset)
          rest a c ty)
        (ZIP (cases,tyrest)) (ZIP (ass,css)) ∧
      EVERY (λ(cn,pvars,rest). ALL_DISTINCT pvars) cases ∧
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
      LENGTH final_as = LENGTH final_cs ∧ ar + SUC n ≤ l` by (
      qpat_x_assum `get_typedef _ _ _ = _` kall_tac >>
      qpat_x_assum `PERM _ _` kall_tac >>
      rpt $ qpat_x_assum `infer _ _ _ _ = _` kall_tac >>
      `∀mvar. mvar ∈ domain mset ⇒ mvar < ar + SUC n` by (
        rw[] >> last_x_assum drule >> simp[]) >>
      last_x_assum assume_tac >>
      ntac 4 $ last_x_assum kall_tac >>
      rpt $ pop_assum mp_tac >>
      map_every qid_spec_tac [`n`,`l`,`tyrest`,`asrest`,`csrest`] >>
      Induct_on `cases` >> rw[] >> simp[]
      >- (
        qexistsl_tac [`[]`,`[]`,`[]`,`[]`] >>
        simp[assumptions_rel_def, iFunctions_def] >>
        simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
        ) >>
      gvs[Abbr `f`] >> pairarg_tac >> gvs[] >>
      reverse $ Cases_on `ALL_DISTINCT pvars` >> gvs[inferM_rws] >>
      qpat_x_assum `_ = OK ((_,_,_),_)` mp_tac >> rpt (TOP_CASE_TAC >> gvs[]) >>
      pairarg_tac >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[]) >>
      strip_tac >> gvs[inferM_rws, PULL_EXISTS, EXISTS_PROD] >>
      qmatch_asmsub_abbrev_tac `FOLDR f` >>
      rename1 `FOLDR _ _ _ _ = OK ((tysrest,asrest,csrest),rm)` >>
      rename1 `infer _ _ _ _ = OK ((ty,as,cs),mm)` >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      last_x_assum drule >> disch_then drule >> simp[] >>
      strip_tac >> gvs[] >>
      first_x_assum drule >> impl_tac
      >- (
        rw[domain_list_insert, MEM_GENLIST] >> gvs[] >>
        first_x_assum drule >> simp[]
        ) >>
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
        qexists_tac `{v | ar + SUC n ≤ v ∧ v < rm}` >>
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
      ) >>
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
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF] >>
          first_x_assum $ rev_drule_at Any >> simp[]
          )
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
          first_x_assum $ rev_drule_at Any >> disch_then $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          CCONTR_TAC >> gvs[] >>
          first_x_assum $ rev_drule_at Any >> disch_then $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF] >>
          first_x_assum $ rev_drule_at Any >> simp[EL_MEM]
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
          disch_then $ drule_at Any >> simp[EL_MEM] >>
          disch_then drule >> simp[]
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
        last_x_assum drule >> simp[]
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
          gvs[EVERY_EL] >> last_x_assum drule >> simp[] >> strip_tac >> gvs[EL_MAP] >>
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
      )
    >- (
      print_tac "Case case - NON-exhaustive" >>
      PairCases_on `x` >> rename1 `us_cn_ars,usrest` >> gvs[] >>
      every_case_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `oreturn _ foo` >>
      Cases_on `foo` >> gvs[inferM_rws] >> rename1 `SOME (tyid,ar,cdefs)` >>
      gvs[inferM_rws] >> every_case_tac >> gvs[] >>
      gvs[ALOOKUP_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
      qmatch_asmsub_abbrev_tac `FOLDR f` >>
      rename [
        `infer _ _ _ _ = OK ((ety,eas,ecs),m)`,
        `FOLDR _ _ _ _ = OK ((tyrest,asrest,csrest),l)`] >>
      drule get_typedef_SOME >>
      disch_then $ qspec_then `FST ns` assume_tac >> gvs[] >>
      `EVERY (λ(cn,pvs,_).
        MEM (cn, LENGTH pvs) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)) cases` by (
        rw[EVERY_MEM] >> pairarg_tac >> simp[] >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        simp[SF DNF_ss, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >> rw[] >>
        pop_assum kall_tac >> first_x_assum drule >> simp[]) >>
      `ALL_DISTINCT (MAP FST cdefs)` by (
        qpat_x_assum `namespace_ok _` assume_tac >> PairCases_on `ns` >>
        gvs[namespace_ok_def] >> gvs[ALL_DISTINCT_APPEND, MAP_FLAT] >>
        drule miscTheory.ALL_DISTINCT_FLAT_EVERY >>
        simp[EVERY_EL, EL_MAP] >> gvs[oEL_THM] >>
        disch_then drule >> simp[]) >>
      `∃ass css final_as final_cs.
      LIST_REL (λ((cname,pvars,rest),ty) (a,c).
        minfer ns (n INSERT set (GENLIST (λn'. n' + SUC n) ar) ∪ domain mset)
          rest a c ty)
        (ZIP (cases,tyrest)) (ZIP (ass,css)) ∧
      EVERY (λ(cn,pvars,rest). ALL_DISTINCT pvars) cases ∧
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
      LENGTH final_as = LENGTH final_cs ∧ ar + SUC n ≤ l` by (
      qpat_x_assum `get_typedef _ _ _ = _` kall_tac >>
      qpat_x_assum `PERM _ _` kall_tac >>
      rpt $ qpat_x_assum `infer _ _ _ _ = _` kall_tac >>
      `∀mvar. mvar ∈ domain mset ⇒ mvar < ar + SUC n` by (
        rw[] >> last_x_assum drule >> simp[]) >>
      last_x_assum assume_tac >>
      ntac 4 $ last_x_assum kall_tac >>
      rpt $ pop_assum mp_tac >>
      map_every qid_spec_tac [`n`,`l`,`tyrest`,`asrest`,`csrest`] >>
      Induct_on `cases` >> rw[] >> simp[]
      >- (
        qexistsl_tac [`[]`,`[]`,`[]`,`[]`] >>
        simp[assumptions_rel_def, iFunctions_def] >>
        simp[cvars_disjoint_def, new_vars_def, list_disjoint_def, pure_vars]
        ) >>
      gvs[Abbr `f`] >> pairarg_tac >> gvs[] >>
      reverse $ Cases_on `ALL_DISTINCT pvars` >> gvs[inferM_rws] >>
      qpat_x_assum `_ = OK ((_,_,_),_)` mp_tac >> rpt (TOP_CASE_TAC >> gvs[]) >>
      pairarg_tac >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[]) >>
      strip_tac >> gvs[inferM_rws, PULL_EXISTS, EXISTS_PROD] >>
      qmatch_asmsub_abbrev_tac `FOLDR f` >>
      rename1 `FOLDR _ _ _ _ = OK ((tysrest,asrest,csrest),rm)` >>
      rename1 `infer _ _ _ _ = OK ((ty,as,cs),mm)` >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      last_x_assum drule >> disch_then drule >> simp[] >>
      strip_tac >> gvs[] >>
      first_x_assum drule >> impl_tac
      >- (
        rw[domain_list_insert, MEM_GENLIST] >> gvs[] >>
        first_x_assum drule >> simp[]
        ) >>
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
        qexists_tac `{v | ar + SUC n ≤ v ∧ v < rm}` >>
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
      ) >>
      rename1 `infer _ _ usrest m = OK ((usty,usas,uscs),k)` >>
      rw[] >> gvs[] >>
      last_x_assum drule >> impl_tac >- (rw[] >> last_x_assum drule >> simp[]) >>
      strip_tac >> gvs[] >>
      last_x_assum drule >> impl_tac
      >- (
        simp[domain_list_insert, MEM_GENLIST] >> rw[] >> gvs[] >>
        last_x_assum drule >> simp[]
        ) >>
      strip_tac >> gvs[] >>
      simp[Once minfer_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
      gvs[domain_list_insert_alt, INSERT_UNION_EQ] >>
      goal_assum $ drule_at $ Pat `LIST_REL _ _ _` >>
      rpt $ goal_assum $ drule_at Any >> simp[SF ETA_ss, combinTheory.o_DEF] >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, new_vars_def,
          LIST_TO_SET_MAP, IMAGE_IMAGE, pure_vars, pure_vars_iFunctions,
          BIGUNION_SUBSET, PULL_EXISTS, MEM_GENLIST, EXISTS_PROD] >>
      rw[]
      >- (
        gvs[assumptions_rel_def, aunion_def] >> simp[PULL_FORALL] >> rpt gen_tac >>
        DEP_REWRITE_TAC[lookup_unionWith, lookup_delete] >>
        DEP_REWRITE_TAC[cj 1 unionWith_thm, cj 2 unionWith_thm] >> simp[] >>
        DEP_REWRITE_TAC[cj 1 delete_thm, cj 2 delete_thm] >> simp[] >>
        simp[maunion_def, FLOOKUP_FMERGE, DOMSUB_FLOOKUP_THM] >>
        simp[GSYM maunion_def] >>
        rw[] >> every_case_tac >> gvs[] >> metis_tac[wf_union, domain_union]
        )
      >- (
        simp[AC UNION_ASSOC UNION_COMM] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        imp_res_tac LIST_TO_SET_get_assumptions >> simp[]
        )
      >- (unabbrev_all_tac >> gvs[])
      >- (Cases_on `us_cn_ars` >> gvs[])
      >- (
        gvs[cvars_disjoint_def] >>
        once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
        once_rewrite_tac[CONS_APPEND] >> rewrite_tac[list_disjoint_append] >>
        simp[list_disjoint_def, MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> conj_tac
        >- (
          rpt gen_tac >>
          DEP_REWRITE_TAC[MEM_ZIP] >> DEP_REWRITE_TAC[cj 1 LENGTH_ZIP] >> simp[] >>
          imp_res_tac LIST_REL_LENGTH >> gvs[] >> simp[PULL_EXISTS] >> rw[] >>
          pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >> strip_tac >> gvs[] >>
          irule SUBSET_DISJOINT >>
          qexistsl_tac [`{v | m ≤ v ∧ v < k}`,`{v | n ≤ v ∧ v < l}`] >>
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
          ) >>
        rw[]
        >- (
          irule SUBSET_DISJOINT >>
          qexistsl_tac [`{v | l ≤ v ∧ v < m}`,`{v | m ≤ v ∧ v < k}`] >>
          conj_tac >- rw[DISJOINT_ALT] >> gvs[] >>
          simp[new_vars_def, BIGUNION_SUBSET, IMAGE_IMAGE, PULL_EXISTS] >> rw[]
          )
        >- (
          pop_assum mp_tac >>
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
        )
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule_all >> simp[])
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule_all >> simp[])
      >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum drule_all >> simp[])
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
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF] >>
          first_x_assum $ rev_drule_at Any >> simp[]
          )
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF, PULL_FORALL] >>
          first_x_assum drule_all >> simp[]
          )
        >- (CCONTR_TAC >> gvs[SUBSET_DEF] >> first_x_assum $ drule_at Any >> simp[])
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF] >>
          first_x_assum $ rev_drule_at Any >> simp[]
          )
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF] >>
          first_x_assum $ rev_drule_at Any >> simp[]
          )
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF] >>
          first_x_assum $ rev_drule_at Any >> simp[]
          ) >>
        rpt gen_tac >> DEP_REWRITE_TAC[MEM_ZIP] >> simp[] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> strip_tac >> gvs[] >>
        pop_assum mp_tac >> DEP_REWRITE_TAC[EL_ZIP] >> simp[] >>
        strip_tac >> gvs[SUBSET_DEF, PULL_FORALL, GSYM CONJ_ASSOC, AND_IMP_INTRO] >>
        rw[]
        >- (
          CCONTR_TAC >> gvs[] >>
          first_x_assum $ rev_drule_at Any >> disch_then $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          CCONTR_TAC >> gvs[] >>
          first_x_assum $ rev_drule_at Any >> disch_then $ drule_at Any >> simp[EL_MEM]
          )
        >- (
          CCONTR_TAC >> gvs[SUBSET_DEF] >>
          first_x_assum $ rev_drule_at Any >> simp[EL_MEM]
          )
        )
      >- (
        gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, BIGUNION_SUBSET] >>
        pop_assum mp_tac >> simp[maunion_def] >>
        simp[FLOOKUP_FMERGE, DOMSUB_FLOOKUP_THM] >> simp[GSYM maunion_def] >>
        rw[] >> every_case_tac >> gvs[SUBSET_DEF, PULL_FORALL]
        >- (first_x_assum drule >> rw[] >> first_x_assum drule >> simp[])
        >- (
          gen_tac >> strip_tac >> gvs[FLOOKUP_FOLDR_maunion] >>
          qpat_x_assum `MEM _ _` mp_tac >> simp[MEM_EL] >> strip_tac >>
          gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[EL_ZIP] >>
          pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
          gvs[FLOOKUP_FDIFF, PULL_EXISTS, FLOOKUP_DEF, GSYM CONJ_ASSOC]
          )
        >- (
          rpt gen_tac >> first_x_assum drule >> strip_tac >> conj_tac
          >- (strip_tac >> first_x_assum drule >> simp[]) >>
          gvs[FLOOKUP_FOLDR_maunion] >> strip_tac >> gvs[] >>
          qpat_x_assum `MEM _ _` mp_tac >> simp[MEM_EL] >> strip_tac >>
          gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[EL_ZIP] >>
          pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
          gvs[FLOOKUP_FDIFF, PULL_EXISTS, FLOOKUP_DEF, GSYM CONJ_ASSOC]
          )
        >- (first_x_assum drule >> rw[] >> first_x_assum drule >> simp[])
        >- (first_x_assum drule >> rw[] >> first_x_assum drule >> simp[])
        >- (
          first_x_assum drule >> rw[] >> first_x_assum drule >> simp[] >>
          disch_then drule >> simp[]
          )
        >- (
          gen_tac >> strip_tac >> gvs[FLOOKUP_FOLDR_maunion] >>
          qpat_x_assum `MEM _ _` mp_tac >> simp[MEM_EL] >> strip_tac >>
          gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[EL_ZIP] >>
          pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
          gvs[FLOOKUP_FDIFF, PULL_EXISTS, FLOOKUP_DEF, GSYM CONJ_ASSOC] >>
          first_x_assum $ drule_at Any >> simp[EL_MEM] >>
          disch_then $ drule_at Any >> simp[EL_MEM] >>
          disch_then drule >> simp[]
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
        >- (
          rpt gen_tac >> ntac 2 (first_x_assum drule >> strip_tac) >>
          conj_tac >- (strip_tac >> first_x_assum drule >> simp[]) >>
          conj_tac >- (strip_tac >> first_x_assum drule >> simp[]) >>
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
      >- (gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule >> simp[])
      >- (
        gvs[SUBSET_DEF] >> gen_tac >> strip_tac >>
        Cases_on `tyrest` >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
        last_x_assum drule >> simp[] >>
        disch_then drule >> strip_tac >> simp[]
        )
      >- (
        gvs[SUBSET_DEF] >> gen_tac >> strip_tac >>
        Cases_on `tyrest` >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
        first_x_assum drule_all >> simp[]
        )
      >- (
        gvs[IN_FRANGE_FLOOKUP, get_assumptions_def, assumptions_rel_def, PULL_EXISTS] >>
        every_case_tac >> gvs[miscTheory.toAList_domain] >>
        first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
        )
      >- (
        gvs[IN_FRANGE_FLOOKUP, get_assumptions_def, assumptions_rel_def, PULL_EXISTS] >>
        every_case_tac >> gvs[miscTheory.toAList_domain] >>
        first_x_assum drule >> simp[SUBSET_DEF] >> disch_then drule >> simp[]
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
          gvs[EVERY_EL] >> last_x_assum drule >> simp[] >> strip_tac >> gvs[EL_MAP] >>
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
      >- (gvs[SUBSET_DEF] >> rw[] >> first_x_assum drule_all >> simp[])
      )
    )
  >- simp[Once minfer_cases] (* Annot *)
  >- gvs[fail_def] (* NestedCase *)
QED


val _ = export_theory();
