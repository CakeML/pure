(*
  Type inference in the style of:
  "Generalizing Hindley-Milner Type Inference Algorithms" by Heeren et al.
  (http://www.cs.uu.nl/research/techreps/repo/CS-2002/2002-031.pdf)

  Other resources include
  - https://www.researchgate.net/profile/Martin-Sulzmann/publication/2802561_HindleyMilner_[…]0/Hindley-Milner-style-type-systems-in-constraint-form.pdf
  - http://gallium.inria.fr/~fpottier/publis/emlti-final.pdf
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory finite_mapTheory sptreeTheory monadsyntax;
open pure_typingTheory pure_cexpTheory pure_configTheory
     pure_inference_commonTheory;

val _ = new_theory "pure_inference";


(******************** Inference monad ********************)
(*
  For now this is just a state/error monad.
  The state (a number) keeps track of the next fresh variable.

  TODO make return type a sum, with some basic errors:
    unbound variable
    incorrect arity (e.g. supplying arguments to Lit, nullary functions, ...)

  Some of these errors will be picked up by the parser, but still should be
  handled gracefully.
*)
Type inferM[pp] = ``:num -> ('a # num) option``

Definition infer_bind_def:
  infer_bind (g : 'a inferM) f s =
    case g s of
    | NONE => NONE
    | SOME (x, s') => (f x : 'b inferM) s'
End

Definition infer_ignore_bind_def:
  infer_ignore_bind g f = infer_bind g (λ_ s. f s)
End

Definition return_def:
  return x =  λs. SOME (x, s)
End

Definition fail_def:
  fail : 'a inferM = λs. NONE
End

val infer_monadinfo : monadinfo = {
  bind = “infer_bind”,
  ignorebind = SOME “infer_ignore_bind”,
  unit = “return”,
  fail = SOME “fail”,
  choice = NONE,
  guard = NONE
  };

val _ = declare_monad ("infer", infer_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "infer";

(********** Key monadic helpers **********)

Definition oreturn_def:
  oreturn NONE = fail ∧
  oreturn (SOME x) = return x
End

Definition fresh_var_def:
  fresh_var : num inferM = λs. SOME (s, SUC s)
End

Definition fresh_vars_def:
  fresh_vars vars : num list inferM =
    λs. SOME (GENLIST (λn:num. s + n) vars, s + vars)
End


(******************** Constraint types ********************)

Datatype:
  constraint = Unify 'a itype itype
             | Instantiate 'a itype (num # itype)
             | Implicit 'a itype (num_set) itype
End

Type assumptions[pp] = ``:string |-> num_set``;

Definition aunion_def:
  aunion = FUNION_KEYS union : assumptions -> assumptions -> assumptions
End

val _ = set_mapped_fixity {term_name = "aunion", tok = UTF8.chr 0x22D3,
                           fixity = Infixl 500}

Definition get_assumptions_def:
  get_assumptions var (assumptions : assumptions) =
    case FLOOKUP assumptions var of
    | NONE => []
    | SOME cvars => MAP FST $ toAList cvars
End


(******************** Constraint generation ********************)

Definition infer_cons_def:
  infer_cons n ([] : typedefs) cname = NONE ∧
  infer_cons n ((ar,cs)::tds) cname =
    case ALOOKUP cs cname of
    | SOME ts => SOME (n, ar, ts)
    | NONE => infer_cons (SUC n) tds cname
End

(*
  We include arity as an argument to handle the fact that
  Substring/Concat/Implode separately have multiple possible arities.
*)
Definition infer_atom_op_def:
  (infer_atom_op ar (Lit $ Int i) =
    if ar = 0n then SOME ([], Integer) else NONE) ∧
  (infer_atom_op ar (Lit $ Str s) =
    if ar = 0 then SOME ([], String) else NONE) ∧
  (infer_atom_op ar (Lit $ Msg s1 s2) =
    if ar = 0 then SOME ([], Message) else NONE) ∧
  (infer_atom_op ar (Lit $ Loc n) = NONE) ∧
  (infer_atom_op ar Add =
    if ar = 2 then SOME ([Integer; Integer], Integer) else NONE) ∧
  (infer_atom_op ar Sub =
    if ar = 2 then SOME ([Integer; Integer], Integer) else NONE) ∧
  (infer_atom_op ar Mul =
    if ar = 2 then SOME ([Integer; Integer], Integer) else NONE) ∧
  (infer_atom_op ar Div =
    if ar = 2 then SOME ([Integer; Integer], Integer) else NONE) ∧
  (infer_atom_op ar Mod =
    if ar = 2 then SOME ([Integer; Integer], Integer) else NONE) ∧
  (infer_atom_op ar Eq =
    if ar = 2 then SOME ([Integer; Integer], Bool) else NONE) ∧
  (infer_atom_op ar Lt =
    if ar = 2 then SOME ([Integer; Integer], Bool) else NONE) ∧
  (infer_atom_op ar Leq =
    if ar = 2 then SOME ([Integer; Integer], Bool) else NONE) ∧
  (infer_atom_op ar Gt =
    if ar = 2 then SOME ([Integer; Integer], Bool) else NONE) ∧
  (infer_atom_op ar Geq =
    if ar = 2 then SOME ([Integer; Integer], Bool) else NONE) ∧
  (infer_atom_op ar Len =
    if ar = 1 then SOME ([String], Integer) else NONE) ∧
  (infer_atom_op ar Elem =
    if ar = 2 then SOME ([String; Integer], Integer) else NONE) ∧
  (infer_atom_op ar Concat = SOME (REPLICATE ar String, String)) ∧
  (infer_atom_op ar Implode = SOME (REPLICATE ar Integer, String)) ∧
  (infer_atom_op ar Substring =
    if ar = 2 then SOME ([String; Integer], String)
    else if ar = 3 then SOME ([String; Integer; Integer], String) else NONE) ∧
  (infer_atom_op ar StrEq =
    if ar = 2 then SOME ([String; String], Bool) else NONE) ∧
  (infer_atom_op ar StrLt =
    if ar = 2 then SOME ([String; String], Bool) else NONE) ∧
  (infer_atom_op ar StrLeq =
    if ar = 2 then SOME ([String; String], Bool) else NONE) ∧
  (infer_atom_op ar StrGt =
    if ar = 2 then SOME ([String; String], Bool) else NONE) ∧
  (infer_atom_op ar StrGeq =
    if ar = 2 then SOME ([String; String], Bool) else NONE) ∧
  (infer_atom_op ar (Message s) =
    if ar = 1 then SOME ([String], Message : prim_ty) else NONE)
End

Definition get_typedef_def:
  get_typedef n ([] : typedefs) cnames_arities = NONE ∧
  get_typedef n ((ar,cs)::tds) cnames_arities =
    if
      LENGTH cs = LENGTH cnames_arities ∧
      EVERY (λ(cn,ts). MEM (cn, LENGTH ts) cnames_arities) cs
    then SOME (n, ar, cs)
    else get_typedef (SUC n) tds cnames_arities
End

(**********
  infer :
       exndef # typedefs -- type definitions for exceptions and datatypes
    -> cexp -> (itype, assumptions, constraint list) inferM
**********)
Definition infer_def:
  infer (ns : exndef # typedefs) mset (pure_cexp$Var d x) = do
    fresh <- fresh_var;
    return (CVar fresh, FEMPTY |+ (x, insert fresh () LN), []) od ∧

  infer ns mset (Prim d (Cons s) es) = (
    if s = "" then do
      (tys,as,cs) <- FOLDR
            (λe acc. do
                (tys, as, cs) <- acc;
                (ty, as', cs') <- infer ns mset e;
                return (ty::tys, as ⋓ as', cs' ++ cs) od)
            (return ([],FEMPTY,[])) es;
      return (Tuple tys, as, cs) od

    else if s = "Ret" then (
      case es of
      | [e] => do (ty, as, cs) <- infer ns mset e; return (M ty, as, cs) od
      | _ => fail)

    else if s = "Bind" then (
      case es of
      | [e1; e2] => do
          (ty2, as2, cs2) <- infer ns mset e2;
          (ty1, as1, cs1) <- infer ns mset e1;
          fresh1 <- fresh_var; fresh2 <- fresh_var;
          return
            (M $ CVar fresh2, as1 ⋓ as2,
             (Unify d ty1 $ M $ CVar fresh1)::
              (Unify d ty2 $ Function (CVar fresh1) (M $ CVar fresh2))::(cs1++cs2))
          od
      | _ => fail)

    else if s = "Raise" then (
      case es of
      | [e] => do
          (ty, as, cs) <- infer ns mset e;
          fresh <- fresh_var;
          return (M $ CVar fresh, as, (Unify d ty Exception)::cs) od
      | _ => fail)

    else if s = "Handle" then (
      case es of
      | [e1; e2] => do
          (ty2, as2, cs2) <- infer ns mset e2;
          (ty1, as1, cs1) <- infer ns mset e1;
          fresh1 <- fresh_var; fresh2 <- fresh_var;
          return
            (M $ CVar fresh2, as1 ⋓ as2,
             (Unify d ty1 $ M $ CVar fresh1)::
              (Unify d ty2 $ Function Exception (M $ CVar fresh2))::(cs1++cs2))
          od
      | _ => fail)

    else if s = "Act" then (
      case es of
      | [e] => do
          (ty, as, cs) <- infer ns mset e;
          return (M $ PrimTy String, as, (Unify d ty $ PrimTy Message)::cs) od
      | _ => fail)

    else if s = "Alloc" then (
      case es of
      | [e1; e2] => do
          (ty2, as2, cs2) <- infer ns mset e2;
          (ty1, as1, cs1) <- infer ns mset e1;
          return
            (M $ Array ty2, as1 ⋓ as2, (Unify d ty1 $ PrimTy Integer)::(cs1++cs2))
          od
      | _ => fail)

    else if s = "Length" then (
      case es of
      | [e] => do
          (ty, as, cs) <- infer ns mset e;
          fresh <- fresh_var;
          return
            (M $ PrimTy Integer, as, (Unify d ty $ Array $ CVar fresh)::cs)
          od
      | _ => fail)

    else if s = "Deref" then (
      case es of
      | [e1; e2] => do
          (ty2, as2, cs2) <- infer ns mset e2;
          (ty1, as1, cs1) <- infer ns mset e1;
          fresh <- fresh_var;
          return
            (M $ CVar fresh, as1 ⋓ as2,
              (Unify d ty2 $ PrimTy Integer)::
              (Unify d ty1 $ Array $ CVar fresh)::(cs1++cs2))
          od
      | _ => fail)

    else if s = "Update" then (
      case es of
      | [e1; e2; e3] => do
          (ty3, as3, cs3) <- infer ns mset e3;
          (ty2, as2, cs2) <- infer ns mset e2;
          (ty1, as1, cs1) <- infer ns mset e1;
          fresh <- fresh_var;
          return
            (M $ Tuple [], as1 ⋓ as2 ⋓ as3,
              (Unify d ty3 $ CVar fresh)::(Unify d ty2 $ PrimTy Integer)::
                (Unify d ty1 $ Array $ CVar fresh)::(cs1++cs2++cs3))
          od
      | _ => fail)

    else if s = "True" ∨ s = "False" then (
      case es of
      | [] => return (PrimTy Bool, FEMPTY, [])
      | _ => fail)

    else if s = "Subscript" then (
      case es of
      | [] => return (Exception, FEMPTY, [])
      | _ => fail)

    else do
      (tys,as,cs) <- FOLDR
            (λe acc. do
                (tys, as, cs) <- acc;
                (ty, as', cs') <- infer ns mset e;
                return (ty::tys, as ⋓ as', cs' ++ cs) od)
            (return ([],FEMPTY,[])) es;
      case ALOOKUP (FST ns) s of
      (* Exceptions *)
      | SOME arg_tys => (
          if LENGTH arg_tys = LENGTH tys then
            return (Exception, as,
                    (list$MAP2 (λt a. Unify d t $ itype_of a) tys arg_tys) ++ cs)
          else fail)
      | NONE => case infer_cons 0 (SND ns) s of
      (* Constructors *)
      | SOME (n, ar, arg_tys) => do
          freshes <- fresh_vars ar;
          cfreshes <<- MAP CVar freshes;
          return (TypeCons n cfreshes, as,
          (list$MAP2
            (λt a. Unify d t (isubst cfreshes $ itype_of a)) tys arg_tys) ++ cs) od
      | NONE => fail od) ∧

  infer ns mset (Prim d (AtomOp aop) es) = do
    (arg_tys, ret_ty) <- oreturn $ infer_atom_op (LENGTH es) aop;
    (tys, as, cs) <- FOLDR
          (λe acc. do
              (tys, as, cs) <- acc;
              (ty, as', cs') <- infer ns mset e;
              return (ty::tys, as ⋓ as', cs' ++ cs) od)
          (return ([],FEMPTY,[])) es;
    return (PrimTy ret_ty, as,
            (list$MAP2 (λt a. Unify d t (PrimTy a)) tys arg_tys) ++ cs) od ∧

  infer ns mset (Prim d Seq [e1;e2]) = do
    (ty2, as2, cs2) <- infer ns mset e2;
    (ty1, as1, cs1) <- infer ns mset e1;
    return (ty2, as1 ⋓ as2, cs1++cs2) od ∧

  infer ns mset (App d e es) = (
    if NULL es then fail else do
    (tys, as, cs) <- FOLDR
          (λe acc. do
              (tys, as, cs) <- acc;
              (ty, as', cs') <- infer ns mset e;
              return (ty::tys, as ⋓ as', cs' ++ cs) od)
          (return ([],FEMPTY,[])) es;
    (tyf, asf, csf) <- infer ns mset e;
    fresh <- fresh_var;
    return (CVar fresh, as ⋓ asf,
            (Unify d tyf (iFunctions tys $ CVar fresh))::(csf ++ cs)) od) ∧

  infer ns mset (Lam d xs e) = (
    if NULL xs then fail else do
    freshes <- fresh_vars (LENGTH xs);
    cfreshes <<- MAP CVar freshes;
    (ty, as, cs) <- infer ns (list_insert freshes mset) e;
    return (iFunctions cfreshes ty, FDIFF as (set xs),
            FLAT (list$MAP2
              (λf x. MAP (Unify d (CVar f) o CVar) $ get_assumptions x as)
            freshes xs) ++ cs) od) ∧

  infer ns mset (Let d x e1 e2) = do
    (ty2, as2, cs2) <- infer ns mset e2;
    (ty1, as1, cs1) <- infer ns mset e1;
    return (ty2, as1 ⋓ (as2 \\ x),
            (MAP (λn. Implicit d (CVar n) mset ty1) $ get_assumptions x as2) ++
              cs1 ++ cs2) od ∧

  infer ns mset (Letrec d fns e) = do
    (tye, ase, cse) <- infer ns mset e;
    (tyfns, asfns, csfns) <- FOLDR
          (λ(fn,e) acc. do
              (tys, as, cs) <- acc;
              (ty, as', cs') <- infer ns mset e;
              return (ty::tys, as ⋓ as', cs' ++ cs) od)
          (return ([],FEMPTY,[])) fns;
    return (tye, FDIFF (ase ⋓ asfns) (set (MAP FST fns)),
            (FLAT $ list$MAP2
                (λ(x,b) tyfn. MAP (λn. Implicit d (CVar n) mset tyfn) $
                                              get_assumptions x (ase ⋓ asfns))
                fns tyfns) ++
            csfns ++ cse) od ∧

  (* TODO check handling of variables *)
  infer ns mset (Case d e v css) = (
    if MEM v (FLAT (MAP (FST o SND) css)) then fail else
    case css of
    | [] => fail (* no empty case statements *)
    | [("", pvars, rest)] => do (* tuple pattern match *)
      fresh_v <- fresh_var;
      cfresh_v <<- CVar fresh_v;
      fresh_tyargs <- fresh_vars (LENGTH pvars);
      cfresh_tyargs <<- MAP CVar fresh_tyargs;
      (tyrest, asrest, csrest) <-
        infer ns (list_insert (fresh_v::fresh_tyargs) mset) rest;
      (tye, ase, cse) <- infer ns mset e;
      pvar_constraints <<- list$MAP2
        (λv t. MAP (λn. Unify d (CVar n) t) $ get_assumptions v asrest)
          (v::pvars) (cfresh_v::cfresh_tyargs);
      return (tyrest, ase ⋓ (FDIFF asrest (v INSERT set pvars)),
                (Unify d cfresh_v tye)::(Unify d tye (Tuple cfresh_tyargs))::
                (FLAT pvar_constraints) ++ cse ++ csrest) od

    | _::_ => do
      (id, ar, cdefs) <- oreturn (get_typedef 0 (SND ns)
                                    (MAP (λ(cn,pvs,_). (cn, LENGTH pvs)) css));
      fresh_v <- fresh_var;
      cfresh_v <<- CVar fresh_v;
      fresh_tyargs <- fresh_vars ar;
      cfresh_tyargs <<- MAP CVar fresh_tyargs;
      mono_vars <<- fresh_v::fresh_tyargs;
      expected_arg_tys <<-
        MAP (λ(cn,ts). (cn, MAP (isubst cfresh_tyargs o itype_of) ts)) cdefs;
      (tys, as, cs) <- FOLDR
            (λ(cname,pvars,rest) acc. do
                (tys, as, cs) <- acc;
                (ty, as', cs') <- infer ns (list_insert mono_vars mset) rest;
                expected_cname_arg_tys <- oreturn (ALOOKUP expected_arg_tys cname);
                pvar_constraints <<- list$MAP2
                  (λv t. MAP (λn. Unify d (CVar n) t) $ get_assumptions v as')
                    (v::pvars) (cfresh_v::expected_cname_arg_tys);
                return (ty::tys, ((FDIFF as' (v INSERT set pvars)) ⋓ as),
                        (FLAT pvar_constraints) ++ cs' ++ cs) od)
            (return ([],FEMPTY,[])) css;
      (tye, ase, cse) <- infer ns mset e;

      return (HD tys, ase ⋓ as,
              (Unify d cfresh_v tye)::(Unify d tye (TypeCons id cfresh_tyargs))::
              (MAP (λt. Unify d (HD tys) t) (TL tys)) ++ cse ++ cs) od) ∧

  infer _ _ _ = fail
Termination
  WF_REL_TAC `measure ( λ(_,_,e). cexp_size (K 0) e)` >> rw[] >>
  rename1 `MEM _ es` >> pop_assum mp_tac >> rpt $ pop_assum kall_tac >>
  Induct_on `es` >> rw[] >> gvs[cexp_size_def]
End


(********************)

val _ = export_theory();
