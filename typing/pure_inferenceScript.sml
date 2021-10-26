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
open pure_typingTheory pure_cexpTheory pure_configTheory pure_varsTheory
     pure_inference_commonTheory pure_unificationTheory pure_miscTheory;

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

Type assumptions[pp] = ``:num_set var_map``;

Definition aunion_def:
  aunion = unionWith sptree$union : assumptions -> assumptions -> assumptions
End

val _ = set_mapped_fixity {term_name = "aunion", tok = UTF8.chr 0x22D3,
                           fixity = Infixl 500}

Definition get_assumptions_def:
  get_assumptions var (assumptions : assumptions) =
    case lookup assumptions var of
    | NONE => []
    | SOME cvars => MAP FST $ toAList cvars
End

Definition singleton_def:
  singleton k v = insert empty k v
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
    return (CVar fresh, singleton x (insert fresh () LN), []) od ∧

  infer ns mset (Prim d (Cons s) es) = (
    if s = "" then do
      (tys,as,cs) <- FOLDR
            (λe acc. do
                (tys, as, cs) <- acc;
                (ty, as', cs') <- infer ns mset e;
                return (ty::tys, as ⋓ as', cs' ++ cs) od)
            (return ([],empty,[])) es;
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
          fresh <- fresh_var;
          return
            (M $ CVar fresh, as1 ⋓ as2,
             (Unify d ty1 $ M $ CVar fresh)::
              (Unify d ty2 $ Function Exception (M $ CVar fresh))::(cs1++cs2))
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
      | [] => return (PrimTy Bool, empty, [])
      | _ => fail)

    else if s = "Subscript" then (
      case es of
      | [] => return (Exception, empty, [])
      | _ => fail)

    else do
      (tys,as,cs) <- FOLDR
            (λe acc. do
                (tys, as, cs) <- acc;
                (ty, as', cs') <- infer ns mset e;
                return (ty::tys, as ⋓ as', cs' ++ cs) od)
            (return ([],empty,[])) es;
      case ALOOKUP (FST ns) s of
      (* Exceptions *)
      | SOME arg_tys => (
          if LENGTH arg_tys = LENGTH tys then
            return (Exception, as,
                    (list$MAP2 (λt a. Unify d t $ itype_of a) tys arg_tys) ++ cs)
          else fail)
      | NONE => case infer_cons 0 (SND ns) s of
      (* Constructors *)
      | SOME (n, ar, arg_tys) => (
          if LENGTH arg_tys = LENGTH tys then do
            freshes <- fresh_vars ar;
            cfreshes <<- MAP CVar freshes;
            return (TypeCons n cfreshes, as,
            (list$MAP2
              (λt a. Unify d t (isubst cfreshes $ itype_of a)) tys arg_tys) ++ cs) od
          else fail)
      | NONE => fail od) ∧

  infer ns mset (Prim d (AtomOp aop) es) = do
    (arg_tys, ret_ty) <- oreturn $ infer_atom_op (LENGTH es) aop;
    (tys, as, cs) <- FOLDR
          (λe acc. do
              (tys, as, cs) <- acc;
              (ty, as', cs') <- infer ns mset e;
              return (ty::tys, as ⋓ as', cs' ++ cs) od)
          (return ([],empty,[])) es;
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
          (return ([],empty,[])) es;
    (tyf, asf, csf) <- infer ns mset e;
    fresh <- fresh_var;
    return (CVar fresh, as ⋓ asf,
            (Unify d tyf (iFunctions tys $ CVar fresh))::(csf ++ cs)) od) ∧

  infer ns mset (Lam d xs e) = (
    if NULL xs then fail else do
    freshes <- fresh_vars (LENGTH xs);
    cfreshes <<- MAP CVar freshes;
    (ty, as, cs) <- infer ns (list_insert freshes mset) e;
    return (iFunctions cfreshes ty, list_delete as xs,
            FLAT (list$MAP2
              (λf x. MAP (Unify d (CVar f) o CVar) $ get_assumptions x as)
            freshes xs) ++ cs) od) ∧

  infer ns mset (Let d x e1 e2) = do
    (ty2, as2, cs2) <- infer ns mset e2;
    (ty1, as1, cs1) <- infer ns mset e1;
    return (ty2, as1 ⋓ (delete as2 x),
            (MAP (λn. Implicit d (CVar n) mset ty1) $ get_assumptions x as2) ++
              cs1 ++ cs2) od ∧

  infer ns mset (Letrec d fns e) = do
    (tye, ase, cse) <- infer ns mset e;
    (tyfns, asfns, csfns) <- FOLDR
          (λ(fn,e) acc. do
              (tys, as, cs) <- acc;
              (ty, as', cs') <- infer ns mset e;
              return (ty::tys, as ⋓ as', cs' ++ cs) od)
          (return ([],empty,[])) fns;
    return (tye, list_delete (ase ⋓ asfns) (MAP FST fns),
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
      return (tyrest, ase ⋓ (list_delete asrest (v :: pvars)),
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
                return (ty::tys, ((list_delete as' (v :: pvars)) ⋓ as),
                        (FLAT pvar_constraints) ++ cs' ++ cs) od)
            (return ([],empty,[])) css;
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


(******************** Constraint solving ********************)

(*
  Generalise CVars greater than/equal to `cv`, starting at deBruijn index `db`.
  Avoid generalising the CVars given by `avoid`.
  Return the number generalised, the generalised type, and a substitution
  encapsulating the generalisation.
*)
Definition generalise_def:
  generalise cv db (avoid : num_set) s (DBVar n) = (0n, s, DBVar n) ∧
  generalise cv db avoid s (PrimTy p) = (0, s, PrimTy p) ∧
  generalise cv db avoid s  Exception = (0, s, Exception) ∧

  generalise cv db avoid s (TypeCons id ts) = (
    let (n, s', ts') = generalise_list cv db avoid s ts in (n, s', TypeCons id ts')) ∧

  generalise cv db avoid s (Tuple ts) = (
    let (n, s', ts') = generalise_list cv db avoid s ts in (n, s', Tuple ts')) ∧

  generalise cv db avoid s (Function t1 t2) = (
    let (n1, s', t1') = generalise cv db avoid s t1 in
    let (n2, s'', t2') = generalise cv (db + n1) avoid s' t2 in
    (n1 + n2, s'', Function t1' t2')) ∧

  generalise cv db avoid s (Array t) = (
    let (n, s', t') = generalise cv db avoid s t in (n, s', Array t')) ∧

  generalise cv db avoid s (M t) = (
    let (n, s', t') = generalise cv db avoid s t in (n, s', M t')) ∧

  generalise cv db avoid s (CVar c) = (
    if cv ≤ c ∧ lookup c avoid = NONE then (
      case FLOOKUP s c of
      | SOME n => (0, s, DBVar n)
      | NONE => (1, s |+ (c,db), DBVar db))
    else (0, s, CVar c)) ∧

  generalise_list cv db avoid s [] = (0, s, []) ∧
  generalise_list cv db avoid s (t::ts) =
    let (n, s', t') = generalise cv db avoid s t in
    let (ns, s'', ts') = generalise_list cv (db + n) avoid s' ts in
    (n + ns, s'', t'::ts')
End

Definition satisfies_def:
  satisfies s (Unify d t1 t2) = (pure_walkstar s t1 = pure_walkstar s t2) ∧

  satisfies s (Instantiate d t (vars, scheme)) = (
    ∃subs.
      LENGTH subs = vars ∧
      pure_walkstar s t = pure_walkstar s (isubst subs scheme)) ∧

  satisfies s (Implicit d tsub vars tsup) = (
    let (vars, s', scheme) = generalise 0 0 vars FEMPTY tsup in
    ∃subs.
      LENGTH subs = vars ∧
      pure_walkstar s tsub = pure_walkstar s (isubst subs scheme))
End

Definition freecvars_def:
  freecvars (DBVar n) = LN ∧
  freecvars (PrimTy p) = LN ∧
  freecvars  Exception = LN ∧
  freecvars (TypeCons id ts) = FOLDL union LN (MAP freecvars ts) ∧
  freecvars (Tuple ts) = FOLDL union LN (MAP freecvars ts) ∧
  freecvars (Function t1 t2) = union (freecvars t1) (freecvars t2) ∧
  freecvars (Array t) = freecvars t ∧
  freecvars (M t) = freecvars t ∧
  freecvars (CVar n) = insert n () LN
Termination
  WF_REL_TAC `measure itype_size` >> rw[itype_size_def] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[itype_size_def] >> gvs[]
End

Definition subst_vars_def:
  subst_vars s (vars : num_set) =
    foldi (λn u acc. union acc $ freecvars $ pure_walkstar s (CVar n)) 0 LN vars
End

Definition subst_constraint_def:
  subst_constraint s (Unify d t1 t2) =
    Unify d (pure_walkstar s t1) (pure_walkstar s t2) ∧
  subst_constraint s (Instantiate d t1 (vars, t2)) =
    Instantiate d (pure_walkstar s t1) (vars, pure_walkstar s t2) ∧
  subst_constraint s (Implicit d t1 vs t2) =
    Implicit d (pure_walkstar s t1) (subst_vars s vs) (pure_walkstar s t2)
End

Definition activevars_def:
  activevars (Unify d t1 t2) = union (freecvars t1) (freecvars t2) ∧
  activevars (Implicit d t1 vars t2) =
    union (freecvars t1) (inter vars (freecvars t2)) ∧
  activevars (Instantiate d t (vars, scheme)) =
    union (freecvars t) (freecvars scheme)
End


(* TODO this approach is naive *)

Definition is_solveable_def:
  is_solveable (Unify d t1 t2) cs = T ∧
  is_solveable (Instantiate d t sch) cs = T ∧
  is_solveable (Implicit d t1 vars t2) cs =
    let active = FOLDL (λacc c. union (activevars c) acc) LN cs in
    (inter (difference (freecvars t2) vars) active = LN)
End

(* TODO reverse shouldn't be necessary here *)
Definition get_solveable_def:
  get_solveable [] cs = NONE ∧
  get_solveable (c::rest) cs =
    if is_solveable c (REVERSE cs ++ rest) then
      SOME (c, REVERSE cs ++ rest)
    else get_solveable rest (c::cs)
End

Theorem get_solveable_SOME:
  ∀cs rev_cs c cs'.
    get_solveable cs rev_cs = SOME (c, cs')
  ⇒ ∃left right.
      cs = left ++ [c] ++ right ∧
      cs' = REVERSE rev_cs ++ left ++ right ∧
      is_solveable c cs'
Proof
  Induct >> rw[get_solveable_def] >> simp[]
  >- (qexists_tac `[]` >> simp[]) >>
  last_x_assum drule >> rw[] >> qexists_tac `h::left` >> simp[]
QED

Definition constraint_weight_def:
  constraint_weight (Unify _ _ _) = 1n ∧
  constraint_weight (Instantiate _ _ _ ) = 2n ∧
  constraint_weight (Implicit _ _ _ _ ) = 3n
End

Theorem constraint_weight_subst_constraint[simp]:
  ∀t s. constraint_weight (subst_constraint s t) = constraint_weight t
Proof
  Cases >> rw[subst_constraint_def, constraint_weight_def] >>
  PairCases_on `p` >> rw[subst_constraint_def, constraint_weight_def]
QED

Definition solve_def:
  solve [] = return [] ∧

  solve cs = case get_solveable cs [] of
    | NONE => fail

    | SOME $ (Unify d t1 t2, cs) => do
        sub <- oreturn $ pure_unify FEMPTY t1 t2;
        cs' <<- MAP (subst_constraint sub) cs;
        solve_rest <- solve cs';
        return (sub :: solve_rest) od

    | SOME $ (Instantiate d t (vs, scheme), cs) => do
        freshes <- fresh_vars vs;
        inst_scheme <<- isubst (MAP CVar freshes) scheme;
        solve (Unify d t inst_scheme :: cs) od

    | SOME $ (Implicit d t1 vs t2, cs) => do
        (n, s, scheme) <<- generalise 0 0 vs FEMPTY t2;
        solve (Instantiate d t1 (n, scheme) :: cs) od
Termination
  WF_REL_TAC `measure $ λl. SUM $ MAP constraint_weight l` >>
  rw[constraint_weight_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  drule get_solveable_SOME >> strip_tac >> gvs[] >>
  Cases_on `left` >> gvs[SUM_APPEND, constraint_weight_def]
End

Definition subst_solution_def:
  subst_solution [] ty = ty ∧
  subst_solution (s::ss) ty = subst_solution ss (pure_walkstar s ty)
End


(********************)

val _ = export_theory();
