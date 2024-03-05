open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open mlstringTheory;
open pure_configTheory;

val _ = new_theory "typeclass_types";


(******************** Types ********************)

Datatype:
  prim_ty = Integer | String | Message | Bool
End

Datatype:
  comp_prim_ty = Function | Array | M | Tuple num
End

Datatype:
  atom_ty =
      | PrimTy prim_ty
      | Exception
      | TypeCons (num + comp_prim_ty)
      (* concrete type constructor:
      * INL: user-defined types, INR: built-in types *)
      | VarTypeCons num
      (* variable type constructor *)
      (* eg. fmap :: (a -> b) -> f a -> f b *)
End

Datatype:
  type = Atom atom_ty | Cons type type
  (* eg. m f [a] = (m f) a -->
  * Cons (Cons (Atom m) (Atom f)) (Atom ) *)
End

Type class = ``:mlstring``; (* key for map from classname to class *)

Datatype:
  PredType = Pred ((class # type) list) type
    (* e.g. Monad m, Monad m2, Functor f => m1 (f a) -> m2 a *)
End

Overload Unit = ``Atom $ TypeCons (INR $ Tuple 0)``;
Overload TypeVar = ``\x. Atom (VarTypeCons x)``;
Overload UserType = ``\x. Atom (TypeCons $ INL x)``;
Type type_scheme[pp] = ``:num # type``;
Type PredType_scheme[pp] = ``:num # PredType``;

Definition collect_type_vars_def:
  (collect_type_vars (Cons t1 t2) =
    collect_type_vars t1 ∪ collect_type_vars t2) ∧
  (collect_type_vars (Atom $ VarTypeCons v) = {v}) /\
  (collect_type_vars _ = {})
End

(********** Substitutions and shifts **********)

Definition subst_db_def:
  (subst_db skip ts (Atom (VarTypeCons v)) =
    if skip ≤ v ∧ v < skip + LENGTH ts
      then EL (v - skip) ts 
    else if skip ≤ v
      then Atom (VarTypeCons $ v - LENGTH ts)
    else
      Atom (VarTypeCons v)) ∧
  (subst_db skip ts (Atom a) = Atom a) ∧
  subst_db skip ts (Cons t1 t2) =
    Cons (subst_db skip ts t1) (subst_db skip ts t2)
End

Definition shift_db_def:
  (shift_db skip n (Atom (VarTypeCons db)) =
    if skip ≤ db
      then Atom (VarTypeCons $ db + n)
      else Atom (VarTypeCons db)) ∧
  (shift_db skip n (Atom a) = Atom a) ∧
  shift_db skip n (Cons t1 t2) =
    Cons (shift_db skip n t1) (shift_db skip n t2)
End

Overload subst_db_scheme =
  ``λn ts (vars,scheme).
      (vars, subst_db (n + vars) (MAP (shift_db 0 vars) ts) scheme)``;
Overload shift_db_scheme =
  ``λskip shift (vars,scheme).
      (vars, shift_db (skip + vars) shift scheme)``;
Overload tsubst = ``subst_db 0``;
Overload tshift = ``shift_db 0``;
Overload tshift_scheme = ``λn (vars,scheme). (vars, shift_db vars n scheme)``;
Overload tshift_env = ``λn. MAP (λ(x,scheme). (x, tshift_scheme n scheme))``;

Definition Functions_def:
  Functions [] t = t ∧
  Functions (at::ats) t =
    Cons
      (Cons (Atom $ TypeCons $ INR Function) at) $
      Functions ats t
End


(* What's the proper way to do this *)
Definition generalise_def:
  generalise db (avoid : num_set) s (DBVar n) = (0n, s, DBVar n) ∧
  generalise db avoid s (PrimTy p) = (0, s, PrimTy p) ∧
  generalise db avoid s  Exception = (0, s, Exception) ∧

  generalise db avoid s (TypeCons id ts) = (
    let (n, s', ts') = generalise_list db avoid s ts in (n, s', TypeCons id ts')) ∧

  generalise db avoid s (Tuple ts) = (
    let (n, s', ts') = generalise_list db avoid s ts in (n, s', Tuple ts')) ∧

  generalise db avoid s (Function t1 t2) = (
    let (n1, s', t1') = generalise db avoid s t1 in
    let (n2, s'', t2') = generalise (db + n1) avoid s' t2 in
    (n1 + n2, s'', Function t1' t2')) ∧

  generalise db avoid s (Array t) = (
    let (n, s', t') = generalise db avoid s t in (n, s', Array t')) ∧

  generalise db avoid s (M t) = (
    let (n, s', t') = generalise db avoid s t in (n, s', M t')) ∧

  generalise db avoid s (CVar c) = (
    if lookup c avoid = NONE then (
      case FLOOKUP s c of
      | SOME n => (0, s, DBVar n)
      | NONE => (1, s |+ (c,db), DBVar db))
    else (0, s, CVar c)) ∧

  generalise_list db avoid s [] = (0, s, []) ∧
  generalise_list db avoid s (t::ts) =
    let (n, s', t') = generalise db avoid s t in
    let (ns, s'', ts') = generalise_list (db + n) avoid s' ts in
    (n + ns, s'', t'::ts')
End


Definition max_db_def:
  max_db (Cons t1 t2) = MAX (max_db t1) (max_db t2) ∧
  max_db (Atom (VarTypeCons v)) = 1 + v ∧
  max_db (Atom a) = 0
End

Definition to_scheme_def:
  to_scheme db avoid s (Cons t1 t2) =
    let (n,s',t1') = to_scheme db avoid s t1 in
    let (n',s'',t2') = to_scheme (db + n) avoid s t2 in
    (n+n',s'',Cons t1' t2') ∧
  to_scheme db avoid s (Atom (VarTypeCons v)) =
    if lookup v avoid = NONE
    then (0,s,Atom (VarTypeCons v))
    else (1,s,Atom (VarTypeCons db))
End

(******************** Properties of types ********************)

Definition freetyvars_ok_def:
  (freetyvars_ok n (Atom (VarTypeCons v)) = (v < n)) ∧
  (freetyvars_ok n (Atom a) = T) ∧
  (freetyvars_ok n (Cons t1 t2) =
    (freetyvars_ok n t1 ∧ freetyvars_ok n t2))
End

Overload freetyvars_ok_scheme =
  ``λn (vars,scheme). freetyvars_ok (n + vars) scheme``;

val _ = export_theory();
