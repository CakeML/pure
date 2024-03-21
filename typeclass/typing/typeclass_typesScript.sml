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
  built_in_ty = Prim prim_ty | CompPrim comp_prim_ty
End

(* concrete type constructor:
* INL: user-defined types, INR: built-in types *)
Type ty_cons = ``:num + built_in_ty``;

Datatype:
  atom_ty =
      | Exception
      | TypeCons ty_cons 
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

Overload PrimTy = ``\x. TypeCons (INR $ Prim x)``;
Overload CompPrimTy = ``\x. TypeCons (INR $ CompPrim x)``;
Overload Unit = ``Atom $ CompPrimTy $ Tuple 0``;
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
      (Cons (Atom $ CompPrimTy Function) at) $
      Functions ats t
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
