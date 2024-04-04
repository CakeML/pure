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
  built_in_ty = PrimT prim_ty | CompPrimT comp_prim_ty
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

Overload PrimTy = ``\x. TypeCons (INR $ PrimT x)``;
Overload CompPrimTy = ``\x. TypeCons (INR $ CompPrimT x)``;
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

Definition cons_types_def:
  cons_types thd [] = thd ∧
  cons_types thd (t1::targs) = cons_types (Cons thd t1) targs
End

(* Apply the type constructor to the list of types.
* Transforming from the representation of `F [a;b]` to `((F a) b)` *)
Definition tcons_to_type_def:
  tcons_to_type tcons targs = cons_types (Atom $ TypeCons tcons) targs
End

Theorem tcons_to_type_alt:
  (∀tcons. tcons_to_type tcons [] = Atom $ TypeCons tcons) ∧
  (∀tcons t1 targs.
    tcons_to_type tcons (t1::targs) =
      cons_types (Cons (Atom $ TypeCons tcons) t1) targs)
Proof
  rw[tcons_to_type_def] >>
  simp[Once cons_types_def]
QED

Theorem cons_types_APPEND:
   ∀t ts1 ts2.
     cons_types t (ts1 ++ ts2) = cons_types (cons_types t ts1) ts2
Proof
  Induct_on `ts1` >>
  rw[cons_types_def]
QED

Theorem cons_types_SNOC:
  ∀t ts1 t2. cons_types t (ts1 ++ [t2]) = Cons (cons_types t ts1) t2
Proof
  simp[cons_types_APPEND,cons_types_def]
QED

Theorem tcons_to_type_APPEND:
  tcons_to_type tcons (ts1 ++ ts2) = cons_types (tcons_to_type tcons ts1) ts2
Proof
  simp[tcons_to_type_def,cons_types_APPEND]
QED

Theorem tcons_to_type_SNOC:
  tcons_to_type tcons (SNOC t ts1) = Cons (tcons_to_type tcons ts1) t
Proof
  simp[tcons_to_type_APPEND,SNOC_APPEND,cons_types_def]
QED

Theorem subst_db_cons_types:
  ∀thd. subst_db n ts (cons_types thd targs) =
    cons_types (subst_db n ts thd) $ MAP (subst_db n ts) targs
Proof
  Induct_on `targs` >>
  rw[cons_types_def,subst_db_def]
QED

Theorem subst_db_tcons_to_type:
  subst_db n ts (tcons_to_type tcons targs) =
    tcons_to_type tcons $ MAP (subst_db n ts) targs
Proof
  rw[tcons_to_type_def,subst_db_cons_types,subst_db_def]
QED

Theorem tsubst_cons_types:
  ∀thd. tsubst ts (cons_types thd targs) =
    cons_types (tsubst ts thd) $ MAP (tsubst ts) targs
Proof
  rw[subst_db_cons_types]
QED

Theorem tsubst_tcons_to_type:
  tsubst ts (tcons_to_type tcons targs) =
    tcons_to_type tcons $ MAP (tsubst ts) targs
Proof
  rw[subst_db_tcons_to_type]
QED

val _ = export_theory();
