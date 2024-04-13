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

Definition subst_db_pred_def:
  subst_db_pred skip ts (Pred ps t) =
    Pred (MAP (I ## subst_db skip ts) ps) (subst_db skip ts t)
End

Definition shift_db_pred_def:
  shift_db_pred skip n (Pred ps t) =
    Pred (MAP (I ## shift_db skip n) ps) (shift_db skip n t)
End

Overload tsubst = ``subst_db 0``;
Overload tshift = ``shift_db 0``;
Overload tsubst_pred = ``subst_db_pred 0``;
Overload tshift_pred = ``shift_db_pred 0``;

Definition Functions_def:
  Functions [] t = t ∧
  Functions (at::ats) t =
    Cons
      (Cons (Atom $ CompPrimTy Function) at) $
      Functions ats t
End

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

(* Functions to split the type in the form `F v1 v2 ...` to
* F and [v1;v2...] *)
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

Theorem ty_args_alt:
  (∀t1 t2. ty_args (Cons t1 t2) = SNOC t2 (ty_args t1)) ∧
  (∀x. ty_args (Atom x) = [])
Proof
  simp[ty_args_SNOC] >> simp[ty_args_def,ty_args_aux_def]
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

val _ = export_theory();
