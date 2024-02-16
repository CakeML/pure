(* Definitions common to inference theories. *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory optionTheory listTheory;
open typeclass_typesTheory;

val _ = new_theory "typeclass_inference_common";

Datatype:
  itype = iAtom atom_ty
        | iCons itype itype
        | iCVar num
End

Overload Unit = ``iAtom $ TypeCons (INR $ Tuple 0)``;
Overload IntTy = ``iAtom $ PrimTy Integer``;
Overload BoolTy = ``iAtom $ PrimTy Bool``;
Overload StrTy = ``iAtom $ PrimTy String``;

Definition iFunctions_def:
  iFunctions [] t = t ∧
  iFunctions (at::ats) t =
    iCons (iCons (iAtom (TypeCons $ INR Function)) at) $ iFunctions ats t
End

Definition freedbvars_def:
  (freedbvars (iCons it1 it2) = freedbvars it1 ∪ freedbvars it2) ∧
  (freedbvars (iAtom (VarTypeCons v)) = {v}) ∧
  (freedbvars _ = {})
End

(*
Definition itype_wf_def:
  itype_wf (typedefs : typedefs) (DBVar n) = T ∧
  itype_wf typedefs (PrimTy pty) = T ∧
  itype_wf typedefs  Exception = T ∧
  itype_wf typedefs (TypeCons id tyargs) = (
    EVERY (itype_wf typedefs) tyargs ∧
    ∃arity constructors.
      (* Type definition exists: *)
        oEL id typedefs = SOME (arity, constructors) ∧
      (* And has correct arity: *)
        LENGTH tyargs = arity) ∧
  itype_wf typedefs (Tuple ts) =
    EVERY (itype_wf typedefs) ts ∧
  itype_wf typedefs (Function tf t) = (
    itype_wf typedefs t ∧ itype_wf typedefs tf) ∧
  itype_wf typedefs (Array t) = itype_wf typedefs t ∧
  itype_wf typedefs (M t) = itype_wf typedefs t ∧
  itype_wf typedefs (CVar cv) = T
Termination
  WF_REL_TAC `measure (itype_size o SND)` >> rw[fetch "-" "itype_size_def"] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[fetch "-" "itype_size_def"] >> gvs[]
End

Definition itype_ok_def:
  itype_ok typedefs db t ⇔
    freedbvars t ⊆ count db ∧
    itype_wf typedefs t
End
*)

Definition isubst_def:
  (isubst ts (iAtom $ VarTypeCons v) =
    if v < LENGTH ts then EL v ts else iAtom $ VarTypeCons $ v - LENGTH ts) ∧
  (isubst ts (iCons t1 t2) = iCons (isubst ts t1) (isubst ts t2)) ∧
  isubst ts t = t
End

Definition ishift_def:
  ishift n (iAtom $ VarTypeCons v) = iAtom $ VarTypeCons (v + n) ∧
  ishift n (iCons t1 t2) = iCons (ishift n t1) (ishift n t2) ∧
  ishift n t = t
End

Definition itype_of_def:
  itype_of (Atom at) = iAtom at ∧
  itype_of (Cons t1 t2) = iCons (itype_of t1) (itype_of t2)
End

Definition type_of_def:
  type_of (iCons t1 t2) = lift2 Cons (type_of t1) (type_of t2) ∧
  type_of (iAtom at) = SOME $ Atom at ∧
  type_of (iCVar v) = NONE
End

val _ = export_theory();

