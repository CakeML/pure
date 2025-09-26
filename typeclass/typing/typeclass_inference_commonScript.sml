(* Definitions common to inference theories. *)
Theory typeclass_inference_common
Ancestors
  arithmetic option list typeclass_types typeclass_kindCheck
Libs
  BasicProvers dep_rewrite

Datatype:
  itype = iAtom atom_ty
        | iCons itype itype
        | iCVar num
End

Overload Unit = ``iAtom $ CompPrimTy $ Tuple 0``;
Overload IntTy = ``iAtom $ PrimTy Integer``;
Overload BoolTy = ``iAtom $ PrimTy Bool``;
Overload StrTy = ``iAtom $ PrimTy String``;

Definition iFunctions_def:
  iFunctions [] t = t ∧
  iFunctions (at::ats) t =
    iCons (iCons (iAtom (CompPrimTy Function)) at) $ iFunctions ats t
End

Definition freedbvars_def:
  (freedbvars (iCons it1 it2) = freedbvars it1 ∪ freedbvars it2) ∧
  (freedbvars (iAtom (VarTypeCons v)) = {v}) ∧
  (freedbvars _ = {})
End

Inductive ikind_ok:
[~Prim:]
  ∀t. ikind_ok cdb vdb cvdb kindType (iAtom $ PrimTy t)
[~Exception:]
  ikind_ok cdb vdb cvdb kindType (iAtom Exception)
[~VarTypeCons:]
  ∀v k.
    LLOOKUP vdb v = SOME k ⇒
    ikind_ok cdb vdb cvdb k (iAtom $ VarTypeCons v)
[~TyConsINL:]
  ∀c k.
    LLOOKUP cdb c = SOME k ⇒
    ikind_ok cdb vdb cvdb k (iAtom $ TypeCons (INL c))
[~TyConsFunction:]
   ikind_ok cdb vdb cvdb
     (kindArrow kindType $ kindArrow kindType kindType)
     (iAtom $ CompPrimTy Function)
[~TypeConsArray:]
   ikind_ok cdb vdb cvdb (kindArrow kindType kindType)
     (iAtom $ CompPrimTy Array)
[~TypeConsM:]
   ikind_ok cdb vdb cvdb (kindArrow kindType kindType)
     (iAtom $ CompPrimTy M)
[~TypeConsTuple:]
   ∀n.
     ikind_ok cdb vdb cvdb (kind_arrows (GENLIST (K kindType) n) kindType)
       (iAtom $ CompPrimTy $ Tuple n)
[~Cons:]
   ∀k1 k2 t1 t2.
     ikind_ok cdb vdb cvdb (kindArrow k1 k2) t1 ∧
     ikind_ok cdb vdb cvdb k1 t2 ⇒
       ikind_ok cdb vdb cvdb k2 (iCons t1 t2)
[~CVar:]
  ∀n k.
    LLOOKUP cvdb n = SOME k ⇒
    ikind_ok cdb vbd cvdb k (iCVar n)
End

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

