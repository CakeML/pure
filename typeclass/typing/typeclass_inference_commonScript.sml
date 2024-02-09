(* Definitions common to inference theories. *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory optionTheory listTheory;
open typeclass_typesTheory;

val _ = new_theory "typeclass_inference_common";

Datatype:
  itype = DBVarCons num (itype list)
        | PrimTy prim_ty
        | Exception
        | TypeCons (num + comp_prim_ty) (itype list)
        | CVarCons num (itype list)
End

Overload Unit = ``TypeCons (INR $ Tuple 0) []``;
Overload IntTy = ``PrimTy Integer``;
Overload BoolTy = ``PrimTy Bool``;
Overload StrTy = ``PrimTy String``;

Theorem itype_ind:
  ∀P.
    (∀n ts. (∀a. MEM a ts ⇒ P a) ⇒ P (DBVarCons n ts)) ∧
    (∀p. P (PrimTy p)) ∧ P Exception ∧
    (∀id ts. (∀a. MEM a ts ⇒ P a) ⇒ P (TypeCons id ts)) ∧
    (∀n ts. (∀a. MEM a ts ⇒ P a) ⇒ P (CVarCons n ts))
  ⇒ ∀v. P v
Proof
  ntac 3 strip_tac >>
  completeInduct_on `itype_size v` >> rw[] >>
  Cases_on `v` >> gvs[fetch "-" "itype_size_def"] >>
  last_x_assum irule >> rw[] >>
  first_x_assum irule >> simp[] >>
  Induct_on `l` >> rw[] >> gvs[fetch "-" "itype_size_def"]
QED

Definition iFunctions_def:
  iFunctions [] t = t ∧
  iFunctions (at::ats) t = TypeCons (INR Function)
    [at; (iFunctions ats t)]
End

Definition freedbvars_def:
  (freedbvars (DBVarCons n its) =
    {n} ∪ BIGUNION (set $ MAP freedbvars its)) ∧
  (freedbvars (PrimTy pty) = {}) ∧
  (freedbvars Exception = {}) ∧
  (freedbvars (TypeCons id its) = BIGUNION (set (MAP freedbvars its))) ∧
  (freedbvars (CVarCons cv its) = BIGUNION (set (MAP freedbvars its)))
Termination
  WF_REL_TAC `measure itype_size` >> rw[fetch "-" "itype_size_def"]
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

Definition isubstDBVarCons_def:
  isubstDBVarCons (DBVarCons v tcs) ts = DBVarCons v (tcs ++ ts) ∧
  isubstDBVarCons (TypeCons v tcs) ts = TypeCons v (tcs ++ ts) ∧
  isubstDBVarCons (CVarCons v tcs) ts = CVarCons v (tcs ++ ts) ∧
  isubstDBVarCons p ts = p
End

Definition isubst_def:
  isubst ts (DBVarCons v tcs) = (
    if v < LENGTH ts
      then isubstDBVarCons (EL v ts) (MAP (isubst ts) tcs)
      else DBVarCons (v - LENGTH ts) (MAP (isubst ts) tcs)) ∧
  isubst ts (PrimTy p) = PrimTy p ∧
  isubst ts  Exception = Exception ∧
  isubst ts (TypeCons v tcs) = TypeCons v (MAP (isubst ts) tcs) ∧
  isubst ts (CVarCons v tcs) = CVarCons v (MAP (isubst ts) tcs)
Termination
  WF_REL_TAC `measure (itype_size o SND)` >> rw[fetch "-" "itype_size_def"]
End

Definition ishift_def:
  ishift n (DBVarCons v tcs) = DBVarCons (v + n) (MAP (ishift n) tcs) ∧
  ishift n (PrimTy p) = PrimTy p ∧
  ishift n  Exception = Exception ∧
  ishift n (TypeCons v tcs) = TypeCons v (MAP (ishift n) tcs) ∧
  ishift n (CVarCons v tcs) = CVarCons v (MAP (ishift n) tcs)
Termination
  WF_REL_TAC `measure (itype_size o SND)` >> rw[fetch "-" "itype_size_def"]
End

Definition itype_of_def:
  itype_of (VarTypeCons n ts) = DBVarCons n (MAP itype_of ts) ∧
  itype_of (PrimTy p) = PrimTy p ∧
  itype_of Exception = Exception ∧
  itype_of (TypeCons n ts) = TypeCons n (MAP itype_of ts)
Termination
  WF_REL_TAC `measure type_size` >> rw[type_size_def]
End

Definition type_of_def:
  type_of (DBVarCons n ts) =
    OPTION_MAP (VarTypeCons n) $ OPT_MMAP type_of ts ∧
  type_of (PrimTy p) = SOME $ PrimTy p ∧
  type_of Exception = SOME $ Exception ∧
  type_of (TypeCons n ts) =
    OPTION_MAP (TypeCons n) $ OPT_MMAP type_of ts ∧
  type_of (CVarCons n ts) = NONE
Termination
  WF_REL_TAC `measure itype_size` >> rw[fetch "-" "itype_size_def"]
End

val _ = export_theory();

