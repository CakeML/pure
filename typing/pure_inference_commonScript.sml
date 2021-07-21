(* Definitions common to inference theories. *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory optionTheory listTheory;
open pure_typingTheory;

val _ = new_theory "pure_inference_common";

Datatype:
  itype = DBVar num
        | PrimTy prim_ty
        | Exception
        | TypeCons num (itype list)
        | Tuple (itype list)
        | Function itype itype
        | Array itype
        | M itype
        | CVar num
End

Definition iFunctions_def:
  iFunctions [] t = t ∧
  iFunctions (at::ats) t = Function at (iFunctions ats t)
End

Definition freecvars_def:
  freecvars (DBVar n) = {} ∧
  freecvars (PrimTy p) = {} ∧
  freecvars  Exception = {} ∧
  freecvars (TypeCons id ts) = BIGUNION (set (MAP freecvars ts)) ∧
  freecvars (Tuple ts) = BIGUNION (set (MAP freecvars ts)) ∧
  freecvars (Function t1 t2) = freecvars t1 ∪ freecvars t2 ∧
  freecvars (Array t) = freecvars t ∧
  freecvars (M t) = freecvars t ∧
  freecvars (CVar n) = {n}
Termination
  WF_REL_TAC `measure itype_size` >> rw[fetch "-" "itype_size_def"] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[fetch "-" "itype_size_def"] >> gvs[]
End

Definition isubst_def:
  isubst ts (DBVar v) = (
    if v < LENGTH ts then EL v ts else DBVar (v - LENGTH ts)) ∧
  isubst ts (PrimTy p) = PrimTy p ∧
  isubst ts  Exception = Exception ∧
  isubst ts (TypeCons n tcs) = TypeCons n (MAP (isubst ts) tcs) ∧
  isubst ts (Tuple tcs) = Tuple  (MAP (isubst ts) tcs) ∧
  isubst ts (Function tf t) =
    Function (isubst ts tf) (isubst ts t) ∧
  isubst ts (Array t) = Array (isubst ts t) ∧
  isubst ts (M t) = M (isubst ts t) ∧
  isubst ts (CVar c) = CVar c
Termination
  WF_REL_TAC `measure (itype_size o SND)` >> rw[fetch "-" "itype_size_def"] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[fetch "-" "itype_size_def"] >> gvs[]
End

Definition ishift_def:
  ishift n (DBVar v) = DBVar (v + n) ∧
  ishift n (PrimTy p) = PrimTy p ∧
  ishift n  Exception = Exception ∧
  ishift n (TypeCons tn tcs) = TypeCons tn (MAP (ishift n) tcs) ∧
  ishift n (Tuple tcs) = Tuple  (MAP (ishift n) tcs) ∧
  ishift n (Function tf t) =
    Function (ishift n tf) (ishift n t) ∧
  ishift n (Array t) = Array (ishift n t) ∧
  ishift n (M t) = M (ishift n t) ∧
  ishift n (CVar c) = CVar c
Termination
  WF_REL_TAC `measure (itype_size o SND)` >> rw[fetch "-" "itype_size_def"] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[fetch "-" "itype_size_def"] >> gvs[]
End

Definition itype_of_def:
  itype_of (TypeVar n) = DBVar n ∧
  itype_of (PrimTy p) = PrimTy p ∧
  itype_of Exception = Exception ∧
  itype_of (TypeCons n ts) = TypeCons n (MAP itype_of ts) ∧
  itype_of (Tuple ts) = Tuple (MAP itype_of ts) ∧
  itype_of (Function t1 t2) = Function (itype_of t1) (itype_of t2) ∧
  itype_of (Array t) = Array (itype_of t) ∧
  itype_of (M t) = M (itype_of t)
Termination
  WF_REL_TAC `measure type_size` >> rw[type_size_def] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[] >> gvs[type_size_def]
End

Definition type_of_def:
  type_of (DBVar n) = SOME $ TypeVar n ∧
  type_of (PrimTy p) = SOME $ PrimTy p ∧
  type_of Exception = SOME $ Exception ∧
  type_of (TypeCons n ts) =
    OPTION_MAP (TypeCons n) $
      FOLDR (λt ts_opt. OPTION_MAP2 CONS (type_of t) ts_opt) (SOME []) ts ∧
  type_of (Tuple ts) =
    OPTION_MAP Tuple $
      FOLDR (λt ts_opt. OPTION_MAP2 CONS (type_of t) ts_opt) (SOME []) ts ∧
  type_of (Function t1 t2) =
    OPTION_BIND (type_of t1)
    (λit1. OPTION_BIND (type_of t2) (λit2. SOME $ Function it1 it2)) ∧
  type_of (Array t) = OPTION_MAP Array (type_of t) ∧
  type_of (M t) = OPTION_MAP M (type_of t) ∧
  type_of (CVar n) = NONE
Termination
  WF_REL_TAC `measure itype_size` >> rw[fetch "-" "itype_size_def"] >>
  rename1 `MEM _ ts` >> Induct_on `ts` >> rw[fetch "-" "itype_size_def"] >> gvs[]
End

val _ = export_theory();

