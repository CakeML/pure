(* Implement specialization for predicated types using unification *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     pred_setTheory relationTheory listTheory alistTheory finite_mapTheory;
open typeclass_unificationTheory typeclass_typesTheory;
(* typeclass_typingTheory *)
open typeclass_inference_commonTheory;

val _ = new_theory "typeclass_specialize";

Definition VarType_to_CVar_def:
  (VarType_to_CVar (iAtom (VarTypeCons v)) = iCVar v) ∧
  (VarType_to_CVar (iCons i1 i2) = iCons (VarType_to_CVar i1) (VarType_to_CVar i2)) ∧
  (VarType_to_CVar (iCVar n) = IntTy) ∧ (* this should never happend *)
  (VarType_to_CVar i = i)
End

Definition specialize_def:
  specialize t t' = (?ts. tsubst ts t = t')
End

Definition specialize_impl_def:
  specialize_impl t t' = pure_unify FEMPTY (VarType_to_CVar (itype_of t)) (itype_of t')
End

Definition is_specialize_impl_def:
  is_specialize_impl t t' = IS_SOME (specialize_impl t t')
End

val _ = export_theory();
