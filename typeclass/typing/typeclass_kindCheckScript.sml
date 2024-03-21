open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open typeclass_typesTheory;

val _ = new_theory "typeclass_kindCheck";

Datatype:
  Kind = kindType | kindArrow Kind Kind (* | kindVar num *)
End

(* helper function to create a kind *)
Definition kind_arrows_def:
  (kind_arrows [] ret = ret) ∧
  (kind_arrows (k::ks) ret = kindArrow k (kind_arrows ks ret))
End

Inductive kind_wf:
[~Prim:]
  ∀t. kind_wf cdb vdb kindType (Atom $ PrimTy t)
[~Exception:]
  kind_wf cdb vdb kindType (Atom Exception)
[~VarTypeCons:]
  ∀v k.
    vdb v = SOME k ⇒
    kind_wf cdb vdb k (Atom $ VarTypeCons v)
[~TyConsINL:]
  ∀c k.
    cdb c = SOME k ⇒
    kind_wf cdb vdb k (Atom $ TypeCons (INL c))
[~TyConsFunction:]
   kind_wf cdb vdb
     (kindArrow kindType $ kindArrow kindType kindType)
     (Atom $ CompPrimTy Function)
[~TypeConsArray:]
   kind_wf cdb vdb (kindArrow kindType kindType)
     (Atom $ CompPrimTy Array)
[~TypeConsM:]
   kind_wf cdb vdb (kindArrow kindType kindType)
     (Atom $ CompPrimTy M)
[~TypeConsTuple:]
   ∀n.
     kind_wf cdb vdb (kind_arrows (GENLIST (K kindType) n) kindType)
       (Atom $ CompPrimTy $ Tuple n)
[~Cons:]
   ∀k1 k2 t1 t2.
     kind_wf cdb vdb (kindArrow k1 k2) t1 ∧
     kind_wf cdb vdb k1 t2 ⇒
       kind_wf cdb vdb k2 (Cons t1 t2)
End

(* predicate to check if a predicated type is well-kinded *)
Definition pred_type_kind_ok_def:
  pred_type_kind_ok cldb cdb vdb (Pred cls ty) =
    (kind_wf cdb vdb kindType ty ∧
    ∀v cl. MEM (cl,v) cls ==>
      kind_wf cdb vdb (cldb cl) v)
End

Definition kind_to_arities_def:
  (kind_to_arities (kindArrow a b) = 1 + kind_to_arities b) ∧
  (kind_to_arities kindType = 0)
End

val _ = export_theory();
