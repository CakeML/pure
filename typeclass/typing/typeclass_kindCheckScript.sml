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
  (∀cdb vdb t. kind_wf cdb vdb kindType (PrimTy t))
[~Exception:]
  (∀cdb vdb. kind_wf cdb vdb kindType Exception)
[~VarTypeConsBase:]
  (∀cdb vdb v.
    kind_wf cdb vdb (vdb v) (VarTypeCons v []))
[~VarTypeConsCons:]
  (∀cdb vdb k1 k2 v t ts.
     kind_wf cdb vdb (kindArrow k1 k2) (VarTypeCons v ts) ∧
     kind_wf cdb vdb k1 t ⇒
       kind_wf cdb vdb k2 (VarTypeCons v (t::ts)))
[~TyConsBase:]
  (∀cdb vdb v.
     kind_wf cdb vdb (cdb v) (TypeCons (INL v) []))
[~TyConsCons:]
  (∀cdb vdb k1 k2 v t ts.
     kind_wf cdb vdb (kindArrow k1 k2) (TypeCons v ts) ∧
     kind_wf cdb vdb k1 t ⇒
       kind_wf cdb vdb k2 (TypeCons v (t::ts)))
[~TypeConsFunction:]
  (∀cdb vdb.
     kind_wf cdb vdb
       (kindArrow kindType $ kindArrow kindType kindType)
       (TypeCons (INR Function) []))
[~TypeConsArray:]
  (∀cdb vdb.
     kind_wf cdb vdb
       (kindArrow kindType kindType)
       (TypeCons (INR Array) []))
[~TypeConsM:]
  (∀cdb vdb.
     kind_wf cdb vdb
       (kindArrow kindType kindType)
       (TypeCons (INR M) []))
[~TypeConsTuple:]
  (∀cdb vdb n.
     kind_wf cdb vdb
       (kind_arrows (GENLIST (K kindType) n) kindType)
       (TypeCons (INR $ Tuple n) []))
End

(* predicate to check if the predicated type is well-kinded *)
Definition kind_ok_def:
  kind_ok cldb cdb vdb (Pred cls ty) =
    (kind_wf cdb vdb kindType ty ∧
    ∀v cl. MEM (cl,v) cls ==>
      kind_wf cdb vdb (cldb cl) v)
End

Definition kind_to_arities_def:
  (kind_to_arities (kindArrow a b) = 1 + kind_to_arities b) ∧
  (kind_to_arities kindType = 0)
End

(*
Definition ns_cns_kind_def:
  ns_cns_kind (exndef: exndef, tdefs : typedefs) =
    set (MAP (λ(cn,ts). cn, _ ts) exndef) INSERT
    {(«True», kindType); («False», kindType)} (* Booleans considered built-in *) INSERT
    set (_ tdefs)
    (* there could be mutual-recursive types and
    * needs to do kind inference at the same time *)
End
*)
val _ = export_theory();
