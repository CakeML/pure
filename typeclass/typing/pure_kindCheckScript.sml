open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open pure_typesTheory;

val _ = new_theory "pure_kindCheck";

Datatype:
  Kind = kindType | kindArrow Kind Kind (* | kindVar num *)
End

Inductive kind_wf:
[~TyVar:]
  (!cdb vdb v.
    vdb v = kindType ==>
      kind_wf cdb vdb kindType (TypeVar v)) /\
[~Prim:]
  (!cdb vdb t. kind_wf cdb vdb kindType (PrimTy t)) /\
[~Exception:]
  (!cdb vdb. kind_wf cdb vdb kindType Exception) /\
[~Tuple:]
  (!cdb vdb ts.
    EVERY (kind_wf cdb vdb kindType) ts ==>
      kind_wf cdb vdb kindType (Tuple ts)) /\
[~Function:]
  (!cdb vdb a b.
    kind_wf cdb vdb kindType a /\
    kind_wf cdb vdb kindType b ==>
      kind_wf cdb vdb kindType (Function a b)) /\
[~Array:]
  (!cdb vdb t.
    kind_wf cdb vdb kindType t ==>
      kind_wf cdb vdb kindType (Array t)) /\
[~M:]
  (!cdb vdb t.
    kind_wf cdb vdb kindType t ==>
      kind_wf cdb vdb kindType (M t)) /\
[~VarTypeConsBase:]
   (!cdb vdb v.
      kind_wf cdb vdb (vdb v) (VarTypeCons v [])) /\
[~VarTypeConsCons:]
   (!cdb vdb v t ts k1 k2.
      kind_wf cdb vdb (kindArrow k1 k2) (VarTypeCons v ts) /\
      kind_wf cdb vdb k1 t ==>
        kind_wf cdb vdb k2 (VarTypeCons v (t::ts))) /\
[~TyConsBase:]
   (!cdb vdb.
      kind_wf cdb vdb (cdb v) (TypeCons v [])) /\
[~TyConsCons:]
   (!cdb vdb.
      kind_wf cdb vdb (kindArrow k1 k2) (TypeCons v ts) /\
      kind_wf cdb vdb k1 t ==>
        kind_wf cdb vdb k2 (TypeCons v (t::ts)))
End

Definition kind_ok_def:
  kind_ok cldb cdb vdb (Pred cls ty) =
    (kind_wf cdb vdb kindType ty /\
    !v cl. MEM (cl,v) cls ==>
      kind_wf cdb vdb (cldb cl) v)
End

Definition kind_list_def:
  (kind_list [] ret = ret) /\
  (kind_list (k::ks) ret = kindArrow k (kind_list ks ret))
End

Definition kind_to_arities_def:
  (kind_to_arities (kindArrow a b) = 1 + kind_to_arities b) /\
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
