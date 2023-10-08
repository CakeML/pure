open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open pure_tyingTheory;

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
   (!cdd vdb v t ts k1 k2.
      kind_wf cdb vdb (kindArrow k1 k2) (VarTypeCons v ts) /\
      kind_wf cdb vdb k1 t ==>
        kind_wf cdb vdb k2 (VarTypeCons v (t::ts))) /\
[~TyConsBase:]
   (!cdb vdb.
      kind_wf cdb vdb (cdb v) (TypeCons v [])) /\
[~TyConsCons:]
   (!cdd vdb.
      kind_wf cdb vdb (kindArrow k1 k2) (TypeCons v ts) /\
      kind_wf cdb vdb k1 t ==>
        kind_wf cdb vdb k2 (TypeCons v (t::ts)))
End

Definition kind_ok_def:
  kind_ok cldb cdb vdb (Pred cls ty) =
    (kind_wf cdb vdb kindType ty /\
    EVERY (λ(cl,v). vdb v = cldb cl) cls)
End
