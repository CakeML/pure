Inductive ikind_wf:
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

