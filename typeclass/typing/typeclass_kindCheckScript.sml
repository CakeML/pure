open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open typeclass_typesTheory;

val _ = new_theory "typeclass_kindCheck";

Datatype:
  Kind = kindType | kindArrow Kind Kind
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
Definition pred_kind_wf_def:
  pred_kind_wf cldb cdb vdb (Pred cls ty) =
    (kind_wf cdb vdb kindType ty ∧
    ∀cl. MEM cl cls ⇒
      ∃k. cldb (FST cl) = SOME k ∧ kind_wf cdb vdb k (SND cl))
End

Definition kind_to_arities_def:
  (kind_to_arities (kindArrow a b) = 1n + kind_to_arities b) ∧
  (kind_to_arities kindType = 0n)
End

Theorem kind_to_arities_kind_arrow:
  kind_to_arities (kind_arrows ks k) = LENGTH ks + kind_to_arities k
Proof
  Induct_on `ks` >>
  simp[kind_to_arities_def,kind_arrows_def]
QED

Theorem kind_wf_subst_db:
  ∀k t. kind_wf cdb vdb k t ⇒
  (∀v k. v < n ∧ vdb v = SOME k ⇒ vdb' v = SOME k) ∧
  (∀v k. n ≤ v ∧ v < n + LENGTH ts ∧ vdb v = SOME k ⇒
    kind_wf cdb vdb' k (EL (v - n) ts)) ∧
  (∀v k. n + LENGTH ts ≤ v ∧ vdb v = SOME k ⇒ vdb' (v - LENGTH ts) = SOME k) ⇒
    kind_wf cdb vdb' k (subst_db n ts t)
Proof
  ho_match_mp_tac kind_wf_ind >>
  rw[kind_wf_rules,subst_db_def] >>
  gvs[] >>
  metis_tac[kind_wf_Cons]
QED

Theorem kind_wf_shift_db:
  ∀k t. kind_wf cdb vdb k t ⇒
  (∀v k. skip ≤ v ∧ vdb v = SOME k ⇒ vdb' (n + v) = SOME k) ∧
  (∀v k. v < skip ∧ vdb v = SOME k ⇒ vdb' v = SOME k) ⇒
    kind_wf cdb vdb' k (shift_db skip n t)
Proof
  ho_match_mp_tac kind_wf_ind >>
  rw[kind_wf_rules,shift_db_def] >>
  gvs[] >>
  metis_tac[kind_wf_Cons]
QED

Theorem pred_kind_wf_subst_db_pred:
   pred_kind_wf cldb cdb vdb pt ∧
   (∀v k. v < n ∧ vdb v = SOME k ⇒ vdb' v = SOME k) ∧
   (∀v k. n ≤ v ∧ v < n + LENGTH ts ∧ vdb v = SOME k ⇒
      kind_wf cdb vdb' k (EL (v - n) ts)) ∧
   (∀v k. n + LENGTH ts ≤ v ∧ vdb v = SOME k ⇒
      vdb' (v - LENGTH ts) = SOME k) ⇒
    pred_kind_wf cldb cdb vdb' (subst_db_pred n ts pt)
Proof
  Cases_on `pt` >>
  rw[pred_kind_wf_def,subst_db_pred_def]
  >- (
    drule_then irule kind_wf_subst_db >>
    rw[] >> metis_tac[]
  ) >>
  gvs[MEM_MAP,pairTheory.PAIR_MAP] >>
  last_x_assum $ drule_then strip_assume_tac >>
  first_x_assum $ irule_at (Pos hd) >>
  drule_then irule kind_wf_subst_db >>
  rw[] >> metis_tac[]
QED

Theorem pred_kind_wf_shift_db_pred:
   pred_kind_wf cldb cdb vdb pt ∧
   (∀v k. skip ≤ v ∧ vdb v = SOME k ⇒ vdb' (n + v) = SOME k) ∧
   (∀v k. v < skip ∧ vdb v = SOME k ⇒ vdb' v = SOME k) ⇒
     pred_kind_wf cldb cdb vdb' (shift_db_pred skip n pt)
Proof
  Cases_on `pt` >>
  rw[pred_kind_wf_def,shift_db_pred_def]
  >- (
    drule_then irule kind_wf_shift_db >>
    metis_tac[]
  ) >>
  gvs[MEM_MAP,pairTheory.PAIR_MAP] >>
  last_x_assum $ drule_then strip_assume_tac >>
  first_x_assum $ irule_at (Pos hd) >>
  drule_then irule kind_wf_shift_db >>
  metis_tac[]
QED

val _ = export_theory();
