(*
   Formalises a notion of a weaker evaluation that doesn't differentiate errors from diverging.
*)

open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory dep_rewrite
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_miscTheory pure_exp_relTheory pure_congruenceTheory;

val _ = new_theory "pure_no_err_rel";


Definition no_err_eval_wh_def:
  no_err_eval_wh e = case eval_wh e of
    | wh_Error => wh_Diverge
    | wh => wh
End

val _ = set_fixity "no_err_rel" (Infixl 480);

Definition no_err_rel_def:
  e1 no_err_rel e2 =
  ∀f. freevars e1 ⊆ FDOM f ∧
        freevars e2 ⊆ FDOM f ∧
        no_err_eval_wh (subst f e1) = no_err_eval_wh (subst f e2)
End

Theorem exp_eq_IMP_no_err_rel:
  e ≅ e' ⇒ e no_err_rel e'
Proof
  cheat
QED

Theorem no_err_eq_Prim_cong:
  LIST_REL $no_err_rel xs xs' ⇒ Prim p xs no_err_rel Prim p xs'
Proof
  cheat
QED

Theorem no_err_eq_Lam_cong:
  e no_err_rel e' ⇒ Lam x e no_err_rel Lam x e'
Proof
  cheat
QED

Theorem no_err_eq_App_cong:
  f no_err_rel f' ∧ e no_err_rel e' ⇒ App f e no_err_rel App f' e'
Proof
  cheat
QED

Theorem no_err_eq_refl:
  ∀e. e no_err_rel e
Proof
  fs [exp_eq_IMP_no_err_rel, exp_eq_refl]
QED

Theorem no_err_eq_trans:
  ∀x y z. x no_err_rel y ∧ y no_err_rel z ⇒ x no_err_rel z
Proof
  cheat
QED

Theorem no_err_eq_sym:
  ∀x y. x no_err_rel y ⇒ y no_err_rel x
Proof
  cheat
QED

Theorem Seq_App:
  App (Seq p f) e ≅ Seq p (App f e)
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_App, eval_wh_Seq]
  \\ fs []
QED

Theorem no_err_Seq_App:
  App (Seq p f) e no_err_rel Seq p (App f e)
Proof
  fs [Seq_App, exp_eq_IMP_no_err_rel]
QED

Theorem no_err_Seq_id:
  Seq e e no_err_rel e
Proof
  fs [exp_eq_IMP_no_err_rel, Seq_id]
QED

Theorem no_err_Seq_assoc:
  Seq (Seq x y) z no_err_rel Seq x (Seq y z)
Proof
  fs [Seq_assoc, exp_eq_IMP_no_err_rel]
QED

Theorem no_err_Let_Prim_alt:
  Let w e (Prim p []) no_err_rel Prim p [] ∧
  Let w e (Prim p [a]) no_err_rel Prim p [Let w e a] ∧
  Let w e (Prim p [a; b]) no_err_rel Prim p [Let w e a; Let w e b] ∧
  Let w e (Prim p [a; b; c]) no_err_rel Prim p [Let w e a; Let w e b; Let w e c]
Proof
  fs [Let_Prim_alt, exp_eq_IMP_no_err_rel]
QED

Theorem no_err_Let_Var:
  Let w e (Var w) no_err_rel e
Proof
  fs [Let_Var, exp_eq_IMP_no_err_rel]
QED

Theorem no_err_Let_Seq:
  Let w e (Seq x y) no_err_rel Seq (Let w e x) (Let w e y)
Proof
  fs [Let_Seq, exp_eq_IMP_no_err_rel]
QED

Theorem no_err_Proj_Cons:
  Proj s (LENGTH xs) (Cons s (xs ++ y::ys)) no_err_rel y
Proof
  fs [Proj_Cons, exp_eq_IMP_no_err_rel]
QED

Theorem Proj_Seq2:
  Proj x i (Seq e e') ≅ Seq e (Proj x i e')
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_Proj, eval_wh_Seq]
  \\ fs []
QED

Theorem no_err_Proj_Seq2:
  Proj x i (Seq e e') no_err_rel Seq e (Proj x i e')
Proof
  fs [Proj_Seq2, exp_eq_IMP_no_err_rel]
QED

Theorem no_err_Proj_Seq:
  Proj x i e no_err_rel Seq e (Proj x i e)
Proof
  fs [Proj_Seq, exp_eq_IMP_no_err_rel]
QED

Theorem If_Seq:
  If (Seq e e') e'' e''' ≅ Seq e (If e' e'' e''')
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_If, eval_wh_Seq]
  \\ fs []
QED

Theorem no_err_If_Seq:
  If (Seq e e') e'' e''' no_err_rel Seq e (If e' e'' e''')
Proof
  fs [If_Seq, exp_eq_IMP_no_err_rel]
QED

Theorem IsEq_Seq:
  IsEq n i (Seq e e') ≅ Seq e (IsEq n i e')
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_IsEq, eval_wh_Seq]
  \\ fs []
QED

Theorem no_err_IsEq_Seq:
  IsEq n i (Seq e e') no_err_rel Seq e (IsEq n i e')
Proof
  fs [IsEq_Seq, exp_eq_IMP_no_err_rel]
QED

Theorem no_err_Let_Var2:
  v ≠ w ⇒ Let w e (Var v) no_err_rel Var v
Proof
  fs [Let_Var2, exp_eq_IMP_no_err_rel]
QED

Theorem no_err_eq_l_refl:
  ∀l. LIST_REL $no_err_rel l l
Proof
  Induct \\ fs [no_err_eq_refl]
QED

Theorem no_err_Seq_Com:
  Seq (Seq x y) z no_err_rel Seq (Seq y x) z
Proof
  cheat
QED

Definition well_written_def:
  well_written (Cons s) l = T ∧
  well_written (Proj s i) [e] = T ∧
  well_written (IsEq s i) [e] = T ∧
  well_written If [e; e'; e''] = T ∧
  well_written Seq [e; e'] = T ∧
  well_written (AtomOp op) l = T ∧
  well_written _ _ = F
End

Theorem not_well_written_is_fail:
  ¬ well_written ope l ⇒
    Prim ope l no_err_rel Fail
Proof
  rw []
  \\ Cases_on ‘ope’
  \\ fs [well_written_def]
  \\ irule exp_eq_IMP_no_err_rel
  \\ Cases_on ‘l’
  >>~[‘Prim _ [] ≅ Fail’]
  >- (fs [exp_eq_refl])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  \\ rename1 ‘hd::tl’
  \\ Cases_on ‘tl’
  \\ fs [well_written_def]
  >>~[‘Prim _ [hd]’]
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  \\ rename1 ‘h0::h1::tl’
  \\ Cases_on ‘tl’
  \\ fs [well_written_def]
  >~[‘Prim If (h0::h1::h2::tl)’]
  >- (Cases_on ‘tl’
      \\ fs [well_written_def]
      \\ irule eval_wh_IMP_exp_eq
      \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [subst_def, eval_wh_def, eval_wh_to_def]
QED

val _ = export_theory ();
