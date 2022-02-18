(*
   Formalises the notion of "demand" as used in demand/strictness analysis.
*)

open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory dep_rewrite
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_miscTheory pure_exp_relTheory pure_congruenceTheory;

val _ = new_theory "pure_demand";

Definition Projs_def:
  Projs [] e = e ∧
  Projs ((x,i)::ps) e = Projs ps (Proj x i e)
End

Theorem demands_proj_end:
  ∀ ps x i e. Projs (ps++[(x,i)]) e = Proj x i (Projs ps e)
Proof
  Induct THEN1 rw [Projs_def]
  \\ gen_tac \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
QED

Theorem double_Projs:
  ∀ps' ps e. Projs (ps' ++ ps) e = Projs ps (Projs ps' e)
Proof
  Induct >- rw [Projs_def]
  \\ gen_tac \\ rename1 ‘hd::ps'’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
QED

Theorem exp_eq_Projs_cong:
  ∀ps x y. x ≅ y ⇒ Projs ps x ≅ Projs ps y
Proof
  Induct \\ fs [Projs_def,FORALL_PROD]
  \\ rw [] \\ first_x_assum irule
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
QED

Theorem Projs_Seq:
  ∀ps e e'. Projs ps (Seq e e') ≅ Seq e (Projs ps e')
Proof
  Induct
  THEN1 (rw [Projs_def] \\ fs [exp_eq_refl])
  \\ rpt gen_tac
  \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ irule exp_eq_trans \\ qexists_tac ‘Projs ps (Seq e (Proj hd0 hd1 e'))’
  \\ conj_tac
  THEN1 (irule exp_eq_Projs_cong \\ irule eval_wh_IMP_exp_eq \\ rw [subst_def, eval_wh_Proj, eval_wh_Seq])
  \\ rw []
QED

Theorem Let_Projs:
  ∀ps x w y. Let w y (Projs ps x) ≅ Projs ps (Let w y x)
Proof
  Induct \\ fs [Projs_def,exp_eq_refl,FORALL_PROD] \\ rw []
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w y (Proj p_1 p_2 x))’
  \\ conj_tac THEN1 fs []
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Prim_alt]
QED

Theorem Projs_subst:
  ∀ps f e. subst f (Projs ps e) = Projs ps (subst f e)
Proof
  Induct THEN1 rw [Projs_def]
  \\ gen_tac
  \\ rename1 ‘Projs (hd::_) _’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def, subst_def]
QED

Theorem Seq_App:
  App (Seq proj f) e ≅ Seq proj (App f e)
Proof
  irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def, eval_wh_Seq, eval_wh_App]
  \\ rw [] \\ fs []
QED

val _ = set_fixity "demands" (Infixl 480);

Definition demands_def:
  (e demands (p,v)) = (e ≅ Seq (Projs p (Var v)) e)
End

val _ = set_fixity "needs" (Infixl 480);
Definition needs_def:
  (e needs (ps, e')) = (e ≅ Seq (Projs ps e') e)
End

Theorem needs_Var_is_demands:
  e needs (ps, Var v) ⇔ e demands (ps, v)
Proof
  rw [needs_def, demands_def] \\ fs []
QED

Theorem needs_refl:
  ∀e. e needs ([],e)
Proof
  rw [needs_def, Projs_def]
  \\ metis_tac [Seq_id, exp_eq_sym]
QED

Theorem needs_Var:
  (Var v) needs ([], Var v)
Proof
  fs [needs_refl]
QED

Theorem needs_Proj:
  e needs d ⇒ (Proj n i e) needs d
Proof
  PairCases_on ‘d’
  \\ rename1 ‘(ps, e')’
  \\ rw [needs_def, Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Proj n i e)’
  \\ conj_tac >- fs [Proj_Seq]
  \\ qabbrev_tac ‘p = Projs ps e'’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq p e) (Proj n i e)’
  \\ conj_tac
  >- (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq p (Seq e (Proj n i e))’
  \\ conj_tac >- fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl, Let_Var]
  \\ metis_tac [Proj_Seq, exp_eq_sym]
QED

Theorem needs_Projs:
  ∀ps e d. e needs d ⇒ (Projs ps e) needs d
Proof
  Induct
  >- rw [Projs_def]
  \\ gen_tac \\ rename1 ‘(hd::ps)’ \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ first_assum $ irule_at Any
  \\ irule needs_Proj
  \\ fs []
QED

Theorem needs_trans:
  e needs (ps,e') ∧ e' needs (ps',e'') ⇒ e needs (ps',e'')
Proof
  rw [needs_def]
  \\ irule exp_eq_trans
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq (Projs ps' e'') (Projs ps e')) e’
  \\ conj_tac >-
   (irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
    \\ assume_tac needs_Projs \\ metis_tac [needs_def])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Projs ps' e'') (Seq (Projs ps e') e)’
  \\ conj_tac >- fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, exp_eq_sym]
QED

Theorem needs_Projs_Var:
  (Proj s i (Var v)) needs ([(s,i)], Var v)
Proof
  rw [needs_def, Projs_def]
  \\ metis_tac [Seq_id, exp_eq_sym]
QED

Theorem needs_Seq:
  e needs d ⇒ (Seq e e') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq (Projs d0 d1) e) e'’
  \\ conj_tac >-
   (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ fs [Seq_assoc]
QED

Theorem needs_Let1:
  e needs d ∧ e' demands ([],w) ⇒ (Let w e e') needs d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def,needs_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qabbrev_tac ‘p = (Projs d0 d1)’
  \\ qexists_tac ‘Let w e (Seq (Var w) e')’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w e (Var w)) (Let w e e')’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Let w e e')’
  \\ conj_tac
  THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq p e) (Let w e e')’
  \\ conj_tac THEN1
   (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq p (Seq e (Let w e e'))’
  \\ conj_tac THEN1 fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
  \\ once_rewrite_tac [exp_eq_sym]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w e (Seq (Var w) e')’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w e (Var w)) (Let w e e')’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Let w e e')’
  \\ conj_tac THEN1
    (irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var])
  \\ fs [exp_eq_refl]
QED

Theorem needs_Let_Cons: (* expects program to be in ANF *)
  e demands ((s,LENGTH xs)::ps,w) ⇒
  (Let w (Cons s (xs ++ e'::ys)) e) needs (ps,e')
Proof
  rw [demands_def,needs_def,Projs_def]
  \\ qabbrev_tac ‘cons = (Cons s (xs ++ e'::ys))’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w cons (Seq (Projs ps (Proj s (LENGTH xs) (Var w))) e)’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Projs
  \\ fs [Projs_def]
  \\ irule exp_eq_Projs_cong \\ fs [exp_eq_refl,Let_Var]
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_Prim_cong \\ fs [PULL_EXISTS]
  \\ irule_at Any Let_Var
  \\ unabbrev_all_tac
  \\ fs [Proj_Cons]
QED

Theorem needs_Let_Proj: (* expects program to be in ANF *)
  e demands (ps,w) ⇒
  (Let w (Proj s i e') e) needs ((s,i)::ps,e')
Proof
  rw [demands_def,needs_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w (Proj s i e') (Seq (Projs ps (Var w)) e)’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w (Proj s i e') (Projs ps (Var w)))
                      (Let w (Proj s i e') e)’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w (Proj s i e') (Var w))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Theorem needs_App:
  f needs d ⇒ (App f e) needs d
Proof
  PairCases_on ‘d’ \\ rename1 ‘(ps,e')’
  \\ rw [needs_def]
  \\ qabbrev_tac ‘proj = Projs ps e'’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘App (Seq proj f) e’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ rw [exp_eq_refl])
  \\ fs [Seq_App]
QED

Theorem needs_If:
  e needs d ⇒ (If e e' e'') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ qabbrev_tac ‘p = Projs d0 d1’
  \\ irule exp_eq_trans \\ qexists_tac ‘If (Seq p e) e' e''’ \\ conj_tac
  THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def, eval_wh_Seq, eval_wh_If]
  \\ rw [] \\ fs []
QED



        (********************************************)

Theorem demands_Var:
  (Var v) demands ([],v)
Proof
  metis_tac [needs_Var_is_demands, needs_Var]
QED

Theorem demands_Proj:
  e demands d ⇒
  (Proj n i e) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Proj]
QED

Theorem demands_Projs:
  e demands d ⇒
  (Projs ps2 e) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Projs]
QED

Theorem demands_Proj_Var:
  (Proj s i (Var v)) demands ([(s,i)],v)
Proof
  rw [demands_def,Projs_def]
  \\ metis_tac [Seq_id,exp_eq_sym]
QED

Theorem demands_Seq:
  e demands d ⇒ (Seq e e') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Seq]
QED

Theorem demands_Let1:
  e demands d ∧ e' demands ([],w) ⇒ (Let w e e') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_def, needs_Var_is_demands, needs_Let1]
QED

Theorem demands_Let2:
  e' demands (p,v) ∧ v ≠ w ⇒ (Let w e e') demands (p,v)
Proof
  rw [demands_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w e (Seq (Projs p (Var v)) e')’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w e (Projs p (Var v))) (Let w e e')’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ qid_spec_tac ‘p’ \\ Induct
  THEN1 fs [Projs_def,Let_Var2]
  \\ fs [FORALL_PROD,Projs_def] \\ rw []
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ((p_1,p_2)::p') (Let w e (Var v))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var2]
QED

Theorem demands_Let_Proj: (* expects program to be in ANF *)
  e demands (ps,w) ⇒
  (Let w (Proj s i (Var v)) e) demands ((s,i)::ps,v)
Proof
  metis_tac [needs_Let_Proj, needs_Var_is_demands]
QED

Theorem demands_Let_Cons: (* expects program to be in ANF *)
  e demands ((s,LENGTH xs)::ps,w) ⇒
  (Let w (Cons s (xs ++ (Var v)::ys)) e) demands (ps,v)
Proof
  metis_tac [needs_Let_Cons, needs_Var_is_demands]
QED

Theorem demands_App:
  f demands d ⇒ (App f e) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_App, needs_Var_is_demands]
QED

Theorem demands_If:
  e demands d ⇒ (If e e' e'') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_If, needs_Var_is_demands]
QED

Definition well_formed_def:
  well_formed (Cons s) l = (s ≠ s) ∧
  well_formed (Proj s i) l = (∃ e. l = [e]) ∧
  well_formed (IsEq s i) l = (∃e. l = [e]) ∧
  well_formed If (l: exp list) = (∃e e' e''. l = e::e'::e''::[]) ∧
  well_formed Seq l = (∃e e'. l = e::e'::[]) ∧
  well_formed (AtomOp op) l = (op ≠ op)
End

Theorem exp_eq_l_refl:
  ∀l. LIST_REL $≅ l l
Proof
  Induct \\ fs [exp_eq_refl]
QED

Theorem demands_Prim:
  e demands d ∧ well_formed ope (e::l) ⇒ Prim ope (e::l) demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def]
  \\ qabbrev_tac ‘p = Projs d0 (Var d1)’
  \\ irule exp_eq_trans \\ qexists_tac ‘Prim ope ((Seq p e)::l)’
  \\ conj_tac
  >- (irule exp_eq_Prim_cong \\ fs [exp_eq_l_refl])
  \\ Cases_on ‘ope’ \\ fs [well_formed_def]
  \\ irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def, eval_wh_Seq, eval_wh_If, eval_wh_IsEq, eval_wh_Proj]
  \\ rw [] \\ fs []
QED

Theorem demands_IsEq:
  e demands d ⇒ (IsEq n i e) demands d
Proof
  strip_tac
  \\ irule demands_Prim
  \\ fs [well_formed_def]
QED

Definition is_good_def:
  is_good e = (eval_wh e ≠ wh_Error ∧ eval_wh e ≠ wh_Diverge ∧ closed e)
End

Definition can_commute_def:
  can_commute  e e' = ∀f.
                           ¬ (eval_wh (subst f e) = wh_Diverge ∧ eval_wh (subst f e') = wh_Error) ∧
                           ¬ (eval_wh (subst f e) = wh_Error ∧ eval_wh (subst f e') = wh_Diverge)
End

Theorem can_commute_sym:
  can_commute e e' ⇒ can_commute e' e
Proof
  metis_tac [can_commute_def]
QED

Theorem can_commute_Seq_com:
  ∀e e'. can_commute e e' ⇒ ∀e''. Seq (Seq e e') e'' ≅ Seq (Seq e' e) e''
Proof
  rw [can_commute_def]
  \\ irule eval_wh_IMP_exp_eq
  \\ gen_tac
  \\ ‘eval_wh (subst f e) = wh_Diverge ∨ eval_wh (subst f e) = wh_Error ∨ (eval_wh (subst f e) ≠ wh_Diverge ∧ eval_wh (subst f e) ≠ wh_Error)’ by rw [DISJ_EQ_IMP]
  \\ ‘eval_wh (subst f e') = wh_Diverge ∨ eval_wh (subst f e') = wh_Error ∨ (eval_wh (subst f e') ≠ wh_Diverge ∧ eval_wh (subst f e') ≠ wh_Error)’ by rw [DISJ_EQ_IMP]
  \\ rw [subst_def, eval_wh_Seq]
  \\ fs []
  \\ metis_tac []
QED

Theorem is_good_means_can_commute:
  ∀e e'. is_good e ⇒ can_commute e e'
Proof
  fs [is_good_def, can_commute_def]
QED

Theorem demands_Seq_com:
  ∀e e'. is_good e ∨ is_good e' ⇒ ∀e''. Seq (Seq e e') e'' ≅ Seq (Seq e' e) e''
Proof
  rw [is_good_means_can_commute]
  \\ irule can_commute_Seq_com
  \\ fs [is_good_means_can_commute, can_commute_sym]
QED

Theorem needs_Seq2:
  (can_commute e (Projs ps e'')) ∧ e' needs (ps, e'')
  ⇒ (Seq e e') needs (ps, e'')
Proof
  rw [DISJ_EQ_IMP]
  \\ fs [needs_def, Projs_def]
  \\ qabbrev_tac ‘p = Projs ps e''’
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq e (Seq p e')’
  \\ conj_tac
  >- (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Seq e p) e'’
  \\ conj_tac
  >- (‘Seq (Seq e p) e' ≅ Seq e (Seq p e')’ by fs [Seq_assoc]
      \\ fs [exp_eq_sym])
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Seq p e) e'’
  \\ fs [Seq_assoc]
  \\ irule can_commute_Seq_com
  \\ fs [DISJ_EQ_IMP]
QED

Theorem demands_Seq2:
  is_good e ∧ e' demands (ps, v)
   ⇒ (Seq e e') demands (ps, v)
Proof
  metis_tac [is_good_means_can_commute,needs_Var_is_demands, needs_Seq2]
QED

Theorem needs_If2_no_Diverge:
  (∀f. eval_wh (subst f ce) ≠ wh_Diverge ∧ eval_wh (subst f e) ≠ wh_Diverge)
  ∧ te ≅ Seq e te' ∧ ee ≅ Seq e ee'
  ⇒ If ce te ee ≅ Seq e (If ce te' ee')
Proof
  rw []
  \\ irule exp_eq_trans
  \\ qexists_tac ‘If ce (Seq e te') (Seq e ee')’
  \\ conj_tac
  >- (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_Seq, eval_wh_If]
  \\ fs []
QED

Theorem needs_If2:
  ((is_good ce ∧ (eval_wh ce = wh_True ∨ eval_wh ce = wh_False)) ∨ is_good e') ∧ te needs ([], e') ∧ ee needs ([], e') ⇒ (If ce te ee) needs ([], e')
Proof
  rw [is_good_def, needs_def, Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘If ce (Seq e' te) (Seq e' ee)’
  \\ conj_tac
  \\ TRY (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_Seq, eval_wh_If]
  \\ fs []
QED

(*
Definition fun_demands2_def:
  f fun_demands (ps,(k:num),(n:num)) ⇒ ∀l hd v. LENGTH l = n ∧ LENGTH hd = k ∧ (l = hd++v::tl) ⇒ Apps f (MAP Var l) demands ([],v)
End
*)
Definition fun_demands_pre_def:
  fun_demands_pre (k:num) f ps = if k = 0
                        then ∀n. n ∉ freevars f ⇒ (App f (Var n)) demands (ps, n)
                        else ∀e. fun_demands_pre (k - 1) (App f e) ps
End

val _ = set_fixity "fun_demands" (Infixl 478);

Definition fun_demands_def:
  f fun_demands (ps, k) = fun_demands_pre k f ps
End
(*
Theorem Let_Var_eq:
  ∀e v. Let v (Var v) e ≅ e
Proof
  Induct \\ rw []
  THEN1 (qsuff_tac ‘v = s ∨ v ≠ s’
         THEN1 (DISCH_TAC \\ pop_assum DISJ_CASES_TAC
                THEN1 (rw [] \\ fs [Let_Var])
                \\ fs [Let_Var2])
         \\ rw [])
  THEN1 (irule exp_eq_trans \\ qexists_tac ‘Prim o' (MAP (Let v (Var v)) l)’
         \\ conj_tac
         THEN1 fs [Let_Prim]
QED
*)
(*
Theorem fun_demands_Lam:
  e demands (ps, v) ⇒ (Lam v e) fun_demands (ps, 0)
Proof
  rw [fun_demands_def, fun_demands_pre_def, demands_def]
  \\ irule exp_eq_trans
  THEN1 (qexists_tac ‘Let v (Var n) (Seq (Projs ps (Var v)) e)’
         \\ conj_tac
         THEN1 (irule exp_eq_App_cong \\ fs [exp_eq_refl]
                \\ irule exp_eq_Lam_cong \\ fs [])
         \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Let v (Var n) (Projs ps (Var v))) (Let v (Var n) e)’
         \\ conj_tac
         THEN1 fs [Let_Seq]
         \\ irule exp_eq_Prim_cong
         \\ fs [exp_eq_refl]
         \\ irule exp_eq_trans \\ qexists_tac ‘Projs ps (Let v (Var n) (Var v))’
         \\ conj_tac
         THEN1 fs [Let_Projs]
         \\ irule exp_eq_Projs_cong \\ fs [Let_Var])
  \\ qexists_tac ‘e’ \\ conj_tac
  THEN1 fs [Let_Var_eq]
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Projs ps (Var n)) e’
  THEN1 fs []
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
QED

Theorem fun_demands_Let:
  ∀f. (f fun_demands (ps, k) ⇒ ∀e v. (App (Lam v f) e) fun_demands (ps, k))
Proof
  rw [fun_demands_def, Once fun_demands_pre_def, demands_def]
  THEN1 (rw [fun_demands_pre_def]
   \\ rw [demands_def]
   \\ irule exp_eq_trans \\ qexists_tac ‘Let v e (App f (Var n))’
   \\ conj_tac
   THEN1 (irule exp_eq_trans \\ qexists_tac ‘App (Let v e f) (Let v e (Var n))’
    \\ conj_tac
    THEN1 (irule exp_eq_App_cong \\ fs [exp_eq_refl])
*)

Datatype:
  ctxt = Nil
       | IsFree string ctxt
       | Bind bool string exp ctxt ctxt
       | RecBind ((string # exp) list) ctxt
End

Definition ctxt_size_def:
  ctxt_size Nil = 0n ∧
  ctxt_size (IsFree s ctxt) = 1 + ctxt_size ctxt ∧
  ctxt_size (Bind b s e ctxt tl) = 1 + list_size char_size s +  exp_size e + ctxt_size ctxt + ctxt_size tl ∧
  ctxt_size (RecBind sel ctxt) = 1 + exp1_size sel + ctxt_size ctxt
End

Definition subst_ctxt_def:
  (subst_ctxt ctxt (App f e) = App (subst_ctxt ctxt f) (subst_ctxt ctxt e)) ∧
  (subst_ctxt  ctxt (Prim op l) = Prim op (MAP (subst_ctxt ctxt) l)) ∧
  (subst_ctxt ctxt (Lam v e) = Lam v (subst_ctxt (IsFree v ctxt) e)) ∧
  (subst_ctxt Nil (Var n) = Var n) ∧
  (subst_ctxt (IsFree v ctxt) (Var n) = if n = v
                                        then Var n
                                        else subst_ctxt ctxt (Var n)) ∧
  (subst_ctxt (Bind b v exp ctxt tl) (Var n) = if n = v
                                         then subst_ctxt ctxt exp
                                         else subst_ctxt tl (Var n)) ∧
  (subst_ctxt (RecBind nel ctxt) (Var n) = if MEM n (MAP FST nel)
                                                then Var n
                                                else subst_ctxt ctxt (Var n)) ∧
  (subst_ctxt ctxt (Letrec nel e) = Letrec nel (subst_ctxt (RecBind nel ctxt) e))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ(c,e).(exp_size e + ctxt_size c, exp_size e))’
  \\ rw [ctxt_size_def] \\ fs []
End

Definition good_context_def:
  good_context Nil = T ∧
  good_context (IsFree s ctxt) = good_context ctxt ∧
  good_context (RecBind sel ctxt) = good_context ctxt ∧
  good_context (Bind F s e ctxt tl) = good_context tl ∧
  good_context (Bind T s e ctxt tl) = (∀f. eval_wh (subst f (subst_ctxt ctxt e)) ≠ wh_Diverge ∧ good_context tl)
End

Definition well_written_def:
  well_written (Cons s) l = T ∧
  well_written (Proj s i) [e] = T ∧
  well_written (IsEq s i) [e] = T ∧
  well_written If [e; e'; e''] = T ∧
  well_written Seq [e; e'] = T ∧
  well_written (AtomOp op) l = T ∧
  well_written _ _ = F
End

Inductive find: (* i i o o o *)
[find_Bottom:]
  (∀e (c:ctxt).
    find e c {} e F) ∧
[find_Seq:]
  (∀e e' c (p:(string#num) list) ds v b.
    find e c ds e' b ∧ (p,v) ∈ ds ⇒
    find e c ds (Seq (Var v) e') b) ∧
[find_Seq2:]
  (∀e e' e2 e2' c ds ds2 b b2.
     find e c ds e' b ∧ find e2 c ds2 e2' b2 ⇒
     find (Seq e e2) c ds (Seq e' e2') (b ∧ b2)) ∧
[find_If:]
  (∀ec et ee ec' et' ee' c dsc dst dse bc bt be.
     find ec c dsc ec' bc ∧
     find et c dst et' bt ∧
     find ee c dse ee' be ⇒
     find (If ec et ee) c dsc (If ec' et' ee') (bc ∧ bt ∧ be)) ∧
[find_Var:]
  (∀n c. find (Var n) c {([],n)} (Var n) F) ∧
[find_App:]
  (∀f f' e e' c ds ds2 b b2.
     find f c ds f' b ∧
     find e c ds2 e' b2 ⇒
     find (App f e) c ds (App f' e') F) ∧
[find_Prim:]
  (∀c el el' ope.
     LENGTH el = LENGTH el' ∧ (∀k. k < LENGTH el ⇒ ∃ds b. find (EL k el) c ds (EL k el') b)
     ⇒ find (Prim ope el) c {} (Prim ope el') F) ∧
[find_Prim1:]
  (∀c el el' ope ds b.
     LENGTH el = LENGTH el' ∧
     (∀k. k < LENGTH el ⇒ ∃ds' b'. find (EL k el) c ds' (EL k el') b')
     ∧ find (EL 0 el) c ds (EL 0 el') b ∧ el ≠ [] ∧ well_formed ope el ⇒ find (Prim ope el) c ds (Prim ope el') F) ∧
[find_Prim_Fail:]
  (∀c el ope.
     ¬ (well_written ope el) ⇒ find (Prim ope el) c {} Fail T) ∧
[find_Proj:]
  (∀e e' n i c ds b.
     find e c ds e' b ⇒ find (Proj n i e) c ds (Proj n i e') F) ∧
[find_IsEq:]
  (∀e e' n i c ds b.
     find e c ds e' b ⇒ find (IsEq n i e) c ds (IsEq n i e') b) ∧
[find_Subset:]
  (∀e e' c ds ds' b.
     find e c ds e' b ∧ (∀ps v. (ps, v) ∈ ds' ⇒ ∃ps'. (ps++ps', v) ∈ ds) ⇒ find e c ds' e' b) ∧
[find_Let:]
  (∀e e' e2 e2' ds ds' c v b b2.
     find e c ds e' b ∧ find e2 (Bind b v e c c) ds' e2' b2
     ∧ (∀ps. (ps, v) ∉ ds')
     ⇒ find (Let v e e2) c ds' (Let v e' e2') (b ∧ b2)) ∧
[find_Let2:]
  (∀ e e' e2 e2' ds ds' ds'' c v ps b b2.
     find e c ds e' b ∧ find e2 (Bind b v e c c) ds' e2' b2
     ∧ (ps,v) ∈ ds'
     ∧ (∀ps' v'. (ps', v') ∈ ds'' ⇒ ((ps', v') ∈ ds' ∧ v' ≠ v) ∨ (ps', v') ∈ ds)
     ⇒ find (Let v e e2) c ds'' (Let v e' e2') (b ∧ b2)) ∧
[find_Lam:]
  (∀e e' c ds v b.
     find e c ds e' b ⇒ find (Lam v e) c {} (Lam v e') T)
End

Theorem needs_projs_reduce:
  e needs (ps ++ ps', e') ⇒ e needs (ps, e')
Proof
  rw [needs_def, double_Projs]
  \\ qabbrev_tac ‘p = Projs ps e'’
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Seq p (Projs ps' p)) e’
  \\ conj_tac
  >- (irule exp_eq_trans \\ first_assum $ irule_at Any
      \\ irule exp_eq_Prim_cong
      \\ fs [exp_eq_refl]
      \\ ‘p needs ([], p)’ by fs [needs_refl]
      \\ drule needs_Projs
      \\ rw [needs_def, Projs_def])
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq p (Seq (Projs ps' p) e)’
  \\ fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, exp_eq_sym]
QED

Theorem demands_Projs_empty:
  ∀ps v. (Projs ps (Var v)) demands ([], v)
Proof
  Induct \\ rw [demands_def, Projs_def]
  THEN1 (irule eval_wh_IMP_exp_eq
         \\ fs [subst_def, eval_wh_Seq]
         \\ rw [] \\ fs [])
  \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ irule exp_eq_trans \\ qexists_tac ‘Projs ps (Seq (Var v) (Proj hd0 hd1 (Var v)))’
  \\ conj_tac
  THEN1 (irule exp_eq_Projs_cong
         \\ ‘(Proj hd0 hd1 (Var v)) demands ([], v)’
           by (irule demands_Proj \\ fs [demands_Var])
         \\ fs [demands_def, Projs_def])
  \\ fs [Projs_Seq]
QED

Theorem demands_empty_proj:
  e demands (ps, v) ⇒ e demands ([], v)
Proof
  ‘ps = [] ++ ps’ by rw []
  \\ rw []
  \\ metis_tac [needs_projs_reduce, needs_Var_is_demands]
QED

Theorem demands_projs_reduce:
  e demands (ps ++ ps', v) ⇒ e demands (ps, v)
Proof
  metis_tac [needs_projs_reduce, needs_Var_is_demands]
QED

Theorem subst_ctxt_ind_bool:
  ∀e2 c v e. subst_ctxt (Bind F v e c c) e2 = subst_ctxt (Bind T v e c c) e2
Proof
  Induct using freevars_ind
  \\ fs [subst_ctxt_def]
  \\ cheat
QED

Theorem subst_ctxt_soundness:
  ∀v f c e e2.
    subst1 v (subst f (subst_ctxt c e)) (subst (f \\ v) (subst_ctxt (IsFree v c) e2))
    = subst f (subst_ctxt (Bind F v e c c) e2)
Proof
  cheat
QED

Theorem find_soundness_lemma:
  ∀e c ds e' b. good_context c ∧ find e c ds e' b  ⇒ e ≅ e' ∧ (∀d. d ∈ ds ⇒ e demands d) ∧ (b ⇒ ∀f. eval_wh (subst f (subst_ctxt c e)) ≠ wh_Diverge)
Proof
  Induct_on ‘find’
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- fs [exp_eq_refl] (* find_Bottom *)
  >- (strip_tac (* find_Seq *)
      \\ strip_tac
      \\ fs []
      \\ first_x_assum $ drule
      \\ rw []
      \\ dxrule_then assume_tac demands_empty_proj
      \\ fs [demands_def, Projs_def]
      \\ irule exp_eq_trans
      \\ first_assum $ irule_at Any
      \\ irule exp_eq_Prim_cong
      \\ fs [exp_eq_refl])
  >- (strip_tac (* find_Seq2 *)
      \\ strip_tac
      \\ conj_tac
      >- fs [exp_eq_Prim_cong]
      \\ rw []
      >- (irule demands_Seq
          \\ fs [])
      \\ rw [subst_def, eval_wh_Seq, subst_ctxt_def])
  >- (strip_tac (* find_If *)
      \\ strip_tac
      \\ conj_tac
      >- fs [exp_eq_Prim_cong]
      \\ rw []
      >- (irule demands_If
          \\ fs [])
      \\ rw [eval_wh_If, subst_def, subst_ctxt_def])
  >- (fs [exp_eq_refl] (* find_Var *)
      \\ fs [demands_Var])
  >- (strip_tac (* find_App *)
      \\ strip_tac
      \\ fs [exp_eq_App_cong]
      \\ rw []
      \\ fs [demands_App])
  >- (strip_tac (* find_Prim *)
      \\ strip_tac
      \\ fs []
      \\ irule exp_eq_Prim_cong
      \\ rw [LIST_REL_EL_EQN, EL_MAP]
      \\ ‘n < LENGTH el'’ by fs []
      \\ first_x_assum drule
      \\ rw [])
  >- (strip_tac (* find_Prim1 *)
      \\ strip_tac
      \\ conj_tac
      >- (irule exp_eq_Prim_cong
          \\ rw [LIST_REL_EL_EQN, EL_MAP]
          \\ rename1 ‘LENGTH el1 = LENGTH el2’
          \\ ‘n < LENGTH el1’ by fs []
          \\ first_x_assum drule
          \\ first_x_assum drule
          \\ rw []
          \\ fs [])
      \\ rw []
      \\ last_x_assum dxrule
      \\ rw []
      \\ rename1 ‘Prim ope el1’
      \\ Cases_on ‘el1’
      \\ fs []
      \\ irule demands_Prim
      \\ fs [])
  >- (Cases_on ‘ope’ (* find_Prim_Fail *)
      \\ rw [well_written_def]
      \\ Cases_on ‘el'’
      \\ fs [exp_eq_refl, eval_wh_Fail] >>~ [‘Prim _ [] ≅ Fail’]
      >- (irule eval_wh_IMP_exp_eq
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (irule eval_wh_IMP_exp_eq
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (irule eval_wh_IMP_exp_eq
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >>~ [‘eval_wh (subst _ (subst_ctxt c (Prim _ []))) ≠ wh_Diverge’]
      >- (irule $ iffRL eval_wh_neq_Diverge
          \\ rw [eval_wh_def, subst_ctxt_def, eval_wh_to_def])
      >- (irule $ iffRL eval_wh_neq_Diverge
          \\ rw [eval_wh_def, subst_ctxt_def, eval_wh_to_def])
      >- (irule $ iffRL eval_wh_neq_Diverge
          \\ rw [eval_wh_def, subst_ctxt_def, eval_wh_to_def])
      >- (irule $ iffRL eval_wh_neq_Diverge
          \\ rw [eval_wh_def, subst_ctxt_def, eval_wh_to_def])
      \\ rename1 ‘hd::tl’
      \\ Cases_on ‘tl’
      \\ fs [well_written_def] >>~ [‘Prim _ (h0::h1::tl)’]
      >- (Cases_on ‘tl’ (* If ≅ *)
          >- (irule eval_wh_IMP_exp_eq
              \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
          \\ rename1 ‘h0::h1::h2::tl’
          \\ Cases_on ‘tl’
          \\ fs [well_written_def]
          \\ irule eval_wh_IMP_exp_eq
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (Cases_on ‘tl’ (* If ≠ *) >~ [‘h0::h2::h3::tl’]
          >- (Cases_on ‘tl’
              \\ fs [well_written_def]
              \\ irule $ iffRL eval_wh_neq_Diverge
              \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
          \\ irule $ iffRL eval_wh_neq_Diverge
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      \\ fs []
      >- (irule eval_wh_IMP_exp_eq
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (irule $ iffRL eval_wh_neq_Diverge
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (irule eval_wh_IMP_exp_eq
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (irule $ iffRL eval_wh_neq_Diverge
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (Cases_on ‘tl’ (* Seq ≅ *)
          \\ fs [well_written_def]
          \\ irule eval_wh_IMP_exp_eq
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (Cases_on ‘tl’ (* Seq ≠ *)
          \\ fs [well_written_def]
          \\ irule $ iffRL eval_wh_neq_Diverge
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (irule eval_wh_IMP_exp_eq
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (irule $ iffRL eval_wh_neq_Diverge
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (irule eval_wh_IMP_exp_eq
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def])
      >- (irule $ iffRL eval_wh_neq_Diverge
          \\ rw [subst_def, subst_ctxt_def, eval_wh_def, eval_wh_to_def]))
   >- (strip_tac (* find_Proj *)
      \\ fs [exp_eq_Prim_cong]
      \\ rw []
      >- (irule demands_Proj
          \\ fs [])
       \\ fs [])
  >- (strip_tac (* find_IsEq *)
      \\ strip_tac
      \\ fs [exp_eq_Prim_cong]
      \\ rw []
      >- (irule demands_IsEq
          \\ fs [])
      \\ rw [subst_def, subst_ctxt_def, eval_wh_IsEq]
      \\ qabbrev_tac ‘p = eval_wh (subst f (subst_ctxt c e))’
      \\ Cases_on ‘p’
      \\ fs []
      >- (rename1 ‘if v ≠ w then _ else if i = LENGTH l then _ else _’
          \\ ‘v = w ∨ v ≠ w’ by fs []
          \\ fs []
          \\ ‘i = LENGTH l ∨ i ≠ LENGTH l’ by fs []
          \\ fs [])
      \\ first_x_assum irule
      \\ first_x_assum $ irule_at Any)
  >- (strip_tac (* find_Subset *)
      \\ strip_tac
      \\ fs []
      \\ rw []
      \\ rename1 ‘e demands d’ \\ PairCases_on ‘d’
      \\ first_x_assum drule
      \\ rw []
      \\ first_x_assum drule
      \\ rw []
      \\ drule demands_projs_reduce
      \\ fs [])
  >- (strip_tac (* find_Let *)
      \\ strip_tac
      \\ rename1 ‘Bind b v e c c’
      \\ ‘good_context (Bind b v e c c)’ by
        (Cases_on ‘b’
         \\ fs [good_context_def])
      \\ conj_tac
      >- (irule exp_eq_App_cong
          \\ fs [exp_eq_Lam_cong])
      \\ rw []
      >- (PairCases_on ‘d’
          \\ irule demands_Let2
          \\ ‘d1 = v ∨ d1 ≠ v’ by fs []
          \\ fs []
          \\ ‘(d0, v) ∉ ds'’ by (first_x_assum $ irule_at Any))
      \\ rw [subst_def, subst_ctxt_def, eval_wh_App, eval_wh_Lam, bind_def]
      \\ fs []
      >- rw [subst_ctxt_soundness, subst_ctxt_ind_bool]
      \\ fs [eval_wh_Fail])
  >- (strip_tac (* find_Let2 *)
      \\ strip_tac
      \\ rename1 ‘Bind b v e c c’
      \\ ‘good_context (Bind b v e c c)’ by
        (Cases_on ‘b’
         \\ fs [good_context_def])
      \\ conj_tac
      >- (irule exp_eq_App_cong
          \\ fs [exp_eq_Lam_cong])
      \\ rw []
      >- (PairCases_on ‘d’
          \\ first_x_assum drule
          \\ rw []
          >- (irule demands_Let2
              \\ fs [])
          \\ irule demands_Let1
          \\ fs []
          \\ first_x_assum drule
          \\ rw []
          \\ drule demands_empty_proj
          \\ fs [])
      \\ rw [subst_def, subst_ctxt_def, eval_wh_App, eval_wh_Lam, bind_def]
      \\ fs []
      >- rw [subst_ctxt_soundness, subst_ctxt_ind_bool]
      \\ fs [eval_wh_Fail])
  >- (strip_tac
      \\ strip_tac
      \\ fs [exp_eq_Lam_cong]
      \\ gen_tac
      \\ rw [subst_def, eval_wh_Lam, subst_ctxt_def])
QED

Theorem find_soundness:
  find e Nil ds e' b ⇒ e ≅ e'
Proof
  rw []
  \\ ‘good_context Nil’ by fs [good_context_def]
  \\ dxrule find_soundness_lemma
  \\ rw []
  \\ first_x_assum dxrule
  \\ fs []
QED

Datatype:
  demands_tree = DemandNode bool (((string # num) # demands_tree) list)
End

Definition dt_to_set_def:
  dt_to_set (DemandNode T []) ps v = {(ps,v)} ∧
  dt_to_set (DemandNode F []) ps v = {} ∧
  dt_to_set (DemandNode b ((p, dt)::tl)) ps v = (dt_to_set dt (ps ++ [p]) v) ∪ (dt_to_set (DemandNode b tl) ps v)
End

Definition merge_dt_def:
  merge_dt (DemandNode b1 f1) (DemandNode b2 []) = DemandNode (b1 ∨ b2) f1 ∧
  merge_dt (DemandNode b1 []) (DemandNode b2 f2) = DemandNode (b1 ∨ b2) f2 ∧
  merge_dt (DemandNode b1 ((id1,dt1)::tl1)) (DemandNode b2 ((id2,dt2)::tl2)) =
  if id1 = id2
  then
    case merge_dt (DemandNode b1 tl1) (DemandNode b2 tl2) of
    | DemandNode b3 tl3 => DemandNode b3 ((id1, merge_dt dt1 dt2)::tl3) (* id1 = id2 *)
  else
    if FST id1 < FST id2 ∨ (FST id1 = FST id2 ∧ SND id1 < SND id2)
    then
      case merge_dt (DemandNode b1 tl1) (DemandNode b2 ((id2,dt2)::tl2)) of
      | DemandNode b3 tl3 => DemandNode b3 ((id1, dt1)::tl3) (* id1 < id2 *)
    else
      case merge_dt (DemandNode b1 ((id1,dt1)::tl1)) (DemandNode b2 tl2) of
      | DemandNode b3 tl3 => DemandNode b3 ((id2, dt2)::tl3) (* id2 < id1 *)
End

Definition find_function_def:
  find_function (Var v) c = ((FEMPTY : (string |-> demands_tree)) |+ (v, DemandNode T []), Var v, F) ∧
  (find_function (If ce te ee) c =
   let (cd, ce', b1) = find_function ce c in
     let (td, te', b2) = find_function te c in
       let (ed, ee', b3) = find_function ee c in
         (cd, If ce' te' ee', b1 ∧ b2 ∧ b3)) ∧
  (find_function (Prim If _) c = (FEMPTY, Fail, T)) ∧
  (find_function (Proj s i e) c =
   let (d, e', b) = find_function e c in
     (d, Proj s i e', F)) ∧
  (find_function (Prim (Proj s i) _) c = (FEMPTY, Fail, T)) ∧
  (find_function (IsEq s i e) c =
   let (d, e', b) = find_function e c in
     (d, IsEq s i e', b)) ∧
  (find_function (Prim (IsEq s i) _) c = (FEMPTY, Fail, T)) ∧
  (find_function (Seq e1 e2) c =
   let (d1, e1', b1) = find_function e1 c in
     let (d2, e2', b2) = find_function e2 c in
       (d1, Seq e1' e2', b1 ∧ b2)) ∧
  (find_function (Prim Seq _) c = (FEMPTY, Fail, T)) ∧
  (find_function (Prim op l) c: ((string |-> demands_tree) # exp # bool)) =
  (FEMPTY, Prim op (MAP (λe. (FST o SND) (find_function e c)) l), F) ∧
  (find_function (App (Lam v e2) e) c = let (d, e', b1) = find_function e c in
                                          let (d2, e2', b2) = find_function e2 (Bind b1 v e c c) in
                                           case FLOOKUP d2 v of
                                             | NONE => (d2, App (Lam v e2') e', b1 ∧ b2)
                                             | SOME s => (FMERGE merge_dt d (d2 \\ v), Let v e' (Seq (Var v) e2'), b1 ∧ b2)) ∧
  (find_function (App f e) c = let (d, f', _) = find_function f c in
                                 let (_, e', _) = find_function e c in
                                   (d, App f' e', F)) ∧
  find_function e c = ((FEMPTY, e, F) : (string |-> demands_tree) # exp # bool)
Termination
  WF_REL_TAC ‘measure (exp_size o FST)’
  \\ rw [] \\ fs []
  \\ assume_tac exp_size_lemma
  \\ fs []
  \\ first_x_assum dxrule
  \\ fs []
End

Theorem exp_size_cmp_exp3_size:
  ∀l e. MEM e l ⇒ exp_size e < exp3_size l
Proof
  fs [exp_size_lemma]
QED

Definition demands_tree_size_def:
  demands_tree_size (DemandNode b []) = 1 ∧
  demands_tree_size (DemandNode b ((v,dt)::tl)) = 1 + demands_tree_size dt + demands_tree_size (DemandNode b tl)
End

Theorem dt_to_set_union:
  ∀l b p v. dt_to_set (DemandNode T l) p v = {(p, v)} ∪ dt_to_set (DemandNode b l) p v
Proof
  Induct
  \\ rw [dt_to_set_def]
  >- (rename1 ‘DemandNode b []’
      \\ Cases_on ‘b’
      \\ rw [dt_to_set_def])
  \\ rename1 ‘DemandNode b (hd::tl)’
  \\ Cases_on ‘hd’
  \\ rw [dt_to_set_def]
  \\ metis_tac [UNION_COMM, UNION_ASSOC]
QED

Theorem merge_dt_is_set_union:
  ∀dt1 dt2 p v. dt_to_set (merge_dt dt1 dt2) p v = (dt_to_set dt1 p v) ∪ (dt_to_set dt2 p v)
Proof
  Induct using demands_tree_size_ind
  >- (Cases
      \\ Cases
      \\ rename1 ‘DemandNode b2 l’
      \\ Cases_on ‘b2’
      \\ Cases_on ‘l’
      \\ rw [merge_dt_def, dt_to_set_def]
      \\ fs [dt_to_set_union])
  \\ Induct using demands_tree_size_ind
  >- (rpt gen_tac
      \\ rename1 ‘DemandNode b2 []’
      \\ Cases_on ‘b2’
      \\ rw [dt_to_set_def, merge_dt_def]
      \\ metis_tac [dt_to_set_union, UNION_COMM, UNION_ASSOC])
  \\ rpt gen_tac
  \\ rename1 ‘merge_dt (DemandNode b1 ((v1,dt1)::tl1)) (DemandNode b2 ((v2,dt2)::tl2))’
  \\ rw [merge_dt_def]
  >- (qabbrev_tac ‘dt3 = merge_dt (DemandNode b1 tl1) (DemandNode b2 tl2)’
      \\ Cases_on ‘dt3’
      \\ rw [dt_to_set_def]
      \\ unabbrev_all_tac
      \\ metis_tac [UNION_COMM, UNION_ASSOC])
  >- (qabbrev_tac ‘dt3 = merge_dt (DemandNode b1 tl1) (DemandNode b2 ((v2,dt2)::tl2))’
      \\ Cases_on ‘dt3’
      \\ rw [dt_to_set_def]
      \\ unabbrev_all_tac
      \\ metis_tac [UNION_COMM, UNION_ASSOC, dt_to_set_def])
  >- (qabbrev_tac ‘dt3 = merge_dt (DemandNode b1 tl1) (DemandNode b2 ((v2,dt2)::tl2))’
      \\ Cases_on ‘dt3’
      \\ rw [dt_to_set_def]
      \\ unabbrev_all_tac
      \\ metis_tac [UNION_COMM, UNION_ASSOC, dt_to_set_def])
  \\ qabbrev_tac ‘dt3 = merge_dt (DemandNode b1 ((v1, dt1)::tl1)) (DemandNode b2 tl2)’
  \\ Cases_on ‘dt3’
  \\ rw [dt_to_set_def]
  \\ unabbrev_all_tac
  \\ metis_tac [UNION_COMM, UNION_ASSOC]
QED

Theorem find_function_soundness_lemma:
  ∀k e c d e' b.
    exp_size e < k ⇒
    find_function e c = (d, e', b) ⇒
    ∃ds. find e c ds e' b ∧
         (∀s ps. (ps, s) ∈ ds ⇒ ∃dt. FLOOKUP d s = SOME dt ∧ (ps, s) ∈ dt_to_set dt [] s) ∧
         (∀s. s ∈ FDOM d ⇒ ∃ps. (ps, s) ∈ ds)
Proof
  Induct
  \\ gen_tac \\ Cases_on ‘e’
  \\ fs [exp_size_def]
  >- (rw [find_function_def] (* Var v *)
      \\ rename1 ‘(v, DemandNode T [])’
      \\ qexists_tac ‘{([], v)}’
      \\ fs [find_Var]
      \\ qexists_tac ‘DemandNode T []’
      \\ rw [dt_to_set_def, FLOOKUP_UPDATE])
  >- (rw [] (* Prim op l *)
      \\ rename1 ‘Prim op es’
      \\ Cases_on ‘es’
      >- (Cases_on ‘op’ (* Prim op [] *)
          \\ fs [find_function_def]
          \\ qexists_tac ‘{}’
          \\ fs [find_Bottom]
          \\ irule find_Prim_Fail
          \\ fs [well_written_def])
      \\ rename1 ‘h::t’
      \\ Cases_on ‘op’ >~[‘Prim (Cons s) (h::tl)’]
      >- (fs [find_function_def]
          \\ qabbrev_tac ‘es = h::tl’
          \\ qexists_tac ‘{}’
          \\ fs []
          \\ rw []
          \\ irule find_Prim
          \\ rw [] >~[‘LENGTH _ = _’] >- (unabbrev_all_tac \\ fs [])
          \\ rename1 ‘EL k' es’
          \\ ‘exp_size (EL k' es) < k’ by
            (‘exp_size (EL k' es) < exp3_size es’ by
               (irule exp_size_cmp_exp3_size
                \\ fs [MEM_EL]
                \\ qexists_tac ‘k'’
                \\ fs []
                \\ unabbrev_all_tac
                \\ fs [])
             \\ fs [])
          \\ first_x_assum dxrule
          \\ qabbrev_tac ‘de = find_function (EL k' es) c’
          \\ PairCases_on ‘de’
          \\ rw []
          \\ ‘de1 = EL k' (MAP (λe. FST (SND (find_function e c))) es)’ by
            fs [EL_MAP]
          \\ fs[]
          \\ unabbrev_all_tac
          \\ fs []
          \\ first_x_assum drule
          \\ rw []
          \\ first_x_assum $ irule_at Any)
      >- (Cases_on ‘t’
          >- (fs [find_function_def] (* Prim If [e] *)
              \\ qexists_tac ‘{}’
              \\ fs []
              \\ rw []
              \\ fs [find_Prim_Fail, well_written_def])
          \\ rename1 ‘h::h1::t’
          \\ Cases_on ‘t’
          >- (fs [find_function_def] (* Prim If [e, e'] *)
              \\ qexists_tac ‘{}’
              \\ rw []
              \\ fs [find_Prim_Fail, well_written_def])
          \\ rename1 ‘ce::te::ee::t’
          \\ Cases_on ‘t’
          >- (fs [find_function_def] (* If _ _ _ *)
              \\ qabbrev_tac ‘ce' = find_function ce c’ \\ PairCases_on ‘ce'’
              \\ qabbrev_tac ‘te' = find_function te c’ \\ PairCases_on ‘te'’
              \\ qabbrev_tac ‘ee' = find_function ee c’ \\ PairCases_on ‘ee'’
              \\ fs []
              \\ ‘exp_size ce < k’ by fs [exp_size_def]
              \\ first_assum dxrule
              \\ ‘exp_size te < k’ by fs [exp_size_def]
              \\ first_assum dxrule
              \\ ‘exp_size ee < k’ by fs [exp_size_def]
              \\ first_x_assum dxrule
              \\ rw []
              \\ first_x_assum dxrule
              \\ rw []
              \\ rename1 ‘find ce c ds ce'1’
              \\ first_x_assum dxrule
              \\ first_x_assum dxrule
              \\ rw []
              \\ qexists_tac ‘ds’
              \\ fs []
              \\ irule find_If
              \\ fs []
              \\ conj_tac
              \\ first_x_assum $ irule_at Any)
          \\ fs [find_function_def]
          \\ qexists_tac ‘{}’
          \\ rw []
          \\ fs [find_Prim_Fail, well_written_def])
      >- (Cases_on ‘t’ (* IsEq *)
          \\ fs [find_function_def]
          >- (qabbrev_tac ‘ff = find_function h c’
              \\ PairCases_on ‘ff’
              \\ ‘exp_size h < k’ by fs [exp_size_def]
              \\ first_x_assum dxrule
              \\ rw []
              \\ fs []
              \\ first_x_assum drule
              \\ rw []
              \\ qexists_tac ‘ds’
              \\ fs []
              \\ fs [find_IsEq])
          \\ qexists_tac ‘{}’
          \\ fs [find_Prim_Fail, well_written_def])
      >- (Cases_on ‘t’ (* Proj *)
          \\ fs [find_function_def]
          >- (qabbrev_tac ‘ff = find_function h c’
              \\ PairCases_on ‘ff’
              \\ ‘exp_size h < k’ by fs [exp_size_def]
              \\ first_x_assum dxrule
              \\ rw []
              \\ fs []
              \\ first_x_assum drule
              \\ rw []
              \\ qexists_tac ‘ds’
              \\ fs []
              \\ irule find_Proj
              \\ first_assum $ irule_at Any)
          \\ qexists_tac ‘{}’
          \\ fs [find_Prim_Fail, well_written_def])
      >- (qabbrev_tac ‘l = h::t’ (* AtomOp *)
         \\ qexists_tac ‘{}’
         \\ fs [find_function_def]
         \\ rw []
         \\ irule find_Prim
         \\ rw []
         \\ rename1 ‘n < LENGTH l’
         \\ ‘exp_size (EL n l) < k’ by
           (‘exp_size (EL n l) < exp3_size l’ by fs [exp_size_cmp_exp3_size, EL_MEM]
           \\ fs [])
          \\ first_x_assum dxrule
          \\ rw []
          \\ qabbrev_tac ‘triple = find_function (EL n l) c’
          \\ PairCases_on ‘triple’
          \\ fs []
          \\ first_x_assum drule
          \\ rw [EL_MAP]
          \\ first_x_assum $ irule_at Any)
      >- (Cases_on ‘t’ (* Seq *)
          >- (fs [find_function_def]
              \\ qexists_tac ‘{}’
              \\ fs [find_Prim_Fail, well_written_def])
          \\ rename1 ‘h0::h1::tl’
          \\ Cases_on ‘tl’
          >- (‘exp_size h0 < k’ by fs [exp_size_def]
              \\ first_assum dxrule
              \\ ‘exp_size h1 < k’ by fs [exp_size_def]
              \\ first_x_assum dxrule
              \\ rw []
              \\ fs [find_function_def]
              \\ qabbrev_tac ‘f1 = find_function h1 c’
              \\ PairCases_on ‘f1’
              \\ qabbrev_tac ‘f0 = find_function h0 c’
              \\ PairCases_on ‘f0’
              \\ fs []
              \\ first_x_assum drule
              \\ first_x_assum drule
              \\ rw []
              \\ qexists_tac ‘ds'’
              \\ fs []
              \\ irule find_Seq2
              \\ fs []
              \\ first_x_assum $ irule_at Any)
          \\ fs [find_function_def]
          \\ qexists_tac ‘{}’
          \\ fs [find_Prim_Fail, well_written_def]))
  >- (rw [] (* App *)
      \\ rename1 ‘App f e’
      \\ ‘exp_size f < k’ by fs []
      \\ first_assum dxrule
      \\ qabbrev_tac ‘e1p = find_function f c’
      \\ PairCases_on ‘e1p’
      \\ strip_tac
      \\ fs []
      \\ first_x_assum drule
      \\ strip_tac
      \\ Cases_on ‘f’ >~[‘Let s e e2’]
      >- (
       fs [find_function_def]
       \\ qabbrev_tac ‘ep = find_function e c’
       \\ PairCases_on ‘ep’
       \\ qabbrev_tac ‘e2p = find_function e2 (Bind ep2 s e c c)’
       \\ PairCases_on ‘e2p’
       \\ fs []
       \\ ‘exp_size e < k’ by fs []
       \\ first_assum dxrule
       \\ ‘exp_size e2 < k’ by
         (‘exp_size e2 < exp_size (Lam s e2)’ by fs [exp_size_def]
          \\ rw [] \\ fs [])
       \\ first_x_assum dxrule
       \\ rw []
       \\ first_x_assum drule
       \\ first_x_assum drule
       \\ rw []
       \\ ‘s ∈ FDOM e2p0 ∨ s ∉ FDOM e2p0’ by fs []
       \\ fs [FLOOKUP_DEF]
       \\ rw []
       >- (
         ‘∃ds'''. ∀ps v. (ps, v) ∈ ds''' ⇔ ((ps, v) ∈ ds' ∧ v ≠ s) ∨ (ps, v) ∈ ds''’ by
            (qexists_tac ‘ds'' ∪ BIGUNION (IMAGE (λ(ps,v). if v = s then {} else {(ps,v)}) ds')’
             \\ rw []
             \\ eq_tac
             \\ rw []
             \\ fs []
             >- (rename1 ‘p ∈ ds'’
                 \\ PairCases_on ‘p’
                 \\ fs []
                 \\ ‘p1 = s ∨ p1 ≠ s’ by fs []
                 \\ fs [])
             \\ rw [DISJ_EQ_IMP]
             \\ qexists_tac ‘{(ps, v)}’
             \\ fs []
             \\ first_x_assum $ irule_at Any
             \\ fs [])
         \\ irule_at Any find_Let2
         \\ first_assum $ irule_at Any
         \\ last_assum dxrule
         \\ rw []
         \\ first_assum $ irule_at Any
         \\ irule_at Any find_Seq
         \\ first_assum $ irule_at Any
         \\ qexists_tac ‘ds'''’
         \\ fs []
         \\ rw []
         >- (first_assum dxrule
             \\ first_x_assum dxrule
             \\ fs [])
         >- (rw [FMERGE_DEF]
             >- (first_assum dxrule
                 \\ first_x_assum dxrule
                 \\ rw []
                 \\ qsuff_tac ‘FLOOKUP (e2p0 \\ s) s' = FLOOKUP e2p0 s'’
                 >- rw [FLOOKUP_DEF]
                 \\ fs [DOMSUB_FLOOKUP_NEQ])
             >- (last_assum dxrule
                 \\ last_x_assum dxrule
                 \\ fs [])
             \\ last_assum dxrule
             \\ last_assum dxrule
             \\ rw [merge_dt_is_set_union]
             \\ qsuff_tac ‘FLOOKUP (e2p0 \\ s) s' = FLOOKUP e2p0 s'’
             >- rw [FLOOKUP_DEF]
             \\ fs [DOMSUB_FLOOKUP_NEQ])
         >- (first_x_assum dxrule
             \\ first_x_assum dxrule
             \\ fs [])
         >- (first_x_assum dxrule
             \\ rw [FMERGE_DEF, merge_dt_is_set_union])
         >- (first_x_assum dxrule
             \\ rw []
             \\ qexists_tac ‘ps'’
             \\ fs [])
         \\ first_x_assum dxrule
         \\ rw []
         \\ qexists_tac ‘ps'’
         \\ fs [])
       \\ irule_at Any find_Let
       \\ last_x_assum $ irule_at Any
       \\ last_x_assum $ irule_at Any
       \\ fs []
       \\ rw []
       >- (strip_tac
           \\ first_x_assum dxrule
           \\ fs [])
       \\ first_assum drule
       \\ fs [])
      \\ fs [find_function_def]
      \\ ‘exp_size e < k’ by fs []
      \\ first_x_assum dxrule
      \\ rw []
      \\ qabbrev_tac ‘ep = find_function e c’
      \\ PairCases_on ‘ep’
      \\ fs []
      \\ first_x_assum drule
      \\ rw []
      \\ irule_at Any find_App
      \\ first_assum $ irule_at Any >~[‘Var s’]
      >- (irule_at Any find_Var
          \\ qexists_tac ‘[]’
          \\ fs []
          \\ rw [FLOOKUP_UPDATE, dt_to_set_def])
      \\ first_assum $ irule_at Any
      \\ fs [])
  >- (rw [find_function_def] (* Lam *)
      \\ irule_at Any find_Bottom
      \\ fs [])
  >- (rw [find_function_def] (* Letrec *)
      \\ irule_at Any find_Bottom
      \\ fs [find_Bottom])
QED


Definition demand_analysis_def:
  demand_analysis = FST o SND o (λe. find_function e Nil)
End

Theorem demand_analysis_soundness:
  ∀e. is_closed e ⇒ e ≅ demand_analysis e
Proof
  rw [demand_analysis_def]
  \\ qabbrev_tac ‘p = find_function e Nil’
  \\ PairCases_on ‘p’
  \\ fs []
  \\ irule find_soundness
  \\ ‘exp_size e < SUC (exp_size e)’ by fs []
  \\ drule find_function_soundness_lemma
  \\ rw []
  \\ first_x_assum dxrule
  \\ rw []
  \\ first_assum $ irule_at Any
QED

(*
  let foo = lam (a + 2) in
    lam x (foo x)
-->
  let foo = lam a (seq a (a + 2)) in
    lam x (foo x)
-->
  let foo = lam a (seq a (a + 2)) in
    lam x (seq x (foo x))

  Letrec [(f,x)] rest
*)

val _ = export_theory();
