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
       | Bind string exp ctxt ctxt
       | RecBind ((string # exp) list) ctxt
End

Definition ctxt_size_def:
  ctxt_size Nil = 0n ∧
  ctxt_size (IsFree s ctxt) = 1 + ctxt_size ctxt ∧
  ctxt_size (Bind s e ctxt tl) = 1 + list_size char_size s +  exp_size e + ctxt_size ctxt + ctxt_size tl ∧
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
  (subst_ctxt (Bind v exp ctxt tl) (Var n) = if n = v
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

Inductive find: (* i i o o *)
[find_Bottom:]
  (∀e (c:ctxt).
    find e c {} e) ∧
[find_Seq:]
  (∀e e' c (p:(string#num) list) ds v.
    find e c ds e' ∧ (p,v) ∈ ds ⇒
    find e c ds (Seq (Var v) e')) ∧
[find_Seq2:]
  (∀e e' e2 e2' c ds ds2.
     find e c ds e' ∧ find e2 c ds2 e2' ⇒
     find (Seq e e2) c ds (Seq e' e2')) ∧
[find_If:]
  (∀ec et ee ec' et' ee' c dsc dst dse.
     find ec c dsc ec' ∧
     find et c dst et' ∧
     find ee c dse ee' ⇒
     find (If ec et ee) c dsc (If ec' et' ee')) ∧
[find_Var:]
  (∀n c. find (Var n) c {([],n)} (Var n)) ∧
[find_App:]
  (∀f f' e e' c ds ds2.
     find f c ds f' ∧
     find e c ds2 e' ⇒
     find (App f e) c ds (App f' e')) ∧
[find_Prim:]
  (∀c el el' ope.
     LENGTH el = LENGTH el' ∧ (∀k. k < LENGTH el ⇒ ∃ds. find (EL k el) c ds (EL k el'))
     ⇒ find (Prim ope el) c {} (Prim ope el')) ∧
[find_Prim1:]
  (∀c edsel tl ope e ds e'.
     (∀ e ds e'. MEM (e, ds, e') edsel ⇒ find e c ds e')
     ∧ edsel = (e, ds, e')::tl ∧ well_formed ope (MAP FST edsel) ⇒ find (Prim ope (MAP FST edsel)) c ds (Prim ope (MAP (SND o SND) edsel))) ∧
[find_Proj:]
  (∀e e' n i c ds.
     find e c ds e' ⇒ find (Proj n i e) c ds (Proj n i e')) ∧
[find_Subset:]
  (∀e e' c ds ds'.
     find e c ds e' ∧ (∀ps v. (ps, v) ∈ ds' ⇒ ∃ps'. (ps++ps', v) ∈ ds) ⇒ find e c ds' e') ∧
[find_Let:]
  (∀e e' e2 e2' ds ds' c v.
     find e c ds e' ∧ find e2 (Bind v e c c) ds' e2'
     ∧ (∀ps. (ps, v) ∉ ds')
     ⇒ find (Let v e e2) c ds' (Let v e' e2')) ∧
[find_Let2:]
  (∀ e e' e2 e2' ds ds' ds'' c v ps.
     find e c ds e' ∧ find e2 (Bind v e c c) ds' e2'
     ∧ (ps,v) ∈ ds'
     ∧ (∀ps' v'. (ps', v') ∈ ds'' ⇒ ((ps', v') ∈ ds' ∧ v' ≠ v) ∨ (ps', v') ∈ ds)
     ⇒ find (Let v e e2) c ds'' (Let v e' e2')) ∧
[find_Lam:]
  (∀e e' c ds v.
     find e c ds e' ⇒ find (Lam v e) c {} (Lam v e'))
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

Theorem find_soundness_lemma:
  ∀e c ds e'. find e c ds e'  ⇒ e ≅ e' ∧ ∀d. d ∈ ds ⇒ e demands d
Proof
  Induct_on ‘find’
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- fs [exp_eq_refl] (* find_Bottom *)
  >- (strip_tac (* find_Seq *)
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
      \\ conj_tac
      >- fs [exp_eq_Prim_cong]
      \\ rw []
      \\ irule demands_Seq
      \\ fs [])
  >- (strip_tac (* find_If *)
      \\ conj_tac
      >- fs [exp_eq_Prim_cong]
      \\ rw []
      \\ irule demands_If
      \\ fs [])
  >- (fs [exp_eq_refl] (* find_Var *)
      \\ fs [demands_Var])
  >- (strip_tac (* find_App *)
     \\ fs [exp_eq_App_cong]
     \\ rw []
     \\ fs [demands_App])
  >- (strip_tac (* find_Prim *)
      \\ fs []
      \\ irule exp_eq_Prim_cong
      \\ rw [LIST_REL_EL_EQN, EL_MAP]
      \\ ‘n < LENGTH el'’ by fs []
      \\ first_x_assum drule
      \\ rw [])
  >- (strip_tac (* find_Prim1 *)
     \\ conj_tac
     >- (irule exp_eq_Prim_cong
         \\ rw [LIST_REL_EL_EQN, EL_MAP]
         \\ ‘MEM (EL n ((e,ds,e')::tl)) ((e,ds,e')::tl)’ by fs [EL_MEM]
         \\ qabbrev_tac ‘t = EL n ((e,ds,e')::tl)’
         \\ PairCases_on ‘t’
         \\ rw []
         \\ first_x_assum drule
         \\ fs [])
      \\ rw []
      \\ ‘e demands d’ by (‘MEM (e,ds,e') ((e,ds,e')::tl)’ by fs [EL_MEM]
                           \\ first_x_assum drule
                           \\ fs [])
      \\ irule demands_Prim
      \\ fs [])
  >- (strip_tac (* find_Proj *)
      \\ fs [exp_eq_Prim_cong]
      \\ rw []
      \\ irule demands_Proj
      \\ fs [])
  >- (strip_tac (* find_Subset *)
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
      \\ conj_tac
      >- (irule exp_eq_App_cong \\ fs []
          \\ irule exp_eq_Lam_cong
          \\ fs [])
      \\ rw []
      \\ PairCases_on ‘d’
      \\ irule demands_Let2
      \\ conj_tac
      \\ ‘d1 = v ∨ d1 ≠ v’ by fs []
      \\ fs []
      \\ ‘(d0, v) ∉ ds'’ by (first_x_assum $ irule_at Any)
      \\ first_x_assum drule
      \\ fs [])
  >- (strip_tac (* find_Let2 *)
      \\ conj_tac
      >- (irule exp_eq_App_cong \\ fs []
          \\ irule exp_eq_Lam_cong
          \\ fs [])
      \\ rw []
      \\ PairCases_on ‘d’
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
  >- (strip_tac
      \\ fs [exp_eq_Lam_cong])
QED

Theorem find_soundness:
  find e Nil ds e' ⇒ e ≅ e'
Proof
  rw []
  \\ drule find_soundness_lemma
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
  find_function (Var v) c = ((FEMPTY : (string |-> demands_tree)) |+ (v, DemandNode T []), Var v) ∧
  (find_function (If ce te ee) c =
   let (cd, ce') = find_function ce c in
     let (td, te') = find_function te c in
       let (ed, ee') = find_function ee c in
         (cd, If ce' te' ee')) ∧
  (find_function (Prim op l) c: ((string |-> demands_tree) # exp)) =
  (FEMPTY, Prim op (MAP (λe. SND (find_function e c)) l)) ∧
  (find_function (App (Lam v e2) e) c = let (d2, e2') = find_function e2 (Bind v e c c) in
                                         let (d, e') = find_function e c in
                                           case FLOOKUP d2 v of
                                             | NONE => (d2, App (Lam v e2') e')
                                             | SOME s => (FMERGE merge_dt d (d2 \\ v), Let v e' (Seq (Var v) e2'))) ∧
  (find_function (App f e) c = let (d, f') = find_function f c in
                                 let (_, e') = find_function e c in
                                   (d, App f' e')) ∧
  find_function e c = ((FEMPTY, e) : (string |-> demands_tree) # exp)
Termination
  WF_REL_TAC ‘measure (exp_size o FST)’
  \\ rw [] \\ fs []
  \\ qsuff_tac ‘exp_size e < exp3_size v58’ >- rw []
  \\ assume_tac exp_size_lemma
  \\ fs []
  \\ first_x_assum irule
End

Theorem exp_size_cmp_exp3_size:
  ∀l e. MEM e l ⇒ exp_size e < exp3_size l
Proof
  Induct
  \\ rw [exp_size_def]
  \\ fs []
  \\ first_x_assum dxrule
  \\ fs []
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
  ∀k e c d e'.
    exp_size e < k ⇒
    find_function e c = (d, e') ⇒
    ∃ds. find e c ds e' ∧
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
      \\ Cases_on ‘op’
      >- (Cases_on ‘es’ (* If *)
          >- (qexists_tac ‘{}’ (* Prim If [] *)
              \\ fs [find_Bottom, find_function_def])
          \\ rename1 ‘h::t’
          \\ Cases_on ‘t’
          >- (fs [find_function_def] (* Prim If [e] *)
              \\ qexists_tac ‘{}’
              \\ fs []
              \\ rw []
              \\ irule find_Prim
              \\ qabbrev_tac ‘p = find_function h c’ \\ PairCases_on ‘p’
              \\ rw []
              \\ rename1 ‘EL n [_]’
              \\ ‘n = 0’ by fs []
              \\ ‘exp_size h < k’ by fs [exp_size_def]
              \\ first_x_assum drule
              \\ rw []
              \\ first_x_assum drule
              \\ rw []
              \\ first_x_assum $ irule_at Any)
          \\ rename1 ‘h::h1::t’
          \\ Cases_on ‘t’
          >- (fs [find_function_def] (* Prim If [e, e'] *)
              \\ qexists_tac ‘{}’
              \\ rw []
              \\ irule find_Prim
              \\ rw []
              \\ rename1 ‘EL n [_; _]’
              \\ ‘exp_size (EL n [h; h1]) < k’ by
                (‘n = 0 ∨ n = 1’ by fs []
                 \\ rw []
                 \\ fs [exp_size_def])
              \\ first_x_assum drule
              \\ rw []
              \\ qabbrev_tac ‘e = find_function (EL n [h; h1]) c’
              \\ PairCases_on ‘e’
              \\ fs []
              \\ first_x_assum drule
              \\ ‘n = 0 ∨ n = 1’ by fs []
              \\ rw []
              \\ fs []
              \\ first_x_assum $ irule_at Any)
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
          \\ irule find_Prim
          \\ rw []
          \\ qabbrev_tac ‘l = ce::te::ee::h::t'’
          \\ rename1 ‘EL n _’
          \\ ‘exp_size (EL n l) < k’ by
            (‘exp_size (EL n l) < exp3_size l’ by
               (irule exp_size_cmp_exp3_size
                \\ fs [MEM_EL]
                \\ qexists_tac ‘n’
                \\ fs []
                \\ unabbrev_all_tac
                \\ fs [])
             \\ rw [])
          \\ first_x_assum drule
          \\ rw []
          \\ qabbrev_tac ‘p = find_function (EL n l) c’ \\ PairCases_on ‘p’
          \\ fs []
          \\ first_x_assum drule
          \\ rw []
          \\ rename1 ‘find (EL n l) c ds p1’
          \\ qexists_tac ‘ds’
          \\ ‘EL n (MAP (λe. SND (find_function e c)) l) = (λe. SND (find_function e c)) (EL n l)’
            by (irule EL_MAP
                \\ unabbrev_all_tac
                \\ fs [])
          \\ unabbrev_all_tac
          \\ rw []
          \\ fs []
          \\ first_x_assum $ irule_at Any)
      \\ fs [find_function_def]
      \\ qexists_tac ‘{}’
      \\ fs []
      \\ rw []
      \\ irule find_Prim \\ rw []
      \\ rw [EL_MAP]
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
      \\ fs []
      \\ first_x_assum dxrule
      \\ rw []
      \\ first_x_assum $ irule_at Any)
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
       \\ qabbrev_tac ‘e2p = find_function e2 (Bind s e c c)’
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
         \\ qexists_tac ‘ds'''’
         \\ conj_tac
         >- (irule find_Let2
             \\ first_assum $ irule_at Any
             \\ first_assum dxrule
             \\ rw []
             \\ first_assum $ irule_at Any
             \\ fs []
             \\ irule find_Seq
             \\ fs []
             \\ first_assum $ irule_at Any)
         \\ rw []
         \\ fs []
         \\ first_x_assum dxrule
         \\ strip_tac
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
         >- fs []
         >- rw [FMERGE_DEF, merge_dt_is_set_union]
         >- (qexists_tac ‘ps’
             \\ fs [])
         \\ qexists_tac ‘ps’
         \\ fs [])
       \\ rename1 ‘find e2 (Bind s e c c) ds' e2p1’
       \\ qexists_tac ‘ds'’
       \\ fs []
       \\ conj_tac
       >- (irule find_Let
           \\ fs []
           \\ conj_tac
           >- (gen_tac
               \\ strip_tac
               \\ first_assum drule
               \\ fs [])
           \\ first_x_assum $ irule_at Any)
       \\ rw []
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
      >~[‘Letrec’] >-
       (qexists_tac ‘{}’
        \\ fs []
        \\ irule find_App
        \\ fs [find_Bottom]
        \\ first_assum $ irule_at Any)
      \\ qexists_tac ‘ds’
      \\ fs []
      >- (conj_tac
          >- (irule find_App
              \\ fs []
              \\ first_x_assum $ irule_at Any)
          \\ first_x_assum $ irule_at Any)
      \\ irule find_App
      \\ fs []
      \\ first_assum $ irule_at Any)
  >- (rw [find_function_def] (* Lam *)
      \\ qexists_tac ‘{}’
      \\ fs [find_Bottom])
  >- (rw [find_function_def] (* Letrec *)
      \\ qexists_tac ‘{}’
      \\ fs [find_Bottom])
QED

Theorem find_function_soundness:
  ∀e. is_closed e ⇒ e ≅ SND (find_function e Nil)
Proof
  rw []
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
