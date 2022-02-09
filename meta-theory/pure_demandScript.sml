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

val _ = set_fixity "demands" (Infixl 480);

Definition demands_def:
  (e demands (p,v)) = (e ≅ Seq (Projs p (Var v)) e)
End

Theorem demands_Var:
  (Var v) demands ([],v)
Proof
  fs [demands_def,Projs_def]
  \\ metis_tac [Seq_id,exp_eq_sym]
QED

Theorem demands_Proj:
  e demands (ps,v) ⇒
  (Proj n i e) demands (ps,v)
Proof
  rw [demands_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Proj n i e)’
  \\ conj_tac THEN1 fs [Proj_Seq]
  \\ qabbrev_tac ‘p = Projs ps (Var v)’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq p e) (Proj n i e)’
  \\ conj_tac THEN1
   (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq p (Seq e (Proj n i e))’
  \\ conj_tac THEN1 fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ metis_tac [Proj_Seq,exp_eq_sym]
QED

Theorem demands_Proj_Var:
  (Proj s i (Var v)) demands ([(s,i)],v)
Proof
  rw [demands_def,Projs_def]
  \\ metis_tac [Seq_id,exp_eq_sym]
QED

Theorem exp_eq_Projs_cong:
  ∀ps x y. x ≅ y ⇒ Projs ps x ≅ Projs ps y
Proof
  Induct \\ fs [Projs_def,FORALL_PROD]
  \\ rw [] \\ first_x_assum irule
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
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

Theorem demands_Let1:
  e demands d ∧ e' demands ([],w) ⇒ (Let w e e') demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qabbrev_tac ‘p = (Projs d0 (Var d1))’
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
  rw [demands_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w (Proj s i (Var v)) (Seq (Projs ps (Var w)) e)’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w (Proj s i (Var v)) (Projs ps (Var w)))
                      (Let w (Proj s i (Var v)) e)’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w (Proj s i (Var v)) (Var w))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Theorem demands_Let_Cons: (* expects program to be in ANF *)
  e demands ((s,LENGTH xs)::ps,w) ⇒
  (Let w (Cons s (xs ++ (Var v)::ys)) e) demands (ps,v)
Proof
  rw [demands_def,Projs_def]
  \\ qabbrev_tac ‘cons = (Cons s (xs ++ Var v::ys))’
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


Theorem Seq_App:
  App (Seq proj f) e ≅ Seq proj (App f e)
Proof
  irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def, eval_wh_Seq, eval_wh_App]
  \\ rw [] \\ fs []
QED

Theorem demands_App:
  f demands (ps, v) ⇒ (App f e) demands (ps, v)
Proof
  rw [demands_def]
  \\ qabbrev_tac ‘proj = Projs ps (Var v)’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘App (Seq proj f) e’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ rw [exp_eq_refl])
  \\ fs [Seq_App]
QED

val _ = set_fixity "fun_demands" (Infixl 479);


Theorem demands_If:
  e demands d ⇒ (If e e' e'') demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def]
  \\ qabbrev_tac ‘p = Projs d0 (Var d1)’
  \\ irule exp_eq_trans \\ qexists_tac ‘If (Seq p e) e' e''’ \\ conj_tac
  THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def, eval_wh_Seq, eval_wh_If]
  \\ rw [] \\ fs []
QED

(*
Theorem demands_If2:
  wh_eval e ≠ wh_Diverge ∧ wh_eval e ≠ wh_Error ∧ e1 demands d ∧ e2 demands d ⇒ (If e e1 e2) demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def]
  \\ rename1 ‘Projs ps (Var v)’
  \\ qabbrev_tac ‘p = Projs ps (Var v)’
  \\ irule exp_eq_trans \\ qexists_tac ‘If e (Seq p e1) (Seq p e2)’
  \\ conj_tac
  THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule eval_wh_IMP_exp_eq \\ rw []
  \\ fs [subst_def, eval_wh_Seq, eval_wh_If]
  \\ rw [] \\ fs []
QED
*)

Definition fun_demands_def:
  f fun_demands ps = ∀n. App f (Var n) demands (ps, n)
End

Theorem fun_demands_lambda:
  e demands (ps, v) ⇒ (Lam v e) fun_demands ps
Proof
  rw [demands_def, fun_demands_def]
  \\ rename1 ‘Let v (Var w) e’
  \\ irule exp_eq_trans \\ qexists_tac ‘Let v (Var w) (Seq (Projs ps (Var v)) e)’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl, exp_eq_Lam_cong])
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Let v (Var w) (Projs ps (Var v))) (Let v (Var w) e)’
  \\ conj_tac
  THEN1 fs [Let_Seq]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
  \\ irule exp_eq_trans \\ qexists_tac ‘Projs ps (Let v (Var w) (Var v))’
  \\ conj_tac
  THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Datatype:
  ctxt = Nil
       | Append ctxt ctxt
       | Bind string exp ctxt
       | RecBind (string # exp) ctxt
End

Inductive find: (* i i o o *)
[find_Bottom:]
  (∀e c.
    find e c {} e) ∧
[find_Seq:]
  (∀e c p ds v.
    find e c ds e ∧ (p,v) ∈ ds ⇒
    find e c ds (Seq (Var v) e))
End

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
