
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory expTheory
     ltreeTheory llistTheory bagTheory pairTheory pred_setTheory;
open pure_langTheory expPropsTheory


val _ = new_theory "ctxt_equiv";

Datatype:
  ctxt = Hole
       | Prim op (exp list) ctxt (exp list)
       | AppL ctxt exp
       | AppR exp ctxt
       | Lam vname ctxt
       | LetrecL ((vname # exp) list)
                  (vname # ctxt)
                 ((vname # exp) list) exp
       | LetrecR ((vname # exp) list) ctxt
End

Definition plug_def:
  plug Hole n = n ∧
  plug (Prim op xs1 h xs2) n = Prim op (xs1 ++ [plug h n] ++ xs2) ∧
  plug (AppL h y) n = App (plug h n) y ∧
  plug (AppR x h) n = App x (plug h n) ∧
  plug (Lam v h) n = Lam v (plug h n) ∧
  plug (LetrecL xs1 (f,h) xs2 x) n = Letrec (xs1 ++ [(f,plug h n)] ++ xs2) x ∧
  plug (LetrecR xs h) n = Letrec xs (plug h n)
End

Definition exp_equiv_def:
  exp_equiv x y ⇔
    ∀bindings.
      set (freevars x) ∪ set (freevars y) ⊆ FDOM bindings ⇒
      exp_rel (bind bindings x) (bind bindings y)
End

Triviality exp_rel_Fail:
  exp_rel Fail Fail
Proof
  gvs[exp_rel_def, eval_thm, v_rel_def]
  \\ Cases \\ simp[v_rel'_def]
QED

Theorem exp_equiv_closed:
  closed x ∧ closed y ⇒
  exp_equiv x y = exp_rel x y
Proof
  fs [closed_def,exp_equiv_def,bind_def]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1 (first_x_assum (qspec_then ‘FEMPTY’ mp_tac) \\ fs [bind_def, subst_FEMPTY])
  \\ IF_CASES_TAC \\ fs[exp_rel_Fail]
QED

Theorem exp_equiv_Lam:
  exp_equiv x y ⇒ exp_equiv (Lam s x) (Lam s y)
Proof
  fs [exp_equiv_def] \\ rw []
  \\ fs [bind_def]
  \\ rw [] \\ fs [exp_rel_Fail]
  \\ fs [exp_rel_def,v_rel_refl,subst_def,eval_Lam]
  \\ fs [v_rel_def]
  \\ Cases \\ fs [v_rel'_def]
  \\ rw []
  \\ fs [PULL_FORALL,bind_def]
  \\ cheat (* TODO *)
QED

Inductive similar:
  (∀x y.
     exp_rel x y ∧ closed x ∧ closed y ⇒ similar x y)
  ∧
  (∀s.
     similar (Var s) (Var s))
  ∧
  (∀f1 f2 x1 x2.
     similar f1 f2 ∧ similar x1 x2 ⇒
     similar (App f1 x1) (App f2 x2))
  ∧
  (∀s x1 x2.
     similar x1 x2 ⇒
     similar (Lam s x1) (Lam s x2))
  ∧
  (∀p xs ys.
     LIST_REL similar xs ys ⇒
     similar (Prim p xs) (Prim p ys))
End

Triviality closed_Lam:
  closed (Lam s1 x1) ∧ closed z ⇒ closed (subst s1 z x1)
Proof
  cheat
QED

Theorem similar_refl[simp]:
  ∀x. similar x x
Proof
  Induct \\ fs []
  \\ simp [Once similar_cases] \\ fs []
  \\ cheat (* cases are missing in similar *)
QED

(* this is the crucial lemma *)
Theorem similar_Lam_IMP:
  similar (Lam s1 x1) (Lam s2 x2) ∧ closed z ⇒
  similar (subst s1 z x1) (subst s2 z x2)
Proof
  simp [Once similar_cases] \\ rw []
  THEN1
   (simp [Once similar_cases] \\ disj1_tac \\ fs [closed_Lam]
    \\ last_x_assum mp_tac
    \\ fs [exp_rel_def,eval_Lam,v_rel_def] \\ rw []
    \\ first_x_assum (qspec_then ‘SUC n’ mp_tac)
    \\ fs [v_rel'_def,bind_def]
    \\ disch_then (qspec_then ‘z’ mp_tac) \\ fs []
    \\ cheat (* TODO *))
  \\ qid_spec_tac ‘s1’
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘x2’
  \\ qid_spec_tac ‘x1’
  \\ ho_match_mp_tac similar_strongind
  \\ rw [] \\ rw []
  THEN1 (simp [Once similar_cases])
  THEN1 (fs [subst_def] \\ metis_tac [similar_cases])
  THEN1 (fs [subst_def] \\ rw [] \\ simp [Once similar_cases] \\ cheat (* TODO *))
  THEN1
   (simp [Once similar_cases]
    \\ fs [subst_def] \\ disj2_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS])
QED

(* TODO: the following lemmas about similar probably ought to
         be proved together *)

Theorem similar_Cons:
  similar x y ∧ eval x = Constructor s xs ⇒
  ∃u t. eval x = eval (Cons s t) ∧
        eval y = eval (Cons s u) ∧ LIST_REL similar t u
Proof
  cheat
QED

Theorem similar_Lam:
  similar x y ∧ eval x = Closure s z ⇒
  ∃s1 z1. eval y = Closure s1 z1 ∧ similar (Lam s z) (Lam s1 z1)
Proof
  cheat
QED

Theorem similar_Atom:
  similar x y ∧ eval x = Atom a ⇒
  eval y = Atom a
Proof
  cheat
QED

Theorem similar_Diverge:
  similar x y ∧ eval x = Diverge ⇒
  eval y = Diverge
Proof
  cheat
QED

Theorem similar_Error:
  similar x y ∧ eval x = Error ⇒
  eval y = Error
Proof
  cheat
QED

Theorem similar_imp_exp_equiv:
  ∀x y. similar x y ⇒ exp_rel x y
Proof
  fs [exp_rel_def,v_rel_def,PULL_FORALL,AND_IMP_INTRO]
  \\ Induct_on ‘n’ \\ fs [v_rel'_def] \\ rw []
  \\ Cases_on ‘eval x’ \\ fs [] \\ fs [v_rel'_def]
  THEN1 (drule_all similar_Atom \\ fs [])
  THEN1
   (drule_all similar_Cons \\ rw [] \\ fs [eval_Cons]
    \\ pop_assum mp_tac \\ rename [‘LIST_REL similar xs1 ys1’]
    \\ qid_spec_tac ‘xs1’ \\ qid_spec_tac ‘ys1’
    \\ Induct \\ fs [PULL_EXISTS])
  THEN1
   (rename [‘Closure s1 x1’]
    \\ drule_all similar_Lam \\ rw [eval_Lam] \\ rw []
    \\ rw [] \\ rw [bind_def,v_rel'_refl]
    \\ imp_res_tac similar_Lam_IMP \\ res_tac \\ cheat (* TODO *))
  THEN1 (drule_all similar_Diverge \\ fs [])
  THEN1 (drule_all similar_Error \\ fs [])
QED

Theorem bind_thm:
  (∀v. v ∈ FRANGE bs ⇒ closed v) ⇒
  bind bs (App x1 x2) = App (bind bs x1) (bind bs x2) ∧
  bind bs (Prim p xs) = Prim p (MAP (bind bs) xs)
  (* TODO: add more cases here *)
Proof
  cheat
QED

Theorem bind_fail:
  (∃v. v ∈ FRANGE bs ∧ ¬closed v) ⇒ bind bs x = Fail
Proof
  cheat
QED

Theorem closed_bind:
  set (freevars x) ⊆ FDOM bindings ⇒ closed (bind bindings x)
Proof
  cheat
QED

Triviality exp_rel_bind_closed:
  ((∀v. v ∈ FRANGE bs ⇒ closed v) ⇒
   exp_rel (bind bs x) (bind bs y)) ⇒
  exp_rel (bind bs x) (bind bs y)
Proof
  Cases_on `∀v. v ∈ FRANGE bs ⇒ closed v` >> fs[] >> rw[] >>
  qsuff_tac `bind bs x = Fail ∧ bind bs y = Fail` >> rw[exp_rel_refl] >>
  irule bind_fail >> goal_assum drule >> fs[]
QED

Triviality LIST_REL_similar_refl:
  ∀xs. LIST_REL similar xs xs
Proof
  Induct \\ fs []
QED

Theorem exp_equiv_plug:
  ∀h x y. exp_equiv x y ⇒ exp_equiv (plug h x) (plug h y)
Proof
  ho_match_mp_tac plug_ind \\ rw []
  THEN1 (rename [‘Hole’] \\ fs [plug_def])
  THEN1 (rename [‘Prim’]
    \\ rw [exp_equiv_def,plug_def]
    \\ match_mp_tac exp_rel_bind_closed \\ rw [bind_thm]
    \\ match_mp_tac similar_imp_exp_equiv
    \\ simp [Once similar_cases] \\ disj2_tac
    \\ match_mp_tac rich_listTheory.EVERY2_APPEND_suff
    \\ fs [LIST_REL_similar_refl]
    \\ simp [Once similar_cases] \\ disj1_tac
    \\ fs [closed_bind]
    \\ first_x_assum drule
    \\ fs [exp_equiv_def])
  THEN1 (rename [‘AppL’]
    \\ rw [exp_equiv_def,plug_def]
    \\ match_mp_tac exp_rel_bind_closed \\ rw [bind_thm]
    \\ match_mp_tac similar_imp_exp_equiv
    \\ simp [Once similar_cases] \\ disj2_tac
    \\ simp [Once similar_cases] \\ disj1_tac
    \\ fs [closed_bind]
    \\ first_x_assum drule
    \\ fs [exp_equiv_def])
  THEN1 (rename [‘AppR’]
    \\ rw [exp_equiv_def,plug_def]
    \\ match_mp_tac exp_rel_bind_closed \\ rw [bind_thm]
    \\ match_mp_tac similar_imp_exp_equiv
    \\ simp [Once similar_cases] \\ disj2_tac
    \\ simp [Once similar_cases] \\ disj1_tac
    \\ fs [closed_bind]
    \\ first_x_assum drule
    \\ fs [exp_equiv_def])
  THEN1 (rename [‘Lam’] \\ fs [plug_def,exp_equiv_Lam])
  \\ cheat (* ... can be done once similar def covers all cases ... *)
QED

val _ = export_theory();
