
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory bagTheory pure_langTheory pairTheory pred_setTheory;


val _ = new_theory "ctxt_equiv";

Datatype:
  ctxt = Hole
       | Prim op (exp list) ctxt (exp list)
       | AppL ctxt exp
       | AppR exp ctxt
       | Lam vname ctxt
       | LetrecL ((fname # vname # exp) list)
                  (fname # vname # ctxt)
                 ((fname # vname # exp) list) exp
       | LetrecR ((fname # vname # exp) list) ctxt
       | CaseL ctxt vname ((vname # vname list # exp) list)
       | CaseR exp vname ((vname # vname list # exp) list)
                          (vname # vname list # ctxt)
                         ((vname # vname list # exp) list)
End

Definition plug_def:
  plug Hole n = n ∧
  plug (Prim op xs1 h xs2) n = Prim op (xs1 ++ [plug h n] ++ xs2) ∧
  plug (AppL h y) n = App (plug h n) y ∧
  plug (AppR x h) n = App x (plug h n) ∧
  plug (Lam v h) n = Lam v (plug h n) ∧
  plug (LetrecL xs1 (f,v,h) xs2 x) n = Letrec (xs1 ++ [(f,v,plug h n)] ++ xs2) x ∧
  plug (LetrecR xs h) n = Letrec xs (plug h n) ∧
  plug (CaseL h w rows) n = Case (plug h n) w rows ∧
  plug (CaseR x w rows1 (v,vs,h) rows2) n =
    Case x w (rows1 ++ [(v,vs,plug h n)] ++ rows2)
End

Definition exp_equiv_def:
  exp_equiv x y ⇔
    ∀bindings.
      set (freevars x) ∪ set (freevars y) ⊆ set (MAP FST bindings) ⇒
      exp_rel (bind bindings x) (bind bindings y)
End

Theorem exp_equiv_closed:
  closed x ∧ closed y ⇒
  exp_equiv x y = exp_rel x y
Proof
  fs [closed_def,exp_equiv_def,bind_def]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1 (first_x_assum (qspec_then ‘[]’ mp_tac) \\ fs [bind_def])
  \\ fs [GSYM closed_def]
  \\ rpt (pop_assum mp_tac)
  \\ qid_spec_tac ‘x’
  \\ qid_spec_tac ‘y’
  \\ qid_spec_tac ‘bindings’
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ fs [bind_def] \\ rw []
  \\ rewrite_tac [SNOC_APPEND,GSYM bind_bind,bind_def]
  \\ rename [‘bind [t]’] \\ PairCases_on ‘t’ \\ fs [bind_def]
  \\ reverse IF_CASES_TAC \\ fs [AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac \\ fs [exp_rel_def,v_rel_refl]
  \\ EVAL_TAC
QED

Theorem bind_Lam:
  ∀xs s x.
    bind xs (Lam s x) =
      if EVERY closed (MAP SND xs) then
        Lam s (bind (FILTER (λy. FST y ≠ s) xs) x)
      else Fail
Proof
  Induct \\ fs [bind_def,FORALL_PROD]
  \\ rw [subst_def,bind_def] \\ fs []
QED

Theorem exp_equiv_Lam:
  exp_equiv x y ⇒ exp_equiv (Lam s x) (Lam s y)
Proof
  fs [exp_equiv_def] \\ rw []
  \\ fs [bind_Lam]
  \\ rw [] \\ fs []
  \\ fs [exp_rel_def,v_rel_refl,eval_Lam]
  \\ fs [v_rel_def]
  \\ Cases \\ fs [v_rel'_def]
  \\ rw []
  \\ fs [PULL_FORALL,bind_bind]
  \\ first_x_assum match_mp_tac
  \\ fs [EXTENSION,MEM_MAP,MEM_FILTER,EXISTS_PROD,SUBSET_DEF]
  \\ metis_tac []
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
    \\ disch_then (qspec_then ‘z’ mp_tac) \\ fs [])
  \\ qid_spec_tac ‘s1’
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘x2’
  \\ qid_spec_tac ‘x1’
  \\ ho_match_mp_tac similar_strongind
  \\ rw [] \\ rw []
  THEN1 (simp [Once similar_cases])
  THEN1 (fs [subst_def] \\ metis_tac [similar_cases])
  THEN1 (fs [subst_def] \\ rw [] \\ simp [Once similar_cases])
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
    \\ imp_res_tac similar_Lam_IMP \\ res_tac)
  THEN1 (drule_all similar_Diverge \\ fs [])
  THEN1 (drule_all similar_Error \\ fs [])
QED

Theorem bind_thm:
  EVERY closed (MAP SND bs) ⇒
  bind bs (App x1 x2) = App (bind bs x1) (bind bs x2) ∧
  bind bs (Prim p xs) = Prim p (MAP (bind bs) xs)
  (* TODO: add more cases here *)
Proof
  cheat
QED

Theorem bind_fail:
  ~EVERY closed (MAP SND bs) ⇒ bind bs x = Fail
Proof
  cheat
QED

Theorem closed_bind:
  set (freevars x) ⊆ set (MAP FST bindings) ⇒ closed (bind bindings x)
Proof
  cheat
QED

Triviality exp_rel_bind_closed:
  (EVERY closed (MAP SND bs) ⇒
   exp_rel (bind bs x) (bind bs y)) ⇒
  exp_rel (bind bs x) (bind bs y)
Proof
  Cases_on ‘EVERY closed (MAP SND bs)’
  \\ full_simp_tac bool_ss [bind_fail,exp_rel_refl]
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
