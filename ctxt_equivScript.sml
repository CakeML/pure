
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

Definition exp_sim_def:
  exp_sim x y ⇔
    ∀bindings.
      set (freevars x) ∪ set (freevars y) ⊆ set (MAP FST bindings) ⇒
      exp_rel (bind bindings x) (bind bindings y)
End

Theorem exp_sim_closed:
  closed x ∧ closed y ⇒
  exp_sim x y = exp_rel x y
Proof
  fs [closed_def,exp_sim_def,bind_def]
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

Theorem exp_sim_Lam:
  exp_sim x y ⇒ exp_sim (Lam s x) (Lam s y)
Proof
  fs [exp_sim_def] \\ rw []
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

Theorem exp_sim_plug:
  ∀h x y. exp_sim x y ⇒ exp_sim (plug h x) (plug h y)
Proof
  ho_match_mp_tac plug_ind \\ rw []
  THEN1 (rename [‘Hole’] \\ fs [plug_def])
  THEN1 (rename [‘Prim’] \\ cheat (* help? *))
  THEN1 (rename [‘AppL’] \\ cheat (* help? *))
  THEN1 (rename [‘AppR’] \\ cheat (* help? *))
  THEN1 (rename [‘Lam’] \\ fs [plug_def,exp_sim_Lam])
  \\ cheat (* help? *)
QED

val _ = export_theory();
