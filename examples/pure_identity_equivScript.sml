open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory bagTheory pairTheory pred_setTheory;
open pure_exp_relTheory pure_exp_lemmasTheory pure_congruenceTheory
     pure_alpha_equivTheory pure_beta_equivTheory pure_ctxt_equivTheory;

val _ = new_theory "pure_identity_equiv";

Definition id_def:
  id = Lam "x" (Var "x")
End

Definition iidd_def:
  iidd = Lam "y" (App id (Var "y"))
End

(*TODO: a tactic that, given a goal like:

        exp_alpha (Lam "y" (Var "y")) (Lam "x" (Var "x"))
        
        checks whether two closed expressions are exp_alpha, and, if so,
        proves the goal.
        Alternatively, de Bruijn indexes.
*)

Theorem id_iidd_equivalence:
  id ≅ iidd
Proof
 simp[id_def,iidd_def]
 \\ once_rewrite_tac [exp_eq_sym]
 \\ qspecl_then [‘"x"’,‘Var "x"’,‘Var "y"’] assume_tac (GEN_ALL beta_equivalence)
 \\ fs[CA_subst_def,avoid_vars_def,subst_single_def]
 \\ qspecl_then [‘Lam "y" Hole’] assume_tac exp_equiv_plug
 \\ res_tac
 \\ fs[plug_def]
 \\ irule exp_eq_trans
 \\ qexists_tac ‘Lam "y" (Var "y")’ \\ fs[]
 \\ irule exp_alpha_exp_eq 
 \\ qspecl_then [‘"x"’,‘"y"’,‘Lam "y" (Var "y")’] assume_tac exp_alpha_perm_irrel
 \\ fs[perm_exp_def,perm1_def]
QED

Theorem id_iidd_equivalence_expanded =
   id_iidd_equivalence |> REWRITE_RULE [iidd_def,id_def]

            
val _ = export_theory();
