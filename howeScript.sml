(*
   This file formalises Howe's method following the description of
   Pitts 2011 chapter "Howe's method for higher-order languages".
*)
open HolKernel Parse boolLib bossLib term_tactic;
open expTheory valueTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory pure_langTheory
     pred_setTheory;

val _ = new_theory "howe";


(* -- basics -- *)

(* the set of all values with at most free variables vars *)
Definition Vals_def:
  Vals vars = { v | freevars_v v ⊆ set vars }
End

(* the set of all expressions with at most free variables vars *)
Definition Exps_def:
  Exps vars = { e | set (freevars e) ⊆ set vars }
End

Theorem Exps_EMPTY_closed[simp]:
  e IN Exps [] ⇔ closed e
Proof
  fs [Exps_def,closed_def]
QED


(* -- applicative (bi)similarity -- *)

Definition unfold_rel_def:
  unfold_rel rel (e1, e2) ⇔
    closed e1 ∧ closed e2 ∧
    (* this follows the paper directly *)
    ∀x e1'. eval e1 = Closure x e1' ⇒
            ∃e2'. eval e2 = Closure x e2' ∧
                  ∀e. closed e ⇒ rel (subst x e e1', subst x e e2')
    (* but I think we need one such conjunct for each result alternative *)
End

Definition app_simulation_def:
  app_simulation S ⇔
    ∀e1 e2. S (e1, e2) ⇒ unfold_rel S (e1, e2)
End

Definition opp_def:
  opp s (x,y) ⇔ (y,x) IN s
End

Definition app_bisimulation_def:
  app_bisimulation S ⇔ app_simulation S ∧ app_simulation (opp S)
End

Definition FF_def:
  FF s = { (e1, e2) | unfold_rel s (e1, e2) }
End

Triviality monotone_similarity:
  monotone FF
Proof
  fs [fixedPointTheory.monotone_def,FF_def,unfold_rel_def]
  \\ fs [SUBSET_DEF,FORALL_PROD,IN_DEF]
  \\ metis_tac []
QED

Definition app_similarity_def:
  app_similarity = gfp FF
End

val _ = set_fixity "≲" (Infixl 480);
Overload "≲" = “λx y. app_similarity (x,y)”;

Theorem app_similarity_thm =
  MATCH_MP fixedPointTheory.gfp_greatest_fixedpoint monotone_similarity
  |> SIMP_RULE std_ss [GSYM app_similarity_def]

Theorem app_similarity_iff = (* result (5.4) *)
  app_similarity_thm |> CONJUNCT1 |> GSYM
    |> SIMP_RULE std_ss [FF_def,EXTENSION,FORALL_PROD,GSPECIFICATION,EXISTS_PROD]
    |> SIMP_RULE std_ss [IN_DEF];

Theorem app_simulation_SUBSET_app_similarity:
  app_simulation R ⇒ R ⊆ app_similarity
Proof
  rw [app_similarity_def,app_simulation_def]
  \\ fs [fixedPointTheory.gfp_def,SUBSET_DEF,FORALL_PROD]
  \\ fs [IN_DEF,FF_def,EXISTS_PROD] \\ metis_tac []
QED

Theorem app_simulation_app_similarity:
  app_simulation app_similarity
Proof
  fs [app_simulation_def]
  \\ assume_tac app_similarity_iff
  \\ metis_tac []
QED

Triviality monotone_bisimilarity:
  monotone (λs. { (e1,e2) | (e1,e2) IN FF s ∧ (e2,e1) IN FF (opp s) })
Proof
  fs [fixedPointTheory.monotone_def,FF_def,unfold_rel_def,opp_def]
  \\ fs [SUBSET_DEF,FORALL_PROD,IN_DEF,opp_def]
  \\ metis_tac []
QED

Definition app_bisimilarity_def:
  app_bisimilarity = gfp (λs. { (e1,e2) | (e1,e2) IN FF s ∧ (e2,e1) IN FF (opp s) })
End

val _ = set_fixity "≃" (Infixl 480);
Overload "≃" = “λx y. app_bisimilarity (x,y)”;

Theorem app_bisimilarity_thm =
  MATCH_MP fixedPointTheory.gfp_greatest_fixedpoint monotone_bisimilarity
  |> SIMP_RULE std_ss [GSYM app_bisimilarity_def]

Theorem app_bisimilarity_iff = (* result (5.5) *)
  app_bisimilarity_thm |> CONJUNCT1 |> GSYM
    |> SIMP_RULE std_ss [FF_def,EXTENSION,FORALL_PROD,GSPECIFICATION,EXISTS_PROD]
    |> SIMP_RULE (std_ss++boolSimps.CONJ_ss) [IN_DEF,unfold_rel_def,opp_def]
    |> REWRITE_RULE [GSYM CONJ_ASSOC];

Theorem app_bisimulation_SUBSET_app_bisimilarity:
  app_bisimulation R ⇒ R ⊆ app_bisimilarity
Proof
  rw [app_bisimilarity_def,app_bisimulation_def,app_simulation_def]
  \\ fs [fixedPointTheory.gfp_def,SUBSET_DEF,FORALL_PROD,opp_def,IN_DEF]
  \\ fs [IN_DEF,FF_def,EXISTS_PROD,unfold_rel_def,opp_def]
  \\ rw [] \\ qexists_tac ‘R’ \\ rw []
  \\ res_tac \\ fs []
QED

Theorem app_bisimulation_app_bisimilarity:
  app_bisimulation app_bisimilarity
Proof
  fs [app_bisimulation_def,app_simulation_def,opp_def,IN_DEF,unfold_rel_def]
  \\ assume_tac app_bisimilarity_iff
  \\ metis_tac [unfold_rel_def]
QED

Theorem PreOrder_app_similarity: (* exercise (5.3.3) *)
  PreOrder $≲
  (* hrmm, the statement isn't right because it needs to be
     restricted to consider only closed expressions *)
Proof
  cheat
QED

Theorem equivalence_app_bisimilarity: (* exercise (5.3.3) *)
  equivalence $≃
  (* hrmm, the statement isn't right because it needs to be
     restricted to consider only closed expressions *)
Proof
  cheat
QED

Theorem app_bisimilarity_similarity: (* prop (5.3.4) *)
  e1 ≃ e2 ⇔ e1 ≲ e2 ∧ e2 ≲ e1
Proof
  eq_tac \\ rw []
  THEN1
   (assume_tac app_bisimulation_app_bisimilarity
    \\ fs [app_bisimulation_def]
    \\ imp_res_tac app_simulation_SUBSET_app_similarity
    \\ fs [SUBSET_DEF,IN_DEF])
  THEN1
   (assume_tac app_bisimulation_app_bisimilarity
    \\ fs [app_bisimulation_def]
    \\ imp_res_tac app_simulation_SUBSET_app_similarity
    \\ fs [SUBSET_DEF,IN_DEF,opp_def])
  \\ assume_tac (GEN_ALL app_bisimulation_SUBSET_app_bisimilarity)
  \\ fs [app_bisimulation_def]
  \\ assume_tac app_simulation_app_similarity
  \\ first_x_assum drule
  \\ fs [SUBSET_DEF,IN_DEF,opp_def,PULL_FORALL,AND_IMP_INTRO]
  \\ disch_then match_mp_tac \\ fs []
  \\ fs [app_simulation_def,opp_def,IN_DEF,unfold_rel_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ cheat (* issue with one of the definitions? *)
QED


(* -- congruence -- *)


(* -- Howe's construction -- *)


(* -- contextual equivalence -- *)



val _ = export_theory();
