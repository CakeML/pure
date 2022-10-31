(*
  Correctness for cexp compilation from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     envLangTheory thunkLang_primitivesTheory
     stateLangTheory env_semanticsTheory env_to_state_2ProofTheory
     state_caseProofTheory state_unthunkProofTheory state_app_unitProofTheory
     env_cexpTheory state_cexpTheory env_to_stateTheory
     state_app_unitProofTheory state_namesProofTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_to_stateProof";

val _ = set_grammar_ancestry
  ["env_to_state_2Proof", "state_namesProof", "state_app_unitProof",
   "env_to_state"];

Theorem itree_of_compile_to_state:
  cexp_wf x ⇒
  itree_of (exp_of x) ---> itree_of (exp_of (compile_to_state x))
Proof
  strip_tac
  \\ irule pure_semanticsTheory.compiles_to_trans
  \\ irule_at (Pos hd) env_to_state_2ProofTheory.itree_of_to_state
  \\ fs [compile_to_state_def]
  \\ simp [Once (GSYM itree_of_push_app_unit)]
  \\ fs [itree_of_give_all_names]
QED

Theorem IMP_state_cexp_wf:
  envLang$cexp_wf x ⇒
  cexp_wf (compile_to_state x) ∧
  cns_arities (compile_to_state x) ⊆ cns_arities x
Proof
  cheat
QED

val _ = export_theory ();
