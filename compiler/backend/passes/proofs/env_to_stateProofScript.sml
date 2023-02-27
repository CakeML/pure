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
  itree_of (exp_of x) ---> itree_of (exp_of (compile_to_state c x))
Proof
  strip_tac
  \\ irule pure_semanticsTheory.compiles_to_trans
  \\ irule_at (Pos hd) env_to_state_2ProofTheory.itree_of_to_state
  \\ fs [compile_to_state_def]
  \\ irule pure_semanticsTheory.compiles_to_trans
  \\ irule_at (Pos last) itree_of_give_all_names
  \\ fs [itree_of_optimise_app_unit]
  \\ irule pure_semanticsTheory.eq_imp_compiles_to \\ fs []
QED

Theorem IMP_state_cexp_wf:
  envLang$cexp_wf x ⇒
  cexp_wf (compile_to_state c x) ∧
  cns_arities (compile_to_state c x) ⊆ cns_arities x ∪ {{("",0)}; {("True", 0)}; {("False", 0)}}
Proof
  strip_tac
  \\ simp [compile_to_state_def]
  \\ dxrule_then assume_tac to_state_cexp_wf
  \\ qspec_then ‘compile x’ assume_tac $ GEN_ALL cexp_wwf_optimise_app_unit
  \\ pop_assum $ qspec_then ‘c.do_app_unit’ strip_assume_tac
  \\ gs []
  \\ dxrule_then assume_tac give_all_names_cexp_wf
  \\ fs []
  \\ irule SUBSET_TRANS
  \\ first_x_assum $ irule_at Any
  \\ simp []
QED

val _ = export_theory ();
