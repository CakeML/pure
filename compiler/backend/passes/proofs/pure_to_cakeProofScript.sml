(*
  Proof of composition from pureLang to CakeML
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory combinTheory
     pure_to_thunkProofTheory thunk_to_envProofTheory pure_letrecProofTheory
     env_to_stateProofTheory state_to_cakeProofTheory pure_to_cakeTheory;

val _ = new_theory "pure_to_cakeProof";

val _ = set_grammar_ancestry
  ["pure_to_cake", "pure_semantics", "pure_cexp", "pureLang", "pure_letrecProof"];

Theorem pure_to_env_correct:
  cexp_wf x ∧ closed (exp_of x) ∧ NestedCase_free x ∧
  safe_itree (itree_of (exp_of x)) ∧ letrecs_distinct (exp_of x)
  ⇒
  itree_of (exp_of x) =
  env_semantics$itree_of (envLang$exp_of (pure_to_env c x)) ∧
  envLang$cexp_wf (pure_to_env c x) ∧
  cns_arities (pure_to_env c x) ⊆
    IMAGE (IMAGE (explode ## I)) (cns_arities x)
Proof
  strip_tac
  \\ drule_all pure_to_thunkProofTheory.compile_to_thunk_itree_of
  \\ disch_then $ qspec_then ‘c’ assume_tac
  \\ fs [pure_to_env_def]
  \\ irule_at Any thunk_to_envProofTheory.thunk_to_env_semantics
  \\ drule_all IMP_thunk_cexp_wf \\ fs []
  \\ disch_then $ qspec_then ‘c’ strip_assume_tac
  \\ drule_all IMP_env_cexp_wf \\ fs []
  \\ rw [] \\ irule SUBSET_TRANS
  \\ first_assum $ irule_at Any \\ fs []
QED

Theorem pure_to_state_correct:
  cexp_wf x ∧ closed (exp_of x) ∧ NestedCase_free x ∧
  safe_itree (itree_of (exp_of x)) ∧ letrecs_distinct (exp_of x)
  ⇒
  itree_of (exp_of x) =
  stateLang$itree_of (stateLang$exp_of (pure_to_state c x)) ∧
  state_cexp$cexp_wf (pure_to_state c x) ∧
  cns_arities (pure_to_state c x) ⊆
    IMAGE (IMAGE (explode ## I)) (cns_arities x) ∪ {{("",0)}; {("True",0)}; {("False",0)}}
Proof
  strip_tac
  \\ drule_all pure_to_env_correct
  \\ disch_then $ qspec_then ‘c’ strip_assume_tac
  \\ fs [pure_to_state_def]
  \\ drule env_to_stateProofTheory.itree_of_compile_to_state
  \\ disch_then $ qspec_then ‘c’ strip_assume_tac
  \\ drule_all pure_semanticsTheory.safe_itree_compiles_to_IMP_eq
  \\ strip_tac \\ fs []
  \\ drule_all IMP_state_cexp_wf \\ fs []
  \\ disch_then $ qspec_then ‘c’ strip_assume_tac
  \\ rw [] \\ irule SUBSET_TRANS
  \\ first_assum $ irule_at Any
  \\ fs [SUBSET_DEF]
QED

Theorem pure_to_cake_correct:
  cexp_wf x ∧ closed (exp_of x) ∧ NestedCase_free x ∧
  safe_itree (itree_of (exp_of x)) ∧ letrecs_distinct (exp_of x) ∧
  namespace_init_ok ((I ## K ns) initial_namespace) ∧
  state_to_cakeProof$cns_ok ((I ## K ns) initial_namespace)
    (IMAGE (IMAGE (explode ## I)) (pure_cexp$cns_arities x))
  ⇒
  state_to_cakeProof$itree_rel
    (itree_of (exp_of x))
    (itree_semantics$itree_semantics (pure_to_cake c ns x)) ∧
  itree_semantics$safe_itree state_to_cakeProof$ffi_convention
    (itree_semantics$itree_semantics (pure_to_cake c ns x))
Proof
  strip_tac
  \\ drule_all pure_to_state_correct
  \\ disch_then $ qspec_then ‘c’ strip_assume_tac
  \\ fs [pure_to_cake_def]
  \\ irule state_to_cakeProofTheory.compile_correct
  \\ fs [GSYM cns_ok_def]
  \\ irule state_to_cakeProofTheory.cns_ok_SUBSET
  \\ first_x_assum $ irule_at $ Pos hd
  \\ irule state_to_cakeProofTheory.cns_ok_UNION
  \\ fs []
QED

val _ = export_theory ();
