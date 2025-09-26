(*
  Correctness for cexp compilation from envLang to stateLang
 *)
Theory env_to_stateProof
Ancestors
  string option sum pair list alist finite_map
  pred_set rich_list arithmetic pure_exp_lemmas pure_misc
  pure_config envLang thunkLang_primitives stateLang
  env_semantics state_caseProof state_unthunkProof env_cexp
  state_cexp pure_semantics[qualified]
  env_to_state_2Proof state_namesProof state_app_unitProof
  env_to_state
Libs
  BasicProvers dep_rewrite


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
