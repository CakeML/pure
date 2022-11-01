(*
  Composition of compiler passes from pureLang to CakeML, not including
  pureLang-to-pureLang passes.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open pure_to_thunkTheory thunk_to_envTheory env_to_stateTheory state_to_cakeTheory;

val _ = new_theory "pure_to_cake";

val _ = set_grammar_ancestry
  ["pure_to_thunk", "thunk_to_env", "env_to_state", "state_to_cake"];

Definition pure_to_env_def:
  pure_to_env e =
    thunk_to_env$to_env (pure_to_thunk$compile_to_thunk e)
End

Definition pure_to_state_def:
  pure_to_state e =
    compile_to_state (pure_to_env e)
End

Definition pure_to_cake_def:
  pure_to_cake ns e =
    compile_with_preamble ((I ## K ns) initial_namespace) (pure_to_state e)
End

val _ = export_theory ();
