(*
  Translation of pure-to-cake compiler backend.
 *)
open basis
     pure_to_thunkTheory
     thunk_to_envTheory
     env_to_stateTheory
     state_to_cakeTheory
     pure_to_cakeTheory;

val _ = new_theory "pure_backendProg";

val _ = set_grammar_ancestry ["pure_to_cake", "ml_translator", "basisProg"];

val _ = translation_extends "basisProg";

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val _ = (max_print_depth := 1000);

(* pure_to_thunk *)

val r = translate var_setTheory.insert_var_def;
val r = translate var_setTheory.insert_vars_def;
val r = translate var_setTheory.invent_var_aux_def;
val r = translate rich_listTheory.REPLICATE;
val r = translate var_setTheory.invent_var_def;
val r = translate FLAT;

(*
val r = translate pure_namesTheory.extract_names_def;
val r = translate pure_to_thunkTheory.to_thunk_def;
val r = translate pure_to_thunkTheory.compile_to_thunk_def;
*)

(* thunk_to_env *)

val r = translate thunk_to_envTheory.Lams_def;
val r = translate thunk_to_envTheory.Apps_def;
val r = translate thunk_to_envTheory.get_arg_def;
val r = translate thunk_to_envTheory.remove_Delay_def;
val r = translate thunk_to_envTheory.to_env_def;

(* env_to_state *)

val r = translate env_to_stateTheory.dest_Message_def;
val r = translate env_to_stateTheory.dest_Delay_def;
val r = translate env_to_stateTheory.dest_Lam_def;
val r = translate env_to_stateTheory.Lets_def;
val r = translate env_to_stateTheory.Bool_def;
val r = translate env_to_stateTheory.some_ref_bool_def;
val r = translate env_to_stateTheory.unsafe_update_def;
val r = translate (env_to_stateTheory.Letrec_imm_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate env_to_stateTheory.Letrec_split_def;
val r = translate env_to_stateTheory.to_state_def;
val r = translate env_to_stateTheory.compile_def;
val r = translate state_app_unitTheory.unit_apps_def;
(* val r = translate state_app_unitTheory.push_app_unit_def; *) (* TODO *)
(*
val r = translate env_to_stateTheory.compile_to_state_def;
*)

(* state_to_cake *)

val r = translate pure_typingTheory.initial_namespace_def;
val r = translate locationTheory.unknown_loc_def;
val r = translate compile_exndef_def;
val r = translate compile_typedefs_def;
val r = translate compile_namespace_def;
val r = translate pure_configTheory.max_FFI_return_size_def;
val r = translate state_to_cakeTheory.strle_exp_def;
val r = translate state_to_cakeTheory.char_list_exp_def;
val r = translate preamble_def;
val r = translate state_to_cakeTheory.cexp_var_prefix_def;
val r = translate state_to_cakeTheory.compile_atomop_def;
val r = translate state_to_cakeTheory.compile_op_def;
val r = translate oEL_def;
val r = translate state_to_cakeTheory.failure_def;
val r = translate state_to_cakeTheory.list_to_exp_def;
val r = translate state_to_cakeTheory.cexp_pat_row_def;
val r = translate state_to_cakeTheory.compile_def;
val r = translate compile_with_preamble_def;

val _ = export_theory ();
