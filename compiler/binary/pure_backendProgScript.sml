(*
  Translation of pure-to-cake compiler backend.
 *)
open basis lispProgTheory
     pure_to_thunkTheory
     thunk_to_envTheory
     env_to_stateTheory
     state_to_cakeTheory
     pure_to_cakeTheory;

val _ = new_theory "pure_backendProg";

val _ = set_grammar_ancestry ["pure_to_cake", "ml_translator", "basisProg"];

val _ = translation_extends "lispProg";

val _ = (max_print_depth := 1000);

(* pure_to_thunk *)

val _ = register_type “:'a pure_cexp$cexp”;

val r = translate pure_cexpTheory.dest_Lam_def;
val r = translate pure_cexpTheory.dest_App_def;
val r = translate pure_cexpTheory.SmartLam_def;
val r = translate pure_cexpTheory.SmartApp_def;
val r = translate pure_cexpTheory.is_Lam_def;
val r = translate pure_cexpTheory.Lets_def;

val r = translate var_setTheory.insert_var_def;
val r = translate var_setTheory.insert_vars_def;
val r = translate var_setTheory.invent_var_aux_def;
val r = translate rich_listTheory.REPLICATE;
val r = translate var_setTheory.invent_var_def;
val r = translate FLAT;
val r = translate var_setTheory.empty_vars_def;

val res = translate_no_ind pure_namesTheory.extract_names_def;

Triviality extract_names_ind:
  extract_names_ind (:α)
Proof
  once_rewrite_tac [fetch "-" "extract_names_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ reverse (rpt strip_tac)
  \\ last_x_assum match_mp_tac
  \\ simp_tac std_ss [CONS_11] \\ asm_rewrite_tac []
  \\ fs []
QED

val _ = extract_names_ind |> update_precondition;

val r = translate pure_namesTheory.pure_names_def;

val r = translate FOLDL;
val r = translate FOLDR;
val r = translate thunk_cexpTheory.dest_Var_def;
val r = translate thunk_split_Delay_LamTheory.dest_Delay_Lam_def;
val r = translate thunk_split_Delay_LamTheory.letrec_split_def;
val r = translate_no_ind thunk_split_Delay_LamTheory.split_Delayed_Lam_def;
val r = translate thunk_split_Delay_LamTheory.split_delated_lam_def;

val r = translate thunk_let_forceTheory.can_keep_def;
val r = translate (thunk_let_forceTheory.can_keep_list_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate thunk_let_forceTheory.d_Var_def;
val r = translate thunk_let_forceTheory.d_Force_Var_def;
val r = translate thunk_let_forceTheory.let_force_def;
val r = translate thunk_let_forceTheory.simp_let_force_def;

val r = translate pure_to_thunkTheory.mk_delay_def;
val r = translate pure_to_thunkTheory.any_el_def;
val r = translate pure_to_thunkTheory.get_var_name_def;
val r = translate MAP2_DEF;
val r = translate mop_of_mlstring_def;
val r = translate delay_arg_def;
val r = translate monad_to_thunk_def;
val r = translate_no_ind pure_to_thunkTheory.to_thunk_def;

Triviality to_thunk_ind:
  to_thunk_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "to_thunk_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ reverse (rpt strip_tac)
  \\ last_x_assum match_mp_tac
  \\ simp_tac std_ss [CONS_11] \\ asm_rewrite_tac []
  \\ fs []
QED

val _ = to_thunk_ind |> update_precondition;

val r = translate compile_to_thunk_def;

(* thunk_to_env *)

val r = translate env_cexpTheory.Lams_def;
val r = translate env_cexpTheory.Apps_def;
val r = translate thunk_to_envTheory.get_arg_def;
val r = translate thunk_to_envTheory.remove_Delay_def;
val r = translate thunk_to_envTheory.op_to_env_def;
val r = translate thunk_to_envTheory.to_env_def;
val r = translate env_boxTheory.is_Lit_def;
val r = translate env_boxTheory.to_box_def;
val r = translate env_boxTheory.compile_to_box_def;
val r = translate thunk_to_envTheory.thunk_to_env_def;

(* env_to_state *)

val r = translate pure_configTheory.dest_Message_def;
val r = translate env_cexpTheory.dest_Delay_def;
val r = translate env_cexpTheory.dest_Lam_def;
val r = translate state_cexpTheory.Lets_def;
val r = translate env_to_stateTheory.Bool_def;
val r = translate env_to_stateTheory.some_ref_bool_def;
val r = translate env_to_stateTheory.unsafe_update_def;
val r = translate (env_to_stateTheory.Letrec_imm_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate env_to_stateTheory.Letrec_split_def;
val r = translate env_to_stateTheory.to_state_def;
val r = translate env_to_stateTheory.compile_def;
val r = translate state_app_unitTheory.unit_apps_def;
val r = translate state_app_unitTheory.any_el_def;
val r = translate state_app_unitTheory.push_app_unit_def;
val r = translate state_app_unitTheory.optimise_app_unit_def;
val r = translate state_namesTheory.max_name_def;
val r = translate state_namesTheory.list_max_def;
val r = translate state_namesTheory.make_name_def;
val r = translate state_namesTheory.give_names_def;
val r = translate state_namesTheory.give_all_names_def;
val r = translate env_to_stateTheory.compile_to_state_def;

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
val r = translate state_to_cakeTheory.final_gc_def;
val r = translate compile_with_preamble_def;

(* compositions *)

val r = translate pure_to_env_def;
val r = translate pure_to_state_def;
val r = translate pure_to_cake_def;

val _ = export_theory ();
