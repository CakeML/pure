(*
  Translation of PureCake compiler's front end
 *)
Theory pure_frontendProg
Ancestors
  pure_dead_let pure_letrec_spec_cexp pure_compiler
  pure_inferProg pure_letrec_cexp pure_demands_analysis
  pure_freshen pure_inline_cexp pure_print
Libs
  basis

val _ = translation_extends "pure_inferProg";

val _ = (max_print_depth := 1000);

(*-----------------------------------------------------------------------*
   code for fetching definitions automatically
 *-----------------------------------------------------------------------*)

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";

Theorem NOT_NIL_AND_LEMMA:
   (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = (extra_preprocessing := [MEMBER_INTRO,MAP]);

(*-----------------------------------------------------------------------*
   str_of
 *-----------------------------------------------------------------------*)

val r = translate source_valuesTheory.list_def;
val r = translate pure_printTheory.sexp_of_op_def;
val r = translate (pure_printTheory.sexp_of_def |> DefnBase.one_line_ify NONE)
val r = translate printingTheory.vs2str_def;
val r = translate pure_printTheory.str_of_def;

(*-----------------------------------------------------------------------*
   transform_cexp
 *-----------------------------------------------------------------------*)

val r = translate init_sets_def;
val r = translate letrec_recurse_cexp_def;
val r = translate make_distinct_def;
val r = translate distinct_cexp_def;
val r = translate letrec_recurse_fvs_def;
val r = translate subspt_eq;
val r = translate split_all_cexp_def;
val r = translate clean_all_cexp_def;
val r = translate transform_cexp_def;
val r = translate clean_cexp_def;

(*-----------------------------------------------------------------------*
   demands_analysis
 *-----------------------------------------------------------------------*)

val r = translate demands_analysis_fun_def;
val r = translate demands_analysis_def;

(*-----------------------------------------------------------------------*
   freshening
 *-----------------------------------------------------------------------*)

val r = translate freshen_return_def;
val r = translate freshen_bind_def;
val r = translate freshen_ignore_bind_def;
val r = translate freshen_mapM_def;
val r = translate fresh_boundvar_def;
val r = translate fresh_boundvars_def;
val r = translate_no_ind freshen_aux_def; (* TODO bad induction *)
val r = translate freshen_cexp_def;

(*-----------------------------------------------------------------------*
   inlining TODO various unproved side conditions
 *-----------------------------------------------------------------------*)

val r = translate_no_ind dead_let_def; (* TODO bad induction *)
val r = translate_no_ind boundvars_of_def; (* TODO bad induction *)

val r = translate min_call_args_def;
val r = translate const_call_args_def;
val r = translate all_somes_def;
val r = translate split_at_def;
val r = translate drop_common_prefix_def;
val r = translate drop_common_suffix_def;
val r = translate delete_with_def;
val r = translate spec_one_def;
val r = translate specialise_each_def;
val r = translate specialise_def;
val r = translate cheap_def;
val r = translate App_Lam_to_Lets_def;

val r = translate_no_ind inline_def;

Theorem inline_ind[local]:
  inline_ind (:'a)
Proof
  once_rewrite_tac[fetch "-" "inline_ind_def"] >>
  rpt gen_tac >>
  rpt $ disch_then strip_assume_tac >>
  match_mp_tac $ latest_ind () >>
  rpt strip_tac >>
  last_x_assum match_mp_tac >>
  rpt strip_tac >>
  gvs[FORALL_PROD, LAMBDA_PROD, ADD1] >>
  metis_tac[PAIR]
QED

val r = inline_ind |> update_precondition;

val r = translate inline_all_def;
val r = translate_no_ind tree_size_heuristic_rec_def; (* TODO bad induction *)
val r = translate tree_size_heuristic_def;
val r = translate inline_top_level_def;

(*-----------------------------------------------------------------------*
   ast_to_string
 *-----------------------------------------------------------------------*)

val r = translate num_to_dec_string_def;

val r = translate num_to_hex_string_def;

val r = translate ast_to_string_def;
