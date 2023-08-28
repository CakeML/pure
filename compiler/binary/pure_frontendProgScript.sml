(*
  Translation of PureCake compiler's front end
 *)
open basis
     pure_demands_analysisTheory
     pure_letrec_cexpTheory
     pure_freshenTheory
     pure_compilerTheory
     pure_inferProgTheory;

val _ = new_theory "pure_frontendProg";

val _ = set_grammar_ancestry ["pure_inferProg", "pure_letrec_cexp",
                              "pure_demands_analysis", "pure_freshen"];

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
val r = translate freshen_mfoldl_def;
val r = translate fresh_boundvar_def;
val r = translate fresh_boundvars_def;
val r = translate_no_ind freshen_aux_def; (* TODO bad induction *)
val r = translate freshen_cexp_def;

(*-----------------------------------------------------------------------*
   ast_to_string
 *-----------------------------------------------------------------------*)

val r = translate num_to_dec_string_def;

val r = translate num_to_hex_string_def;

val r = translate ast_to_string_def;

val _ = export_theory ();
