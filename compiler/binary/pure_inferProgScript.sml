(*
  Translation of PureLang parser
 *)
open basis
     pure_inferenceTheory
     pure_backendProgTheory;

val _ = new_theory "pure_inferProg";

val _ = set_grammar_ancestry ["pure_backendProg", "pure_inference"];

val _ = translation_extends "pure_backendProg";

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

Theorem monad_unitbind_assert:
  !b x. OPTION_IGNORE_BIND (OPTION_GUARD b) x = if b then x else NONE
Proof
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []
QED

Theorem OPTION_BIND_THM:
   !x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i
Proof
  Cases THEN SRW_TAC [] []
QED

val _ = (extra_preprocessing :=
  [MEMBER_INTRO,MAP,OPTION_BIND_THM,monad_unitbind_assert]);

(*-----------------------------------------------------------------------*
   infer
 *-----------------------------------------------------------------------*)

Theorem LLOOKUP_INTRO:
  ∀ts v d. (if v < LENGTH ts then EL v ts else d) =
           case LLOOKUP ts v of SOME x => x | NONE => d
Proof
  Induct \\ fs [LLOOKUP_def]
  \\ rw [] \\ fs []
  \\ Cases_on ‘v’ \\ fs []
  \\ metis_tac []
QED

val r = translate (def_of_const “isubst” |> RW [LLOOKUP_INTRO]);

val r = translate (pure_inferenceTheory.get_typedef_def
                     |> DefnBase.one_line_ify NONE |> RW [ADD1]);

val r = translate sptreeTheory.insert_def;
val r = translate sptreeTheory.union_def;
val r = translate sptreeTheory.lrnext_def;
val r = translate sptreeTheory.foldi_def;
val r = translate pure_inferenceTheory.infer_cons_def;
val r = translate pure_inference_commonTheory.itype_of_def;
val r = translate pure_inference_commonTheory.iFunctions_def;
val r = translate FOLDL;
val r = translate list_insert_def;
val r = translate pure_varsTheory.list_delete_def;

Theorem infer_bind_eq:
  infer_bind g f =
    λs. case g s of NONE => NONE | SOME (x,s') => f x s'
Proof
  fs [FUN_EQ_THM,infer_bind_def]
QED

Theorem infer_bind_eq:
  infer_bind g f =
    λs. case g s of NONE => NONE | SOME (x,s') => f x s'
Proof
  fs [FUN_EQ_THM,infer_bind_def]
QED

Theorem infer_ignore_bind_eq:
  infer_ignore_bind g f =
    λs. case g s of NONE => NONE | SOME (x,s') => f s'
Proof
  fs [FUN_EQ_THM,infer_bind_def,infer_ignore_bind_def]
QED

val r = translate
  (apply_foldr_def
   |> SIMP_RULE std_ss [infer_bind_eq,infer_ignore_bind_eq]);

val r = translate
  (pure_inferenceTheory.infer'_prim_def
   |> SIMP_RULE std_ss [infer_bind_eq,infer_ignore_bind_eq]);

val r = translate
  (pure_inferenceTheory.infer'_def
   |> SIMP_RULE std_ss [infer_bind_eq,infer_ignore_bind_eq]);

val r = translate pure_inferencePropsTheory.infer'_infer;

val _ = (length (hyp r) = 0) orelse fail (); (* no side conditions *)

(*-----------------------------------------------------------------------*
   pure_unify
 *-----------------------------------------------------------------------*)

(*-----------------------------------------------------------------------*
   solve
 *-----------------------------------------------------------------------*)

val PRECONDITION_INTRO = Q.prove(
  ‘(b ==> (x = y)) ==> (x = if PRECONDITION b then y else x)’,
  Cases_on `b` THEN SIMP_TAC std_ss [PRECONDITION_def]);

val _ = export_theory ();
