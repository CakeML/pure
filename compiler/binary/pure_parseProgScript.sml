(*
  Translation of PureLang parser
 *)
open basis
     pureParseTheory
     pure_typingTheory
     pure_backendProgTheory;

val _ = new_theory "pure_parseProg";

val _ = set_grammar_ancestry ["pure_backendProg", "pureParse"];

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

(*-----------------------------------------------------------------------*
   lexer
 *-----------------------------------------------------------------------*)

val r = translate pure_lexer_implTheory.num_from_dec_string_alt_def;
val r = translate pure_lexer_implTheory.num_from_hex_string_alt_def;

Theorem l2n_side:
  ∀b a. a ≠ 0 ⇒ l2n_side a b
Proof
  Induct>>
  rw[Once (fetch"-""l2n_side_def")]
QED

val _ = update_precondition l2n_side;

val num_from_dec_string_alt_side = Q.prove(`
  ∀x. num_from_dec_string_alt_side x ⇔ T`,
  simp[Once (fetch"-""num_from_dec_string_alt_side_def")]>>
  strip_tac>>CONJ_TAC
  >-
    simp[Once (fetch"-""s2n_side_def"),l2n_side]
  >>
    simp[Once (fetch"-""unhex_alt_side_def"),Once (fetch"-""unhex_side_def"),
         isDigit_def,isHexDigit_def]>>Cases>>
    fs[ORD_CHR]>>
    strip_tac>>
    fs[]) |> update_precondition;

val num_from_hex_string_alt_side = Q.prove(`
  ∀x. num_from_hex_string_alt_side x ⇔ T`,
  simp[Once (fetch"-""num_from_hex_string_alt_side_def")]>>
  strip_tac>>CONJ_TAC
  >-
    simp[Once (fetch"-""s2n_side_def"),l2n_side]
  >>
    simp[Once (fetch"-""unhex_alt_side_def"),Once (fetch"-""unhex_side_def"),
         isDigit_def,isHexDigit_def]>>Cases>>
    fs[ORD_CHR]>>
    strip_tac>>
    fs[]) |> update_precondition;

val r = translate pure_lexer_implTheory.read_string_def;

val read_string_side = Q.prove(`
  ∀x y l.
  read_string_side x y l ⇔ T`,
  ho_match_mp_tac pure_lexer_implTheory.read_string_ind>>
  rw[]>>
  simp[Once (fetch"-""read_string_side_def")])
  |> update_precondition;

val r = translate EL;

val el_side = Q.prove(`
  ∀x l.
  el_side x l ⇔ x < LENGTH l`,
  Induct_on ‘x’ \\ Cases_on ‘l’ \\ simp [Once (fetch"-""el_side_def")])
  |> update_precondition;

Triviality and_to_if:
  (xs ≠ [] ∧ c ⇔ if xs = [] then F else c) ∧
  ((b ⇒ c) ⇔ if b then c else T)
Proof
  Cases_on ‘xs = []’ \\ fs []
  \\ Cases_on ‘b’ \\ fs []
QED

val r = translate (pure_lexer_implTheory.next_sym_alt_def |> RW [and_to_if]);

val next_sym_alt_side = Q.prove(`
  ∀x l. next_sym_alt_side x l ⇔ T`,
  ho_match_mp_tac pure_lexer_implTheory.next_sym_alt_ind>>rw[]>>
  simp[Once (fetch"-""next_sym_alt_side_def"),num_from_dec_string_alt_side,
       read_string_side,num_from_hex_string_alt_side]>>
  rw[]>> gvs []) |> update_precondition;

val r = translate pure_lexer_implTheory.lexer_fun_def;

(*-----------------------------------------------------------------------*
   parser
 *-----------------------------------------------------------------------*)

val _ = register_type “:expAST”;

val r = translate listTheory.LIST_REL_def;
val r = translate purePEGTheory.mktoklf_def;
val r = translate purePEGTheory.purePEG_def;

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

Theorem THE_orelse:
  THE (x ++ SOME y) = case x of SOME z => z | NONE => y
Proof
  Cases_on ‘x’ \\ fs [optionTheory.OPTION_CHOICE_def]
QED

val _ = (extra_preprocessing :=
  [MEMBER_INTRO,MAP,OPTION_BIND_THM,monad_unitbind_assert,THE_orelse]);

val r = translate (def_of_const “cst_to_ast$mkSym”)

val r = translate (def_of_const “cst_to_ast$mkFunTy”);

val r = translate_no_ind (def_of_const “cst_to_ast$astType”);

val ind_lemma = Q.prove(
  `^(first is_forall (hyp r))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ full_simp_tac bool_ss [NOT_CONS_NIL,NOT_NIL_CONS,CONS_11,SOME_11]
  \\ gvs [PULL_EXISTS]
  \\ gvs [AllCaseEqs()])
  |> update_precondition;

val res = translate_no_ind cst_to_astTheory.optLAST_def;

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac \\ fs []
  \\ gvs [FORALL_PROD, SF ETA_ss])
  |> update_precondition;

val r = translate precparserTheory.isFinal_def;
val r = translate (def_of_const “precparse1”);
val r = translate (def_of_const “precparse” |> DefnBase.one_line_ify NONE);

val precparse_side = Q.prove(`
  ∀x y. precparse_side x y ⇔ T`,
  simp [FORALL_PROD] >>
  ho_match_mp_tac precparserTheory.precparse_ind >> rw [] >>
  simp [Once (fetch "-" "precparse_side_def")] >>
  rw [] >>
  gvs [DefnBase.one_line_ify NONE precparserTheory.isFinal_def] >>
  every_case_tac \\ fs [fetch "-" "outr_side_def"])
  |> update_precondition;

val r = translate (def_of_const “cst_to_ast$tok_action”);

val r = translate cst_to_astTheory.handlePrecs_def;

Triviality OPT_MMAP_eq:
  ∀xs f. OPT_MMAP f xs = OPT_MMAP I (MAP f xs)
Proof
  Induct \\ fs [OPT_MMAP_def]
QED

val r = translate (cst_to_astTheory.exp_to_pat_def |> RW1 [OPT_MMAP_eq]);

val r = translate (def_of_const “grab”);
val r = translate (def_of_const “grabPairs”);
val r = translate (def_of_const “grabsepby”);
val r = translate (def_of_const “strip_comb”);

val r = translate_no_ind (def_of_const “cst_to_ast$astExp”);



(*

val r = translate cst_to_astTheory.astValBinding_def
val r = translate cst_to_astTheory.astDecl_def
val r = translate cst_to_astTheory.astDecls_def

string_to_cst_def
string_to_asts_def
string_to_cexp_def

*)

val _ = export_theory ();
