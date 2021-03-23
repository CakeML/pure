(*
  A CakeML program that reads from stdio, applies a pure function, and
  prints to stdout.
 *)
open basis pure_printTheory;

val _ = new_theory "ioProg";

val _ = set_grammar_ancestry["pure_print", "basisProg", "basis_ffi"];

val _ = translation_extends "basisProg";

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

(* -- lexer -- *)

val res = translate parsingTheory.end_line_def;
val res = translate parsingTheory.read_num_def;

val res = translate_no_ind
  (REWRITE_RULE [ml_translatorTheory.MEMBER_INTRO] parsingTheory.lex_def);

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ gvs [MEMBER_def])
  |> update_precondition;

val res = translate parsingTheory.lexer_def;

(* -- parser -- *)

val res = translate source_valuesTheory.isNum_def;
val res = translate source_valuesTheory.head_def;
val res = translate source_valuesTheory.tail_def;
val res = translate source_valuesTheory.list_def;
val res = translate source_valuesTheory.el1_def;
val res = translate source_valuesTheory.el2_def;
val res = translate source_valuesTheory.name_def;
val res = translate parsingTheory.quote_def;
val res = translate parsingTheory.parse_def;
val res = translate num_to_str_aux_def;
val res = translate num_to_str_def;
val res = translate num_of_def;
val res = translate name_of_def;
val res = translate names_of_def;
val res = translate cop_of_def;
val res = translate cexp_of_def;
val res = translate bindings_of_def;
val res = translate parse_prog_def;

(* -- printer -- *)

val res = translate dropWhile_def;
val res = translate printingTheory.is_comment_def;
val res = translate printingTheory.flatten_def;

val res = translate printingTheory.num2str_def;

val _ = Q.prove(
  ‘∀n. num2str_side n’,
  ho_match_mp_tac printingTheory.num2str_ind
  \\ rw [] \\ rw [Once (fetch "-" "num2str_side_def")]
  \\ gvs []
  \\ ‘n MOD 10 < 10’ by gvs []
  \\ decide_tac)
  |> update_precondition;

val res = translate printingTheory.num2ascii_def;
val res = translate printingTheory.ascii_name_def;

val _ = Q.prove(
  ‘∀n. ascii_name_side n’,
  fs [fetch "-" "ascii_name_side_def"]
  \\ once_rewrite_tac [printingTheory.num2ascii_def]
  \\ rw [] \\ gvs [AllCaseEqs()])
  |> update_precondition;

val res = translate printingTheory.name2str_def;

val res = translate printingTheory.dest_list_def;
val res = translate printingTheory.dest_quote_def;
val res = translate printingTheory.newlines_def;
val res = translate printingTheory.v2pretty_def;
val res = translate printingTheory.get_size_def;
val res = translate printingTheory.get_next_size_def;
val res = translate printingTheory.remove_all_def;
val res = translate printingTheory.smart_remove_def;
val res = translate printingTheory.annotate_def;
val res = translate printingTheory.v2str_def;
val res = translate printingTheory.vs2str_def;

val res = translate sexp_of_op_def;

val _ = Q.prove(
  ‘∀n. sexp_of_op_side n’,
  fs [fetch "-" "sexp_of_op_side_def"]
  \\ gvs [] \\ intLib.COOPER_TAC)
  |> update_precondition;

val res = translate sexp_of_def;
val res = translate str_of_def;

Definition compile_def:
  compile (s:mlstring) =
    implode (str_of (parse_prog (explode s)))
End

val compile_v_thm = translate compile_def;

(*
  Read prints reads all input from stdin, applies f (any function from
  string to string), and then prints the result to stdout.
 *)

val read_print = process_topdecs ‘
  fun read_print f =
    TextIO.print (f (TextIO.inputAll TextIO.stdIn));
  ’;

val _ = append_prog read_print;
val read_print_v_tm = fetch_v "read_print" (get_ml_prog_state ());

(*
  'map_stdin' is the specification of what read_print does to the
  file system model. It is parametrized on the file system and the function
  applied to process the input.
 *)

Definition map_stdin_def:
  map_stdin f fs =
    add_stdout (fastForwardFD fs 0)
               (f (implode (THE (ALOOKUP fs.inode_tbl (UStream «stdin»)))))
End

(*
  This is the CF specification for read_print.
 *)

Theorem read_print_spec:
  (∃inp. stdin fs inp 0) ⇒
  (STRING_TYPE --> STRING_TYPE) f fv ⇒
    app (p: 'ffi ffi_proj) ^read_print_v_tm [fv]
      (COMMANDLINE cl * STDIO fs)
      (POSTv uv.
         &UNIT_TYPE () uv *
         STDIO (map_stdin f fs))
Proof
  xcf_with_def "read_print" (fetch "-" "read_print_v_def")
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [STDIO_def] \\ xpull)
  \\ assume_tac INSTREAM_stdin
  \\ drule_then assume_tac stdin_get_file_content
  \\ drule_then strip_assume_tac STD_streams_get_mode
  \\ xlet_auto
  >- (
    xsimpl)
  \\ xlet_auto
  >- (
    xsimpl)
  \\ xapp
  \\ xsimpl
  \\ first_assum (irule_at Any) \\ fs []
  \\ qexists_tac ‘fastForwardFD fs 0’
  \\ xsimpl
  \\ fs [map_stdin_def, stdin_def]
  \\ xsimpl
QED

(*
  This is the main function. You should apply read_print to some pure function
  that has been translated using the translator. Use the name of this function
  in place of 'id' and 'I' in the definitions and specs below.
 *)

val main = process_topdecs ‘
  fun main u = read_print compile;
’;

val _ = append_prog main;
val main_v = fetch_v "main" (get_ml_prog_state ());

Theorem main_spec:
  (∃inp. stdin fs inp 0) ⇒
    app (p: 'ffi ffi_proj) ^main_v [Conv NONE []]
      (COMMANDLINE cl * STDIO fs)
      (POSTv uv.
        &UNIT_TYPE () uv *
        STDIO (map_stdin compile fs))
Proof
  xcf_with_def "main" (fetch "-" "main_v_def")
  \\ xapp
  \\ irule_at Any compile_v_thm \\ fs []
  \\ first_assum (irule_at Any)
QED

Theorem main_whole_prog_spec:
  (∃inp. stdin fs inp 0) ⇒
    whole_prog_spec ^main_v cl fs NONE ((=) (map_stdin compile fs))
Proof
  rw [whole_prog_spec_def, SEP_CLAUSES]
  \\ irule_at Any main_spec
  \\ first_assum (irule_at Any)
  \\ rw [map_stdin_def, GSYM add_stdo_with_numchars,
         GSYM fastForwardFD_with_numchars, with_same_numchars]
QED

val (semantics_thm, prog_tm) =
  whole_prog_thm (get_ml_prog_state ()) "main" (UNDISCH main_whole_prog_spec);

Definition io_prog_def:
  io_prog = ^prog_tm
End

Theorem io_prog_semantics_thm =
  semantics_thm
  |> ONCE_REWRITE_RULE [GSYM io_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO, GSYM CONJ_ASSOC];

val _ = export_theory ();
