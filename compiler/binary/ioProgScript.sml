(*
  A CakeML program that reads from stdio, applies a pure function, and
  prints to stdout.
 *)
open basis;

val _ = new_theory "ioProg";

val _ = translation_extends "basisProg";

(*
  Read prints reads all input from stdin, applies f (any function from
  string to string), and then prints the result to stdout.
 *)

val read_print = process_topdecs ‘
  fun read_print f =
    TextIO.print (f (TextIO.inputAll TextIO.stdIn));
  ’;

val _ = append_prog read_print;
val st = get_ml_prog_state ();
val read_print_v_tm = fetch_v "read_print" st;

(*
  'process_stdin_using' is the specification of what read_print does to the
  file system model. It is parametrized on the file system and the function
  applied to process the input.
 *)

Definition process_stdin_using_def:
  process_stdin_using fs f =
    add_stdout (fastForwardFD fs 0)
               (f (concat (all_lines_inode fs (UStream «stdin»))))
End

(*
  This is the CF specification for read_print.
 *)

Theorem read_print_spec:
  (∃inp. stdin fs inp 0) ⇒
  (STRING_TYPE --> STRING_TYPE) f fv ⇒
    app (p: 'ffi ffi_proj) ^read_print_v_tm [fv]
      (STDIO fs * COMMANDLINE cl)
      (POSTv uv.
         &UNIT_TYPE () uv *
         STDIO (process_stdin_using fs f) *
         COMMANDLINE cl)
Proof
  xcf "read_print" st
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
  \\ simp [process_stdin_using_def]
  \\ fs [stdin_def]
  \\ cheat
QED

(*
  This is the main function. You should apply read_print to some pure function
  that has been translated using the translator. Use the name of this function
  in place of 'id' and 'I' in the definitions and specs below.
 *)

val main = process_topdecs ‘
  fun main u = read_print id;
  ’;

val _ = append_prog main;
val st = get_ml_prog_state ();
val main_v = fetch_v "main" st;

Theorem main_spec:
  app (p: 'ffi ffi_proj) ^main_v [fv]
    (STDIO fs * COMMANDLINE cl)
    (POSTv uv.
      &UNIT_TYPE () uv *
      STDIO (process_stdin_using fs I) *
      COMMANDLINE cl)
Proof
  xcf "main" st
  \\ xapp
  \\ irule_at Any i_v_thm \\ fs []
  \\ cheat
QED

Theorem main_whole_prog_spec:
  whole_prog_spec ^main_v cl fs NONE
    ((=) (process_stdin_using fs I))
Proof
  cheat
QED

val st = get_ml_prog_state ();
val (semantics_thm, prog_tm) =
  whole_prog_thm st "main" ((*UNDISCH*) main_whole_prog_spec);

Definition io_prog_def:
  io_prog = ^prog_tm
End

Theorem io_prog_semantics_thm =
  semantics_thm
  |> ONCE_REWRITE_RULE [GSYM io_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO, GSYM CONJ_ASSOC];

val _ = export_theory ();

