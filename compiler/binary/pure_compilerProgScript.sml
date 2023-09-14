(*
  Translation of top-level pure-to-cake compiler function.
 *)
open basis
     mlstringTheory
     pure_backendProgTheory
     pure_frontendProgTheory;

val _ = new_theory "pure_compilerProg";

val _ = set_grammar_ancestry ["pure_frontendProg", "mlstring"];

val _ = translation_extends "pure_frontendProg";

val _ = (max_print_depth := 30);

val res = translate pure_inferenceTheory.to_option_def;
val res = translate pure_compilerTheory.compile_def;
val res = translate pure_comp_confTheory.all_flags_def;
val res = translate (pure_comp_confTheory.read_cline_args_def
                       |> REWRITE_RULE [ml_translatorTheory.MEMBER_INTRO]);

Definition main_function_def:
  main_function cl s =
    case read_cline_args cl of
    | INR err_msg => err_msg
    | INL c =>
      case pure_compiler$compile c (explode s) of
      | NONE => strlit "ERROR"
      | SOME s => implode s
End

val _ = (next_ml_names := ["main_function"]);
val res = translate main_function_def;

val _ = type_of “main_function” = “:mlstring list -> mlstring -> mlstring”
        orelse failwith "The main_function has the wrong type.";

val main = process_topdecs
  `print (main_function (CommandLine.arguments())
                        (TextIO.inputAll TextIO.stdIn));`;

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand

Definition pure_compiler_prog_def:
  pure_compiler_prog = ^prog
End

val _ = export_theory ();
