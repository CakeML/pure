(*
  Compiles the PureCake compiler using the CakeML compiler
*)

open preamble pure_compilerProgTheory
     eval_cake_compile_x64Lib
     eval_cake_compile_arm8Lib

val _ = new_theory "pure_compilerCompile"

Theorem pure_compiler_compiled_x64 =
  Feedback.trace ("Theory.allow_rebinds", 1)
    (eval_cake_compile_x64 "" pure_compiler_prog_def) "pure.S";

Theorem pure_compiler_compiled_arm8 =
  Feedback.trace ("Theory.allow_rebinds", 1)
    (eval_cake_compile_arm8 "" pure_compiler_prog_def) "pure_arm8.S";

val _ = export_theory ();
