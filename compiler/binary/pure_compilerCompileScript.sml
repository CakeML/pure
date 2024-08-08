(*
  Compiles the PureCake compiler using the CakeML compiler
*)

open preamble pure_compilerProgTheory eval_cake_compile_x64Lib

val _ = new_theory "pure_compilerCompile"

Theorem pure_compiler_compiled =
  eval_cake_compile_x64 "" pure_compiler_prog_def "pure.S";

val _ = export_theory ();
