(*
  Compiles the PureCake compiler using the CakeML compiler
*)

open preamble compilationLib pure_compilerProgTheory;

val _ = new_theory "pure_compilerCompile"

Theorem pure_compiler_compiled =
  compile_x64 "pure" pure_compiler_prog_def;

val _ = export_theory ();
