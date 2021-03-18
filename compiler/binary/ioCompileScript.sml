(*
  Compiles the io program using the x86_64 backend.
*)
open ioProgTheory compilationLib x64_configTheory;

val _ = new_theory "ioCompile";

Theorem io_prog_compiled = compile_x64 "ioprog" io_prog_def;

val _ = export_theory ();

