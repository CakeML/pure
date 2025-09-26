(*
  Compiles the PureCake compiler using the CakeML compiler
*)
Theory pure_compilerCompile
Ancestors
  pure_compilerProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib


Theorem pure_compiler_compiled_x64 =
  eval_cake_compile_x64 "x64_" pure_compiler_prog_def "pure.S";

Theorem pure_compiler_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" pure_compiler_prog_def "pure_arm8.S";

