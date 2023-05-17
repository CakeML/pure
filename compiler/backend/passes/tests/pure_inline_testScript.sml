
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory;
open intLib pure_printTheory pure_printLib;
open pure_inline_cexpTheory;

val _ = new_theory "pure_inline_test";

Definition example_1_def:
  example_1 = parse_cexp "(let x (int 7) (lam (m) (app m x)))"
End

val inline_example_1 =
  EVAL “inline_all_new (tree_size_heuristic 100) example_1” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp

Definition example_2_def:
  example_2 = parse_cexp "(let f (lam (x) (+ x (int 5))) (let y (app f (int 1)) (+ 1 y)))"
End

val inline_example_2 =
  EVAL “inline_all_new (tree_size_heuristic 100) example_2” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp

Definition example_3_def:
  example_3 = parse_cexp "(letrec (map (lam (f) (lam (lst) (case lst temp ((((nil) nil) ((con (x xs)) (app (app (cons con) (app f x)) (app (app map f) xs))))  .  NONE))))) (let foo (lam (v) (+ v (int 1))) (app map foo)))"
End

val inline_example_3 =
  EVAL “inline_all_new (tree_size_heuristic 100) example_3” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp

Definition example_4_def:
  example_4 = parse_cexp "(let f (lam (x) (+ x (int 5))) (app f (int 1)))"
End

val inline_example_4 =
  EVAL “inline_all_new (tree_size_heuristic 100) example_4” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp

val _ = export_theory();
