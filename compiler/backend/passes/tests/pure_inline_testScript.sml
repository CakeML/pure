
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory;
open intLib pure_printTheory pure_printLib;
open pure_inline_cexpTheory;

val _ = new_theory "pure_inline_test";

val toMLstring = stringLib.fromMLstring o dest_QUOTE;

val ex = toMLstring `
  (letrec
    (map
        (lam (f lst)
          (case lst temp
              ((((Nil) (cons Nil))
                    ((Cons x xs) (cons Cons (app f x) (app map f xs))))
                  .  NONE))))
    (let f (lam (v) (+ v (int 1)))
        (letrec
          (map1
              (lam (lst)
                (case lst temp
                    ((((Nil) (cons Nil))
                          ((Cons x xs) (cons Cons (app f x) (app map1 f xs))))
                        .  NONE))))
          map1)))`;

val ex_cexp = “parse_cexp ^ex”
  |> EVAL |> concl |> rand;

val inline_paper =
  EVAL “inline_all 2 (tree_size_heuristic 100) ^ex_cexp” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp;

val example_paper = toMLstring `
  (letrec
    (map (lam (f lst)
      (case lst temp
        ((((Nil) (cons Nil))
          ((Cons (x xs)) (cons Cons (app f x) (app map f xs)))) . NONE))))

  (app map (lam (v) (+ v (int 1)))))`;

val example_paper_cexp = “parse_cexp ^example_paper”
  |> EVAL |> concl |> rand;

val inline_paper =
  EVAL “inline_all 1 (tree_size_heuristic 100) ^example_paper_cexp” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp;

Definition example_1_def:
  example_1 = parse_cexp "(let x (int 7) (lam (m) (app m x)))"
End

val inline_example_1 =
  EVAL “inline_all 2 (tree_size_heuristic 100) example_1” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp

Definition example_2_def:
  example_2 = parse_cexp "(let f (lam (x) (+ x (int 5))) (let y (app f (int 1)) (+ 1 y)))"
End

val inline_example_2 =
  EVAL “inline_all 2 (tree_size_heuristic 100) example_2” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp

Definition example_3_def:
  example_3 = parse_cexp "(letrec (map (lam (f) (lam (lst) (case lst temp ((((nil) nil) ((con (x xs)) (app (app (cons con) (app f x)) (app (app map f) xs))))  .  NONE))))) (let foo (lam (v) (+ v (int 1))) (app map foo)))"
End

val inline_example_3 =
  EVAL “inline_all 2 (tree_size_heuristic 100) example_3” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp

Definition example_4_def:
  example_4 = parse_cexp "(let f (lam (x) (+ x (int 5))) (app f (int 1)))"
End

val inline_example_4 =
  EVAL “inline_all 2 (tree_size_heuristic 100) example_4” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp

Definition example_5_def:
  example_5 = parse_cexp "(letrec (map (lam (f) (lam (lst) (case lst temp ((((nil) nil) ((con (x xs)) (app (app (cons con) (app f x)) (app (app map f) xs))))  .  NONE))))) (app map (lam (v) (+ v (int 1)))))"
End

val _ =
  EVAL “example_5” |> print_thm

val inline_example_5 =
  EVAL “inline_all 1 (tree_size_heuristic 100) example_5” |>
  concl |>
  rand |>
  rator |> rand |>
  print_cexp

val _ = export_theory();
