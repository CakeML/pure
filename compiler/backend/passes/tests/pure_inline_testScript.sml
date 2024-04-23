
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory;
open intLib pure_printTheory pure_printLib pureParseTheory;
open pure_inline_cexpTheory pure_letrec_spec_cexpTheory;

val _ = new_theory "pure_inline_test";

val toMLstring = stringLib.fromMLstring o dest_QUOTE;

val example_paper_partially_specialised = toMLstring `
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

val example_paper_partially_specialised_cexp = “parse_cexp ^example_paper_partially_specialised”
  |> EVAL |> concl |> rand;

val inline_example_paper_partially_specialised =
  EVAL “inline_all 5 (tree_size_heuristic 100) ^example_paper_partially_specialised_cexp” |>
  concl |>
  rand |>
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

val inline_example_paper =
  EVAL “inline_all 5 (tree_size_heuristic 100) ^example_paper_cexp” |>
  concl |>
  rand |>
  print_cexp;

val example_foldr_sum = toMLstring `
  (letrec
    (foldr (lam (f x lst)
      (case lst temp
        ((((Nil) x)
          ((Cons (y ys)) (app f y (app foldr f x ys)))) . NONE))))

  (app foldr (lam (v w) (+ v w)) (int 0)))`;

val example_foldr_sum_cexp = “parse_cexp ^example_foldr_sum”
  |> EVAL |> concl |> rand;

val inline_example_foldr_sum =
  EVAL “inline_all 5 (tree_size_heuristic 100) ^example_foldr_sum_cexp” |>
  concl |>
  rand |>
  print_cexp;

val map_def = toMLstring `
    (lam (f lst)
      (case lst temp
        ((((Nil) (cons Nil))
          ((Cons (x xs)) (cons Cons (app f x) (app map f xs)))) . NONE)))`;

val map_def_cexp = “parse_cexp ^map_def”
  |> EVAL |> concl |> rand;

val specialise_map_def =
  EVAL “specialise «map» ^map_def_cexp” |>
  concl |>
  rand |>
  rand |>
  print_cexp;

val mapfy_def = toMLstring `
    (lam (f lst y)
      (case lst temp
        ((((Nil) (cons Nil))
          ((Cons (x xs)) (cons Cons (app f x y) (app mapfy f xs y)))) . NONE)))`;

val mapfy_def_cexp = “parse_cexp ^mapfy_def”
  |> EVAL |> concl |> rand;

val specialise_mapfy_def =
  EVAL “specialise «mapfy» ^mapfy_def_cexp” |>
  concl |>
  rand |>
  rand |>
  print_cexp;

val sum_letrec = toMLstring `
  (letrec
    (sum (lam (lst)
      (case lst temp
        ((((Nil) (int 0))
          ((Cons (x xs)) (+ x (app sum xs)))) . NONE))))

  (app sum (cons Cons (int 1) (cons Cons (int 2) (cons Cons (int 3) (cons Nil))))))`;

val sum_letrec_cexp = “parse_cexp ^sum_letrec”
  |> EVAL |> concl |> rand;

val inline_sum_letrec =
  EVAL “inline_all 5 (tree_size_heuristic 100) ^sum_letrec_cexp” |>
  concl |>
  rand |>
  print_cexp;

Definition example_1_def:
  example_1 = parse_cexp "(let x (int 7) (lam (m) (app m x)))"
End

val inline_example_1 =
  EVAL “inline_all 2 (tree_size_heuristic 100) example_1” |>
  concl |>
  rand |>
  print_cexp

Definition example_2_def:
  example_2 = parse_cexp "(let f (lam (x) (+ x (int 5))) (let y (app f (int 1)) (+ 1 y)))"
End

val inline_example_2 =
  EVAL “inline_all 2 (tree_size_heuristic 100) example_2” |>
  concl |>
  rand |>
  print_cexp

Definition example_3_def:
  example_3 = parse_cexp "(letrec (map (lam (f) (lam (lst) (case lst temp ((((nil) nil) ((con (x xs)) (app (app (cons con) (app f x)) (app (app map f) xs))))  .  NONE))))) (let foo (lam (v) (+ v (int 1))) (app map foo)))"
End

val inline_example_3 =
  EVAL “inline_all 2 (tree_size_heuristic 100) example_3” |>
  concl |>
  rand |>
  print_cexp

Definition example_4_def:
  example_4 = parse_cexp "(let f (lam (x) (+ x (int 5))) (app f (int 1)))"
End

val inline_example_4 =
  EVAL “inline_all 2 (tree_size_heuristic 100) example_4” |>
  concl |>
  rand |>
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
  print_cexp

val _ = export_theory();
