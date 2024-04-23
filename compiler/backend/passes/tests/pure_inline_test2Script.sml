open HolKernel Parse boolLib bossLib;
open cst_to_astTheory purePEGTheory testutils ast_to_cexpTheory;
open pureParseTheory;
open pure_inline_cexpTheory pure_letrec_spec_cexpTheory;
open pure_printTheory pure_printLib;

open pure_inferenceLib pure_letrec_cexpTheory pure_demands_analysisTheory;

val _ = new_theory "pure_inline_test2";

val _ = computeLib.add_funs [pure_lexer_implTheory.get_token_def,
                             listTheory.LIST_REL_def,
                             ASCIInumbersTheory.s2n_compute,
                             numposrepTheory.l2n_def];

Theorem annot_example_1 = EVAL ``
    let parse_res = (string_to_cexp0
      "f i j = let g x = x + 2\n\
      \            {-# INLINE g #-}\n\
      \        in  i + (g j)\n"
    ) in
    case parse_res of
    | SOME (cexp, _) => SOME (str_of (inline_all 5 (tree_size_heuristic 5) cexp))
    | NONE => NONE
  ``;

Theorem odd_even = EVAL ``
    let parse_res = (string_to_cexp0
      "odd i = if i == 0 then False else even (i - 1)\n\
      \{-# INLINE odd #-}\n\
      \even i = if i == 0 then True else odd (i - 1)\n"
    ) in
    case parse_res of
    | SOME (cexp, _) => SOME (str_of (inline_all 5 (tree_size_heuristic 5) cexp))
    | NONE => NONE
  ``;

Theorem annot_let_1 = EVAL ``
    let parse_res = (string_to_cexp0
      "i = 1\n\
      \{-# INLINE i #-}\n\
      \j = i + 1"
    ) in
    case parse_res of
    | SOME (cexp, _) => SOME (str_of (inline_all 5 (tree_size_heuristic 5) cexp))
    | NONE => NONE
  ``;

Theorem map_spec = EVAL ``
    let parse_res = (string_to_cexp0
      "suc_list = let map f l = case l of\n\
      \                           [] -> []\n\
      \                           x:xs -> f x : map f xs\n\
      \           in map (\\ x -> x + 1)"
    ) in
    case parse_res of
    | SOME (cexp, _) => SOME (str_of (inline_all 5 (tree_size_heuristic 5) cexp))
    | NONE => NONE
  ``;

Theorem map_spec_annot = EVAL ``
    let parse_res = (string_to_cexp0
      "suc_list = let {-# INLINE map #-}\n\
      \               map f l = case l of\n\
      \                           [] -> []\n\
      \                           x:xs -> f x : map f xs\n\
      \           in map (\\ x -> x + 1)"
    ) in
    case parse_res of
    | SOME (cexp, _) => SOME (str_of (inline_all 5 (tree_size_heuristic 5) cexp))
    | NONE => NONE
  ``;

val _ = export_theory();
