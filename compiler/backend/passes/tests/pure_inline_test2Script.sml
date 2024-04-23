open HolKernel Parse boolLib bossLib
open cst_to_astTheory purePEGTheory testutils ast_to_cexpTheory
open pureParseTheory;

open pure_inferenceLib pure_letrec_cexpTheory pure_demands_analysisTheory

val _ = new_theory "pure_inline_test2";

val _ = computeLib.add_funs [pure_lexer_implTheory.get_token_def,
                             listTheory.LIST_REL_def,
                             ASCIInumbersTheory.s2n_compute,
                             numposrepTheory.l2n_def]


Theorem test = EVAL ``string_to_cexp0
             "f :: Int -> Int -> Int\n\
             \f i j = let g x = x + 2\n\
             \            {-# INLINE g #-}\n\
             \        in  i + (g j)\n"``;

val _ = export_theory();
