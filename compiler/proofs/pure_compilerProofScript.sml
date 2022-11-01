(*
   Correctness of PureLang compiler: concrete syntax -> CakeML AST
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_demandTheory
open pure_cexpTheory pure_to_cakeProofTheory pureParseTheory
     pure_inferenceProofTheory
     pure_letrec_cexpProofTheory pure_demands_analysisProofTheory
     fromSexpTheory simpleSexpParseTheory;

val _ = set_grammar_ancestry
          ["pure_cexp", "pure_to_cakeProof", "pureParse", "pure_inferenceProof",
           "pure_letrec_cexpProof", "pure_demands_analysisProof", "fromSexp"];

val _ = new_theory "pure_compilerProof";





val _ = export_theory();
