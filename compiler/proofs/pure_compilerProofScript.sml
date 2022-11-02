(*
   Correctness of PureLang compiler: concrete syntax -> CakeML AST
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_demandTheory
open pure_cexpTheory pure_to_cakeProofTheory pureParseTheory
     pure_inferenceProofTheory state_to_cakeProofTheory
     pure_letrec_cexpProofTheory pure_demands_analysisProofTheory
     fromSexpTheory simpleSexpParseTheory pure_compilerTheory
     pure_obs_sem_equalTheory;

val _ = set_grammar_ancestry
          ["pure_cexp", "pure_to_cakeProof", "pureParse", "pure_inferenceProof",
           "pure_letrec_cexpProof", "pure_demands_analysisProof", "fromSexp",
           "simpleSexpParse", "state_to_cakeProof", "pure_compiler"];

val _ = new_theory "pure_compilerProof";

(* ---- misc ---- *)

Definition string_to_ast_def:
  string_to_ast s =
    case parse_sexp (MAP (λx. (x,ARB)) s) of
    | NONE => NONE
    | SOME x => sexplist sexpdec x
End

Theorem string_to_ast_ast_to_string:
  string_to_ast (ast_to_string p) = SOME p
Proof
  fs [string_to_ast_def,ast_to_string_def,AllCaseEqs()]
  \\ fs [fromSexpTheory.sexplist_SOME,PULL_EXISTS]
  \\ qabbrev_tac ‘l1 = print_sexp (listsexp (MAP decsexp p))’
  \\ qabbrev_tac ‘l2 = MAP (λx. (x,ARB:locs)) l1’
  \\ irule_at Any simpleSexpParseTheory.parse_print
  \\ qexists_tac ‘MAP decsexp p’ \\ fs []
  \\ fs [Abbr‘l2’] \\ fs [MAP_MAP_o,combinTheory.o_DEF,SF ETA_ss]
  \\ irule fromSexpTheory.listsexp_valid
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

(* ---- main theorem ---- *)

Theorem pure_compiler_correct:
  compile s = SOME t ⇒
  ∃pure_ce ty cake_prog.
    string_to_cexp s = SOME (pure_ce,ty) ∧
    string_to_ast t = SOME cake_prog ∧
    safe_exp (exp_of pure_ce) ∧
    itree_rel
       (itree_of (exp_of pure_ce))
       (itree_semantics cake_prog)
Proof
  strip_tac \\ gvs [compile_def,AllCaseEqs()]
  \\ fs [string_to_ast_ast_to_string]
  \\ qabbrev_tac ‘e2 = demands_analysis (transform_cexp e1)’
  \\ qsuff_tac ‘itree_of (exp_of e1) = itree_of (exp_of e2)’
  >-
   (disch_then $ rewrite_tac o single
    \\ irule_at Any pure_to_cakeProofTheory.pure_to_cake_correct
    \\ fs [cns_ok_def]
    \\ imp_res_tac infer_types_SOME \\ fs [])
  \\ qabbrev_tac ‘e3 = transform_cexp e1’
  \\ qspec_then ‘e3’ mp_tac demands_analysis_soundness \\ fs []
  \\ dxrule_then strip_assume_tac infer_types_SOME
  \\ dxrule_then strip_assume_tac infer_types_SOME
  \\ fs [] \\ strip_tac
  \\ mp_tac safe_exp_app_bisim_F_IMP_same_itree
  \\ gvs [pure_exp_relTheory.app_bisimilarity_eq]
  \\ disch_then drule_all \\ fs []
  \\ qspec_then ‘e1’ mp_tac transform_cexp_correct
  \\ gvs [] \\ rpt strip_tac
  \\ mp_tac bisimilarity_IMP_semantics_eq
  \\ gvs [pure_exp_relTheory.app_bisimilarity_eq,GSYM pure_semanticsTheory.itree_of_def]
  \\ disch_then drule \\ fs []
  \\ disch_then irule
  \\ unabbrev_all_tac
  \\ imp_res_tac close_transform_cexp
QED

val _ = export_theory();