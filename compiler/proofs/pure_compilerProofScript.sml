(*
   Correctness of PureLang compiler: concrete syntax -> CakeML AST
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_demandTheory pure_letrecProofTheory;
open pure_cexpTheory pure_to_cakeProofTheory pureParseTheory
     pure_inferenceProofTheory state_to_cakeProofTheory
     pure_letrec_cexpProofTheory pure_demands_analysisProofTheory
     fromSexpTheory simpleSexpParseTheory pure_compilerTheory
     pure_obs_sem_equalTheory;

val _ = set_grammar_ancestry
          ["pure_cexp", "pure_to_cakeProof", "pureParse", "pure_inferenceProof",
           "pure_letrec_cexpProof", "pure_demands_analysisProof", "fromSexp",
           "simpleSexpParse", "state_to_cakeProof", "pure_compiler", "pure_letrecProof"];

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
  compile c s = SOME t ⇒
  ∃pure_ce ty cake_prog.
    string_to_cexp s = SOME (pure_ce,ty) ∧
    string_to_ast t = SOME cake_prog ∧
    safe_exp (exp_of pure_ce) ∧
    itree_rel
       (itree_of (exp_of pure_ce))
       (itree_semantics cake_prog)
Proof
  cheat
  (* strip_tac \\ gvs [compile_def,AllCaseEqs()]
  \\ fs [string_to_ast_ast_to_string]
  \\ qabbrev_tac ‘e3 = transform_cexp c e1’
  \\ qabbrev_tac ‘e2 = demands_analysis c e3’
  \\ ‘letrecs_distinct (exp_of e3)’
     by simp [Abbr ‘e3’, transform_cexp_letrecs_distinct]
  \\ qspec_then ‘e3’ assume_tac demands_analysis_soundness \\ fs []
  \\ gvs[DefnBase.one_line_ify NONE pure_inferenceTheory.to_option_def, AllCaseEqs()]
  \\ drule_then strip_assume_tac infer_types_SOME
  \\ gvs[pure_inferenceTheory.infer_types_def, pure_inferenceTheory.fail_def,
         pure_typingTheory.namespace_init_ok_def, AllCaseEqs()] >>
     drule $ INST_TYPE [alpha |-> ``:(mlstring,unit) map``] infer_top_level_typed >>
     disch_then $ qspecl_then [`empty`,`e3`] assume_tac >> gvs[] >>
     gvs[pure_demands_analysisTheory.demands_analysis_def] >>
     qabbrev_tac `d = demands_analysis_fun Nil e3 (empty str_compare)` >>
     PairCases_on `d` >> gvs[] >>
     dxrule_then assume_tac $ cj 5 demands_analysis_fun_insert_seq >> gvs[] >>
     dxrule_all_then assume_tac pure_typingPropsTheory.insert_seq_imps >> gvs[] >>
     dxrule well_typed_program_imps >> disch_then drule >>
     impl_tac >- gvs[pure_tcexp_lemmasTheory.cexp_wf_tcexp_wf] >> strip_tac
  \\ qsuff_tac ‘itree_of (exp_of e1) = itree_of (exp_of d1)’
  >- (
    disch_then $ rewrite_tac o single
    \\ irule_at Any pure_to_cakeProofTheory.pure_to_cake_correct
    \\ fs [cns_ok_def, pure_typingTheory.namespace_init_ok_def, EXISTS_PROD]
    )
  \\ mp_tac safe_exp_app_bisim_F_IMP_same_itree
  \\ gvs [pure_exp_relTheory.app_bisimilarity_eq]
  \\ disch_then drule_all \\ fs []
  \\ qspec_then ‘e1’ mp_tac transform_cexp_correct
  \\ gvs [] \\ rpt strip_tac
  \\ mp_tac bisimilarity_IMP_semantics_eq
  \\ gvs [pure_exp_relTheory.app_bisimilarity_eq,GSYM pure_semanticsTheory.itree_of_def]
  \\ disch_then drule \\ fs []
  \\ disch_then irule
  \\ simp[pure_expTheory.closed_def, pure_cexp_lemmasTheory.freevars_exp_of]
  \\ gvs[string_to_cexp_def] \\ pairarg_tac \\ gvs[]
  \\ drule_at Any $ iffLR ast_to_cexpTheory.closed_under \\ simp[] *)
QED

val _ = export_theory();
