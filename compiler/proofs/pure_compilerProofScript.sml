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

Theorem compiler_correctness:
  compile_to_ast c s = SOME cake ⇒
    ∃pure_ce ns.
      frontend c s = SOME (pure_ce, ns) ∧
      safe_itree $ itree_of (exp_of pure_ce) ∧
      itree_rel
         (itree_of (exp_of pure_ce))
         (itree_semantics cake)
Proof
  strip_tac \\ gvs [compile_to_ast_def,frontend_def,AllCaseEqs()]
  \\ qabbrev_tac ‘e4 = transform_cexp c e1’
  \\ qabbrev_tac ‘e3 = clean_cexp c e4’
  \\ qabbrev_tac ‘e2 = demands_analysis c e3’
  \\ ‘letrecs_distinct (exp_of e3)’ by (
      simp[Abbr `e3`, Abbr `e4`] >>
      irule clean_cexp_letrecs_distinct >> simp[transform_cexp_letrecs_distinct])
  \\ qspec_then ‘e3’ assume_tac demands_analysis_soundness \\ fs []
  \\ gvs[DefnBase.one_line_ify NONE pure_inferenceTheory.to_option_def, AllCaseEqs()]
  \\ drule_then strip_assume_tac infer_types_SOME
  \\ gvs[pure_inferenceTheory.infer_types_def, pure_inferenceTheory.fail_def,
         pure_typingTheory.namespace_init_ok_def, AllCaseEqs()] >>
     drule $ INST_TYPE [alpha |-> ``:(mlstring,unit) map``] infer_top_level_typed >>
     disch_then $ qspecl_then [`empty`,`e4`] assume_tac >> gvs[] >>
     `cexp_wf e3 ∧ NestedCase_free e3 ∧
      type_tcexp (append_ns initial_namespace ns') 0 [] [] (tcexp_of e3) (M Unit)` by (
        gvs[pure_letrec_cexpTheory.clean_cexp_def] >> FULL_CASE_TAC >> gvs[Abbr `e3`] >>
        irule_at Any clean_all_cexp_cexp_wf >> simp[] >>
        drule_all clean_all_preserves_typing >> rw[] >>
        irule pure_typingPropsTheory.type_tcexp_NestedCase_free >> simp[SF SFY_ss]) >>
     `cexp_wf e2 ∧ NestedCase_free e2 ∧
      type_tcexp (append_ns initial_namespace ns') 0 [] [] (tcexp_of e2) (M Unit)`
      by (
        gvs[pure_demands_analysisTheory.demands_analysis_def] >>
        FULL_CASE_TAC >> gvs[] >>
        qabbrev_tac `d = demands_analysis_fun Nil e3 (empty str_compare)` >>
        PairCases_on `d` >> gvs[] >>
        dxrule_then assume_tac $ cj 5 demands_analysis_fun_insert_seq >> gvs[] >>
        dxrule_all_then assume_tac pure_typingPropsTheory.insert_seq_imps >> gvs[]
        ) >>
     dxrule well_typed_program_imps >> simp[] >>
     impl_tac >- gvs[pure_tcexp_lemmasTheory.cexp_wf_tcexp_wf] >> strip_tac
  \\ qsuff_tac ‘itree_of (exp_of e4) = itree_of (exp_of e2)’
  >- (
    disch_then $ rewrite_tac o single \\ simp[]
    \\ irule_at Any pure_to_cakeProofTheory.pure_to_cake_correct
    \\ fs [cns_ok_def, pure_typingTheory.namespace_init_ok_def, EXISTS_PROD]
    ) >>
  qspec_then `e4` mp_tac clean_cexp_correct >> strip_tac >>
  dxrule_at Any $ iffRL pure_exp_relTheory.app_bisimilarity_eq >> simp[] >> impl_tac
  >- (
    imp_res_tac pure_typingPropsTheory.type_tcexp_freevars_tcexp >>
    gvs[pure_tcexp_lemmasTheory.freevars_tcexp_of,
        pure_cexp_lemmasTheory.freevars_exp_of, pure_expTheory.closed_def]
    ) >>
  strip_tac >> dxrule bisimilarity_IMP_semantics_eq >>
  rw[GSYM pure_semanticsTheory.itree_of_def] >>
  irule safe_exp_app_bisim_F_IMP_same_itree >> gvs[] >>
  irule $ iffRL pure_exp_relTheory.app_bisimilarity_eq >> gvs[] >>
  imp_res_tac pure_typingPropsTheory.type_tcexp_freevars_tcexp >>
  gvs[pure_tcexp_lemmasTheory.freevars_tcexp_of,
      pure_cexp_lemmasTheory.freevars_exp_of, pure_expTheory.closed_def]
QED

Theorem alternative_compiler_correctness:
  frontend c s = SOME (pure_ce, ns)
  ⇒ safe_itree $ itree_of (exp_of pure_ce) ∧
    ∃cake.
      compile_to_ast c s = SOME cake ∧
      itree_rel
         (itree_of (exp_of pure_ce))
         (itree_semantics cake)
Proof
  strip_tac >> assume_tac $ Q.GEN `cake` compiler_correctness >>
  gvs[compile_to_ast_alt_def]
QED


(********** AST <-> string **********)

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


(********** Correctness wrt strings **********)

Theorem pure_compiler_to_string_correct:
  compile c s = SOME t ⇒
  ∃pure_ce ty cake_prog.
    string_to_cexp s = SOME (pure_ce,ty) ∧
    string_to_ast t = SOME cake_prog ∧
    safe_exp (exp_of pure_ce) ∧
    itree_rel
       (itree_of (exp_of pure_ce))
       (itree_semantics cake_prog)
Proof
  rw[compile_to_string] >> simp[string_to_ast_ast_to_string] >>
  drule compiler_correctness >> rw[] >> gvs[frontend_def, AllCaseEqs()] >>
  qspec_then `e1` assume_tac transform_cexp_correct >>
  drule_at Any $ iffRL pure_exp_relTheory.app_bisimilarity_eq >> reverse impl_tac
  >- (
    rw[] >> drule bisimilarity_IMP_semantics_eq >>
    simp[GSYM pure_semanticsTheory.itree_of_def]
    ) >>
  gvs[DefnBase.one_line_ify NONE pure_inferenceTheory.to_option_def, AllCaseEqs()] >>
  drule infer_types_SOME >> strip_tac >>
  gvs[string_to_cexp_def] >> pairarg_tac >> gvs[] >>
  drule_at Any $ iffLR ast_to_cexpTheory.closed_under >>
  simp[pure_expTheory.closed_def, pure_cexp_lemmasTheory.freevars_exp_of]
QED

val _ = export_theory();
