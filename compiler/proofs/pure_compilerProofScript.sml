(*
   Correctness of PureLang compiler: concrete syntax -> CakeML AST
*)
Theory pure_compilerProof
Ancestors
  fixedPoint arithmetic list string alist option pair
  ltree llist bag pred_set relation
  rich_list finite_map pure_demand pure_obs_sem_equal
  pure_cexp pure_to_cakeProof pureParse pure_inferenceProof
  pure_letrec_cexpProof pure_demands_analysisProof fromSexp
  simpleSexpParse state_to_cakeProof pure_compiler
  pure_inline_cexpProof pure_letrecProof
Libs
  term_tactic dep_rewrite BasicProvers

Theorem string_to_cexp_wf:
  string_to_cexp s = SOME (ce,ns) ⇒
    closed (exp_of ce) ∧ NestedCase_free ce ∧ cexp_wf ce
Proof
  strip_tac >> gvs[string_to_cexp_def] >> pairarg_tac >> gvs[] >>
  drule_at Any $ iffLR ast_to_cexpTheory.closed_under >>
  simp[pure_expTheory.closed_def, pure_cexp_lemmasTheory.freevars_exp_of]
QED

Theorem transform_cexp_wf:
  transform_cexp c e = e' ∧ cexp_wf e ∧ NestedCase_free e ∧ closed (exp_of e)
  ⇒ cexp_wf e' ∧ NestedCase_free e' ∧ closed (exp_of e') ∧ letrecs_distinct (exp_of e')
Proof
  strip_tac >>
  gvs[transform_cexp_cexp_wf, transform_cexp_NestedCase_free,
      transform_cexp_closed, transform_cexp_letrecs_distinct]
QED

Theorem inline_top_level_wf:
  inline_top_level c e = e' ∧ cexp_wf e ∧ NestedCase_free e ∧
  closed (exp_of e) ∧ letrecs_distinct (exp_of e)
  ⇒ cexp_wf e' ∧ NestedCase_free e' ∧
    closed (exp_of e') ∧ letrecs_distinct (exp_of e')
Proof
  strip_tac >> gvs[pure_inline_cexpTheory.inline_top_level_def] >>
  drule_at Any inline_all_wf >> simp[]
QED

Theorem clean_cexp_wf:
  clean_cexp c e = e' ∧ cexp_wf e ∧ NestedCase_free e ∧ letrecs_distinct (exp_of e) ∧
  namespace_ok ns ∧ type_tcexp ns 0 [] [] (tcexp_of e) t
  ⇒ cexp_wf e' ∧ NestedCase_free e' ∧ letrecs_distinct (exp_of e') ∧
    type_tcexp ns 0 [] [] (tcexp_of e') t ∧ closed (exp_of e')
Proof
  strip_tac >> gvs[pure_letrec_cexpTheory.clean_cexp_def] >>
  `freevars (exp_of e) = {}` by (
    imp_res_tac pure_typingPropsTheory.type_tcexp_freevars_tcexp >>
    gvs[pure_tcexp_lemmasTheory.freevars_tcexp_of,
      pure_cexp_lemmasTheory.freevars_exp_of]) >>
  FULL_CASE_TAC >> gvs[pure_expTheory.closed_def] >>
  irule_at Any clean_all_cexp_cexp_wf >> simp[] >>
  drule_all clean_all_preserves_typing >> simp[] >> strip_tac >>
  drule_all $ SRULE [] pure_typingPropsTheory.type_tcexp_NestedCase_free >>
  simp[] >> strip_tac >> gvs[clean_all_cexp_correct, clean_all_letrecs_distinct] >>
  qspec_then `exp_of e` assume_tac freevars_clean_all >>
  gvs[SUBSET_DEF, pure_miscTheory.EMPTY_iff_NOTIN]
QED

Theorem demand_analysis_wf:
  demands_analysis c e = e' ∧
  NestedCase_free e ∧ cexp_wf e ∧ letrecs_distinct (exp_of e) ∧
  namespace_ok ns ∧ type_tcexp ns 0 [] [] (tcexp_of e) (M Unit)
  ⇒ cexp_wf e' ∧ closed (exp_of e') ∧ NestedCase_free e' ∧
    safe_exp (exp_of e') ∧ letrecs_distinct (exp_of e') ∧
    cns_arities_ok ns (cns_arities e')
Proof
  strip_tac >>
  drule_all demands_analysis_soundness >>
  disch_then $ qspec_then `c` assume_tac >> gvs[] >>
  drule well_typed_program_imps >> simp[] >>
  impl_tac >- gvs[pure_tcexp_lemmasTheory.cexp_wf_tcexp_wf] >> strip_tac >>
  gvs[pure_demands_analysisTheory.demands_analysis_def] >> FULL_CASE_TAC >> gvs[] >>
  qpat_abbrev_tac `d = demands_analysis_fun _ _ _` >>
  PairCases_on `d` >> gvs[] >>
  dxrule_then assume_tac $ cj 5 demands_analysis_fun_insert_seq >> gvs[] >>
  dxrule_all_then assume_tac pure_typingPropsTheory.insert_seq_imps >> gvs[] >>
  drule well_typed_program_imps >> gvs[pure_tcexp_lemmasTheory.cexp_wf_tcexp_wf]
QED

Triviality PAIR_ID:
  (λ(p1,p2). (p1,p2)) = I
Proof
  simp[FUN_EQ_THM] >> PairCases >> simp[]
QED

Triviality exp_eq_itree_eq:
  e1 ≅ e2 ∧ closed e1 ∧ closed e2 ⇒ itree_of e1 = itree_of e2
Proof
  rw[] >> dxrule_all $ iffRL pure_exp_relTheory.app_bisimilarity_eq >> strip_tac >>
  dxrule bisimilarity_IMP_semantics_eq >> rw[GSYM pure_semanticsTheory.itree_of_def]
QED

Theorem compiler_correctness:
  compile_to_ast c s = SOME cake ⇒
    ∃pure_ce ns.
      string_to_cexp s = SOME (pure_ce, ns) ∧
      safe_itree $ itree_of (exp_of pure_ce) ∧
      itree_rel
         (itree_of (exp_of pure_ce))
         (itree_semantics cake) ∧
      itree_semantics$safe_itree ffi_convention (itree_semantics cake)
Proof
  rw[] >> gvs[compile_to_ast_def, frontend_def, AllCaseEqs()] >>
  map_every qabbrev_tac [
    `tr = transform_cexp c e`, `inl = inline_top_level c tr`,
    `cl = clean_cexp c inl`, `dm = demands_analysis c cl`] >>
  drule string_to_cexp_wf >> strip_tac >>
  drule_at Any transform_cexp_wf >> simp[] >>
  disch_then $ qspec_then `c` assume_tac >> gvs[] >>
  drule_at Any inline_top_level_wf >> simp[] >>
  disch_then $ qspec_then `c` assume_tac >> gvs[] >>
  gvs[DefnBase.one_line_ify NONE pure_inferenceTheory.to_option_def, AllCaseEqs()] >>
  dxrule_then strip_assume_tac infer_types_OK >> simp[] >>
  `namespace_ok ((I ## K ns) initial_namespace)` by
    gvs[pure_typingTheory.namespace_init_ok_def] >>
  drule_at Any clean_cexp_wf >> simp[] >> rpt $ disch_then drule >>
  disch_then $ qspec_then `c` assume_tac >> gvs[] >>
  drule_at Any demand_analysis_wf >> simp[] >>
  disch_then $ qspec_then `c` assume_tac >> gvs[] >>
  qsuff_tac `itree_of (exp_of e) = itree_of (exp_of dm)`
  >- (
    strip_tac >> simp[] >>
    irule pure_to_cakeProofTheory.pure_to_cake_correct >> simp[cns_ok_def] >>
    simp[PULL_EXISTS, IMAGE_IMAGE, combinTheory.o_DEF, LAMBDA_PROD, PAIR_ID]
    ) >>
  drule string_to_cexp_wf >> strip_tac >>
  qspec_then `e` assume_tac transform_cexp_correct >> gvs[] >>
  drule_all exp_eq_itree_eq >> strip_tac >> gvs[] >>
  rev_drule_at (Pat `letrecs_distinct _`) $ cj 1 inline_top_level_correct >> simp[] >>
  disch_then $ qspec_then `c` assume_tac >> gvs[] >>
  drule_all exp_eq_itree_eq >> strip_tac >> gvs[] >>
  qspec_then `inl` assume_tac clean_cexp_correct >> gvs[] >>
  drule_all exp_eq_itree_eq >> strip_tac >> gvs[] >>
  qspec_then `cl` assume_tac demands_analysis_soundness >> gvs[] >>
  drule_all $ iffRL pure_exp_relTheory.app_bisimilarity_eq >> strip_tac >>
  irule safe_exp_app_bisim_F_IMP_same_itree >> simp[]
QED

Theorem alternative_compiler_correctness:
  frontend c s = SOME (ce, ns)
  ⇒ ∃ce' cake.
      string_to_cexp s = SOME (ce', ns) ∧
      compile_to_ast c s = SOME cake ∧
      itree_of (exp_of ce) = itree_of (exp_of ce') ∧
      itree_rel
         (itree_of (exp_of ce'))
         (itree_semantics cake) ∧
      itree_semantics$safe_itree ffi_convention (itree_semantics cake)
Proof
  strip_tac >> assume_tac $ Q.GEN `cake` compiler_correctness >>
  gvs[compile_to_ast_alt_def, frontend_def, AllCaseEqs()] >>
  drule string_to_cexp_wf >> strip_tac >>
  drule_at Any transform_cexp_wf >> simp[] >>
  disch_then $ qspec_then `c` assume_tac >> gvs[] >>
  qspec_then `e` assume_tac transform_cexp_correct >>
  drule_all exp_eq_itree_eq >> strip_tac >> gvs[] >>
  drule inline_top_level_correct >> simp[] >>
  disch_then $ qspec_then `c` assume_tac >> gvs[] >>
  drule_all exp_eq_itree_eq >> strip_tac >> gvs[]
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
  ∃pure_ce ns cake.
    string_to_cexp s = SOME (pure_ce,ns) ∧
    string_to_ast t = SOME cake ∧
    safe_exp (exp_of pure_ce) ∧
    itree_rel
       (itree_of (exp_of pure_ce))
       (itree_semantics cake) ∧
    itree_semantics$safe_itree ffi_convention (itree_semantics cake)
Proof
  rw[compile_to_string] >> simp[string_to_ast_ast_to_string] >>
  drule compiler_correctness >> simp[]
QED
