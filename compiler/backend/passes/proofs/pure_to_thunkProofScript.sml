(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory combinTheory
     pure_semanticsTheory thunkLangTheory thunk_semanticsTheory pure_evalTheory
     thunkLang_primitivesTheory pure_exp_lemmasTheory pure_miscTheory pure_expTheory
     pure_to_thunk_2ProofTheory pure_cexpTheory pureLangTheory thunk_cexpTheory
     var_setTheory pure_namesTheory pure_namesProofTheory pure_to_thunkTheory
     thunk_split_Delay_LamTheory thunk_split_Delay_LamProofTheory pure_letrecProofTheory;
local open pure_demands_analysisProofTheory thunk_let_force_1ProofTheory in end

val _ = new_theory "pure_to_thunkProof";

val _ = set_grammar_ancestry
          ["pure_to_thunk", "pure_to_thunk_2Proof", "pure_cexp", "thunk_exp_of",
           "thunkLang", "thunk_cexp", "pureLang", "var_set", "pure_namesProof",
           "thunk_split_Delay_Lam", "pure_letrecProof"];

Triviality BIGUNION_set_MAP_SUBSET:
  ∀ys f t. BIGUNION (set (MAP f ys)) ⊆ t ⇔ EVERY (λy. f y ⊆ t) ys
Proof
  Induct \\ fs []
QED

Theorem MEM_explode_MAP_explode:
  ∀xs. MEM w xs ⇒ MEM (explode w) (MAP explode xs)
Proof
  Induct \\ fs [] \\ rw [] \\ fs []
QED

Theorem freevars_IMP_allvars:
  ∀x i. i IN freevars x ⇒ i IN allvars x
Proof
  ho_match_mp_tac pure_expTheory.freevars_ind
  \\ rw [] \\ gvs [MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ fs []
  >- (first_assum $ irule_at Any \\ fs [])
  \\ rename [‘MEM yy _’] \\ PairCases_on ‘yy’
  \\ fs [EXISTS_PROD,FORALL_PROD]
  \\ res_tac \\ fs [] \\ metis_tac []
QED

Theorem boundvars_lets_for:
  ∀list constr len w e.
    thunkLang$boundvars (lets_for len constr w list e)
    ⊆ {w} ∪ (set (MAP SND list)) ∪ boundvars e
Proof
  Induct
  \\ gs [thunk_exp_ofTheory.lets_for_def, FORALL_PROD, thunkLangTheory.boundvars_def]
  \\ rw []
  \\ irule SUBSET_TRANS
  \\ last_x_assum $ irule_at Any
  \\ simp [SUBSET_DEF]
QED

Theorem boundvars_rows_of_NONE:
  ∀rows w. boundvars (thunk_exp_of$rows_of w rows NONE) ⊆ {w} ∪ BIGUNION (set (MAP (set o FST o SND) rows))
                     ∪ BIGUNION (set (MAP (boundvars o SND o SND) rows))
Proof
  Induct
  \\ gs [FORALL_PROD, thunk_exp_ofTheory.rows_of_def, thunkLangTheory.boundvars_def]
  \\ rw []
  >- (irule SUBSET_TRANS
      \\ irule_at Any boundvars_lets_for
      \\ simp [SUBSET_DEF, MEM_EL, EL_MAP, indexedListsTheory.EL_MAPi, PULL_EXISTS]
      \\ gen_tac \\ strip_tac
      \\ metis_tac [])
  \\ irule SUBSET_TRANS
  \\ pop_assum $ irule_at Any
  \\ simp [SUBSET_DEF]
QED

Theorem boundvars_rows_of_SOME:
  ∀rows w pats e. boundvars (thunk_exp_of$rows_of w rows (SOME (pats, e)))
                     ⊆ {w} ∪ BIGUNION (set (MAP (set o FST o SND) rows))
                     ∪ BIGUNION (set (MAP (boundvars o SND o SND) rows))
                     ∪ boundvars e
Proof
  Induct
  \\ gs [FORALL_PROD, thunk_exp_ofTheory.rows_of_def,
         thunkLangTheory.boundvars_def, boundvars_Disj]
  \\ rw []
  >- (irule SUBSET_TRANS
      \\ irule_at Any boundvars_lets_for
      \\ simp [SUBSET_DEF, MEM_EL, EL_MAP, indexedListsTheory.EL_MAPi, PULL_EXISTS]
      \\ gen_tac \\ strip_tac
      \\ metis_tac [])
  \\ irule SUBSET_TRANS
  \\ pop_assum $ irule_at Any
  \\ simp [SUBSET_DEF]
QED

Theorem LIST_REL_MAP_ALT:
  ∀xs ys. LIST_REL P xs (MAP f ys) ⇔ LIST_REL (λx y. P x (f y)) xs ys
Proof
  Induct \\ fs [PULL_EXISTS,MAP_EQ_CONS]
QED

Theorem IMP_mk_delay_eq_Delay:
  exp_rel x1 y1 ∧ (∀c v. x1 = Var c v ⇒ mk_delay flag y1 ≠ Var v) ⇒
  ∃x2. exp_rel x1 x2 ∧ mk_delay flag y1 = Delay x2
Proof
  Cases_on ‘∃c m. x1 = Var c m’ \\ gvs []
  >- (
    simp [Once exp_rel_cases] \\ rw [] \\ fs [mk_delay_def, AllCaseEqs()] >>
    simp[Once exp_rel_cases]
    ) >>
  Cases_on ‘x1’ \\ gvs []
  \\ strip_tac
  \\ first_assum $ irule_at $ Pos hd
  \\ pop_assum mp_tac
  \\ rw[Once exp_rel_cases]
  \\ gvs [mk_delay_def]
QED

Theorem cns_arities_mk_delay:
  ∀e flag. cns_arities (mk_delay flag e) = cns_arities e
Proof
  Cases \\ simp [mk_delay_def, thunk_cexpTheory.cns_arities_def]
  \\ CASE_TAC \\ simp [thunk_cexpTheory.cns_arities_def]
  \\ Cases \\ simp[thunk_cexpTheory.cns_arities_def]
QED

Theorem boundvars_exp_of_mk_delay:
  ∀e flag. boundvars (exp_of (mk_delay flag e)) = boundvars (exp_of e)
Proof
  Cases \\ simp [mk_delay_def, Once exp_of_def, thunkLangTheory.boundvars_def]
  \\ CASE_TAC \\ simp [exp_of_def, thunkLangTheory.boundvars_def]
  \\ Cases \\ simp[exp_of_def, thunkLangTheory.boundvars_def]
QED

Theorem cexp_wf_mk_delay:
  ∀e flag. cexp_wf (mk_delay flag e) = cexp_wf e
Proof
  Cases \\ simp [mk_delay_def, thunk_exp_ofTheory.cexp_wf_def]
  \\ CASE_TAC \\ simp [thunk_exp_ofTheory.cexp_wf_def]
  \\ Cases \\ simp [thunk_exp_ofTheory.cexp_wf_def]
QED

Triviality mop_of_mlstring_NONE:
  mop_of_mlstring m = NONE ⇒ ~(explode m ∈ monad_cns)
Proof
  rw [mop_of_mlstring_def]
  \\ Cases_on ‘m’ \\ gvs []
  \\ EVAL_TAC \\ rw []
QED

Triviality mop_of_mlstring_SOME:
  mop_of_mlstring m = SOME x ⇒ explode m ∈ monad_cns
Proof
  rw [mop_of_mlstring_def]
  \\ gvs [EVAL “monad_cns”]
QED

Theorem mk_delay_not_Delay:
  mk_delay flag y ≠ Delay y ⇔ flag ∧ ∃n. y = Force (Var n)
Proof
  fs [mk_delay_def] \\ rw [] \\ Cases_on ‘y’ \\ fs []
  \\ Cases_on ‘c’ \\ gvs []
QED

Theorem to_thunk_eq_Force_Var:
  to_thunk b s h = (Force (Var n),s') ∧ NestedCase_free h ⇒ ∃a. h = Var a n
Proof
  Cases_on ‘h’ \\ gvs [to_thunk_def]
  \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()] \\ rw [])
  \\ gvs [monad_to_thunk_def |> DefnBase.one_line_ify NONE, AllCaseEqs()]
QED

Theorem exp_rel_to_thunk:
  (∀flag s (x:'a pure_cexp$cexp) x1 s1.
    to_thunk flag s x = (x1,s1) ∧ NestedCase_free x ∧ vars_ok s ∧
    allvars_of x ⊆ set_of s ∧ cexp_wf x ∧ letrecs_distinct (exp_of x) ⇒
    exp_rel x x1 ∧ set_of s ⊆ set_of s1 ∧ vars_ok s1 ∧ boundvars (exp_of x1) ⊆ set_of s1 ∧
    cexp_wf x1 ∧
    cns_arities x1 ⊆ IMAGE (IMAGE (explode ## I)) (cns_arities x)) ∧
  (∀flag s (xs:('a pure_cexp$cexp) list) xs1 s1.
    to_thunk_list flag s xs = (xs1,s1) ∧ EVERY NestedCase_free xs ∧ vars_ok s ∧
    EVERY (λx.  allvars_of x ⊆ set_of s) xs ∧ EVERY cexp_wf xs ∧
    EVERY (λe. letrecs_distinct (exp_of e)) xs ⇒
    LIST_REL exp_rel xs xs1 ∧ set_of s ⊆ set_of s1 ∧ vars_ok s1 ∧
    EVERY (λx. boundvars (exp_of x) ⊆ set_of s1) xs1 ∧
    EVERY cexp_wf xs1 ∧
    LIST_REL (λx x1. cns_arities x1 ⊆ IMAGE (IMAGE (explode ## I)) (cns_arities x)) xs xs1)
Proof
  ho_match_mp_tac to_thunk_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ rewrite_tac [to_thunk_def]
  \\ strip_tac \\ fs [] \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY strip_tac
  \\ rpt BasicProvers.var_eq_tac
  \\ fs [cexp_wf_def, thunkLangTheory.boundvars_def, thunk_exp_ofTheory.cexp_wf_def,
         exp_of_def, letrecs_distinct_def, letrecs_distinct_Lams, letrecs_distinct_Apps,
         thunk_cexpTheory.cns_arities_def, pure_cexpTheory.cns_arities_def]
  >~ [‘exp_rel (Var _ _)’] >-
   (irule exp_rel_Var)
  >~ [‘exp_rel (Lam _ ns x)’] >-
   (simp [thunkLangTheory.boundvars_Lams]
    \\ conj_tac
    >- (irule exp_rel_Lam \\ fs [])
    >- (irule SUBSET_TRANS
        \\ first_x_assum $ irule_at $ Pos hd
        \\ fs []))
  >~ [‘exp_rel (App _ _ _)’] >-
   (irule_at Any exp_rel_App \\ fs [thunkLangTheory.boundvars_Apps]
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac
    \\ impl_tac
    >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
    \\ fs [] \\ imp_res_tac SUBSET_TRANS \\ fs []
    \\ strip_tac
    \\ conj_tac
    >- (qpat_x_assum ‘LIST_REL exp_rel _ _’ mp_tac
        \\ simp [LIST_REL_MAP_ALT]
        \\ match_mp_tac LIST_REL_mono \\ rw []
        \\ rename [‘exp_rel x1 y1’]
        \\ irule IMP_mk_delay_eq_Delay \\ fs [])
    \\ conj_tac
    >- (gs [EVERY_MEM]
        \\ simp [BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, boundvars_exp_of_mk_delay])
    \\ fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, cexp_wf_mk_delay]
    \\ conj_tac
    >- (strip_tac \\ fs [])
    \\ simp [BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, cns_arities_mk_delay]
    \\ fs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
    \\ gen_tac \\ strip_tac
    \\ gs []
    \\ first_x_assum $ drule_then mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ rpt $ pop_assum kall_tac
    \\ strip_tac \\ strip_tac \\ strip_tac
    \\ simp [SUBSET_DEF, MEM_EL, PULL_EXISTS]
    \\ gen_tac \\ strip_tac
    \\ disj2_tac
    \\ first_assum $ irule_at Any
    \\ simp [EL_MAP]
    \\ gs [SUBSET_DEF])
  >~ [‘exp_rel (Letrec _ _ _)’] >-
   (irule_at Any exp_rel_Letrec \\ fs []
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
    >- (fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, EVERY_MAP]
        \\ fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss, FORALL_PROD])
    \\ strip_tac
    \\ conj_tac
    >- (qpat_x_assum ‘LIST_REL exp_rel _ _’ mp_tac
        \\ qid_spec_tac ‘ys’
        \\ qid_spec_tac ‘xs’
        \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD])
    \\ drule_then assume_tac LIST_REL_LENGTH
    \\ fs []
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP2_ZIP]
    \\ simp [GSYM LAMBDA_PROD, GSYM MAP2_ZIP]
    \\ irule_at (Pos hd) SUBSET_TRANS
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at (Pos hd) SUBSET_TRANS
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ conj_tac
    \\ simp [SUBSET_DEF, PULL_EXISTS, thunkLangTheory.boundvars_def, MEM_EL]
    \\ rpt $ gen_tac \\ strip_tac
    \\ gs [EVERY_EL, EL_MAP2, SUBSET_DEF]
    >- first_x_assum $ dxrule_all_then irule
    >- (rpt $ gen_tac \\ strip_tac
        \\ pairarg_tac \\ gs [MEM_EL, EL_MAP, PULL_EXISTS]
        \\ qpat_x_assum ‘∀n. _ < _ ⇒ explode _ ∈ _’ $ drule_then assume_tac
        \\ gs [])
    \\ Cases_on ‘ys = []’ \\ fs []
    \\ rw []
    >- (pairarg_tac \\ fs []
        \\ pairarg_tac \\ fs []
        \\ rw [thunk_exp_ofTheory.cexp_ok_bind_def, thunk_exp_ofTheory.cexp_wf_def])
    >- (Cases_on ‘xs’ \\ fs []
        \\ Cases_on ‘ys’ \\ fs [])
    >- (‘MAP FST (MAP FST (ZIP (xs, ys))) = MAP FST xs’ by simp [MAP_ZIP]
        \\ fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
        \\ fs [MAP2_ZIP, pure_demands_analysisProofTheory.ALL_DISTINCT_IMP2])
    >- (gs [EL_MAP2, thunk_cexpTheory.cns_arities_def, LIST_REL_EL_EQN]
        \\ first_x_assum $ drule_all_then assume_tac
        \\ disj1_tac
        \\ first_assum $ irule_at Any
        \\ fs [EL_MAP]
        \\ irule_at Any EQ_REFL
        \\ pairarg_tac \\ gs [EL_MAP]))
  >~ [‘exp_rel (Case _ _ _ _ _)’]
  >- (
    gvs[COND_RAND, letrecs_distinct_def] >>
    last_x_assum (fn th => mp_tac th \\ impl_tac)
    >- (fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
        \\ fs [letrecs_distinct_rows_of, EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS]
        \\ rw []
        \\ first_x_assum $ dxrule_then irule)
    \\ strip_tac
    \\ irule_at Any SUBSET_TRANS
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any SUBSET_TRANS
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ gvs [AllCaseEqs()]
    \\ drule_all invent_var_thm
    \\ strip_tac \\ fs []
    \\ fs [BIGUNION_set_MAP_SUBSET]
    \\ ‘v ≠ w’ by (CCONTR_TAC \\ gvs [SUBSET_DEF] \\ metis_tac [])
    >-
     (conj_tac
      >- (irule exp_rel_Case \\ fs []
          \\ conj_tac >- (strip_tac \\ irule IMP_mk_delay_eq_Delay \\ fs [])
          \\ qpat_x_assum ‘LIST_REL exp_rel _ _’ mp_tac
          \\ rpt $ qpat_x_assum ‘EVERY _ _’ mp_tac
          \\ qid_spec_tac ‘ys’
          \\ qid_spec_tac ‘rs’
          \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD,MAP_EQ_CONS,AND_IMP_INTRO]
          \\ rpt gen_tac \\ strip_tac
          \\ rename [‘set (MAP explode p1) ⊆ set_of s’]
          \\ Cases_on ‘MEM w p1’ \\ fs []
          >-
           (fs [SUBSET_DEF]
            \\ drule_then assume_tac MEM_explode_MAP_explode
            \\ first_x_assum $ drule_then assume_tac
            \\ fs [SUBSET_DEF] \\ metis_tac [])
          \\ drule_all pureLangTheory.allvars_of \\ strip_tac
          \\ fs [SUBSET_DEF]
          \\ CCONTR_TAC \\ fs []
          \\ drule expof_caseProofTheory.freevars_exp_of'
          \\ strip_tac \\ fs []
          \\ drule freevars_IMP_allvars
          \\ strip_tac
          \\ metis_tac [])
      \\ simp [thunkLangTheory.boundvars_def, boundvars_exp_of_mk_delay, GSYM CONJ_ASSOC]
      \\ conj_tac
      >- gs [SUBSET_DEF]
      \\ conj_tac
      >- (irule SUBSET_TRANS
          \\ irule_at Any boundvars_rows_of_NONE
          \\ simp []
          \\ conj_tac
          \\ simp [BIGUNION_SUBSET, MEM_EL, PULL_EXISTS, EL_MAP]
          \\ gen_tac \\ strip_tac
          \\ fs [MEM_FLAT, MEM_MAP, MEM_EL, EL_MAP2, LIST_REL_EL_EQN, EVERY_EL]
          \\ qpat_x_assum ‘∀n. _ < _ ⇒ set (MAP _ _) ⊆ _’ $ drule_then assume_tac
          \\ qpat_x_assum ‘∀n. _ < _ ⇒ boundvars _ ⊆ _’ $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs []
          \\ gs [SUBSET_DEF])
      \\ conj_tac
      >- gs [SUBSET_DEF]
      \\ simp [thunk_exp_ofTheory.cexp_wf_def, cexp_wf_mk_delay, GSYM CONJ_ASSOC]
      \\ conj_tac
      >- (fs [EVERY_EL, EL_MAP2, EL_MAP]
          \\ rw []
          \\ first_x_assum $ drule_then assume_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      \\ conj_tac
      >- (rename1 ‘MAP2 _ ys rs’
          \\ Cases_on ‘rs’ \\ fs []
          \\ Cases_on ‘ys’ \\ fs [])
      \\ conj_tac
      >- (strip_tac \\ fs [MEM_FLAT, MEM_MAP, MEM_EL, EL_MAP2, LIST_REL_EL_EQN, EVERY_EL]
          \\ qpat_x_assum ‘∀n. _ < _ ⇒ set (MAP _ _) ⊆ _’ $ drule_then assume_tac
          \\ gs [EL_MAP2]
          \\ pairarg_tac \\ fs [SUBSET_DEF, MEM_EL, EL_MAP, PULL_EXISTS]
          \\ first_x_assum $ drule_then assume_tac
          \\ gs [])
      \\ conj_tac
      >- (‘∀l1 l2 : mlstring list. ALL_DISTINCT l1 ∧ l1 = l2 ⇒ ALL_DISTINCT l2’ by simp []
          \\ pop_assum $ dxrule_then irule
          \\ irule LIST_EQ
          \\ gs [LIST_REL_EL_EQN, EL_MAP, EL_MAP2]
          \\ rw []
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      \\ conj_tac
      >- (fs [MEM_EL, PULL_EXISTS, EL_MAP, EL_MAP2]
          \\ gen_tac \\ strip_tac
          \\ first_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      \\ simp [thunk_cexpTheory.cns_arities_def, cns_arities_mk_delay]
      \\ conj_tac
      >- gs [SUBSET_DEF]
      \\ conj_tac
      >- (disj1_tac \\ disj1_tac
          \\ drule LIST_REL_LENGTH
          \\ rpt $ pop_assum kall_tac
          \\ simp [SET_EQ_SUBSET, SUBSET_DEF, MEM_EL, EL_MAP, EL_MAP2, PULL_EXISTS]
          \\ rw []
          \\ first_assum $ irule_at Any
              \\ simp [EL_MAP, EL_MAP2]
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ fs [])
      >- (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ rpt $ pop_assum kall_tac
          \\ rw [BIGUNION_SUBSET, MEM_EL, LIST_REL_EL_EQN]
          \\ simp [EL_MAP, EL_MAP2]
          \\ pairarg_tac \\ fs []
          \\ pairarg_tac \\ gs []
          \\ first_x_assum $ drule_then assume_tac
          \\ rw [SUBSET_DEF, MEM_EL, PULL_EXISTS]
          \\ disj2_tac
          \\ first_assum $ irule_at Any
          \\ gs [EL_MAP, SUBSET_DEF]))
    \\ pairarg_tac \\ gvs []
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
    >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss,
            letrecs_distinct_rows_of, IfDisj_def, letrecs_distinct_def]
    \\ strip_tac \\ fs []
    \\ conj_tac
    >- (irule exp_rel_Case \\ fs []
        \\ once_rewrite_tac [CONJ_COMM] \\ rewrite_tac [GSYM CONJ_ASSOC]
        \\ conj_tac >- (strip_tac \\ irule IMP_mk_delay_eq_Delay \\ fs [])
        \\ qpat_x_assum ‘LIST_REL exp_rel _ _’ mp_tac
        \\ rpt $ qpat_x_assum ‘EVERY _ _’ mp_tac
        \\ qid_spec_tac ‘ys’
        \\ qid_spec_tac ‘rs’
        \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD,MAP_EQ_CONS,AND_IMP_INTRO]
        >-
         (imp_res_tac expof_caseProofTheory.freevars_exp_of' \\ fs []
          \\ rw [] \\ fs [SUBSET_DEF]
          \\ CCONTR_TAC \\ fs []
          \\ imp_res_tac freevars_IMP_allvars
          \\ drule_all allvars_of \\ strip_tac \\ fs[]
          \\ res_tac \\ res_tac \\ res_tac \\ metis_tac [])
        \\ rpt gen_tac \\ strip_tac
        \\ rename [‘set (MAP explode p1) ⊆ set_of s’]
        \\ Cases_on ‘MEM w p1’ \\ fs []
        >-
         (fs [SUBSET_DEF]
          \\ drule_then assume_tac MEM_explode_MAP_explode
          \\ first_x_assum $ drule_then assume_tac
          \\ fs [SUBSET_DEF] \\ metis_tac [])
        \\ imp_res_tac allvars_of \\ fs[SUBSET_DEF]
        \\ CCONTR_TAC \\ fs []
        \\ imp_res_tac expof_caseProofTheory.freevars_exp_of' \\ fs []
        \\ imp_res_tac freevars_IMP_allvars \\ fs []
        \\ fs [SUBSET_DEF]
        \\ metis_tac [])
    \\ simp [thunkLangTheory.boundvars_def, boundvars_exp_of_mk_delay]
    \\ conj_tac
    >- (simp [GSYM CONJ_ASSOC]
        \\ conj_tac
        >- gs [SUBSET_DEF]
        \\ reverse conj_tac
        >- gs [SUBSET_DEF]
        \\ irule SUBSET_TRANS
        \\ irule_at Any boundvars_rows_of_SOME
        \\ simp []
        \\ rw [SUBSET_DEF, MEM_EL]
        \\ gs [MEM_EL, EL_MAP, EL_MAP2, EVERY_EL, SUBSET_DEF, PULL_EXISTS]
        \\ pairarg_tac \\ gs []
        \\ pairarg_tac \\ gs [EL_MAP]
        >- (rpt $ qpat_x_assum ‘∀n. _ < LENGTH _ ⇒ _’ $ drule_then assume_tac
            \\ gs [])
        >- (qpat_x_assum ‘∀n. _ < LENGTH _ ⇒ ∀x. _ ∈ boundvars _ ⇒ _ ∈ _’ $ drule_then assume_tac
            \\ gs []))
    \\ fs [thunk_exp_ofTheory.cexp_wf_def, EVERY_EL, EL_MAP2, EL_MAP, GSYM CONJ_ASSOC, cexp_wf_mk_delay]
    \\ rw []
    >- (first_x_assum $ dxrule_then assume_tac
        \\ first_x_assum $ dxrule_then assume_tac
        \\ pairarg_tac \\ gs []
        \\ pairarg_tac \\ gs [])
    >- (Cases_on ‘ys’ \\ fs [])
    >- (strip_tac \\ fs [MEM_FLAT, MEM_MAP, MEM_EL, EL_MAP2, LIST_REL_EL_EQN]
        \\ qpat_x_assum ‘∀n. _ < _ ⇒ set (MAP _ _) ⊆ _’ $ drule_then assume_tac
        \\ gs [EL_MAP2]
        \\ pairarg_tac \\ fs [SUBSET_DEF, MEM_EL, EL_MAP, PULL_EXISTS]
        \\ first_x_assum $ drule_then assume_tac
        \\ gs [])
    >- (‘∀l1 l2 : mlstring list. ALL_DISTINCT l1 ∧ l1 = l2 ⇒ ALL_DISTINCT l2’ by simp []
        \\ pop_assum $ dxrule_then irule
        \\ AP_THM_TAC \\ AP_TERM_TAC
        \\ irule LIST_EQ
        \\ gs [LIST_REL_EL_EQN, EL_MAP, EL_MAP2]
        \\ rw []
        \\ pairarg_tac \\ fs []
        \\ pairarg_tac \\ fs [])
    >- (first_x_assum irule
        \\ gs [MEM_EL, EL_MAP, EL_MAP2]
        \\ first_assum $ irule_at Any
        \\ simp [EL_MAP]
        \\ pairarg_tac \\ fs []
        \\ pairarg_tac \\ fs [])
    \\ simp [thunk_cexpTheory.cns_arities_def, cns_arities_mk_delay]
    \\ conj_tac
    >- gs [SUBSET_DEF]
    \\ simp [GSYM CONJ_ASSOC]
    \\ conj_tac
    >- (disj1_tac \\ disj1_tac
        \\ disj1_tac
        \\ simp [GSYM LIST_TO_SET_MAP]
        \\ ‘MAP (λ(cn, ar). (explode cn, ar)) a = MAP (explode ## I) a’
          by (irule LIST_EQ
              \\ simp [EL_MAP]
              \\ rw []
              \\ pairarg_tac \\ simp [])
        \\ simp []
        \\ AP_TERM_TAC
        \\ AP_TERM_TAC
        \\ irule LIST_EQ
        \\ gs [EL_MAP, EL_MAP2, LIST_REL_EL_EQN]
        \\ rw []
        \\ pairarg_tac \\ fs []
        \\ pairarg_tac \\ fs [])
    \\ conj_tac
    >- (irule_at Any SUBSET_TRANS
        \\ first_x_assum $ irule_at Any
        \\ simp [SUBSET_DEF])
    >- (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
        \\ rpt $ pop_assum kall_tac
        \\ rw [BIGUNION_SUBSET, MEM_EL, LIST_REL_EL_EQN]
        \\ simp [EL_MAP, EL_MAP2]
        \\ pairarg_tac \\ fs []
        \\ pairarg_tac \\ gs []
        \\ first_x_assum $ drule_then assume_tac
        \\ rw [SUBSET_DEF, MEM_EL, PULL_EXISTS]
        \\ disj2_tac
        \\ first_assum $ irule_at Any
        \\ gs [EL_MAP, SUBSET_DEF]))
  >~ [‘exp_rel (Let c v x y)’] >-
   (irule_at Any exp_rel_Let
    \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
    >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
    \\ strip_tac \\ fs []
    \\ conj_tac
    >- (rw [] \\ irule IMP_mk_delay_eq_Delay \\ fs [])
    \\ irule_at Any SUBSET_TRANS
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any SUBSET_TRANS
    \\ qpat_assum ‘set_of _ ⊆ set_of _’ $ irule_at $ Pos $ el 2 \\ fs []
    \\ simp [boundvars_exp_of_mk_delay, cexp_wf_mk_delay]
    \\ conj_tac >- gs [SUBSET_DEF]
    \\ simp [cns_arities_mk_delay]
    \\ gs [SUBSET_DEF])
  >~ [‘Prim c p xs’] >-
   (Cases_on ‘p’
    >~ [‘Cons m’] >-
     (gvs []
      \\ Cases_on ‘mop_of_mlstring m’ \\ gvs []
      >-
       (imp_res_tac mop_of_mlstring_NONE
        \\ irule_at Any exp_rel_Cons \\ gvs []
        \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
        >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
        \\ strip_tac \\ fs [thunkLangTheory.boundvars_def]
        \\ fs [BIGUNION_SUBSET, EVERY_MEM, MEM_MAP, PULL_EXISTS, thunkLangTheory.boundvars_def]
        \\ conj_tac
        >-
         (gvs [LIST_REL_MAP_ALT, SF ETA_ss]
          \\ qpat_x_assum ‘LIST_REL exp_rel _ _’ mp_tac
          \\ match_mp_tac LIST_REL_mono \\ fs [] \\ rw []
          \\ irule IMP_mk_delay_eq_Delay \\ fs [])
        \\ imp_res_tac LIST_REL_LENGTH
        \\ simp [boundvars_exp_of_mk_delay,cns_arities_def]
        \\ gvs [thunk_exp_ofTheory.cexp_wf_def,thunk_exp_ofTheory.args_ok_def]
        \\ gvs [EVERY_MAP,cexp_wf_mk_delay]
        \\ gvs [EVERY_MEM]
        \\ gvs [SUBSET_DEF] \\ rw []
        \\ disj2_tac
        \\ gvs [MEM_MAP,cns_arities_mk_delay]
        \\ drule_all LIST_REL_MEM_ALT
        \\ strip_tac \\ gvs []
        \\ metis_tac [])
      \\ imp_res_tac mop_of_mlstring_SOME
      \\ gvs [SF ETA_ss,EVERY_MAP,num_args_ok_def]
      \\ last_x_assum mp_tac \\ impl_tac
      >- (gvs [EVERY_MEM,SUBSET_DEF,MEM_MAP,PULL_EXISTS,SF SFY_ss])
      \\ strip_tac
      \\ irule_at Any vars_ok_insert_var \\ fs []
      \\ ‘set_of s ⊆ "v" INSERT set_of s'’ by gvs [SUBSET_DEF] \\ fs []
      \\ qpat_x_assum ‘mop_of_mlstring m = SOME x’ mp_tac
      \\ simp [mop_of_mlstring_def,AllCaseEqs()]
      \\ strip_tac \\ gvs [pure_configTheory.num_monad_args_def]
      \\ gvs [LENGTH_EQ_NUM_compute,monad_to_thunk_def,cns_arities_def,
              thunkLangTheory.boundvars_def,cexp_wf_mk_delay,cns_arities_mk_delay,
              thunk_exp_ofTheory.cexp_wf_def,pure_configTheory.num_mop_args_def,
              boundvars_exp_of_mk_delay]
      \\ gvs [SUBSET_DEF]
      \\ simp [Once exp_rel_cases]
      \\ simp [delay_arg_def,EVAL “LUPDATE x 1 [y1;y2]”,EVAL “LUPDATE x 2 [y1;y2;y3]”,
               any_el_def, boundvars_exp_of_mk_delay]
      \\ simp [IMP_mk_delay_eq_Delay,cexp_wf_mk_delay,cns_arities_mk_delay]
      \\ simp [PULL_EXISTS,SF DNF_ss]
      \\ gvs [to_thunk_def]
      \\ rpt (pairarg_tac \\ gvs [])
      \\ rename [‘mk_delay flag y3’]
      \\ Cases_on ‘mk_delay flag y3 = Delay y3’
      \\ gvs [mk_delay_not_Delay]
      \\ imp_res_tac to_thunk_eq_Force_Var \\ gvs [mk_delay_def])
    >~ [‘AtomOp a’] >-
     (gvs [] \\ irule_at Any exp_rel_Prim \\ gvs []
      \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
      >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
      \\ strip_tac \\ fs [thunk_exp_ofTheory.cexp_wf_def, SF ETA_ss]
      \\ fs [BIGUNION_SUBSET, EVERY_MEM, MEM_MAP, PULL_EXISTS, thunkLangTheory.boundvars_def]
      \\ conj_tac
      >- (drule_then assume_tac LIST_REL_LENGTH
          \\ Cases_on ‘a’
          \\ fs [num_args_ok_def, thunk_exp_ofTheory.args_ok_def,
                 pure_configTheory.num_atomop_args_ok_def]
          \\ rename1 ‘l ≠ Loc _’
          \\ Cases_on ‘l’ \\ gs [])
      >- (simp [thunk_cexpTheory.cns_arities_def]
          \\ simp [BIGUNION_SUBSET, MEM_EL]
          \\ gen_tac \\ strip_tac
          \\ gs [LIST_REL_EL_EQN, EL_MAP, cns_arities_mk_delay]
          \\ first_x_assum $ drule_then mp_tac
          \\ simp [SUBSET_DEF]
          \\ strip_tac \\ gen_tac
          \\ strip_tac
          \\ first_x_assum $ drule_then strip_assume_tac
          \\ simp [MEM_EL, PULL_EXISTS]
          \\ first_assum $ irule_at Any
          \\ irule_at Any EQ_REFL
          \\ simp [EL_MAP]))
    >~ [‘Seq’]
    \\ gvs [num_args_ok_def,LENGTH_EQ_NUM_compute,any_el_def]
    \\ irule_at Any exp_rel_Seq \\ gvs [thunk_exp_ofTheory.cexp_wf_def]
    \\ drule_all invent_var_thm \\ strip_tac \\ gvs []
    \\ imp_res_tac allvars_of \\ fs[SUBSET_DEF]
    \\ conj_tac
    >- (CCONTR_TAC \\ fs []
        \\ drule expof_caseProofTheory.freevars_exp_of'
        \\ strip_tac \\ fs []
        \\ drule freevars_IMP_allvars
        \\ strip_tac
        \\ metis_tac [])
    \\ conj_tac
    >- (simp [thunkLangTheory.boundvars_def]
        \\ rw [] \\ gs [])
    \\ simp [thunk_cexpTheory.cns_arities_def]
    \\ rw []
    \\ metis_tac [])
  \\ qpat_x_assum ‘_ ⇒ _’ mp_tac \\ impl_tac
  >- fs [EVERY_MEM,SUBSET_DEF,PULL_EXISTS,MEM_MAP,PULL_FORALL,SF SFY_ss]
  \\ strip_tac \\ fs [] \\ fs [SUBSET_DEF]
QED

Theorem to_thunk_itree_of:
  cexp_wf x ∧ closed (exp_of x) ∧ NestedCase_free x ∧
  safe_itree (pure_semantics$itree_of (exp_of x)) ∧
  letrecs_distinct (exp_of x) ⇒
  pure_semantics$itree_of (exp_of x) =
  thunk_semantics$itree_of (exp_of (FST (to_thunk flag (pure_names x) x)))
Proof
  Cases_on ‘to_thunk flag (pure_names x) x’ \\ fs []
  \\ drule (exp_rel_to_thunk |> CONJUNCT1) \\ fs []
  \\ fs [pure_names_ok,pure_names_eq_allvars]
  \\ fs [pure_semanticsTheory.itree_of_def]
  \\ rw [thunk_semanticsTheory.itree_of_def]
  \\ fs []
  \\ drule_all exp_rel_semantics \\ fs []
QED

Theorem IMP_to_thunk_cexp_wf:
  cexp_wf x ∧
  closed (exp_of x) ∧
  letrecs_distinct (exp_of x) ∧
  NestedCase_free x ⇒
  thunkLang$closed (thunk_exp_of$exp_of (FST (to_thunk flag (pure_names x) x)))
Proof
  strip_tac
  \\ Cases_on ‘to_thunk flag (pure_names x) x’
  \\ drule_then assume_tac (exp_rel_to_thunk |> CONJUNCT1)
  \\ gs [pure_names_ok,pure_names_eq_allvars]
  \\ dxrule_then assume_tac exp_rel_imp_combined
  \\ gs []
  \\ dxrule_then assume_tac pure_to_thunk_1ProofTheory.compile_rel_freevars
  \\ dxrule_then assume_tac thunk_case_liftProofTheory.compile_rel_freevars
  \\ dxrule_then assume_tac thunk_let_forceProofTheory.exp_rel_NONE_freevars
  \\ dxrule_then assume_tac thunk_case_projProofTheory.compile_rel_closed
  \\ dxrule_then assume_tac thunk_unthunkProofTheory.delay_force_closed
  \\ dxrule_then assume_tac expof_caseProofTheory.freevars_exp_of'
  \\ fs [pure_expTheory.closed_def, thunkLangTheory.closed_def]
QED

Theorem compile_to_thunk_itree_of:
  cexp_wf x ∧ closed (exp_of x) ∧ NestedCase_free x ∧
  letrecs_distinct (exp_of x) ∧
  safe_itree (pure_semantics$itree_of (exp_of x)) ⇒
  pure_semantics$itree_of (exp_of x) =
  thunk_semantics$itree_of (exp_of (compile_to_thunk c x))
Proof
  rw [compile_to_thunk_def]
  \\ Cases_on ‘to_thunk c.do_mk_delay (pure_names x) x’ \\ fs []
  \\ irule_at Any EQ_TRANS
  \\ irule_at Any to_thunk_itree_of \\ qexists `c.do_mk_delay`
  \\ drule (exp_rel_to_thunk |> CONJUNCT1) \\ fs []
  \\ fs [pure_names_ok,pure_names_eq_allvars]
  \\ rw [thunk_semanticsTheory.itree_of_def]
  \\ fs [GSYM thunk_semanticsTheory.itree_of_def]
  \\ drule_all to_thunk_itree_of
  \\ disch_then $ qspec_then ‘c.do_mk_delay’ assume_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ drule_then mp_tac split_delated_lam_soundness
  \\ simp []
  \\ drule_all IMP_to_thunk_cexp_wf
  \\ disch_then $ qspec_then `c.do_mk_delay` assume_tac \\ gs []
  \\ strip_tac
  \\ fs [GSYM thunk_semanticsTheory.itree_of_def]
  \\ drule_all thunk_let_force_1ProofTheory.itree_of_simp_let_force
  \\ disch_then $ qspec_then `c.do_let_force` assume_tac \\ gs []
QED

Theorem IMP_thunk_cexp_wf:
  cexp_wf x ∧
  closed (exp_of x) ∧
  letrecs_distinct (exp_of x) ∧
  NestedCase_free x ⇒
  thunk_exp_of$cexp_wf (compile_to_thunk c x) ∧
  thunkLang$closed (thunk_exp_of$exp_of (compile_to_thunk c x)) ∧
  cns_arities (compile_to_thunk c x) ⊆
              IMAGE (IMAGE (explode ## I)) (cns_arities x)
Proof
  fs [compile_to_thunk_def] \\ strip_tac
  \\ Cases_on ‘to_thunk c.do_mk_delay (pure_names x) x’ \\ fs []
  \\ drule_then assume_tac (exp_rel_to_thunk |> CONJUNCT1)
  \\ gs [pure_names_ok,pure_names_eq_allvars]
  \\ drule_all IMP_to_thunk_cexp_wf
  \\ disch_then $ qspec_then `c.do_mk_delay` assume_tac
  \\ pairarg_tac \\ fs [thunk_let_force_1ProofTheory.simp_let_force_wf_lemmas]
  \\ drule_then mp_tac split_delated_lam_soundness
  \\ impl_tac \\ gvs []
  \\ drule_all IMP_to_thunk_cexp_wf
  \\ disch_then $ qspec_then `c.do_mk_delay` assume_tac
  \\ gs [] \\ rw [] \\ fs []
QED

val _ = export_theory ();
