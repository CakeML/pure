(*
  Correctness for cexp compilation from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     envLangTheory thunkLang_primitivesTheory
     stateLangTheory env_semanticsTheory env_to_state_1ProofTheory
     state_caseProofTheory state_unthunkProofTheory state_app_unitProofTheory
     env_cexpTheory state_cexpTheory env_to_stateTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_to_state_2Proof";

val _ = set_grammar_ancestry
  ["env_to_state", "env_to_state_1Proof", "env_cexp",
   "state_cexp", "state_unthunkProof"];

Overload to_state = “env_to_state_1Proof$compile_rel”
Overload unthunk = “state_unthunkProof$compile_rel”
Overload case_rel = “state_caseProof$compile_rel”
Overload clean = “state_app_unitProof$cexp_rel”

Definition combined_def:
  combined x y ⇔
    ∃x1 x2 y1.
      to_state (exp_of x) x1 ∧
      unthunk x1 x2 ∧
      case_rel (exp_of y1) x2 ∧
      clean y1 y
End

Theorem MEM_combined:
  ∀xs.
    (∀x. MEM x xs ⇒
         ∃x1 x2 y1.
           to_state (exp_of x) x1 ∧ unthunk x1 x2 ∧
           case_rel (exp_of y1) x2 ∧ clean y1 (to_state x)) ⇒
    ∃ys xs1 xs0.
      LIST_REL unthunk xs0 ys ∧ LIST_REL case_rel (MAP exp_of xs1) ys ∧
      LIST_REL to_state (MAP exp_of xs) xs0 ∧
      LIST_REL clean xs1 (MAP to_state xs)
Proof
  Induct \\ fs [PULL_EXISTS] \\ rw []
  \\ fs [SF DNF_ss]
  \\ rpt $ first_x_assum $ irule_at Any
  \\ last_x_assum dxrule \\ rw []
  \\ rpt $ first_x_assum $ irule_at Any
QED

Triviality MEM_explode[simp]:
  ∀xs x. MEM (explode x) (MAP explode xs) = MEM x xs
Proof
  Induct \\ fs []
QED

Theorem unthunk_lets_for:
  ∀xs v h1 h2.
    unthunk h1 h2 ⇒
    unthunk (state_caseProof$lets_for l v s xs h1)
            (state_caseProof$lets_for l v s xs h2)
Proof
  Induct \\ fs [state_caseProofTheory.lets_for_def]
  \\ PairCases \\ fs [state_caseProofTheory.lets_for_def] \\ rw []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_Let \\ fs []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_Let \\ fs []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_If \\ fs []
  \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [])
  \\ irule_at Any state_unthunkProofTheory.compile_rel_Var \\ fs []
QED

Theorem unthnk_Disj:
  ∀x s. unthunk (state_caseProof$Disj s x) (state_caseProof$Disj s x)
Proof
  Induct
  \\ fs [state_caseProofTheory.Disj_def,FORALL_PROD] \\ rw []
  \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [])
  \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_If \\ fs [])
  \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [])
  \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_Var \\ fs [])
QED

Theorem unthunk_rows_of:
  ∀xs ys s d1 d2.
    OPTREL (λ(a,x) (b,y). a = b ∧ unthunk x y) d1 d2 ∧
    MAP FST xs = MAP FST ys ∧
    MAP (FST o SND) xs = MAP (FST o SND) ys ∧
    LIST_REL unthunk (MAP (SND o SND) xs) (MAP (SND o SND) ys) ⇒
    unthunk (state_caseProof$rows_of s xs d1) (state_caseProof$rows_of s ys d2)
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [state_caseProofTheory.rows_of_def]
  >-
   (rw []
    \\ Cases_on ‘d1’ \\ Cases_on ‘d2’ \\ fs []
    \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [])
    \\ PairCases_on ‘x’
    \\ PairCases_on ‘x'’ \\ fs []
    \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_If \\ fs [])
    \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [])
    \\ fs [unthnk_Disj])
  \\ PairCases \\ PairCases_on ‘h’ \\ fs [] \\ rw []
  \\ fs [state_caseProofTheory.rows_of_def]
  \\ irule_at Any state_unthunkProofTheory.compile_rel_If \\ fs []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_Var \\ fs []
  \\ irule unthunk_lets_for
  \\ fs []
QED

Theorem to_state_lets_for:
  ∀xs v h1 h2.
    to_state h1 h2 ∧ v ∉ monad_cns ⇒
    to_state (lets_for l v s xs h1)
             (state_caseProof$lets_for l v s xs h2)
Proof
  Induct
  \\ fs [state_caseProofTheory.lets_for_def,envLangTheory.lets_for_def]
  \\ PairCases
  \\ fs [state_caseProofTheory.lets_for_def,envLangTheory.lets_for_def] \\ rw []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Let \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Let \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_If \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Proj \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Var \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Cons \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_IsEq \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Var \\ fs []
  \\ fs [EVAL “monad_cns”]
  \\ simp [Once env_to_state_1ProofTheory.compile_rel_cases]
QED

Theorem to_state_rows_of:
  ∀xs ys s d1 d2.
    MAP FST xs = MAP FST ys ∧
    MAP (FST o SND) xs = MAP (FST o SND) ys ∧
    OPTREL (λ(a,x) (b,y). a = b ∧ DISJOINT (set (MAP FST a)) monad_cns ∧
                          to_state x y) d1 d2 ∧
    DISJOINT (set (MAP FST xs)) monad_cns ∧
    LIST_REL to_state (MAP (SND o SND) xs) (MAP (SND o SND) ys) ⇒
    to_state (rows_of s xs d1) (state_caseProof$rows_of s ys d2)
Proof
  Induct \\ Cases_on ‘ys’
  \\ fs [state_caseProofTheory.rows_of_def,
         envLangTheory.rows_of_def]
  >-
   (rw [] \\ Cases_on ‘d1’ \\ Cases_on ‘d2’ \\ gvs []
    >- simp [Once env_to_state_1ProofTheory.compile_rel_cases]
    \\ CASE_TAC \\ CASE_TAC \\ gvs []
    \\ simp [Once env_to_state_1ProofTheory.compile_rel_cases]
    \\ reverse conj_tac
    >- simp [Once env_to_state_1ProofTheory.compile_rel_cases]
    \\ rename [‘Disj v xs’]
    \\ Induct_on ‘xs’
    \\ fs [FORALL_PROD,envLangTheory.Disj_def,state_caseProofTheory.Disj_def]
    >- (simp [Once env_to_state_1ProofTheory.compile_rel_cases] \\ simp[monad_cns_def])
    \\ rw []
    \\ ntac 5 $ simp [Once env_to_state_1ProofTheory.compile_rel_cases]
    \\ simp[monad_cns_def])
  \\ PairCases \\ PairCases_on ‘h’ \\ fs [] \\ rw []
  \\ fs [state_caseProofTheory.rows_of_def,
         envLangTheory.rows_of_def]
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_If \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_IsEq \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Var \\ fs []
  \\ irule to_state_lets_for \\ fs []
QED

Inductive thunk_res:
  (∀x s. thunk_res ((Lam s x):stateLang$exp)) ∧
  (∀x. thunk_res (App Ref [False; Lam NONE x]))
End

Definition inv_thunk_def:
  inv_thunk (App Ref [False; Lam NONE x]) = Delay x ∧
  inv_thunk (Lam s x) = Lam s x
End

Theorem imp_letrec_rel:
  ∀xs xs0 ys.
    (∀p_1 p_2. MEM (p_1,p_2) xs ⇒ ∃n m. p_2 = Lam n m ∨ p_2 = Delay m) ∧
    LIST_REL unthunk xs0 ys ∧
    LIST_REL to_state (MAP (λx. exp_of (SND x)) xs) xs0 ⇒
    LIST_REL state_unthunkProof$letrec_rel xs0 (MAP inv_thunk ys) ∧
    EVERY thunk_res ys
Proof
  Induct >- fs []
  \\ Cases_on ‘xs0’ \\ fs [PULL_EXISTS]
  \\ PairCases \\ simp []
  \\ rpt gen_tac
  \\ rpt $ disch_then assume_tac \\ fs []
  \\ last_x_assum $ drule_at $ Pos last
  \\ disch_then $ drule_at $ Pos last
  \\ impl_tac >- metis_tac []
  \\ strip_tac \\ simp []
  \\ last_x_assum $ qspecl_then [‘h'0’,‘h'1’] mp_tac
  \\ simp []
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘to_state _ _’ mp_tac
  \\ simp [Once env_to_state_1ProofTheory.compile_rel_cases]
  \\ strip_tac \\ gvs []
  \\ last_x_assum mp_tac
  \\ simp [Once state_unthunkProofTheory.compile_rel_cases]
  \\ strip_tac \\ gvs []
  \\ simp [Once thunk_res_cases,inv_thunk_def]
  \\ simp [Once state_unthunkProofTheory.compile_rel_cases]
QED

Theorem clean_Lets:
  ∀xs ys x y.
    clean x y ∧ MAP FST xs = MAP FST ys ∧
    LIST_REL clean (MAP SND xs) (MAP SND ys) ⇒
    clean (Lets xs x) (Lets ys y)
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [Lets_def]
  \\ PairCases_on ‘h’ \\ PairCases \\ fs [Lets_def] \\ rw []
  \\ irule_at Any state_app_unitProofTheory.cexp_rel_Let \\ fs []
QED

Theorem case_rel_Lets:
  ∀xs ys x y.
    MAP (OPTION_MAP explode o FST) xs = MAP FST ys ∧
    LIST_REL case_rel (MAP exp_of (MAP SND xs)) (MAP SND ys) ∧
    case_rel (exp_of x) y ⇒
    case_rel (exp_of (Lets xs x)) (Lets ys y)
Proof
  Induct \\ Cases_on ‘ys’ \\ fs []
  \\ fs [state_unthunkProofTheory.Lets_def,Lets_def]
  \\ PairCases \\ PairCases_on ‘h’
  \\ fs [state_unthunkProofTheory.Lets_def,Lets_def]
  \\ rw []
  \\ irule_at Any state_caseProofTheory.compile_rel_Let
  \\ fs []
QED

Triviality Letrec_imm_0:
  env_to_state$Letrec_imm ts m ⇒
  (∃v. m = Var v ∧ MEM v ts) ∨ ∃x y. m = Lam x y
Proof
  Cases_on ‘m’ \\ fs [Letrec_imm_def]
QED

Triviality Letrec_imm_1:
  state_unthunkProof$Letrec_imm ts m ⇒
  (∃v. m = Var v ∧ MEM v ts) ∨ ∃x y. m = Lam (SOME x) y
Proof
  Cases_on ‘m’ \\ fs [state_unthunkProofTheory.Letrec_imm_def]
  \\ rename [‘Lam oo’] \\ Cases_on ‘oo’
  \\ fs [state_unthunkProofTheory.Letrec_imm_def]
QED

Triviality comp_Letrec_neq:
  comp_Letrec sfns se ≠ Var v ∧
  comp_Letrec sfns se ≠ Lam m n
Proof
  fs [comp_Letrec_def]
  \\ pairarg_tac \\ fs []
  \\ Cases_on ‘MAP some_ref_bool delays’ \\ fs []
  \\ fs [state_unthunkProofTheory.Lets_def]
  \\ PairCases_on ‘h’
  \\ fs [state_unthunkProofTheory.Lets_def]
QED

Triviality expand_Case_neq:
  state_caseProof$expand_Case v ses se ≠ Lam x t ∧
  state_caseProof$expand_Case v ses se ≠ False
Proof
  rw [state_caseProofTheory.expand_Case_def]
  \\ Cases_on ‘ses’ \\ fs [state_caseProofTheory.rows_of_def]
  \\ PairCases_on ‘h’ \\ fs [state_caseProofTheory.rows_of_def]
QED

Triviality rows_of_neq:
  rows_of x y z ≠ Lam a b ∧
  rows_of x y z ≠ Var c
Proof
  Cases_on ‘y’ \\ rw [envLangTheory.rows_of_def,AllCaseEqs()]
  \\ PairCases_on ‘h’ \\ fs [envLangTheory.rows_of_def]
QED

Theorem Letrec_split_names:
  ∀xs delays delays' funs funs' xs0 ys.
    Letrec_split ts1 xs = (delays,funs) ∧
    Letrec_split (MAP explode ts1) (ZIP (MAP (λx. explode (FST x)) xs,MAP inv_thunk ys)) =
    (delays',funs') ∧
    LIST_REL unthunk xs0 ys ∧
    LIST_REL to_state (MAP (λx. exp_of (SND x)) xs) xs0 ∧
    (∀p_1 p_2. MEM (p_1,p_2) xs ⇒ ∃n m. p_2 = Lam n m ∨ p_2 = Delay m) ⇒
    MAP (explode ∘ FST) delays = MAP FST delays' ∧
    MAP (FST ∘ SND) delays = MAP (FST ∘ SND) delays' ∧
    MAP (explode ∘ FST) funs = MAP FST funs'
Proof
  Induct
  \\ fs [Letrec_split_def,state_unthunkProofTheory.Letrec_split_def,PULL_EXISTS]
  \\ PairCases \\ fs []
  \\ fs [Letrec_split_def,state_unthunkProofTheory.Letrec_split_def,PULL_EXISTS]
  \\ rpt gen_tac
  \\ rpt $ disch_then assume_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac >- (fs [] \\ metis_tac [])
  \\ strip_tac
  \\ first_x_assum $ qspecl_then [‘h0’,‘h1’] mp_tac
  \\ fs [] \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘to_state _ _’ mp_tac
  \\ simp [Once env_to_state_1ProofTheory.compile_rel_cases]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘unthunk _ _’ mp_tac
  \\ simp [Once state_unthunkProofTheory.compile_rel_cases]
  \\ strip_tac \\ gvs [inv_thunk_def]
  \\ gvs [dest_Delay_def,dest_Lam_def,state_unthunkProofTheory.dest_Delay_def]
  \\ eq_tac \\ rw []
  \\ imp_res_tac Letrec_imm_0
  \\ imp_res_tac Letrec_imm_1
  \\ gvs []
  \\ TRY (qpat_x_assum ‘to_state _ _’ mp_tac
          \\ simp [Once env_to_state_1ProofTheory.compile_rel_cases]
          \\ strip_tac \\ gvs []
          \\ qpat_x_assum ‘unthunk _ _’ mp_tac
          \\ simp [Once state_unthunkProofTheory.compile_rel_cases]
          \\ strip_tac \\ gvs [inv_thunk_def]
          \\ fs [Letrec_imm_def,state_unthunkProofTheory.Letrec_imm_def]
          \\ NO_TAC)
  \\ qpat_x_assum ‘unthunk _ _’ mp_tac
  \\ simp [Once state_unthunkProofTheory.compile_rel_cases,comp_Letrec_neq]
  \\ strip_tac \\ gvs [inv_thunk_def]
  \\ qpat_x_assum ‘to_state _ _’ mp_tac
  \\ simp [Once env_to_state_1ProofTheory.compile_rel_cases]
  \\ strip_tac \\ gvs []
  \\ Cases_on ‘m’ \\ gvs []
  \\ fs [Letrec_imm_def,state_unthunkProofTheory.Letrec_imm_def,rows_of_neq]
QED

Theorem clean_Ref:
  ∀x y z. clean (App Ref [x;y]) z ⇒ ∃x1 y1. z = (App Ref [x1;y1]) ∧ clean y y1
Proof
  Induct_on ‘clean’ \\ rw []
  \\ fs [state_app_unitProofTheory.cexp_rel_refl]
  >- (irule state_app_unitProofTheory.cexp_rel_trans
      \\ first_x_assum $ irule_at Any \\ fs [])
  \\ Cases_on ‘ys’ \\ fs []
QED

Theorem clean_Lam:
  ∀x y z. clean (Lam x y) z ⇒ ∃y1. z = Lam x y1 ∧ clean y y1
Proof
  Induct_on ‘clean’ \\ rw []
  \\ fs [state_app_unitProofTheory.cexp_rel_refl]
  \\ irule state_app_unitProofTheory.cexp_rel_trans
  \\ first_x_assum $ irule_at Any \\ fs []
QED

Theorem Letrec_split_case_clean:
  ∀xs delays delays' funs funs' xs0 ys xs1.
    Letrec_split ts1 xs = (delays,funs) ∧
    Letrec_split (MAP explode ts1) (ZIP (MAP (λx. explode (FST x)) xs,MAP inv_thunk ys)) =
    (delays',funs') ∧
    LIST_REL unthunk xs0 ys ∧
    LIST_REL case_rel (MAP exp_of xs1) ys ∧
    LIST_REL clean xs1 (MAP (λx. to_state (SND x)) xs) ∧
    LIST_REL to_state (MAP (λx. exp_of (SND x)) xs) xs0 ∧
    (∀p_1 p_2. MEM (p_1,p_2) xs ⇒ ∃n m. p_2 = Lam n m ∨ p_2 = Delay m) ⇒
    ∃ds fs.
      EVERY (λf. ∃tt uu. f = Lam (SOME tt) uu) fs ∧
      LIST_REL case_rel (MAP exp_of ds) (MAP (SND o SND) delays') ∧
      LIST_REL case_rel (MAP exp_of fs) (MAP SND funs') ∧
      LIST_REL clean ds (MAP (to_state o SND o SND) delays) ∧
      LIST_REL clean fs (MAP (λ(f,n,x). Lam (SOME n) (to_state x)) funs)
Proof
  Induct
  \\ fs [Letrec_split_def,state_unthunkProofTheory.Letrec_split_def,PULL_EXISTS]
  \\ PairCases \\ fs []
  \\ fs [Letrec_split_def,state_unthunkProofTheory.Letrec_split_def,PULL_EXISTS]
  \\ rpt gen_tac
  \\ rpt $ disch_then assume_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ first_x_assum drule
  \\ rpt $ disch_then drule
  \\ impl_tac >- (fs [] \\ metis_tac [])
  \\ strip_tac
  \\ first_x_assum $ qspecl_then [‘h0’,‘h1’] mp_tac
  \\ fs [] \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘to_state _ _’ mp_tac
  \\ simp [Once env_to_state_1ProofTheory.compile_rel_cases]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘unthunk _ _’ mp_tac
  \\ simp [Once state_unthunkProofTheory.compile_rel_cases]
  \\ strip_tac \\ gvs [inv_thunk_def]
  \\ gvs [dest_Delay_def,dest_Lam_def,state_unthunkProofTheory.dest_Delay_def]
  \\ fs [PULL_EXISTS,to_state_def]
  \\ rpt $ first_x_assum $ irule_at Any
  \\ qpat_x_assum ‘case_rel _ _’ mp_tac
  \\ simp [Once state_caseProofTheory.compile_rel_cases,expand_Case_neq,rows_of_neq]
  >-
   (rw []
    \\ simp [Once state_caseProofTheory.compile_rel_cases]
    \\ Cases_on ‘x’ \\ gvs []
    \\ first_x_assum $ irule_at Any \\ fs [])
  \\ fs [state_caseProofTheory.expand_Case_def,AllCaseEqs()]
  \\ gvs [PULL_EXISTS]
  \\ Cases_on ‘x’ \\ fs []
  >-
   (Cases_on ‘c’ \\ fs []
    \\ Cases_on ‘l’ \\ fs []
    \\ Cases_on ‘t’ \\ fs []
    \\ simp [Once state_caseProofTheory.compile_rel_cases,expand_Case_neq]
    \\ fs [state_caseProofTheory.expand_Case_def,AllCaseEqs()]
    \\ simp [Once state_caseProofTheory.compile_rel_cases,expand_Case_neq]
    \\ fs [state_caseProofTheory.expand_Case_def,AllCaseEqs()]
    \\ Cases_on ‘h'’ \\ fs []
    \\ strip_tac \\ gvs []
    \\ pop_assum $ irule_at Any
    \\ drule clean_Ref \\ fs []
    \\ rw []
    \\ drule clean_Lam \\ fs [])
  \\ rw []
  \\ Cases_on ‘ses’ \\ gvs [state_caseProofTheory.rows_of_def]
  \\ PairCases_on ‘h’ \\ gvs [state_caseProofTheory.rows_of_def]
QED

Definition body_of_def[simp]:
  body_of (Lam _ x) = x:state_cexp$cexp
End

Theorem to_state_rel:
  ∀x. cexp_wf x ⇒ combined x (to_state x)
Proof
  ho_match_mp_tac to_state_ind \\ rpt strip_tac
  >~ [‘Var’] >-
   (rw [to_state_def,combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Var
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Var
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Var \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Var)
  >~ [‘Lam’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Lam
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs [])
  >~ [‘Ret’] >-
   (rw [to_state_def] \\ fs [combined_def] >>
    irule_at Any env_to_state_1ProofTheory.compile_rel_Ret >>
    irule_at Any state_unthunkProofTheory.compile_rel_Lam >>
    irule_at Any state_app_unitProofTheory.cexp_rel_Lam >>
    simp[exp_of_def] >>
    irule_at Any state_caseProofTheory.compile_rel_Lam >>
    rpt $ goal_assum drule)
  >~ [‘Raise’] >-
   (rw [to_state_def] \\ fs [combined_def] >>
    irule_at Any env_to_state_1ProofTheory.compile_rel_Raise >>
    irule_at Any state_unthunkProofTheory.compile_rel_Lam >>
    irule_at Any state_unthunkProofTheory.compile_rel_Raise >>
    irule_at Any state_app_unitProofTheory.cexp_rel_Lam >>
    irule_at Any state_app_unitProofTheory.cexp_rel_Raise >>
    simp[exp_of_def] >>
    irule_at Any state_caseProofTheory.compile_rel_Lam >>
    irule_at Any state_caseProofTheory.compile_rel_Raise >>
    rpt $ goal_assum drule)
  >~ [‘Bind’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs []
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt $ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any compile_rel_Bind \\ fs [])
  >~ [‘Handle’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Handle
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_HandleApp \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Let \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Var \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs []
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_HandleApp \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Let \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Var \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_HandleApp \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Let \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Var \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [])
  >~ [‘Act’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Act
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
  >~ [‘Length’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Length
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs []
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
  >~ [‘Alloc’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Alloc
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
  >~ [‘Update’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Update
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
  >~ [‘Deref’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Deref
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
  >~ [‘Box’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Box
    \\ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Box \\ fs [])
  >~ [‘Delay’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Delay
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Delay \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs [PULL_EXISTS])
    \\ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs [PULL_EXISTS])
  >~ [‘Force’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Force
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Force \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Let \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Var \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_If \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Var \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Let \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Var \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_Let \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_If \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_Let \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_Var \\ fs [PULL_EXISTS]))
  >~ [‘App’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_App
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]))
  >~ [‘Let’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Let
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Let \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Let \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_Let \\ fs [PULL_EXISTS]))
  >~ [‘If’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_If
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_unthunkProofTheory.compile_rel_If \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_If \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_If \\ fs [PULL_EXISTS]))
  >~ [‘Case’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Case \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_Case \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
    \\ fs [state_caseProofTheory.expand_Case_def]
    \\ gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,SF SFY_ss]
    \\ qspec_then ‘MAP (SND o SND) rs’ mp_tac MEM_combined
    \\ impl_tac >- gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,SF SFY_ss]
    \\ strip_tac
    \\ simp [Once SWAP_EXISTS_THM]
    \\ qexists_tac ‘MAP (λ((m,n,_),r). (m,n,r)) (ZIP (rs,xs1))’
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ simp [Once SWAP_EXISTS_THM]
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ irule_at Any to_state_rows_of
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
    \\ qexists_tac ‘MAP (λ((m,n,_),r). (explode m,MAP explode n,r)) (ZIP (rs,xs0))’
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
    \\ ‘∃d2 te sd.
          OPTREL (λ(a,x) (b,y). a = b ∧ unthunk x y) d2 sd ∧
          OPTREL
            (λ(a,x) (b,y). a = b ∧ DISJOINT (set (MAP FST a)) monad_cns ∧ to_state x y)
            (OPTION_MAP (λ(a,e). (MAP (explode ## I) a,exp_of e)) d) d2 ∧
          OPTREL (λ(a,x) (b,y). a = b ∧ case_rel x y)
            (OPTION_MAP (λ(alts,e). (MAP (explode ## I) alts,exp_of e)) te) sd ∧
          OPTREL (λ(a,x) (b,y). a = b ∧ clean x y) te
            (case d of NONE => NONE | SOME (d',e) => SOME (d',to_state e))’ by
     (Cases_on ‘d’ \\ fs []
      \\ fs [] \\ rename [‘xx = (_,_)’]
      \\ PairCases_on ‘xx’ \\ fs [OPTREL_SOME,PULL_EXISTS,EXISTS_PROD]
      \\ rpt $ first_assum $ irule_at Any
      \\ fs [MAP_MAP_o,combinTheory.o_DEF])
    \\ pop_assum $ irule_at Any
    \\ pop_assum $ irule_at Any
    \\ pop_assum $ irule_at Any
    \\ qexists_tac ‘MAP (λ((m,n,_),r). (explode m,MAP explode n,r)) (ZIP (rs,ys))’
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
    \\ ‘ALL_DISTINCT (MAP (λx. explode (FST (FST x))) (ZIP (rs,xs1)))’ by
     (qsuff_tac ‘(MAP (λx. explode (FST (FST x))) (ZIP (rs,xs1))) =
                 MAP explode (MAP FST rs)’ >- fs [ALL_DISTINCT_APPEND]
      \\ drule LIST_REL_LENGTH \\ fs []
      \\ qid_spec_tac ‘rs’
      \\ qid_spec_tac ‘xs1’
      \\ Induct \\ fs [] \\ Cases_on ‘rs'’ \\ fs [])
    \\ fs []
    \\ IF_CASES_TAC
    >-
     (qsuff_tac ‘F’ \\ fs [] \\ gvs []
      \\ imp_res_tac LIST_REL_LENGTH
      \\ gvs [MEM_FLAT,MEM_MAP,MEM_ZIP]
      >- metis_tac [MEM_EL]
      \\ Cases_on ‘rs’ \\ Cases_on ‘ys’ \\ fs [])
    \\ irule_at Any unthunk_rows_of
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
    \\ rpt $ qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac
    \\ rpt $ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ qid_spec_tac ‘xs0’
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘rs’
    \\ qid_spec_tac ‘xs1’
    \\ rpt $ pop_assum kall_tac
    \\ Induct >- fs []
    \\ fs [PULL_EXISTS,PULL_FORALL,MAP_EQ_CONS]
    \\ rpt gen_tac \\ rewrite_tac [AND_IMP_INTRO] \\ strip_tac
    \\ fs []
    \\ last_x_assum drule_all
    \\ strip_tac \\ fs [])
  >~ [‘Letrec’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ rpt $ irule_at Any env_to_state_1ProofTheory.compile_rel_Letrec
    \\ pairarg_tac \\ gvs []
    \\ gvs [EVERY_MEM,SF ETA_ss,FORALL_PROD,MEM_MAP,PULL_EXISTS]
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
    \\ last_x_assum $ irule_at Any
    \\ rpt $ irule_at Any state_unthunkProofTheory.compile_rel_Letrec
    \\ last_x_assum $ irule_at Any
    \\ ‘∀x. MEM x (MAP SND xs) ⇒
            ∃x1 x2 y1.
              to_state (exp_of x) x1 ∧ unthunk x1 x2 ∧
              case_rel (exp_of y1) x2 ∧ clean y1 (to_state x)’ by
      (rename [‘Letrec_split ts’]
       \\ rpt $ pop_assum mp_tac
       \\ qid_spec_tac ‘delays’
       \\ qid_spec_tac ‘funs’
       \\ qid_spec_tac ‘xs’
       \\ Induct >- fs []
       \\ PairCases
       \\ simp_tac (srw_ss()) [Letrec_split_def,SF DNF_ss]
       \\ rpt conj_tac
       \\ qid_spec_tac ‘h1’ \\ simp_tac (srw_ss()) [dest_Delay_def,dest_Lam_def]
       \\ Cases_on ‘Letrec_split ts xs’ \\ simp_tac (srw_ss()) [LET_THM]
       \\ simp_tac (srw_ss()) [Letrec_split_def,SF DNF_ss]
       \\ rpt strip_tac
       THENL [all_tac, last_x_assum irule \\ metis_tac [],
              all_tac, last_x_assum irule \\ metis_tac []]
       \\ last_x_assum kall_tac \\ gvs []
       \\ fs [to_state_def]
       >-
        (simp [Once env_to_state_1ProofTheory.compile_rel_cases,PULL_EXISTS]
         \\ simp [Once state_unthunkProofTheory.compile_rel_cases,PULL_EXISTS]
         \\ first_x_assum $ irule_at $ Pos hd
         \\ first_x_assum $ irule_at $ Pos hd
         \\ rpt $ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs [PULL_EXISTS]
         \\ first_x_assum $ irule_at $ Pos hd
         \\ simp [Once state_caseProofTheory.compile_rel_cases,PULL_EXISTS])
       \\ rpt $ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
       \\ rpt $ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
       \\ rpt $ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs [PULL_EXISTS]
       \\ rpt $ irule_at Any env_to_state_1ProofTheory.compile_rel_Delay
       \\ first_x_assum $ irule_at $ Pos hd
       \\ first_x_assum $ irule_at $ Pos hd
       \\ rpt $ irule_at Any state_unthunkProofTheory.compile_rel_Delay \\ fs [PULL_EXISTS]
       \\ first_x_assum $ irule_at $ Pos hd
       \\ rpt $ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
       \\ rpt $ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
       \\ simp [Once state_caseProofTheory.compile_rel_cases])
    \\ dxrule MEM_combined
    \\ strip_tac
    \\ simp_tac std_ss [Once SWAP_EXISTS_THM]
    \\ qexists_tac ‘ZIP (MAP (λx. explode (FST x)) xs,xs0)’
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ gvs [MAP_ZIP] \\ fs [MAP_MAP_o,combinTheory.o_DEF]
    \\ drule_all imp_letrec_rel
    \\ strip_tac
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ simp_tac std_ss [Once SWAP_EXISTS_THM]
    \\ qexists_tac ‘ZIP (MAP (λx. explode (FST x)) xs,MAP inv_thunk ys)’
    \\ simp [comp_Letrec_def]
    \\ gvs [MAP_ZIP]
    \\ pairarg_tac \\ fs []
    \\ ‘∃ds fs.
          EVERY (λf. ∃tt uu. f = Lam (SOME tt) uu) fs ∧
          LIST_REL case_rel (MAP exp_of ds) (MAP (SND o SND) delays') ∧
          LIST_REL case_rel (MAP exp_of fs) (MAP SND funs') ∧
          LIST_REL clean ds (MAP (to_state o SND o SND) delays) ∧
          LIST_REL clean fs (MAP (λ(f,n,x). Lam (SOME n) (to_state x)) funs)’ by
      (irule Letrec_split_case_clean
       \\ rpt $ first_x_assum $ irule_at Any \\ fs [SF SFY_ss]
       \\ fs [MAP_MAP_o,combinTheory.o_DEF])
    \\ qabbrev_tac ‘ds1 = MAP (λ((m,n,_),x). (m,n,x)) (ZIP (delays,ds))’
    \\ qabbrev_tac ‘fs1 = MAP (λ((m,n,_),x). (m,n,body_of x)) (ZIP (funs,fs))’
    \\ qexists_tac ‘Lets (MAP some_ref_bool ds1) $
                    Letrec fs1 $ Lets (MAP unsafe_update ds1) y1’
    \\ reverse conj_tac >-
     (irule_at Any clean_Lets
      \\ irule_at Any state_app_unitProofTheory.cexp_rel_Letrec \\ fs []
      \\ irule_at Any clean_Lets
      \\ fs []
      \\ fs [Abbr‘fs1’,Abbr‘ds1’]
      \\ ntac 2 $ pop_assum mp_tac
      \\ qpat_x_assum ‘EVERY _ _’ mp_tac
      \\ qid_spec_tac ‘fs’
      \\ qid_spec_tac ‘funs’
      \\ qid_spec_tac ‘ds’
      \\ qid_spec_tac ‘delays’
      \\ rpt $ pop_assum kall_tac
      \\ reverse Induct \\ Cases_on ‘ds’ \\ fs []
      >-
       (fs [] \\ rpt gen_tac \\ rpt $ disch_then strip_assume_tac
        \\ last_x_assum drule_all \\ fs []
        \\ PairCases_on ‘h'’ \\ fs [some_ref_bool_def,unsafe_update_def]
        \\ fs [] \\ rpt gen_tac \\ rpt $ disch_then strip_assume_tac
        \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
        \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Var \\ fs [PULL_EXISTS])
        \\ Cases_on ‘h'1’ \\ fs []
        \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
        \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs [PULL_EXISTS]))
      \\ reverse Induct \\ Cases_on ‘fs’ \\ fs []
      \\ PairCases \\ fs [some_ref_bool_def,unsafe_update_def]
      \\ rpt strip_tac \\ gvs []
      \\ imp_res_tac clean_Lam \\ gvs [])
    \\ irule_at Any case_rel_Lets \\ fs []
    \\ ‘MAP (explode o FST) delays = MAP FST delays' ∧
        MAP (FST o SND) delays = MAP (FST o SND) delays' ∧
        MAP (explode o FST) funs = MAP FST funs'’ by
     (irule Letrec_split_names \\ fs []
      \\ rpt $ first_x_assum $ irule_at Any
      \\ fs [SF SFY_ss, MAP_MAP_o,combinTheory.o_DEF])
    \\ unabbrev_all_tac
    \\ conj_tac
    >-
     (ntac 5 $ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘ds’
      \\ qid_spec_tac ‘delays’
      \\ qid_spec_tac ‘delays'’
      \\ Induct \\ Cases_on ‘ds’ \\ Cases_on ‘delays’ \\ fs []
      \\ PairCases_on ‘h'’ \\ PairCases \\ fs []
      \\ fs [some_ref_bool_def,state_unthunkProofTheory.some_ref_bool_def])
    \\ reverse conj_tac
    >-
     (ntac 5 $ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘ds’
      \\ qid_spec_tac ‘delays’
      \\ qid_spec_tac ‘delays'’
      \\ Induct \\ Cases_on ‘ds’ \\ Cases_on ‘delays’ \\ fs []
      \\ PairCases_on ‘h'’ \\ PairCases \\ fs []
      \\ fs [some_ref_bool_def,state_unthunkProofTheory.some_ref_bool_def]
      \\ rw [] \\ rename [‘Bool bb’] \\ Cases_on ‘bb’ \\ fs []
      \\ rpt $ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
      \\ rpt $ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
    \\ rpt $ irule_at Any state_caseProofTheory.compile_rel_Letrec
    \\ ntac 2 (conj_tac >-
     (ntac 5 $ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘fs’
      \\ qid_spec_tac ‘funs’
      \\ qid_spec_tac ‘funs'’
      \\ Induct \\ Cases_on ‘fs’ \\ Cases_on ‘funs’ \\ fs []
      \\ PairCases_on ‘h'’ \\ PairCases \\ fs []))
    \\ reverse conj_tac >-
     (ntac 8 $ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘fs’
      \\ qid_spec_tac ‘funs’
      \\ qid_spec_tac ‘funs'’
      \\ Induct \\ Cases_on ‘fs’ \\ Cases_on ‘funs’ \\ fs []
      \\ PairCases_on ‘h'’ \\ PairCases \\ fs []
      \\ rpt strip_tac \\ gvs []
      \\ imp_res_tac clean_Lam \\ gvs [])
    \\ irule_at Any case_rel_Lets \\ fs []
    \\ ntac 7 $ pop_assum mp_tac
    \\ rpt $ pop_assum kall_tac
    \\ qid_spec_tac ‘ds’
    \\ qid_spec_tac ‘delays’
    \\ qid_spec_tac ‘delays'’
    \\ Induct \\ Cases_on ‘ds’ \\ Cases_on ‘delays’ \\ fs []
    \\ PairCases_on ‘h'’ \\ PairCases \\ fs []
    \\ fs [unsafe_update_def,state_unthunkProofTheory.unsafe_update_def]
    \\ rw []
    \\ rpt $ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ rpt $ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ rpt $ irule_at Any state_caseProofTheory.compile_rel_Var
    \\ simp [Once state_caseProofTheory.compile_rel_cases])
  >~ [‘Prim (Cons m) xs’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Cons
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ gvs [EVERY_MEM,SF ETA_ss]
    \\ irule MEM_combined \\ metis_tac [])
  >~ [‘Prim (AtomOp b) xs’] >-
   (rw [to_state_def] \\ fs [combined_def]
    \\ Cases_on ‘dest_Message b’ \\ fs []
    >-
     (rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
      \\ rpt $ irule_at Any env_to_state_1ProofTheory.compile_rel_AtomOp
      \\ ‘(∀s. b ≠ Message s)’ by (Cases_on ‘b’ \\ fs [dest_Message_def])
      \\ gvs [EVERY_MEM,SF ETA_ss]
      \\ rpt (irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
      \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
      \\ irule MEM_combined \\ metis_tac [])
    \\ Cases_on ‘b’ \\ gvs [dest_Message_def,LENGTH_EQ_NUM_compute]
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Message
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Let \\ fs [PULL_EXISTS]
    \\ rpt $ first_x_assum $ irule_at $ Any
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Let \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Var \\ fs [PULL_EXISTS]
    \\ first_x_assum $ irule_at $ Any
    \\ irule_at Any state_caseProofTheory.compile_rel_Let \\ fs [PULL_EXISTS]
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs [PULL_EXISTS]
    \\ irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_caseProofTheory.compile_rel_Var \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Var \\ fs [PULL_EXISTS])
QED

Theorem itree_of_to_state:
  cexp_wf x ⇒
  itree_of (exp_of x) ---> itree_of (exp_of (compile x))
Proof
  rw []
  \\ dxrule to_state_rel
  \\ rw [combined_def]
  \\ dxrule env_to_state_1ProofTheory.compile_rel_itree_of
  \\ strip_tac
  \\ irule pure_semanticsTheory.compiles_to_trans
  \\ pop_assum $ irule_at Any
  \\ fs [compile_def]
  \\ qsuff_tac ‘itree_of (app x2 Unit) = itree_of (app (exp_of (to_state x)) Unit)’
  >-
   (disch_then $ rewrite_tac o single o GSYM
    \\ irule state_unthunkProofTheory.compile_rel_itree_of
    \\ irule state_unthunkProofTheory.compile_rel_App \\ fs []
    \\ simp [Once state_unthunkProofTheory.compile_rel_cases] \\ fs [])
  \\ irule EQ_TRANS
  \\ qexists_tac ‘itree_of (app (exp_of y1) Unit)’
  \\ conj_tac
  >-
   (simp [Once EQ_SYM_EQ]
    \\ irule state_caseProofTheory.compile_rel_itree_of
    \\ irule state_caseProofTheory.compile_rel_App \\ fs []
    \\ irule state_caseProofTheory.compile_rel_App \\ fs [])
  \\ ‘clean (app y1 Unit) (app (to_state x) Unit)’ by
   (irule state_app_unitProofTheory.cexp_rel_App \\ fs []
    \\ irule state_app_unitProofTheory.cexp_rel_App \\ fs [])
  \\ drule state_app_unitProofTheory.cexp_rel_itree \\ fs []
QED

Theorem cns_arities_Lets:
  ∀l e. cns_arities (Lets l e) = BIGUNION (set (MAP (cns_arities o SND) l)) ∪ cns_arities e
Proof
  Induct
  \\ fs [Lets_def, FORALL_PROD, state_cexpTheory.cns_arities_def, GSYM UNION_ASSOC]
QED

Theorem Letrec_split_1:
  ∀l1 lnames funs delays p0 p1 p2.
    env_to_state$Letrec_split lnames l1 = (delays, funs) ∧ MEM (p0, p1, p2) delays
    ⇒ MEM (p0, Delay p2) l1
Proof
  Induct \\ gs [FORALL_PROD, Letrec_split_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  >- (CASE_TAC \\ fs []
      >- (rw []
          \\ last_x_assum $ drule_all_then assume_tac
          \\ fs [])
      \\ CASE_TAC \\ fs []
      \\ rw []
      \\ last_x_assum $ drule_all_then assume_tac
      \\ fs [])
  \\ rw []
  \\ fs []
  >- (rename1 ‘dest_Delay p_2’
      \\ Cases_on ‘p_2’ \\ fs [dest_Delay_def])
  \\ last_x_assum $ drule_all_then assume_tac
  \\ fs []
QED

Theorem Letrec_split_2:
  ∀l1 lnames funs delays p0 p1 p2.
    env_to_state$Letrec_split lnames l1 = (delays, funs) ∧ MEM (p0, p1, p2) funs
    ⇒ MEM (p0, Lam p1 p2) l1
Proof
  Induct \\ gs [FORALL_PROD, Letrec_split_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  >- (CASE_TAC \\ fs []
      >- (rw []
          \\ last_x_assum $ drule_all_then assume_tac
          \\ fs [])
      \\ CASE_TAC \\ fs []
      \\ rw [] \\ fs []
      >- (rename1 ‘dest_Lam p_2’
          \\ Cases_on ‘p_2’
          \\ fs [dest_Lam_def])
      \\ last_x_assum $ drule_all_then assume_tac
      \\ fs [])
  \\ rw []
  \\ last_x_assum $ drule_all_then assume_tac
  \\ fs []
QED

Theorem to_state_cns_arities_lemma:
  ∀x.
    cexp_wf x ⇒
    cns_arities (to_state x) ⊆ cns_arities x ∪ {{("", 0)}; {("True", 0)}; {("False", 0)}}
Proof
  ho_match_mp_tac to_state_ind \\ rpt strip_tac
  \\ fs [to_state_def, state_cexpTheory.cns_arities_def,
         env_cexpTheory.cns_arities_def, envLangTheory.cexp_wf_def]
  >- (conj_tac
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF])
  >- (conj_tac
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF])
  >- (conj_tac
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF])
  >- (conj_tac
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF])
  >- (rw []
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF])
  >- (conj_tac
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF])
  >- (pairarg_tac
      \\ fs [cns_arities_Lets, state_cexpTheory.cns_arities_def]
      \\ simp [BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, FORALL_PROD]
      \\ rw []
      >- (simp [some_ref_bool_def, state_cexpTheory.cns_arities_def]
          \\ rename1 ‘Bool b’
          \\ Cases_on ‘b’
          \\ simp [Bool_def, state_cexpTheory.cns_arities_def])
      >- (last_x_assum $ drule_then assume_tac
          \\ dxrule_then (dxrule_then assume_tac) Letrec_split_2
          \\ fs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
          \\ last_x_assum $ drule_then assume_tac
          \\ fs [cexp_wf_def]
          \\ irule SUBSET_TRANS
          \\ first_x_assum $ irule_at Any
          \\ simp [SUBSET_DEF]
          \\ rw [MEM_MAP, PULL_EXISTS]
          \\ disj1_tac \\ disj1_tac
          \\ first_assum $ irule_at Any
          \\ fs [env_cexpTheory.cns_arities_def])
      >- (simp [unsafe_update_def, state_cexpTheory.cns_arities_def]
          \\ last_x_assum $ drule_then assume_tac
          \\ dxrule_then (dxrule_then assume_tac) Letrec_split_1
          \\ fs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
          \\ last_x_assum $ drule_then assume_tac
          \\ fs [cexp_wf_def]
          \\ IF_CASES_TAC \\ simp [state_cexpTheory.cns_arities_def]
          \\ irule SUBSET_TRANS
          \\ first_x_assum $ irule_at Any
          \\ simp [SUBSET_DEF]
          \\ rw [MEM_MAP, PULL_EXISTS]
          \\ disj1_tac \\ disj1_tac
          \\ first_assum $ irule_at Any
          \\ fs [env_cexpTheory.cns_arities_def])
      >- (irule SUBSET_TRANS
          \\ last_x_assum $ irule_at Any
          \\ fs [SUBSET_DEF]))
  >- (conj_tac
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF])
  >- (rw []
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF])
  >- (conj_tac
      >- (CASE_TAC \\ fs []
          >- simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
          \\ CASE_TAC \\ fs []
          \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
          \\ irule SUBSET_TRANS
          \\ first_x_assum $ irule_at Any
          \\ simp [SUBSET_DEF])
      \\ fs [SUBSET_DEF, MEM_EL, EL_MAP, PULL_EXISTS, EVERY_EL]
      \\ rw []
      \\ first_x_assum $ drule_then assume_tac
      \\ first_x_assum $ drule_then assume_tac
      \\ fs [EL_MAP]
      \\ pairarg_tac \\ gs []
      \\ first_x_assum $ dxrule_then assume_tac
      \\ fs []
      \\ disj1_tac \\ disj2_tac
      \\ first_assum $ irule_at Any
      \\ simp [EL_MAP])
  >- (fs [SUBSET_DEF, EVERY_EL, MEM_EL, EL_MAP, PULL_EXISTS]
      \\ rw []
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ fs [EL_MAP]
      \\ first_x_assum $ drule_then assume_tac
      \\ fs []
      \\ disj1_tac \\ disj2_tac
      \\ first_assum $ irule_at Any
      \\ simp [EL_MAP])
  >~[‘dest_Message b’]
  >- (Cases_on ‘dest_Message b’
      \\ fs [state_cexpTheory.cns_arities_def]
      >- (fs [SUBSET_DEF, EVERY_EL, MEM_EL, EL_MAP, PULL_EXISTS]
          \\ rw []
          \\ last_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ fs [EL_MAP]
          \\ first_x_assum $ drule_then assume_tac
          \\ fs []
          \\ disj1_tac
          \\ first_assum $ irule_at Any
          \\ simp [EL_MAP])
      \\ rename1 ‘MAP _ xs’
      \\ Cases_on ‘xs’
      \\ fs [state_cexpTheory.cns_arities_def]
      \\ rename1 ‘cexp_wf h’
      \\ last_x_assum $ qspec_then ‘h’ assume_tac
      \\ gs []
      \\ irule SUBSET_TRANS
      \\ first_x_assum $ irule_at Any
      \\ simp [SUBSET_DEF])
QED

Theorem cexp_wwf_Lets:
  ∀l e. cexp_wwf (Lets l e) ⇔ EVERY cexp_wwf (MAP SND l) ∧ cexp_wwf e
Proof
  Induct \\ simp [cexp_wwf_def, Lets_def, FORALL_PROD, GSYM CONJ_ASSOC]
QED

Theorem Letrec_split_3:
  ∀l lname delays funs. env_to_state$Letrec_split lname l = (delays, funs) ∧
                        ALL_DISTINCT (MAP (λx. explode (FST x)) l)
                        ⇒ ALL_DISTINCT (MAP FST funs)
Proof
  Induct \\ simp [env_to_stateTheory.Letrec_split_def, FORALL_PROD]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs []
  \\ reverse TOP_CASE_TAC \\ fs []
  >- (rw [] \\ last_x_assum $ drule_all_then irule)
  \\ CASE_TAC \\ fs []
  >- (rw [] \\ last_x_assum $ drule_all_then irule)
  \\ CASE_TAC \\ fs []
  \\ rw [] \\ fs []
  \\ last_x_assum $ drule_all_then assume_tac
  \\ fs []
  \\ strip_tac
  \\ first_x_assum irule
  \\ fs [MEM_MAP, EXISTS_PROD]
  \\ dxrule_then (dxrule_then assume_tac) Letrec_split_2
  \\ first_x_assum $ irule_at Any
QED

Theorem to_state_cexp_wf_lemma:
  ∀x.
    cexp_wf x ⇒
    cexp_wwf (to_state x)
Proof
  ho_match_mp_tac to_state_ind \\ rpt strip_tac
  \\ simp [to_state_def]
  >~[‘Letrec’]
  >- (pairarg_tac \\ fs [cexp_wwf_Lets, cexp_wwf_def]
      \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
      \\ simp [GSYM LAMBDA_PROD, GSYM FST_THM]
      \\ drule_all_then (irule_at Any) Letrec_split_3
      \\ fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
      \\ rw []
      \\ drule_then assume_tac Letrec_split_1
      \\ drule_then assume_tac Letrec_split_2
      \\ rpt $ first_x_assum $ drule_then assume_tac
      \\ fs [some_ref_bool_def, unsafe_update_def, cexp_wwf_def, op_args_ok_def]
      >- (rename1 ‘Bool b’
          \\ Cases_on ‘b’
          \\ fs [Bool_def, cexp_wwf_def, op_args_ok_def])
      \\ IF_CASES_TAC \\ fs [cexp_wwf_def])
  >~[‘cexp_wf (Case _ rows d)’]
  >- (fs [envLangTheory.cexp_wf_def, cexp_wwf_def, op_args_ok_def]
      \\ conj_tac
      >- (Cases_on ‘d’ \\ fs []
          \\ CASE_TAC \\ fs [])
      \\ conj_tac
      >- (simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
          \\ simp [GSYM LAMBDA_PROD, GSYM FST_THM]
          \\ Cases_on ‘d’ \\ fs []
          \\ pairarg_tac \\ fs [])
      \\ fs [EVERY_EL, EL_MAP, MEM_EL, PULL_EXISTS]
      \\ rw []
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [])
  >~[‘Prim (Cons _)’]
  >- (fs [envLangTheory.cexp_wf_def, cexp_wwf_def, op_args_ok_def]
      \\ fs [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >~[‘Prim (AtomOp op) xs’]
  >- (Cases_on ‘dest_Message op’ \\ fs []
      >~[‘dest_Message op = SOME _’]
      >- (fs [envLangTheory.cexp_wf_def]
          \\ Cases_on ‘op’
          \\ fs [dest_Message_def]
          \\ Cases_on ‘xs’ \\ fs [cexp_wwf_def, op_args_ok_def]
          \\ strip_tac \\ fs [mlstringTheory.implode_def])
      \\ fs [cexp_wwf_def, op_args_ok_def]
      \\ conj_tac
      >- fs [MEM_EL, PULL_EXISTS, EVERY_EL, EL_MAP]
      \\ Cases_on ‘op’
      \\ fs [num_atomop_args_ok_def, op_args_ok_def]
      >- (rename1 ‘Lit l’
          \\ Cases_on ‘l’ \\ fs [op_args_ok_def])
      \\ fs [dest_Message_def])
  \\ fs [envLangTheory.cexp_wf_def, state_cexpTheory.cexp_wwf_def, op_args_ok_def]
QED

Theorem to_state_cexp_wf:
  envLang$cexp_wf x ⇒
  cexp_wwf (compile x) ∧
  cns_arities (compile x) ⊆ cns_arities x ∪ {{("", 0)}; {("True", 0)}; {("False", 0)}}
Proof
  rw [compile_def, cexp_wwf_def, state_cexpTheory.cns_arities_def, op_args_ok_def]
  >- drule_then irule to_state_cexp_wf_lemma
  \\ drule_then irule to_state_cns_arities_lemma
QED

val _ = export_theory ();
