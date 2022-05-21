(*
  Correctness for cexp compilation from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     envLangTheory thunkLang_primitivesTheory envLang_cexpTheory
     stateLangTheory env_semanticsTheory env_to_state_1ProofTheory
     state_caseProofTheory state_unthunkProofTheory state_app_unitProofTheory
     env_cexpTheory state_cexpTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_to_stateProof";

val _ = set_grammar_ancestry
  ["env_to_state_1Proof", "env_cexp", "state_cexp", "state_unthunkProof"];

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

Definition dest_Message_def:
  dest_Message (Message s) = SOME s ∧
  dest_Message _ = NONE
End

Definition Lets_def:
  Lets [] x = (x:state_cexp$cexp) ∧
  Lets ((v,y)::ys) x = Let v y (Lets ys x)
End

Definition Letrec_imm_def:
  (Letrec_imm vs ((Var v):env_cexp$cexp) ⇔ MEM v vs) ∧
  (Letrec_imm vs (Lam _ _) ⇔ T) ∧
  (Letrec_imm vs _ ⇔ F)
End

Definition dest_Delay_def:
  dest_Delay (Delay x) = SOME (x:env_cexp$cexp) ∧
  dest_Delay _ = NONE
End

Definition dest_Lam_def:
  dest_Lam (Lam v x) = SOME (v,x:env_cexp$cexp) ∧
  dest_Lam _ = NONE
End

Definition Letrec_split_def:
  Letrec_split vs [] = ([],[]) ∧
  Letrec_split vs ((v:mlstring,x)::fns) =
    let (xs,ys) = Letrec_split vs fns in
      case dest_Delay x of
      | SOME y => ((v,Letrec_imm vs y,y)::xs,ys)
      | NONE =>
        case dest_Lam x of
        | SOME (n,z) => (xs,(v,n,z)::ys)
        | NONE => (xs,ys)
End

Definition Bool_def[simp]:
  Bool T = (True  :state_cexp$cexp) ∧
  Bool F = (False :state_cexp$cexp)
End

Definition some_ref_bool_def:
  some_ref_bool (v:mlstring,b,y:state_cexp$cexp) =
    (SOME v, App Ref [Bool b; Bool b])
End

Definition unsafe_update_def:
  unsafe_update (v,b,y) =
    (NONE:mlstring option, App UnsafeUpdate [Var v; IntLit 1; if b then y else Lam NONE y])
End

Triviality Letrec_split_MEM_funs:
  ∀xs delays funs m n x.
    (delays,funs) = Letrec_split ns xs ∧ MEM (m,n,x) funs ⇒
    cexp_size x ≤ list_size (pair_size mlstring_size cexp_size) xs
Proof
  Induct \\ fs [Letrec_split_def]
  \\ PairCases \\ fs [Letrec_split_def] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
  \\ Cases_on ‘h1’ \\ gvs [dest_Lam_def,env_cexpTheory.cexp_size_def]
QED

Triviality Letrec_split_MEM_delays:
  ∀xs delays funs m n x.
    (delays,funs) = Letrec_split ns xs ∧ MEM (m,n,x) delays ⇒
    cexp_size x ≤ list_size (pair_size mlstring_size cexp_size) xs
Proof
  Induct \\ fs [Letrec_split_def]
  \\ PairCases \\ fs [Letrec_split_def] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
  \\ Cases_on ‘h1’ \\ gvs [dest_Delay_def,env_cexpTheory.cexp_size_def]
QED

Definition to_state_def:
  to_state ((Var n):env_cexp$cexp) = (Var n):state_cexp$cexp ∧
  to_state (App x y) =
    app (to_state x) (to_state y) ∧
  to_state (Lam v x) =
    Lam (SOME v) (to_state x) ∧
  to_state (Ret x) =
    Let (SOME «v») (to_state x) (Lam NONE (Var «v»)) ∧
  to_state (Bind x y) =
    Lam NONE (app (app (to_state y) (app (to_state x) Unit)) Unit) ∧
  to_state (Box x) =
    App Ref [True; (to_state x)] ∧
  to_state (Delay x) =
    App Ref [False; Lam NONE (to_state x)] ∧
  to_state (Force x) =
    (Let (SOME «v») (to_state x) $
     Let (SOME «v1») (App UnsafeSub [Var «v»; IntLit 0]) $
     Let (SOME «v2») (App UnsafeSub [Var «v»; IntLit 1]) $
       If (Var «v1») (Var «v2») $
         Let (SOME «wh») (app (Var «v2») Unit) $
         Let NONE (App UnsafeUpdate [Var «v»; IntLit 0; True]) $
         Let NONE (App UnsafeUpdate [Var «v»; IntLit 1; Var «wh»]) $
           Var «wh») ∧
  to_state (Letrec xs y) =
    (let (delays,funs) = Letrec_split (MAP FST xs) xs in
     let delays = MAP (λ(m,n,x). (m,n,to_state x)) delays in
     let funs = MAP (λ(m,n,x). (m,n,to_state x)) funs in
       Lets (MAP some_ref_bool delays) $
       Letrec funs $
       Lets (MAP unsafe_update delays) (to_state y)) ∧
  to_state (Let vo x y) =
    Let vo (to_state x) (to_state y) ∧
  to_state (If x y z) =
    If (to_state x) (to_state y) (to_state z) ∧
  to_state (Case x v rs) =
    Case (to_state x) v (MAP (λ(c,vs,y). (c,vs,to_state y)) rs) ∧
  to_state (Prim (Cons m) xs) =
    App (Cons m) (MAP to_state xs) ∧
  to_state (Prim (AtomOp b) xs) =
    (let ys = MAP to_state xs in
       case dest_Message b of
       | SOME m => Let (SOME «v») (case ys of [] => Var «v» | (y::_) => y)
                     (Lam NONE $ App (FFI (implode m)) [Var «v»])
       | _ => App (AtomOp b) ys)
Termination
  WF_REL_TAC ‘measure cexp_size’
  \\ fs [env_cexpTheory.cexp_size_eq] \\ rw []
  \\ (drule_all Letrec_split_MEM_delays ORELSE drule_all Letrec_split_MEM_funs)
  \\ fs []
End

Definition compile_def:
  compile x = app (to_state x) Unit
End

Definition cexp_wf_def[simp]:
  cexp_wf ((Lam v x):env_cexp$cexp) = cexp_wf x ∧
  cexp_wf (Force x) = cexp_wf x ∧
  cexp_wf (Box x) = cexp_wf x ∧
  cexp_wf (Delay x) = cexp_wf x ∧
  cexp_wf (Ret x) = cexp_wf x ∧
  cexp_wf (If x y z) = (cexp_wf x ∧ cexp_wf y ∧ cexp_wf z) ∧
  cexp_wf (Let _ x y) = (cexp_wf x ∧ cexp_wf y) ∧
  cexp_wf (Bind x y) = (cexp_wf x ∧ cexp_wf y) ∧
  cexp_wf (App x y) = (cexp_wf x ∧ cexp_wf y) ∧
  cexp_wf (Letrec fs x) =
    (EVERY I (MAP (λ(_,x). cexp_wf x) fs) ∧ cexp_wf x ∧
     ALL_DISTINCT (MAP (λx. explode (FST x)) fs) ∧
     EVERY (λ(_,x). ∃n m. x = Lam n m ∨ x = Delay m) fs) ∧
  cexp_wf (Case x v rs) =
    (EVERY I (MAP (λ(_,_,x). cexp_wf x) rs) ∧ cexp_wf x ∧
     DISJOINT (set (MAP (explode o FST) rs)) monad_cns ∧
     ALL_DISTINCT (MAP FST rs) ∧
     ~MEM v (FLAT (MAP (FST o SND) rs))) ∧
  cexp_wf (Prim p xs) =
    (EVERY cexp_wf xs ∧
     (case p of
      | Cons m => explode m ∉ monad_cns
      | AtomOp b => (∀m. b = Message m ⇒ LENGTH xs = 1) ∧
                    (∀s1 s2. b ≠ Lit (Msg s1 s2)) ∧ (∀l. b ≠ Lit (Loc l))))
Termination
  WF_REL_TAC ‘measure cexp_size’
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
    unthunk (state_caseProof$lets_for v s xs h1)
            (state_caseProof$lets_for v s xs h2)
Proof
  Induct \\ fs [state_caseProofTheory.lets_for_def]
  \\ PairCases \\ fs [state_caseProofTheory.lets_for_def] \\ rw []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_Let \\ fs []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_Var \\ fs []
QED

Theorem unthunk_rows_of:
  ∀xs ys s.
    MAP FST xs = MAP FST ys ∧
    MAP (FST o SND) xs = MAP (FST o SND) ys ∧
    LIST_REL unthunk (MAP (SND o SND) xs) (MAP (SND o SND) ys) ⇒
    unthunk (state_caseProof$rows_of s xs) (state_caseProof$rows_of s ys)
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [state_caseProofTheory.rows_of_def]
  >- (irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [])
  \\ PairCases \\ PairCases_on ‘h’ \\ fs [] \\ rw []
  \\ fs [state_caseProofTheory.rows_of_def]
  \\ irule_at Any state_unthunkProofTheory.compile_rel_If \\ fs []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_Let \\ fs []
  \\ irule_at Any state_unthunkProofTheory.compile_rel_Var \\ fs []
  \\ irule unthunk_lets_for
  \\ fs []
QED

Theorem to_state_lets_for:
  ∀xs v h1 h2.
    to_state h1 h2 ∧ v ∉ monad_cns ⇒
    to_state (lets_for v s xs h1)
             (state_caseProof$lets_for v s xs h2)
Proof
  Induct
  \\ fs [state_caseProofTheory.lets_for_def,envLangTheory.lets_for_def]
  \\ PairCases
  \\ fs [state_caseProofTheory.lets_for_def,envLangTheory.lets_for_def] \\ rw []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Let \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Proj \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Var \\ fs []
QED

Theorem to_state_rows_of:
  ∀xs ys s.
    MAP FST xs = MAP FST ys ∧
    MAP (FST o SND) xs = MAP (FST o SND) ys ∧
    DISJOINT (set (MAP FST xs)) monad_cns ∧
    LIST_REL to_state (MAP (SND o SND) xs) (MAP (SND o SND) ys) ⇒
    to_state (rows_of s xs) (state_caseProof$rows_of s ys)
Proof
  Induct \\ Cases_on ‘ys’
  \\ fs [state_caseProofTheory.rows_of_def,
         envLangTheory.rows_of_def]
  >- (irule_at Any env_to_state_1ProofTheory.compile_rel_AtomOp \\ fs [])
  \\ PairCases \\ PairCases_on ‘h’ \\ fs [] \\ rw []
  \\ fs [state_caseProofTheory.rows_of_def,
         envLangTheory.rows_of_def]
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_If \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_IsEq \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Var \\ fs []
  \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Let \\ fs []
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
  Letrec_imm ts m ⇒
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
  \\ fs [Letrec_imm_def,state_unthunkProofTheory.Letrec_imm_def]
QED

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
   (rw [to_state_def] \\ fs [combined_def]
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Let \\ fs []
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs []
    \\ irule_at Any state_app_unitProofTheory.cexp_rel_Var \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Ret
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_Let \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any state_caseProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_caseProofTheory.compile_rel_Var \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Let \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Lam \\ fs []
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Var \\ fs [])
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
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_Case \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any env_to_state_1ProofTheory.compile_rel_Let
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
    \\ fs [state_caseProofTheory.expand_Case_def]
    \\ gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,SF SFY_ss]
    \\ qspec_then ‘MAP (SND o SND) rs’ mp_tac MEM_combined
    \\ impl_tac >- gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,SF SFY_ss]
    \\ strip_tac
    \\ qexists_tac ‘MAP (λ((m,n,_),r). (m,n,r)) (ZIP (rs,xs1))’
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ qexists_tac ‘MAP (λ((m,n,_),r). (explode m,MAP explode n,r)) (ZIP (rs,ys))’
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ last_x_assum kall_tac
    \\ qpat_x_assum ‘∀x. _’ kall_tac
    \\ IF_CASES_TAC
    >-
     (qsuff_tac ‘F’ \\ fs []
      \\ pop_assum mp_tac
      \\ qpat_x_assum ‘~(MEM _ _)’ mp_tac
      \\ ‘LENGTH rs = LENGTH ys’ by (imp_res_tac LIST_REL_LENGTH \\ fs [])
      \\ pop_assum mp_tac
      \\ qid_spec_tac ‘ys’
      \\ qid_spec_tac ‘rs’
      \\ Induct \\ fs [PULL_EXISTS]
      \\ strip_tac \\ Cases \\ fs [])
    \\ irule_at Any state_unthunkProofTheory.compile_rel_Let \\ fs [PULL_EXISTS]
    \\ qexists_tac ‘(state_caseProof$rows_of (explode x')
               (MAP (λ((m,n,_),r). (explode m,MAP explode n,r)) (ZIP (rs,xs0))))’
    \\ rpt $ qpat_x_assum ‘~(MEM _ _)’ kall_tac
    \\ irule_at Any unthunk_rows_of
    \\ irule_at Any to_state_rows_of
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
    \\ ‘ALL_DISTINCT (MAP (λx. explode (FST (FST x))) (ZIP (rs,xs1)))’ by
     (qsuff_tac ‘(MAP (λx. explode (FST (FST x))) (ZIP (rs,xs1))) =
                 MAP explode (MAP FST rs)’ >- simp []
      \\ drule LIST_REL_LENGTH \\ fs []
      \\ qid_spec_tac ‘rs’
      \\ qid_spec_tac ‘xs1’
      \\ Induct \\ fs [] \\ Cases_on ‘rs'’ \\ fs [])
    \\ fs []
    \\ pop_assum kall_tac
    \\ imp_res_tac LIST_REL_LENGTH
    \\ ntac 8 $ pop_assum mp_tac
    \\ qid_spec_tac ‘xs0’
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘rs’
    \\ qid_spec_tac ‘xs1’
    \\ fs [UNCURRY,MAP_MAP_o,combinTheory.o_DEF]
    \\ Induct
    \\ fs [PULL_EXISTS,PULL_FORALL]
    \\ Cases_on ‘rs'’ \\ fs [] \\ metis_tac [])
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
          LIST_REL case_rel (MAP exp_of ds) (MAP (SND o SND) delays') ∧
          LIST_REL case_rel (MAP exp_of fs) (MAP SND funs') ∧
          LIST_REL clean ds (MAP (to_state o SND o SND) delays) ∧
          LIST_REL clean fs (MAP (to_state o SND o SND) funs)’ by cheat
    \\ qabbrev_tac ‘ds1 = MAP (λ((m,n,_),x). (m,n,x)) (ZIP (delays,ds))’
    \\ qabbrev_tac ‘fs1 = MAP (λ((m,n,_),x). (m,n,x)) (ZIP (funs,fs))’
    \\ qexists_tac ‘Lets (MAP some_ref_bool ds1) $
                    Letrec fs1 $ Lets (MAP unsafe_update ds1) y1’
    \\ reverse conj_tac
    >-
     (irule_at Any clean_Lets
      \\ irule_at Any state_app_unitProofTheory.cexp_rel_Letrec \\ fs []
      \\ irule_at Any clean_Lets
      \\ fs []
      \\ fs [Abbr‘fs1’,Abbr‘ds1’]
      \\ ntac 2 $ pop_assum mp_tac
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
      \\ PairCases \\ fs [some_ref_bool_def,unsafe_update_def])
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
     (ntac 6 $ pop_assum mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ qid_spec_tac ‘fs’
      \\ qid_spec_tac ‘funs’
      \\ qid_spec_tac ‘funs'’
      \\ Induct \\ Cases_on ‘fs’ \\ Cases_on ‘funs’ \\ fs []
      \\ PairCases_on ‘h'’ \\ PairCases \\ fs [] \\ cheat (* problem *))
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
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt $ irule_at Any env_to_state_1ProofTheory.compile_rel_Cons
    \\ rpt $ irule_at Any env_to_state_1ProofTheory.compile_rel_AtomOp
    \\ gvs [EVERY_MEM,SF ETA_ss]
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
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
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Let \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Lam \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_Var \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_Let \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Any
    \\ simp [Once state_caseProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ simp [Once state_unthunkProofTheory.compile_rel_cases,PULL_EXISTS]
    \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_unthunkProofTheory.compile_rel_Var \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_Var \\ fs [PULL_EXISTS]))
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

val _ = export_theory ();
