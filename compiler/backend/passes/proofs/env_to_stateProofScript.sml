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
  ["env_to_state_1Proof", "env_cexp", "state_cexp"];

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
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]





    \\ cheat)

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
  \\ cheat
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
