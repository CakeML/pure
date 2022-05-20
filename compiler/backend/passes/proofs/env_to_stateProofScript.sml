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
    App (AtomOp b) (MAP to_state xs)
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
  cexp_wf (Case x v rs) =
    (EVERY I (MAP (λ(_,_,x). cexp_wf x) rs) ∧ cexp_wf x ∧
     ~MEM v (FLAT (MAP (FST o SND) rs))) ∧
  cexp_wf (Prim p xs) =
    (EVERY cexp_wf xs ∧ (∀m. p = Cons m ⇒ explode m ∉ monad_cns))
Termination
  WF_REL_TAC ‘measure cexp_size’
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
    \\ cheat)
  >~ [‘Letrec’] >-
    cheat
  \\ rename [‘Prim pp xs’]
  \\ Cases_on ‘pp’ \\ fs [SF ETA_ss]
  \\ rw [to_state_def] \\ fs [combined_def]
    \\ rpt (irule_at Any state_app_unitProofTheory.cexp_rel_App \\ fs [PULL_EXISTS])
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ rpt $ irule_at Any env_to_state_1ProofTheory.compile_rel_Cons
    \\ rpt $ irule_at Any env_to_state_1ProofTheory.compile_rel_AtomOp
    \\ gvs [EVERY_MEM,SF ETA_ss]
    \\ rpt (irule_at Any state_caseProofTheory.compile_rel_App \\ fs [PULL_EXISTS])
    \\ irule_at Any state_unthunkProofTheory.compile_rel_App \\ fs [PULL_EXISTS]
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
