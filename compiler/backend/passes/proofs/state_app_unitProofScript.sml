(*
  Correctness for compilation that pushes applications to Unit as far in as possible,
  e.g. ‘(Let x = ... in foo) Unit’ becomes ‘Let x = ... in (foo Unit)’.
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory state_cexpTheory
     stateLangTheory state_app_unit_1ProofTheory state_app_unit_2ProofTheory;
local open pure_semanticsTheory in end

val _ = new_theory "state_app_unitProof";

val _ = set_grammar_ancestry
  ["stateLang","state_cexp","state_app_unit_1Proof","state_app_unit_2Proof"];

Overload "app" = “λe1 e2. App AppOp [e1;(e2:cexp)]”;
Overload "Unit" = “App (Cons "") [] :cexp”;

Inductive cexp1_rel:

[~App_Lam:]
  (cexp1_rel x y ⇒
   cexp1_rel (app (Lam NONE x) Unit) y) ∧

[~App_Let:]
  (cexp1_rel x x1 ∧ cexp1_rel y y1 ⇒
   cexp1_rel (app (Let x_opt x y) Unit)
             (Let x_opt x1 (app y1 Unit))) ∧

[~App_If:]
  (cexp1_rel x x1 ∧ cexp1_rel y y1 ∧ cexp1_rel z z1 ⇒
   cexp1_rel (app (If x y z) Unit)
             (If x1 (app y1 Unit) (app z1 Unit))) ∧

[~App_Letrec:]
  (cexp1_rel y y1 ∧
   MAP FST tfns = MAP FST sfns ∧
   MAP (FST o SND) tfns = MAP (FST o SND) sfns ∧
   LIST_REL cexp1_rel (MAP (SND o SND) tfns) (MAP (SND o SND) sfns) ⇒
   cexp1_rel (app (Letrec tfns y) Unit)
             (Letrec sfns (app y1 Unit))) ∧

[~Var:]
  cexp1_rel (state_cexp$Var v) (state_cexp$Var v) ∧

[~Lam:]
  (cexp1_rel x y ⇒
  cexp1_rel (Lam ov x) (Lam ov y)) ∧

[~Raise:]
  (cexp1_rel x y ⇒
  cexp1_rel (Raise x) (Raise y)) ∧

[~Handle:]
  (cexp1_rel x1 y1 ∧ cexp1_rel x2 y2 ⇒
  cexp1_rel (Handle x1 v x2) (Handle y1 v y2)) ∧

[~HandleApp:]
  (cexp1_rel x1 y1 ∧ cexp1_rel x2 y2 ⇒
  cexp1_rel (HandleApp x1 x2) (HandleApp y1 y2)) ∧

[~App:]
  (LIST_REL (cexp1_rel) xs ys ⇒
  cexp1_rel (App op xs) (App op ys)) ∧

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    MAP (FST o SND) tfns = MAP (FST o SND) sfns ∧
    LIST_REL cexp1_rel (MAP (SND o SND) tfns) (MAP (SND o SND) sfns) ∧
    cexp1_rel te se ⇒
    cexp1_rel (Letrec tfns te) (Letrec sfns se)) ∧

[~Let:]
  (cexp1_rel te1 se1 ∧
   cexp1_rel te2 se2 ⇒
  cexp1_rel (Let x_opt te1 te2) (Let x_opt se1 se2)) ∧

[~If:]
  (cexp1_rel te se ∧
   cexp1_rel te1 se1 ∧
   cexp1_rel te2 se2 ⇒
  cexp1_rel (If te te1 te2) (If se se1 se2)) ∧

[~Case:]
  (∀v te se tes ses.
     cexp1_rel te se ∧
     MAP FST tes = MAP FST ses ∧
     MAP (FST o SND) tes = MAP (FST o SND) ses ∧
     LIST_REL cexp1_rel (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
  cexp1_rel (Case te v tes) (Case se v ses))

End

Overload rel1 = “state_app_unit_1Proof$compile_rel”
Overload rel2 = “state_app_unit_2Proof$compile_rel”

Triviality LIST_REL_rel2_rel1:
  ∀xs zs.
    LIST_REL (λx z. cexp1_rel x z ∧ ∃y. rel2 (exp_of x) y ∧ rel1 y (exp_of z)) xs zs ⇒
    ∃ys. LIST_REL rel2 (MAP exp_of xs) ys ∧ LIST_REL rel1 ys (MAP exp_of zs)
Proof
  Induct \\ Cases_on ‘zs’ \\ fs [PULL_EXISTS]
  \\ rw [] \\ res_tac \\ fs [] \\ metis_tac []
QED

Theorem cexp1_rel_thm:
  ∀x z. cexp1_rel x z ⇒ ∃y. rel2 (exp_of x) y ∧ rel1 y (exp_of z)
Proof
  Induct_on ‘cexp1_rel’ \\ rpt strip_tac \\ simp []
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_App_Lam \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_App \\ fs []
    \\ once_rewrite_tac [state_app_unit_2ProofTheory.compile_rel_cases] \\ simp []
    \\ first_x_assum $ irule_at Any \\ fs [])
  >-
   (irule_at Any state_app_unit_2ProofTheory.compile_rel_App_Let \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Let \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Let_Var \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_App_Lam \\ fs [])
  >-
   (irule_at Any state_app_unit_2ProofTheory.compile_rel_App_If \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_If \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Let_Var \\ fs []
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_App_Lam \\ fs []
    \\ rpt (irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs []))
  >-
   (irule_at Any state_app_unit_2ProofTheory.compile_rel_App_Letrec \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ irule_at Any state_app_unit_1ProofTheory.compile_rel_Letrec \\ fs []
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,EVERY_MAP]
    \\ rpt (irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs [])
    \\ drule_all LIST_REL_rel2_rel1
    \\ strip_tac
    \\ qexists_tac ‘MAP2 (λ(n,v,_) y. (n,Lam (SOME v) y)) sfns ys’
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rpt (pop_assum mp_tac)
    \\ qid_spec_tac ‘tfns’
    \\ qid_spec_tac ‘sfns’
    \\ qid_spec_tac ‘ys’
    \\ Induct \\ Cases_on ‘sfns’ \\ Cases_on ‘tfns’ \\ fs []
    \\ PairCases_on ‘h’ \\ PairCases_on ‘h'’ \\ fs []
    \\ strip_tac \\ rpt $ disch_then assume_tac \\ fs []
    \\ once_rewrite_tac [state_app_unit_2ProofTheory.compile_rel_cases] \\ simp []
    \\ once_rewrite_tac [state_app_unit_1ProofTheory.compile_rel_cases] \\ simp []
    \\ first_x_assum drule_all \\ fs [])
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_Var \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Var \\ fs [])
  >-
   (qexists_tac ‘(Lam ov y)’
    \\ once_rewrite_tac [state_app_unit_2ProofTheory.compile_rel_cases] \\ simp []
    \\ once_rewrite_tac [state_app_unit_1ProofTheory.compile_rel_cases] \\ simp [])
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_Raise \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Raise \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_Handle \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Handle \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_HandleApp \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_HandleApp \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_App \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_App \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []) \\ cheat)
  >- cheat
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_Let \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_Let \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (irule_at Any state_app_unit_1ProofTheory.compile_rel_If \\ fs []
    \\ irule_at Any state_app_unit_2ProofTheory.compile_rel_If \\ fs []
    \\ rpt (first_x_assum $ irule_at $ Pos hd \\ fs []))
  \\ cheat
QED

Theorem cexp1_rel_correct:
  ∀x y. cexp1_rel x y ⇒ itree_of (exp_of x) = itree_of (exp_of y)
Proof
  rw [] \\ drule cexp1_rel_thm \\ rw []
  \\ imp_res_tac state_app_unit_2ProofTheory.compile_rel_itree_of
  \\ imp_res_tac state_app_unit_1ProofTheory.compile_rel_itree_of
  \\ simp []
QED

Theorem cexp1_rel_refl[simp]:
  ∀x. cexp1_rel x x
Proof
  ho_match_mp_tac exp_of_ind \\ rw []
  \\ simp [Once cexp1_rel_cases]
  \\ rpt disj2_tac
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘funs’
  \\ qid_spec_tac ‘rows’
  \\ qid_spec_tac ‘xs’ \\ fs []
  \\ Induct \\ fs [FORALL_PROD] \\ metis_tac []
QED

Triviality cexp1_rel_eq: (* TODO: delete *)
  x = y ⇒ cexp1_rel x y
Proof
  rw [] \\ fs []
QED

Inductive cexp_rel:

[~refl:]
  (cexp_rel x x) ∧

[~trans:]
  (cexp_rel x y ∧ cexp_rel y z ⇒ cexp_rel x z) ∧

[~App_Lam:]
  (cexp_rel x y ⇒
   cexp_rel (app (Lam NONE x) Unit) y) ∧

[~App_Lam:]
  (cexp_rel x y ⇒
   cexp_rel (app (Lam NONE x) Unit) y) ∧

[~App_Let:]
  (cexp_rel x x1 ∧ cexp_rel y y1 ⇒
   cexp_rel (app (Let x_opt x y) Unit)
             (Let x_opt x1 (app y1 Unit))) ∧

[~App_If:]
  (cexp_rel x x1 ∧ cexp_rel y y1 ∧ cexp_rel z z1 ⇒
   cexp_rel (app (If x y z) Unit)
             (If x1 (app y1 Unit) (app z1 Unit))) ∧

[~App_Letrec:]
  (cexp_rel y y1 ∧
   MAP FST tfns = MAP FST sfns ∧
   MAP (FST o SND) tfns = MAP (FST o SND) sfns ∧
   LIST_REL cexp_rel (MAP (SND o SND) tfns) (MAP (SND o SND) sfns) ⇒
   cexp_rel (app (Letrec tfns y) Unit)
             (Letrec sfns (app y1 Unit))) ∧

[~Var:]
  cexp_rel (state_cexp$Var v) (state_cexp$Var v) ∧

[~Lam:]
  (cexp_rel x y ⇒
  cexp_rel (Lam ov x) (Lam ov y)) ∧

[~Raise:]
  (cexp_rel x y ⇒
  cexp_rel (Raise x) (Raise y)) ∧

[~Handle:]
  (cexp_rel x1 y1 ∧ cexp_rel x2 y2 ⇒
  cexp_rel (Handle x1 v x2) (Handle y1 v y2)) ∧

[~HandleApp:]
  (cexp_rel x1 y1 ∧ cexp_rel x2 y2 ⇒
  cexp_rel (HandleApp x1 x2) (HandleApp y1 y2)) ∧

[~App:]
  (LIST_REL (cexp_rel) xs ys ⇒
  cexp_rel (App op xs) (App op ys)) ∧

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    MAP (FST o SND) tfns = MAP (FST o SND) sfns ∧
    LIST_REL cexp_rel (MAP (SND o SND) tfns) (MAP (SND o SND) sfns) ∧
    cexp_rel te se ⇒
    cexp_rel (Letrec tfns te) (Letrec sfns se)) ∧

[~Let:]
  (cexp_rel te1 se1 ∧
   cexp_rel te2 se2 ⇒
  cexp_rel (Let x_opt te1 te2) (Let x_opt se1 se2)) ∧

[~If:]
  (cexp_rel te se ∧
   cexp_rel te1 se1 ∧
   cexp_rel te2 se2 ⇒
  cexp_rel (If te te1 te2) (If se se1 se2)) ∧

[~Case:]
  (∀v te se tes ses.
     cexp_rel te se ∧
     MAP FST tes = MAP FST ses ∧
     MAP (FST o SND) tes = MAP (FST o SND) ses ∧
     LIST_REL cexp_rel (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
  cexp_rel (Case te v tes) (Case se v ses))

End

Triviality NRC_Let:
  ∀k x x1 y y1.
    NRC cexp1_rel k x x1 ∧ NRC cexp1_rel k y y1 ⇒
    NRC cexp1_rel k (Let x_opt x y) (Let x_opt x1 y1)
Proof
  Induct \\ fs [NRC,PULL_EXISTS] \\ rw []
  \\ irule_at Any cexp1_rel_Let
  \\ rpt $ last_x_assum $ irule_at Any
QED

Theorem cexp_rel_imp_nrc:
  ∀x y. cexp_rel x y ⇒ ∃n. NRC cexp1_rel n x y
Proof
  Induct_on ‘cexp_rel’ \\ rw []
  >- (qexists_tac ‘0’ \\ fs [])
  >- (qexists_tac ‘n+n'’
      \\ fs [arithmeticTheory.NRC_ADD_EQN]
      \\ first_assum $ irule_at Any \\ fs [])
  >-
   (qexists_tac ‘1+n’
    \\ rewrite_tac [arithmeticTheory.NRC_ADD_EQN]
    \\ pop_assum $ irule_at Any
    \\ fs [] \\ irule cexp1_rel_App_Lam \\ fs [])
  >-
   (qexists_tac ‘1+n’
    \\ rewrite_tac [arithmeticTheory.NRC_ADD_EQN]
    \\ pop_assum $ irule_at Any
    \\ fs [] \\ irule cexp1_rel_App_Lam \\ fs [])
  >-
   (Q.REFINE_EXISTS_TAC ‘1+k’
    \\ rewrite_tac [arithmeticTheory.NRC_ADD_EQN] \\ fs []
    \\ irule_at Any cexp1_rel_App_Let
    \\ rpt $ irule_at Any cexp1_rel_eq \\ fs []
    \\ qexists_tac ‘n+n'’
    \\ irule NRC_Let
    \\ cheat)
  >- cheat
  >-
   (Q.REFINE_EXISTS_TAC ‘1+k’
    \\ rewrite_tac [arithmeticTheory.NRC_ADD_EQN] \\ fs []
    \\ irule_at Any cexp1_rel_App_Letrec
    \\ cheat)
  >- (qexists_tac ‘0’ \\ fs [])
  >- cheat
  \\ cheat
QED

Theorem cexp_rel_itree:
  ∀x y. cexp_rel x y ⇒ itree_of (exp_of x) = itree_of (exp_of y)
Proof
  rw []
  \\ drule cexp_rel_imp_nrc
  \\ fs [PULL_EXISTS]
  \\ qid_spec_tac ‘x’
  \\ qid_spec_tac ‘y’
  \\ Induct_on ‘n’
  \\ fs [NRC,PULL_EXISTS]
  \\ rw [] \\ res_tac
  \\ imp_res_tac cexp1_rel_correct \\ fs []
QED

Definition unit_apps_def:
  unit_apps k x = if k = 0n then (x:cexp) else unit_apps (k-1) (app x Unit)
End

Theorem unit_apps_0[simp]:
  unit_apps 0 x = x
Proof
  EVAL_TAC
QED

Definition push_app_unit_def:
  push_app_unit l ((Var v):cexp) =
    unit_apps l (Var v) ∧
  push_app_unit l (App op xs) =
    (if op = AppOp ∧ LENGTH xs = 2 then
       if EL 1 xs = Unit then
         push_app_unit (l+1n) (EL 0 xs)
       else unit_apps l $ App op (MAP (push_app_unit 0) xs)
     else unit_apps l $ App op (MAP (push_app_unit 0) xs)) ∧
  push_app_unit l (Lam vn x) =
    (if l ≠ 0 ∧ vn = NONE then
       push_app_unit (l-1n) x
     else unit_apps l  (Lam vn (push_app_unit 0 x))) ∧
  push_app_unit l (Letrec funs x) =
    Letrec (MAP (λ(f,v,y). (f,v,push_app_unit 0 y)) funs) (push_app_unit l x) ∧
  push_app_unit l (Let vn x y) =
    Let vn (push_app_unit 0 x) (push_app_unit l y) ∧
  push_app_unit l (If x y z) =
    If (push_app_unit 0 x) (push_app_unit l y) (push_app_unit l z) ∧
  push_app_unit l (Case x v rows) =
    unit_apps l
      (Case (push_app_unit 0 x) v (MAP (λ(v,vs,y). (v,vs,push_app_unit 0 y)) rows)) ∧
  push_app_unit l (Raise x) =
    unit_apps l (Raise (push_app_unit 0 x)) ∧
  push_app_unit l (Handle x v y) =
    unit_apps l (Handle (push_app_unit 0 x) v (push_app_unit 0 y)) ∧
  push_app_unit l (HandleApp x y) =
    unit_apps l (HandleApp (push_app_unit 0 x) (push_app_unit 0 y))
Termination
  WF_REL_TAC ‘measure (cexp_size o SND)’
  \\ gvs [LENGTH_EQ_NUM_compute,PULL_EXISTS,cexp_size_eq,list_size_def]
End

Theorem cexp_rel_unit_apps:
  ∀l x y. cexp_rel x y ⇒ cexp_rel (unit_apps l x) (unit_apps l y)
Proof
  Induct \\ fs []
  \\ once_rewrite_tac [unit_apps_def] \\ fs []
  \\ rw [] \\ first_x_assum irule
  \\ irule cexp_rel_App
  \\ fs [cexp_rel_refl]
QED

Theorem cexp_rel_pust_app_unit:
  ∀l x. cexp_rel (unit_apps l x) (push_app_unit l x)
Proof
  ho_match_mp_tac push_app_unit_ind \\ rpt strip_tac
  >- fs [push_app_unit_def,cexp_rel_refl]
  >-
   (reverse (Cases_on ‘op = AppOp ∧ LENGTH xs = 2 ∧ EL 1 xs = Unit’ \\ gvs [])
    \\ gvs [push_app_unit_def]
    >-
     (rw [] \\ gvs []
      \\ irule cexp_rel_unit_apps
      \\ irule cexp_rel_App
      \\ qpat_x_assum ‘∀x. _’ mp_tac
      \\ qid_spec_tac ‘xs’ \\ Induct \\ fs []
      \\ metis_tac [])
    \\ gvs [LENGTH_EQ_NUM_compute]
    \\ pop_assum mp_tac
    \\ simp [Once unit_apps_def])
  >-
   (Cases_on ‘l = 0’ \\ gvs [push_app_unit_def]
    >- (irule cexp_rel_Lam \\ fs [])
    \\ reverse (Cases_on ‘vn’) \\ fs []
    >- (irule cexp_rel_unit_apps \\ irule cexp_rel_Lam \\ fs [])
    \\ irule cexp_rel_trans
    \\ first_x_assum $ irule_at Any
    \\ simp [Once unit_apps_def]
    \\ irule cexp_rel_unit_apps
    \\ irule cexp_rel_App_Lam \\ fs [cexp_rel_refl])
  \\ cheat
QED

Theorem itree_of_push_app_unit:
  itree_of (exp_of (push_app_unit 0 x)) = itree_of (exp_of x)
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ simp_tac std_ss [Once $ GSYM unit_apps_0]
  \\ irule cexp_rel_itree
  \\ fs [cexp_rel_pust_app_unit]
QED

Triviality push_app_unit_test:
  push_app_unit 0 (App AppOp [Let NONE (Var w) (Lam NONE (Var v)); Unit]) =
  Let NONE (Var w) (Var v)
Proof
  EVAL_TAC
QED

val _ = export_theory ();
