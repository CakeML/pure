(*
  Correctness for compilation that pushes applications to Unit as far in as possible,
  e.g. ‘(Let x = ... in foo) Unit’ becomes ‘Let x = ... in (foo Unit)’.
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     stateLangTheory;
local open pure_semanticsTheory in end

val _ = new_theory "state_app_unitProof";

val _ = set_grammar_ancestry ["stateLang"];

Overload "app" = “λe1 e2. App AppOp [e1;e2]”;

Inductive compile_rel:

[~App_Unit:]
  (compile_rel (n+1:num) x y ⇒
  compile_rel n (app x Unit) y) ∧

[~Lam_Unit:]
  (compile_rel n x y ⇒
  compile_rel (n+1) (Lam NONE x) y) ∧

[~Var:]
  compile_rel 0 (stateLang$Var v) (stateLang$Var v) ∧

[~Lam_SOME:]
  (compile_rel 0 x y ⇒
  compile_rel 0 (Lam ov x) (Lam ov y)) ∧

[~Raise:]
  (compile_rel 0 x y ⇒
  compile_rel 0 (Raise x) (Raise y)) ∧

[~Handle:]
  (compile_rel 0 x1 y1 ∧ compile_rel 0 x2 y2 ⇒
  compile_rel 0 (Handle x1 v x2) (Handle y1 v y2)) ∧

[~HandleApp:]
  (compile_rel 0 x1 y1 ∧ compile_rel 0 x2 y2 ⇒
  compile_rel 0 (HandleApp x1 x2) (HandleApp y1 y2)) ∧

[~App:]
  (LIST_REL (compile_rel 0) xs ys ⇒
  compile_rel 0 (App op xs) (App op ys)) ∧

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL (compile_rel 0) (MAP SND tfns) (MAP SND sfns) ∧
    EVERY (λ(n,x). ∃v y. x = Lam v y) tfns ∧
    compile_rel n te se ⇒
    compile_rel n (Letrec tfns te) (Letrec sfns se)) ∧

[~Let:]
  (compile_rel 0 te1 se1 ∧
   compile_rel n te2 se2 ⇒
  compile_rel n (Let x_opt te1 te2) (Let x_opt se1 se2)) ∧

[~If:]
  (compile_rel 0 te se ∧
   compile_rel n te1 se1 ∧
   compile_rel n te2 se2 ⇒
  compile_rel n (If te te1 te2) (If se se1 se2)) ∧

[~Case:]
  (∀v te se tes ses.
     compile_rel 0 te se ∧
     MAP FST tes = MAP FST ses ∧
     MAP (FST o SND) tes = MAP (FST o SND) ses ∧
     LIST_REL (compile_rel n) (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
  compile_rel n (Case te v tes) (Case se v ses))

End

Inductive v_rel:

[~Atom:]
  (∀a.
     v_rel (Atom a) (Atom a)) ∧

[~Constructor:]
  (∀s tvs svs.
     LIST_REL v_rel tvs svs ⇒
     v_rel (Constructor s tvs) (Constructor s svs)) ∧

[~Closure:]
  (∀tenv senv te se n.
     env_rel tenv senv ∧ compile_rel 0 te se ⇒
     v_rel (Closure n tenv te) (Closure n senv se)) ∧

[~Recclosure:]
  (∀tfns sfns tenv senv n.
     env_rel tenv senv ∧
     LIST_REL (compile_rel 0) (MAP SND tfns) (MAP SND sfns) ∧
     MAP FST tfns = MAP FST sfns ∧
     EVERY (λ(n,x). ∃v y. x = Lam v y) tfns  ⇒
     v_rel (Recclosure tfns tenv n)
           (Recclosure sfns senv n)) ∧

[env_rel:]
  (∀tenv senv.
     (∀(n:string) tv.
       ALOOKUP tenv n = SOME tv ⇒
       ∃sv. ALOOKUP senv n = SOME sv ∧ v_rel tv sv) ⇒
     env_rel tenv senv)

End

Theorem env_rel_def = “env_rel tenv senv”
  |> SIMP_CONV (srw_ss()) [Once v_rel_cases];

Inductive cont_rel:
  (∀n. n = 0 ⇒ cont_rel n [] []) ∧
  (∀n tk sk.
    cont_rel n tk sk ⇒
    cont_rel (n+1:num) (AppK env AppOp [Constructor "" []] []::tk) sk) ∧
  (∀n tk sk.
    cont_rel n tk sk ∧ env_rel tenv senv ∧
    compile_rel n te1 se1 ∧ compile_rel n te2 se2 ⇒
    cont_rel 0 (IfK tenv te1 te2 :: tk)
               (IfK senv se1 se2 :: sk)) ∧
  (∀tenv senv op tvs svs tes ses sk tk.
    cont_rel 0 tk sk ∧ env_rel tenv senv ∧
    LIST_REL v_rel tvs svs ∧ LIST_REL (compile_rel 0) tes ses ⇒
    cont_rel 0 (AppK tenv op tvs tes :: tk)
               (AppK senv op svs ses :: sk)) ∧
  (∀tenv senv n te se sk tk.
    cont_rel m tk sk ∧ env_rel tenv senv ∧
    compile_rel m te se ⇒
    cont_rel 0 (LetK tenv n te :: tk)
               (LetK senv n se :: sk)) ∧
  (∀tenv senv n te se sk tk.
    cont_rel 0 tk sk ∧ env_rel tenv senv ∧
    compile_rel 0 te se ⇒
    cont_rel 0 (HandleK tenv n te :: tk)
               (HandleK senv n se :: sk)) ∧
  (∀tenv senv te se sk tk.
    cont_rel 0 tk sk ∧ env_rel tenv senv ∧
    compile_rel 0 te se ⇒
    cont_rel 0 (HandleAppK tenv te :: tk)
               (HandleAppK senv se :: sk)) ∧
  (∀sk tk.
    cont_rel 0 tk sk ⇒
    cont_rel 0 (RaiseK :: tk)
               (RaiseK :: sk)) ∧
  (∀sk tk v tenv senv.
    cont_rel n tk sk ∧ env_rel tenv senv ∧
    MAP FST tes = MAP FST ses ∧
    MAP (FST o SND) tes = MAP (FST o SND) ses ∧
    LIST_REL (compile_rel n) (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
    cont_rel 0 (CaseK tenv v tes :: tk)
               (CaseK senv v ses :: sk))
End

Inductive step_res_rel:
  (v_rel v1 v2 ∧ cont_rel 0 tk sk ⇒
   step_res_rel (Val v1) tk (Val v2) sk) ∧
  (v_rel v1 v2 ∧ cont_rel 0 tk sk ⇒
   step_res_rel (Exn v1) tk (Exn v2) sk) ∧
  (step_res_rel Error tk Error sk) ∧
  (compile_rel n e1 e2 ∧ env_rel env1 env2 ∧ cont_rel n tk sk ⇒
   step_res_rel (Exp env1 e1) tk (Exp env2 e2) sk) ∧
  (cont_rel 0 tk sk ⇒
   step_res_rel (Action a b) tk (Action a b) sk)
End

Definition rec_env_def:
  rec_env f env =
    MAP (λ(fn,_). (fn,Recclosure f env fn)) f ++ env
End

Inductive snext_res_rel:
  (OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧ cont_rel 0 tk sk ⇒
   snext_res_rel (Act x tk ts) (Act x sk ss)) ∧
  (snext_res_rel Ret Ret) ∧
  (snext_res_rel Div Div) ∧
  (snext_res_rel Err Err)
End

Inductive insert_appk:
  insert_appk tk (AppK env AppOp [Constructor "" []] []::tk) ∧
  (insert_appk tk tk1 ⇒
   insert_appk (IfK tenv te1 te2 :: tk)
               (IfK tenv te1 te2 :: tk1)) ∧
  (insert_appk tk tk1 ⇒
   insert_appk (LetK tenv n te :: tk)
               (LetK tenv n te :: tk1)) ∧
  (insert_appk tk tk1 ⇒
   insert_appk (CaseK tenv v tes :: tk)
               (CaseK tenv v tes :: tk1))
End

Theorem cont_rel_insert_appk:
  ∀n tk sk.
    cont_rel (n+1) tk sk ⇒
    ∃tk0. cont_rel n tk0 sk ∧ insert_appk tk0 tk
Proof
  Induct_on ‘tk’ \\ fs []
  \\ simp [Once cont_rel_cases] \\ rw []
  \\ first_x_assum $ irule_at Any
  \\ simp [Once insert_appk_cases]
QED

Theorem env_rel_cons:
  env_rel xs ys ∧ v_rel x y ⇒
  env_rel ((n,x)::xs) ((n,y)::ys)
Proof
  rw [env_rel_def] \\ rw [] \\ fs []
QED

Theorem env_rel_zip:
  ∀n x y xs ys.
    env_rel xs ys ∧ LIST_REL v_rel x y ∧ LENGTH n = LENGTH x ⇒
    env_rel (REVERSE(ZIP(n,x))++xs) (REVERSE(ZIP(n,y))++ys)
Proof
  Induct \\ fs []
  \\ Cases_on ‘x’ \\ fs [PULL_EXISTS] \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ last_x_assum irule \\ fs []
  \\ irule env_rel_cons \\ fs []
QED

Triviality FST_INTRO:
  (λ(p1,p2). p1) = FST
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem ALOOKUP_rec:
  ALOOKUP (MAP (λ(fn,_). (fn,g fn)) tfns) n = SOME tv <=>
  MEM n (MAP FST tfns) ∧ tv = g n
Proof
  Induct_on ‘tfns’ \\ fs [FORALL_PROD]
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem ALOOKUP_list_rel:
  ∀tfns sfns n x.
    ALOOKUP tfns n = SOME x ∧
    LIST_REL (compile_rel 0) (MAP SND tfns) (MAP SND sfns) ∧
    MAP FST tfns = MAP FST sfns ⇒
    ∃y. ALOOKUP sfns n = SOME y ∧ compile_rel 0 x y
Proof
  Induct \\ fs [FORALL_PROD,PULL_EXISTS] \\ rw []
  \\ Cases_on‘sfns’ \\ gvs [] \\ PairCases_on ‘h’ \\ fs []
QED

Theorem get_atoms_thm:
  ∀tvs svs. LIST_REL v_rel tvs svs ⇒ get_atoms tvs = get_atoms svs
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ simp [Once v_rel_cases]
  \\ rw [] \\ fs [get_atoms_def]
  \\ res_tac \\ fs []
QED

Theorem application_thm:
  application op tenv tvs ts tk = (tr1,ts1,tk1) ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧ cont_rel 0 tk sk ∧
  LIST_REL v_rel tvs svs ∧ env_rel tenv senv ∧
  num_args_ok op (LENGTH svs) ⇒
  ∃sr1 ss1 sk1.
    application op senv svs ss sk = (sr1,ss1,sk1) ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
    step_res_rel tr1 tk1 sr1 sk1
Proof
  Cases_on ‘op’ \\ fs [num_args_ok_def,LENGTH_EQ_NUM_compute,PULL_EXISTS]
  \\ rw [] \\ gvs []
  >~ [‘Cons’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ simp [Once v_rel_cases])
  >~ [‘Proj’] >-
   (gvs [application_def,step,AllCaseEqs()]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs [step_res_rel_cases]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘IsEq’] >-
   (gvs [application_def,step,AllCaseEqs()]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs [step_res_rel_cases]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs [] \\ rw []
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs [step_res_rel_cases])
  >~ [‘AppOp’] >-
   (gvs [application_def]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [dest_anyClosure_def,dest_Closure_def,step,step_res_rel_cases]
    >-
     (rpt $ first_assum $ irule_at Any
      \\ Cases_on ‘n’ \\ gvs [opt_bind_def]
      \\ irule env_rel_cons \\ fs [])
    \\ gvs [AllCaseEqs(),ALOOKUP_NONE]
    \\ drule ALOOKUP_MEM \\ strip_tac
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ first_assum drule \\ simp_tac (srw_ss()) []
    \\ drule_all ALOOKUP_list_rel
    \\ strip_tac \\ fs []
    \\ pop_assum mp_tac
    \\ simp [Once compile_rel_cases]
    \\ strip_tac \\ fs []
    \\ ‘MEM n (MAP FST sfns)’ by
     (imp_res_tac ALOOKUP_MEM \\ fs [MEM_MAP,EXISTS_PROD]
      \\ first_assum $ irule_at Any) \\ fs []
    \\ rpt $ first_assum $ irule_at Any
    \\ Cases_on ‘arg’ \\ fs []
    \\ gvs [opt_bind_def]
    \\ TRY (irule env_rel_cons) \\ fs []
    \\ gvs [env_rel_def,ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE]
    \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO,ALOOKUP_rec]
    \\ strip_tac \\ Cases_on ‘MEM n' (MAP FST sfns)’ \\ fs []
    \\ rw [Once v_rel_cases] \\ fs [env_rel_def]
    \\ fs [EVERY_MEM,FORALL_PROD,LAMBDA_PROD]
    \\ rw [] \\ res_tac \\ fs [])
  >~ [‘Alloc’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘ss’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ simp [Once v_rel_cases]
    \\ fs [LIST_REL_SNOC]
    \\ simp [LIST_REL_EL_EQN,EL_REPLICATE])
  >~ [‘Ref’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ simp [Once v_rel_cases]
    \\ fs [LIST_REL_SNOC])
  >~ [‘Length’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [oEL_THM]
    \\ IF_CASES_TAC \\ gvs []
    \\ simp [Once v_rel_cases]
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘Sub’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [oEL_THM]
    \\ rpt (IF_CASES_TAC \\ gvs [])
    \\ gvs [LIST_REL_EL_EQN]
    \\ ntac 2 (simp [Once compile_rel_cases,env_rel_def])
    \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs []
    \\ simp[Once v_rel_cases]
    \\ rpt $ first_assum $ irule_at Any)
  >~ [‘UnsafeSub’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [oEL_THM]
    \\ rpt (IF_CASES_TAC \\ gvs [])
    \\ gvs [LIST_REL_EL_EQN]
    \\ ntac 2 (simp [Once compile_rel_cases,env_rel_def])
    \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs [])
  >~ [‘Update’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ qpat_x_assum ‘v_rel _ h'’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [oEL_THM]
    \\ rpt (IF_CASES_TAC \\ gvs [])
    \\ gvs [LIST_REL_EL_EQN]
    \\ ntac 2 (simp [Once compile_rel_cases,env_rel_def])
    \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs []
    \\ gvs [EL_LUPDATE] \\ rw []
    \\ gvs [EL_LUPDATE] \\ rw []
    \\ simp [Once v_rel_cases] \\ rpt strip_tac \\ gvs []
    \\ rpt $ first_assum $ irule_at Any)
  >~ [‘UnsafeUpdate’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ qpat_x_assum ‘v_rel _ h'’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [oEL_THM]
    \\ rpt (IF_CASES_TAC \\ gvs [])
    \\ gvs [LIST_REL_EL_EQN]
    \\ ntac 2 (simp [Once compile_rel_cases,env_rel_def])
    \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs []
    \\ gvs [EL_LUPDATE] \\ rw []
    \\ gvs [EL_LUPDATE] \\ rw []
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs [])
  >~ [‘FFI’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs [])
  \\ rename [‘AtomOp’]
  \\ gvs [application_def,step,step_res_rel_cases]
  \\ imp_res_tac get_atoms_thm \\ gvs [AllCaseEqs()]
  \\ simp [Once v_rel_cases]
QED

Theorem step_1_Exp_forward:
  ∀n e1 e2 ts tk sr1 ss1 sk1 ss sk env1 env2.
    step ss sk (Exp env2 e2) = (sr1,ss1,sk1) ∧
    cont_rel n tk sk ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    compile_rel n e1 e2 ∧
    env_rel env1 env2 ⇒
    ∃m tr1 ts1 tk1.
      step_n (m + 1) (Exp env1 e1,ts,tk) = (tr1,ts1,tk1) ∧
      (tr1 ≠ Error ⇒
       OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
       step_res_rel tr1 tk1 sr1 sk1)
Proof
  Induct_on ‘compile_rel’ \\ rpt strip_tac
  >-
   (fs [GSYM ADD1]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’
    \\ first_x_assum irule
    \\ rpt (first_assum $ irule_at $ Pos hd \\ fs [])
    \\ fs [ADD1]
    \\ simp [Once cont_rel_cases])
  >-
   (qpat_x_assum ‘cont_rel (n + 1) tk sk’ mp_tac
    \\ simp [Once cont_rel_cases] \\ strip_tac \\ gvs []
    \\ fs [GSYM ADD1] \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ first_x_assum drule_all \\ strip_tac
    \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ first_x_assum $ irule_at Any \\ gvs [])
  \\ gvs []
  \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
  >~ [‘Var v’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ Cases_on ‘ALOOKUP env1 v’ \\ gvs []
    \\ gvs [env_rel_def]
    \\ res_tac \\ gvs []
    \\ gvs [step_res_rel_cases,env_rel_def])
  >~ [‘If’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ fs [step_res_rel_cases]
    \\ last_x_assum $ irule_at Any \\ fs []
    \\ simp [Once cont_rel_cases]
    \\ rpt (last_x_assum $ irule_at Any \\ fs []))
  >~ [‘Lam’] >-
   (qexists_tac ‘0’ \\ fs []
    \\ gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
    \\ once_rewrite_tac [Once v_rel_cases] \\ fs [env_rel_def])
  >~ [‘Raise’] >-
   (qexists_tac ‘0’ \\ fs []
    \\ gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
    \\ once_rewrite_tac [Once v_rel_cases] \\ fs [env_rel_def]
    \\ last_x_assum $ irule_at Any \\ fs []
    \\ simp [Once cont_rel_cases]
    \\ last_x_assum $ irule_at Any \\ fs [])
  >~ [‘Letrec’] >-
   (qexists_tac ‘0’ \\ fs [step]
    \\ simp [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
    \\ rpt $ first_x_assum $ irule_at Any \\ gvs []
    \\ rpt gen_tac
    \\ gvs [env_rel_def,ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE]
    \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO,ALOOKUP_rec]
    \\ strip_tac \\ Cases_on ‘MEM n' (MAP FST sfns)’ \\ fs []
    \\ rw [Once v_rel_cases] \\ fs [env_rel_def]
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ fs [])
  >~ [‘Let’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ simp [step,AllCaseEqs(),step_res_rel_cases]
    \\ rpt $ first_x_assum $ irule_at Any \\ gvs []
    \\ simp [Once cont_rel_cases]
    \\ rpt $ first_x_assum $ irule_at Any \\ gvs [])
  >~ [‘Handle’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ simp [step,AllCaseEqs(),step_res_rel_cases]
    \\ rpt $ first_x_assum $ irule_at Any \\ gvs []
    \\ simp [Once cont_rel_cases])
  >~ [‘HandleApp’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ simp [step,AllCaseEqs(),step_res_rel_cases]
    \\ rpt $ first_x_assum $ irule_at Any \\ gvs []
    \\ simp [Once cont_rel_cases])
  >~ [‘Case’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ IF_CASES_TAC \\ gvs []
    \\ simp [step,AllCaseEqs(),step_res_rel_cases]
    \\ rpt $ first_x_assum $ irule_at Any \\ gvs []
    \\ simp [Once cont_rel_cases]
    \\ rpt $ first_x_assum $ irule_at Any \\ gvs []
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ fs [])
  >~ [‘App’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ IF_CASES_TAC \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ gvs [AllCaseEqs()]
    >-
     (‘∃a. application op env1 [] ts tk = a’ by fs [] \\ PairCases_on ‘a’
      \\ drule application_thm \\ fs []
      \\ disch_then drule_all \\ strip_tac \\ gvs [])
    \\ gvs [SWAP_REVERSE_SYM]
    \\ Cases_on ‘xs’ using SNOC_CASES \\ fs [PULL_EXISTS]
    \\ gvs [GSYM SWAP_REVERSE_SYM]
    \\ full_simp_tac std_ss [GSYM SNOC_APPEND,LIST_REL_SNOC]
    \\ gvs []
    \\ simp [step,AllCaseEqs(),step_res_rel_cases]
    \\ rpt $ first_x_assum $ irule_at Any \\ gvs []
    \\ simp [Once cont_rel_cases]
    \\ drule EVERY2_REVERSE \\ simp_tac std_ss [REVERSE_REVERSE]
    \\ match_mp_tac LIST_REL_mono \\ fs [])
QED

Theorem cont_rel_Exn:
  ∀n tk sk.
    cont_rel n tk sk ⇒
    ∃tk1. step_n n (Exn v,ts,tk) = (Exn v,ts,tk1) ∧ cont_rel 0 tk1 sk
Proof
  Induct \\ fs [step]
  \\ simp [Once cont_rel_cases,ADD1]
  \\ rw [] \\ fs [step,step_n_add]
  \\ last_x_assum irule
  \\ first_assum $ irule_at Any
QED

Theorem step_1_forward:
  ∀tr ts tk sr1 ss1 sk1 ss sr sk.
    step_n 1 (sr,ss,sk) = (sr1,ss1,sk1) ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    step_res_rel tr tk sr sk ⇒
    ∃m tr1 ts1 tk1.
      step_n (m+1) (tr,ts,tk) = (tr1,ts1,tk1) ∧
      (tr1 ≠ Error ⇒
       OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
       step_res_rel tr1 tk1 sr1 sk1)
Proof
  rpt strip_tac
  \\ Cases_on ‘is_halt (tr,ts,tk)’
  >-
   (‘is_halt (sr,ss,sk)’ by
        (gvs [step_res_rel_cases] \\ gvs [Once cont_rel_cases])
    \\ full_simp_tac std_ss [is_halt_step] \\ gvs [])
  \\ qpat_x_assum ‘step_res_rel tr tk sr sk’ mp_tac
  \\ simp [Once step_res_rel_cases]
  \\ strip_tac \\ gvs []
  >~ [‘Exp’] >-
   (irule step_1_Exp_forward
    \\ rpt $ first_assum $ irule_at Any \\ fs [])
  >~ [‘Exn’] >-
   (Cases_on ‘tk’ \\ gvs []
    \\ Cases_on ‘sk’ \\ gvs []
    >- fs [Once cont_rel_cases]
    \\ rename [‘cont_rel _ (tk1::tk) (sk1::sk)’]
    \\ qpat_x_assum ‘cont_rel _ _ _’ mp_tac
    \\ simp [Once cont_rel_cases]
    \\ rw [] \\ fs [step] \\ gvs []
    \\ TRY (qexists_tac ‘0’ \\ fs [step,step_res_rel_cases]
            \\ irule env_rel_cons \\ fs []
            \\ first_assum $ irule_at $ Pos last \\ fs [] \\ NO_TAC)
    \\ TRY
     (rename [‘cont_rel n’]
      \\ qexists_tac ‘n’ \\ fs [step_n_add,step]
      \\ drule cont_rel_Exn
      \\ disch_then $ qspecl_then [‘v1’,‘ts’] mp_tac
      \\ strip_tac \\ first_assum $ irule_at Any
      \\ fs [step_res_rel_cases] \\ NO_TAC)
    >~ [‘HandleK’] >-
     (qexists_tac ‘0’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
      \\ fs [step_res_rel_cases]
      \\ first_x_assum $ irule_at Any \\ fs []
      \\ irule_at Any env_rel_cons \\ fs [])
    \\ rename [‘HandleAppK’]
    \\ qexists_tac ‘0’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ fs [step_res_rel_cases]
    \\ first_x_assum $ irule_at Any \\ fs []
    \\ simp [Once cont_rel_cases])
  \\ qexists_tac ‘0’
  \\ Cases_on ‘tk’ \\ fs []
  \\ Cases_on ‘sk’ \\ fs []
  >- fs [Once cont_rel_cases]
  \\ rename [‘cont_rel _ (tk1::tk) (sk1::sk)’]
  \\ qpat_x_assum ‘cont_rel _ _ _’ mp_tac
  \\ simp [Once cont_rel_cases] \\ rw []
  >~ [‘IfK’] >-
   (gvs [step]
    \\ Cases_on ‘v1 = Constructor "True" [] ∨ v1 = Constructor "False" []’ \\ gvs []
    \\ gvs [step]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    \\ fs [step_res_rel_cases]
    \\ first_assum $ irule_at Any \\ fs [])
  >~ [‘RaiseK’] >-
   (gvs [step] \\ fs [step_res_rel_cases]
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs [])
  >~ [‘HandleK’] >-
   (gvs [step] \\ fs [step_res_rel_cases])
  >~ [‘HandleAppK’] >-
   (gvs [step] \\ fs [step_res_rel_cases])
  >~ [‘LetK _ n’] >-
   (Cases_on ‘n’ \\ gvs [step,step_res_rel_cases]
    \\ first_assum $ irule_at Any \\ fs []
    \\ irule env_rel_cons \\ simp [])
  >~ [‘CaseK _ v’] >-
   (Cases_on ‘tes’ \\ gvs [step,return_def]
    \\ PairCases_on ‘h’ \\ fs [step]
    \\ Cases_on ‘ses’ \\ gvs []
    \\ PairCases_on ‘h’ \\ fs [step]
    \\ IF_CASES_TAC >- fs []
    \\ CASE_TAC \\ fs []
    \\ qpat_x_assum ‘v_rel (Constructor _ _) _’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [AllCaseEqs()]
    >-
     (fs [step_res_rel_cases,PULL_EXISTS]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ first_assum $ irule_at Any \\ fs []
      \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
      \\ irule env_rel_zip \\ fs []
      \\ irule_at Any env_rel_cons
      \\ first_assum $ irule_at $ Pos hd
      \\ simp [Once v_rel_cases])
    \\ fs [step_res_rel_cases,PULL_EXISTS]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ simp [Once v_rel_cases]
    \\ simp [Once cont_rel_cases]
    \\ first_assum $ irule_at $ Pos hd
    \\ fs [])
  \\ rename [‘AppK’]
  \\ reverse (Cases_on ‘tes’) \\ gvs [] \\ gvs [step]
  >-
   (simp [Once cont_rel_cases, step_res_rel_cases] \\ rw []
    \\ first_assum $ irule_at Any \\ fs []
    \\ simp [Once cont_rel_cases])
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ IF_CASES_TAC \\ gs[]
  \\ ‘∃x. application op tenv (v1::tvs) ts tk = x’ by fs []
  \\ PairCases_on ‘x’
  \\ drule application_thm \\ fs [PULL_EXISTS]
  \\ disch_then drule_all \\ strip_tac \\ gvs []
QED

Theorem step_n_forward:
  ∀n tr ts tk sr1 ss1 sk1 ss sr sk.
    step_n n (sr,ss,sk) = (sr1,ss1,sk1) ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    step_res_rel tr tk sr sk ⇒
    ∃m tr1 ts1 tk1.
      step_n (m+n) (tr,ts,tk) = (tr1,ts1,tk1) ∧
      (tr1 ≠ Error ⇒ OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
                     step_res_rel tr1 tk1 sr1 sk1)
Proof
  Induct \\ fs [] \\ rw []
  >- (qexists_tac ‘0’ \\ fs [])
  \\ full_simp_tac std_ss [ADD_CLAUSES]
  \\ ‘∃a. step_n 1 (sr,ss,sk) = a’ by fs []
  \\ PairCases_on ‘a’
  \\ drule_all step_1_forward
  \\ strip_tac \\ fs []
  \\ Cases_on ‘tr1 = Error’
  >-
   (rewrite_tac [Once ADD_COMM]
    \\ rewrite_tac [ADD1]
    \\ rewrite_tac [GSYM ADD_ASSOC]
    \\ qexists_tac ‘m’
    \\ once_rewrite_tac [step_n_add]
    \\ fs [] \\ gvs [is_halt_step,is_halt_def])
  \\ gvs [step_n_SUC,GSYM ADD1]
  \\ first_x_assum drule_all
  \\ strip_tac
  \\ qexists_tac ‘m+m'’
  \\ rewrite_tac [GSYM ADD_ASSOC]
  \\ rewrite_tac [Once ADD_COMM]
  \\ once_rewrite_tac [step_n_add] \\ fs []
QED

Theorem cont_rel_nil:
  (cont_rel 0 [] y ⇔ y = []) ∧
  (cont_rel 0 x [] ⇔ x = [])
Proof
  ntac 2 $ fs [Once cont_rel_cases]
QED

Theorem step_until_halt_thm:
  step_res_rel tr tk sr sk ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
  step_until_halt (tr,ts,tk) ≠ Err ⇒
  snext_res_rel (step_until_halt (tr,ts,tk))
                (step_until_halt (sr,ss,sk))
Proof
  fs [step_until_halt_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
  >-
   (‘∃a. step_n x (tr,ts,tk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ gvs []
    \\ ‘a0 ≠ Error’ by (strip_tac \\ gvs [])
    \\ reverse (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw [])
    >-
     (‘∃b. step_n x (sr,ss,sk) = b’ by fs []
      \\ PairCases_on ‘b’ \\ gvs []
      \\ drule_all step_n_forward \\ rw []
      \\ gvs [step_n_add,is_halt_step]
      \\ first_x_assum $ qspec_then ‘x’ mp_tac
      \\ fs []
      \\ Cases_on ‘a0’ \\ gvs [step_res_rel_cases,cont_rel_nil])
    \\ ‘∃b. step_n x' (sr,ss,sk) = b’ by fs []
    \\ PairCases_on ‘b’ \\ gvs []
    \\ drule_all step_n_forward \\ rw []
    \\ Cases_on ‘tr1 = Error’
    >-
     (‘step_n x (tr,ts,tk) = step_n (m+x') (tr,ts,tk)’
        by metis_tac [is_halt_imp_eq,is_halt_def] \\ fs [])
    \\ gs []
    \\ ‘is_halt (tr1,ts1,tk1)’ by
     (ntac 5 $ pop_assum mp_tac
      \\ simp [step_res_rel_cases]
      \\ rw [] \\ gvs [cont_rel_nil])
    \\ ‘step_n x (tr,ts,tk) = step_n (m+x') (tr,ts,tk)’
        by metis_tac [is_halt_imp_eq,is_halt_def] \\ fs []
    \\ gvs []
    \\ gvs [step_res_rel_cases]
    \\ fs [snext_res_rel_cases])
  \\ reverse (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw [])
  >- simp [Once snext_res_rel_cases]
  \\ ‘∃a. step_n x (sr,ss,sk) = a’ by fs []
  \\ PairCases_on ‘a’ \\ gvs []
  \\ ‘∃b. step_n x (tr,ts,tk) = b’ by fs []
  \\ PairCases_on ‘b’ \\ gvs []
  \\ drule_all step_n_forward \\ rw []
  \\ last_assum $ qspec_then ‘m+x’ assume_tac
  \\ last_x_assum $ qspec_then ‘x’ assume_tac
  \\ gvs []
  \\ Cases_on ‘tr1 = Error’ \\ gs []
  \\ gvs [step_res_rel_cases,cont_rel_nil]
QED

Theorem semantics_thm:
  compile_rel 0 e1 e2 ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
  env_rel tenv senv ∧
  cont_rel 0 tk sk ⇒
  semantics e1 tenv ts tk --->
  semantics e2 senv ss sk
Proof
  qsuff_tac ‘
    ∀t1 t2.
      (∃e1 e2 ts ss tenv senv tk sk.
        compile_rel 0 e1 e2 ∧
        OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
        env_rel tenv senv ∧
        cont_rel 0 tk sk ∧
        t1 = semantics e1 tenv ts tk ∧
        t2 = semantics e2 senv ss sk) ⇒
      t1 ---> t2’
  >- (rw [PULL_EXISTS]
      \\ last_x_assum drule
      \\ rpt (disch_then drule) \\ fs [])
  \\ ho_match_mp_tac pure_semanticsTheory.compiles_to_coind
  \\ rpt gen_tac \\ strip_tac
  \\ ntac 2 (pop_assum $ mp_tac o GSYM)
  \\ simp [stateLangTheory.semantics_def]
  \\ simp [Once sinterp_def] \\ strip_tac
  \\ simp [Once sinterp_def] \\ strip_tac
  \\ ntac 2 $ pop_assum mp_tac
  \\ once_rewrite_tac [itreeTheory.itree_unfold_err]
  \\ fs []
  \\ simp [GSYM sinterp_def]
  \\ Cases_on ‘step_until_halt (Exp tenv e1,ts,tk) = Err’ >- fs []
  \\ drule_at (Pos last) step_until_halt_thm
  \\ rpt (disch_then $ drule_at $ Pos last)
  \\ disch_then $ qspec_then ‘Exp senv e2’ mp_tac
  \\ disch_then (qspec_then ‘sk’ mp_tac)
  \\ impl_tac
  >- (simp [Once step_res_rel_cases]
      \\ qexists_tac ‘0’ \\ fs [])
  \\ rename [‘snext_res_rel xx yy’]
  \\ simp [snext_res_rel_cases]
  \\ strip_tac \\ fs []
  \\ rw [] \\ gvs []
  \\ Cases \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ fs [] \\ fs [value_def] \\ rw []
  \\ simp [sinterp_def]
  \\ ‘compile_rel 0 (Lit (Str y)) (Lit (Str y))’ by simp [Once compile_rel_cases]
  \\ pop_assum $ irule_at Any
  \\ qpat_x_assum ‘cont_rel _ _ _’ $ irule_at Any \\ fs []
  \\ ‘env_rel [] []’ by fs [env_rel_def]
  \\ pop_assum $ irule_at Any
  \\ first_x_assum $ irule_at Any
  \\ simp [value_def]
  \\ once_rewrite_tac [itreeTheory.itree_unfold_err]
  \\ rpt conj_tac
  \\ rpt AP_THM_TAC
  \\ fs []
  \\ AP_TERM_TAC
  \\ rpt AP_THM_TAC
  \\ AP_TERM_TAC
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ irule step_unitl_halt_unwind
  \\ fs [step_def,application_def,get_atoms_def,value_def]
QED

Theorem compile_rel_itree_of:
  compile_rel 0 e1 e2 ⇒
  itree_of e1 ---> itree_of e2
Proof
  fs [stateLangTheory.itree_of_def] \\ rw []
  \\ irule semantics_thm
  \\ simp [Once cont_rel_cases]
  \\ fs [env_rel_def]
QED

val _ = export_theory ();
