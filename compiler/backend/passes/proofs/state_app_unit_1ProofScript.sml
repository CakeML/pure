(*
  Correctness for compilation that turns ‘app (Lam NONE x) Unit’ into ‘x’.
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     stateLangTheory;
local open pure_semanticsTheory in end

val _ = new_theory "state_app_unit_1Proof";

val _ = set_grammar_ancestry ["stateLang"];

Overload "app" = “λe1 e2. App AppOp [e1;e2]”;

Inductive compile_rel:

[~App_Lam:]
  (compile_rel x y ⇒
  compile_rel (app (Lam NONE x) Unit) y)

[~Let_Var:]
  (compile_rel x y ⇒
  compile_rel (Let (SOME a) x (Var a)) y)

[~Var:]
  compile_rel (stateLang$Var v) (stateLang$Var v)

[~Lam_SOME:]
  (compile_rel x y ⇒
  compile_rel (Lam ov x) (Lam ov y))

[~Raise:]
  (compile_rel x y ⇒
  compile_rel (Raise x) (Raise y))

[~Handle:]
  (compile_rel x1 y1 ∧ compile_rel x2 y2 ⇒
  compile_rel (Handle x1 v x2) (Handle y1 v y2))

[~HandleApp:]
  (compile_rel x1 y1 ∧ compile_rel x2 y2 ⇒
  compile_rel (HandleApp x1 x2) (HandleApp y1 y2))

[~App:]
  (LIST_REL compile_rel xs ys ⇒
  compile_rel (App op xs) (App op ys))

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
    EVERY (λ(n,x). ∃v y. x = Lam v y) tfns ∧
    compile_rel te se ⇒
    compile_rel (Letrec tfns te) (Letrec sfns se))

[~Let:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (Let x_opt te1 te2) (Let x_opt se1 se2))

[~If:]
  (compile_rel te se ∧
   compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (If te te1 te2) (If se se1 se2))

[~Case:]
  (∀v tes ses te se.
     OPTREL (λ(a,x) (b,y). a = b ∧ compile_rel x y) te se ∧
     MAP FST tes = MAP FST ses ∧
     MAP (FST o SND) tes = MAP (FST o SND) ses ∧
     LIST_REL compile_rel (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
  compile_rel (Case v tes te) (Case v ses se))

End

Inductive v_rel:

[~Atom:]
  (∀a.
     v_rel (Atom a) (Atom a))

[~Constructor:]
  (∀s tvs svs.
     LIST_REL v_rel tvs svs ⇒
     v_rel (Constructor s tvs) (Constructor s svs))

[~Closure:]
  (∀tenv senv te se n.
     env_rel tenv senv ∧ compile_rel te se ⇒
     v_rel (Closure n tenv te) (Closure n senv se))

[~Recclosure:]
  (∀tfns sfns tenv senv n.
     env_rel tenv senv ∧
     LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
     MAP FST tfns = MAP FST sfns ∧
     EVERY (λ(n,x). ∃v y. x = Lam v y) tfns  ⇒
     v_rel (Recclosure tfns tenv n)
           (Recclosure sfns senv n))

[env_rel:]
  (∀tenv senv.
     (∀n. ALOOKUP tenv n = NONE ⇔ ALOOKUP senv n = NONE) ∧
     (∀(n:string) tv.
       ALOOKUP tenv n = SOME tv ⇒
       ∃sv. ALOOKUP senv n = SOME sv ∧ v_rel tv sv) ⇒
     env_rel tenv senv)

End

Theorem env_rel_def = “env_rel tenv senv”
  |> SIMP_CONV (srw_ss()) [Once v_rel_cases];

Inductive cont_rel:
  (cont_rel [] []) ∧
  (∀a tk sk.
    cont_rel tk sk ⇒
    cont_rel (LetK env (SOME a) (Var a)::tk) sk) ∧
  (∀tk sk.
    cont_rel tk sk ∧ env_rel tenv senv ∧
    compile_rel te1 se1 ∧ compile_rel te2 se2 ⇒
    cont_rel (IfK tenv te1 te2 :: tk)
             (IfK senv se1 se2 :: sk)) ∧
  (∀tenv senv op tvs svs tes ses sk tk.
    cont_rel tk sk ∧ env_rel tenv senv ∧
    LIST_REL v_rel tvs svs ∧ LIST_REL compile_rel tes ses ⇒
    cont_rel (AppK tenv op tvs tes :: tk)
             (AppK senv op svs ses :: sk)) ∧
  (∀tenv senv n te se sk tk.
    cont_rel tk sk ∧ env_rel tenv senv ∧
    compile_rel te se ⇒
    cont_rel (LetK tenv n te :: tk)
             (LetK senv n se :: sk)) ∧
  (∀tenv senv n te se sk tk.
    cont_rel tk sk ∧ env_rel tenv senv ∧
    compile_rel te se ⇒
    cont_rel (HandleK tenv n te :: tk)
             (HandleK senv n se :: sk)) ∧
  (∀tenv senv te se sk tk.
    cont_rel tk sk ∧ env_rel tenv senv ∧
    compile_rel te se ⇒
    cont_rel (HandleAppK tenv te :: tk)
             (HandleAppK senv se :: sk)) ∧
  (∀sk tk.
    cont_rel tk sk ⇒
    cont_rel (RaiseK :: tk)
             (RaiseK :: sk))
End

Inductive step_res_rel:
  (v_rel v1 v2 ∧ cont_rel tk sk ⇒
   step_res_rel (Val v1) tk (Val v2) sk) ∧
  (v_rel v1 v2 ∧ cont_rel tk sk ⇒
   step_res_rel (Exn v1) tk (Exn v2) sk) ∧
  (step_res_rel Error tk Error sk) ∧
  (compile_rel e1 e2 ∧ env_rel env1 env2 ∧ cont_rel tk sk ⇒
   step_res_rel (Exp env1 e1) tk (Exp env2 e2) sk) ∧
  (cont_rel tk sk ⇒
   step_res_rel (Action a b) tk (Action a b) sk)
End

Definition rec_env_def:
  rec_env f env =
    MAP (λ(fn,_). (fn,Recclosure f env fn)) f ++ env
End

Inductive snext_res_rel:
  (OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧ cont_rel tk sk ⇒
   snext_res_rel (Act x tk ts) (Act x sk ss)) ∧
  (snext_res_rel Ret Ret) ∧
  (snext_res_rel Div Div) ∧
  (snext_res_rel Err Err)
End

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
    LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
    MAP FST tfns = MAP FST sfns ⇒
    ∃y. ALOOKUP sfns n = SOME y ∧ compile_rel x y
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

Theorem compile_rel_Lam:
  ∀n e t. compile_rel (Lam n e) t ⇒ ∃u. t = Lam n u ∧ compile_rel e u
Proof
  rw [Once compile_rel_cases]
QED

Theorem application_thm:
  application op tvs ts tk = (tr1,ts1,tk1) ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧ cont_rel tk sk ∧
  LIST_REL v_rel tvs svs ∧
  num_args_ok op (LENGTH svs) ⇒
  ∃sr1 ss1 sk1.
    application op svs ss sk = (sr1,ss1,sk1) ∧
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
    \\ drule compile_rel_Lam \\ strip_tac \\ fs []
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
    \\ rw [] \\ res_tac \\ fs [ALOOKUP_NONE])
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

Triviality LIST_REL_MAP_MAP:
  ∀xs ys.
    LIST_REL R (MAP f xs) (MAP g ys) =
    LIST_REL (λx y. R (f x) (g y)) xs ys
Proof
  Induct \\ fs [PULL_EXISTS,MAP_EQ_CONS]
QED

Theorem find_match_list_NONE:
  ∀ses tes.
    find_match_list s tvs env1 tes te = NONE ∧
    MAP FST tes = MAP FST ses ∧
    MAP (FST o SND) tes = MAP (FST o SND) ses ∧
    OPTREL (λ(a,x) (b,y). a = b) te se ∧
    LIST_REL v_rel tvs svs ⇒
    find_match_list s svs env2 ses se = NONE
Proof
  Induct
  \\ fs [PULL_EXISTS,find_match_list_def,FORALL_PROD,MAP_EQ_CONS]
  >-
   (rpt CASE_TAC \\ gvs []
    \\ CCONTR_TAC \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ rw [] \\ fs [] \\ metis_tac []
QED

Theorem find_match_list_SOME:
  ∀ses tes.
    find_match_list s tvs env1 tes te = SOME (env1',e1) ∧
    MAP FST tes = MAP FST ses ∧
    MAP (FST o SND) tes = MAP (FST o SND) ses ∧
    LIST_REL v_rel tvs svs ∧ env_rel env1 env2 ∧
    OPTREL (λ(a,x) (b,y). a = b ∧ compile_rel x y) te se ∧
    LIST_REL (λa b. compile_rel (SND (SND a)) (SND (SND b))) tes ses ⇒
    ∃env2' e2.
      find_match_list s svs env2 ses se = SOME (env2',e2) ∧
      env_rel env1' env2' ∧ compile_rel e1 e2
Proof
  Induct
  \\ fs [PULL_EXISTS,find_match_list_def,FORALL_PROD,MAP_EQ_CONS]
  >-
   (rpt CASE_TAC \\ gvs [] \\ rw [] \\ fs []
    \\ CCONTR_TAC \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ rw [] \\ fs []
  >- (irule env_rel_zip \\ fs [])
  \\ first_x_assum irule \\ metis_tac []
QED

Theorem step_1_Exp_forward:
  ∀e1 e2 ts tk sr1 ss1 sk1 ss sk env1 env2.
    step ss sk (Exp env2 e2) = (sr1,ss1,sk1) ∧
    cont_rel tk sk ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    compile_rel e1 e2 ∧
    env_rel env1 env2 ⇒
    ∃m tr1 ts1 tk1.
      step_n (m + 1) (Exp env1 e1,ts,tk) = (tr1,ts1,tk1) ∧
      OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
      step_res_rel tr1 tk1 sr1 sk1
Proof
  Induct_on ‘compile_rel’ \\ rpt strip_tac
  >-
   (fs [GSYM ADD1]
    \\ ntac 4 (Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’
    \\ first_x_assum irule
    \\ rpt (first_assum $ irule_at $ Pos hd \\ fs []))
  >-
   (fs [GSYM ADD1] \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’
    \\ first_x_assum irule
    \\ rpt (first_assum $ irule_at $ Pos hd \\ fs [])
    \\ simp [Once cont_rel_cases])
  \\ gvs []
  \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
  >~ [‘Var v’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ Cases_on ‘ALOOKUP env1 v’ \\ gvs []
    \\ gvs [env_rel_def]
    \\ res_tac \\ gvs []
    \\ gvs [step_res_rel_cases,env_rel_def]
    \\ rw [] \\ fs [])
  >~ [‘If’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ fs [step_res_rel_cases]
    \\ simp [Once cont_rel_cases])
  >~ [‘Lam’] >-
   (qexists_tac ‘0’ \\ fs []
    \\ gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
    \\ once_rewrite_tac [Once v_rel_cases] \\ fs [env_rel_def] \\ rw [] \\ fs [])
  >~ [‘Raise’] >-
   (qexists_tac ‘0’ \\ fs []
    \\ gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
    \\ once_rewrite_tac [Once v_rel_cases] \\ fs [env_rel_def]
    \\ simp [Once cont_rel_cases]
    \\ last_x_assum $ irule_at Any \\ fs [])
  >~ [‘Letrec’] >-
   (qexists_tac ‘0’ \\ fs [step]
    \\ simp [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
    \\ rpt $ first_x_assum $ irule_at Any \\ gvs []
    \\ rpt gen_tac
    \\ gvs [env_rel_def,ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE]
    \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO,ALOOKUP_rec]
    \\ strip_tac \\ Cases_on ‘MEM n (MAP FST sfns)’ \\ fs []
    \\ rw [Once v_rel_cases] \\ fs [env_rel_def,ALOOKUP_NONE]
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
    \\ Cases_on ‘ALOOKUP env1 v’ \\ fs []
    >-
     (fs [env_rel_def,AllCaseEqs()]
      \\ simp [Once step_res_rel_cases]
      \\ res_tac \\ gvs [])
    \\ rename [‘ALOOKUP env1 v = SOME v1’]
    \\ ‘∃v2. ALOOKUP env2 v = SOME v2 ∧ v_rel v1 v2’ by
      (fs [env_rel_def] \\ res_tac \\ fs [])
    \\ gvs []
    \\ gvs [find_match_def]
    \\ ‘ses = [] ⇔ tes = []’ by (Cases_on ‘ses’ \\ Cases_on ‘tes’ \\ gvs [])
    \\ gvs [] \\ IF_CASES_TAC
    >- (gvs [] \\ simp [Once step_res_rel_cases])
    \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs []
    \\ TRY (simp [Once step_res_rel_cases] \\ NO_TAC)
    \\ ‘ss1 = ss ∧ sk = sk1’ by gvs [AllCaseEqs()] \\ gvs []
    \\ qpat_assum ‘OPTREL _ _ _’ $ irule_at Any
    \\ CASE_TAC
    >-
     (qsuff_tac ‘find_match_list s svs env2 ses se = NONE’
      >- (rw [] \\ gvs [] \\ simp [Once step_res_rel_cases])
      \\ drule_then irule find_match_list_NONE
      \\ gvs []
      \\ Cases_on ‘te’ \\ Cases_on ‘se’ \\ gvs []
      \\ fs [UNCURRY])
    \\ PairCases_on ‘x’ \\ fs []
    \\ drule_then drule find_match_list_SOME \\ fs []
    \\ disch_then $ drule_then drule
    \\ disch_then $ qspec_then ‘se’ mp_tac
    \\ reverse impl_tac
    >- (rw [] \\ gvs [] \\ simp [Once step_res_rel_cases])
    \\ conj_tac
    >- (Cases_on ‘te’ \\ Cases_on ‘se’ \\ gvs [] \\ gvs [UNCURRY])
    \\ fs [LIST_REL_MAP_MAP]
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ fs [])
  >~ [‘App’] >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ IF_CASES_TAC \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ gvs [AllCaseEqs()]
    >- fs [step_res_rel_cases]
    >-
     (‘∃a. application op [] ts tk = a’ by fs [] \\ PairCases_on ‘a’
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

Theorem step_1_Exn_forward:
  ∀ts sk tk sr1 ss1 sk1 ss v1 v2.
    step ss sk (Exn v2) = (sr1,ss1,sk1) ∧
    cont_rel tk sk ∧ v_rel v1 v2 ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ⇒
    ∃m tr1 ts1 tk1.
      step_n (m + 1) (Exn v1,ts,tk) = (tr1,ts1,tk1) ∧
      OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
      step_res_rel tr1 tk1 sr1 sk1
Proof
  Induct_on ‘cont_rel’ \\ rpt strip_tac
  >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ simp [Once step_res_rel_cases]
    \\ simp [Once cont_rel_cases])
  >-
   (first_x_assum drule_all \\ strip_tac
    \\ simp [GSYM ADD1,step_n_SUC,step]
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  \\ rw [] \\ fs [step] \\ gvs []
  \\ qexists_tac ‘0’ \\ fs [step,step_res_rel_cases]
  \\ rw [] \\ fs []
  \\ TRY (irule env_rel_cons \\ fs []
          \\ first_assum $ irule_at $ Pos last \\ fs [] \\ NO_TAC)
  \\ simp [Once cont_rel_cases]
QED

Theorem step_1_Val_forward:
  ∀ts sk tk sr1 ss1 sk1 ss v1 v2.
    step ss sk (Val v2) = (sr1,ss1,sk1) ∧
    cont_rel tk sk ∧ v_rel v1 v2 ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ⇒
    ∃m tr1 ts1 tk1.
      step_n (m + 1) (Val v1,ts,tk) = (tr1,ts1,tk1) ∧
      OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
      step_res_rel tr1 tk1 sr1 sk1
Proof
  Induct_on ‘cont_rel’ \\ rpt strip_tac
  >-
   (qexists_tac ‘0’ \\ gvs [step]
    \\ simp [Once step_res_rel_cases]
    \\ simp [Once cont_rel_cases])
  >-
   (first_x_assum drule_all \\ strip_tac
    \\ simp [GSYM ADD1,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  \\ qexists_tac ‘0’
  >~ [‘IfK’] >-
   (gvs [step]
    \\ Cases_on ‘v1 = Constructor "True" [] ∨ v1 = Constructor "False" []’ \\ gvs []
    \\ gvs [step]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    \\ fs [step_res_rel_cases]
    \\ every_case_tac \\ fs [])
  >~ [‘RaiseK’] >-
   (Cases_on ‘ts’ \\ Cases_on ‘ss’
    \\ gvs [step] \\ fs [step_res_rel_cases] \\ rw [] \\ fs [])
  >~ [‘HandleK’] >-
   (gvs [step] \\ fs [step_res_rel_cases] \\ rw [] \\ fs [])
  >~ [‘HandleAppK’] >-
   (gvs [step] \\ fs [step_res_rel_cases] \\ rw [] \\ fs [])
  >~ [‘LetK _ n’] >-
   (Cases_on ‘n’ \\ gvs [step,step_res_rel_cases]
    \\ irule env_rel_cons \\ simp [])
  \\ rename [‘AppK’]
  \\ reverse (Cases_on ‘tes’) \\ gvs [] \\ gvs [step]
  >-
   (simp [Once cont_rel_cases, step_res_rel_cases] \\ rw []
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ simp [Once cont_rel_cases])
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ IF_CASES_TAC >- gvs [step_res_rel_cases]
  \\ ‘∃x. application op (v1::tvs) ts tk = x’ by fs []
  \\ PairCases_on ‘x’
  \\ drule application_thm \\ fs [PULL_EXISTS]
  \\ disch_then drule_all \\ strip_tac \\ gvs []
QED

Theorem step_1_forward:
  ∀tr ts tk sr1 ss1 sk1 ss sr sk.
    step_n 1 (sr,ss,sk) = (sr1,ss1,sk1) ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    step_res_rel tr tk sr sk ⇒
    ∃m tr1 ts1 tk1.
      step_n (m+1) (tr,ts,tk) = (tr1,ts1,tk1) ∧
      OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
      step_res_rel tr1 tk1 sr1 sk1
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
   (irule step_1_Exn_forward
    \\ rpt $ first_assum $ irule_at Any \\ fs [])
  >~ [‘Val’] >-
   (irule step_1_Val_forward
    \\ rpt $ first_assum $ irule_at Any \\ fs [])
QED

Theorem step_n_forward:
  ∀n tr ts tk sr1 ss1 sk1 ss sr sk.
    step_n n (sr,ss,sk) = (sr1,ss1,sk1) ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    step_res_rel tr tk sr sk ⇒
    ∃m tr1 ts1 tk1.
      step_n (m+n) (tr,ts,tk) = (tr1,ts1,tk1) ∧
      OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
      step_res_rel tr1 tk1 sr1 sk1
Proof
  Induct \\ fs [] \\ rw []
  >- (qexists_tac ‘0’ \\ fs [])
  \\ full_simp_tac std_ss [ADD_CLAUSES]
  \\ ‘∃a. step_n 1 (sr,ss,sk) = a’ by fs []
  \\ PairCases_on ‘a’
  \\ drule_all step_1_forward
  \\ strip_tac \\ fs []
  \\ gvs [step_n_SUC,GSYM ADD1]
  \\ first_x_assum drule_all
  \\ strip_tac
  \\ qexists_tac ‘m+m'’
  \\ rewrite_tac [GSYM ADD_ASSOC]
  \\ rewrite_tac [Once ADD_COMM]
  \\ once_rewrite_tac [step_n_add] \\ fs []
QED

Theorem cont_rel_not_nil:
  ∀tk1 sk1. cont_rel tk1 sk1 ∧ sk1 ≠ [] ⇒ tk1 ≠ []
Proof
  Induct_on ‘cont_rel’ \\ fs []
QED

Theorem cont_rel_is_halt_Exn:
  ∀tk1. cont_rel tk1 [] ⇒
        step_n (LENGTH tk1) (Exn v1,ts1,tk1) = (Exn v1,ts1,[])
Proof
  Induct \\ simp [Once cont_rel_cases] \\ rw [] \\ fs [step_n_SUC,step]
QED

Theorem cont_rel_is_halt_Val:
  ∀tk1. cont_rel tk1 [] ⇒
        step_n (2 * LENGTH tk1) (Val v1,ts1,tk1) = (Val v1,ts1,[])
Proof
  Induct \\ simp [Once cont_rel_cases] \\ rw []
  \\ fs [MULT_CLAUSES,DECIDE “n+2 = SUC (SUC n)”,step_n_SUC,step]
QED

Theorem step_n_forward_thm:
  ∀n tr ts tk sr1 ss1 sk1 ss sr sk.
    step_n n (sr,ss,sk) = (sr1,ss1,sk1) ∧
    OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    step_res_rel tr tk sr sk ⇒
    ∃m tr1 ts1 tk1.
      step_n (m+n) (tr,ts,tk) = (tr1,ts1,tk1) ∧
      step_res_rel tr1 tk1 sr1 sk1 ∧
      OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
      is_halt (tr1,ts1,tk1) = is_halt (sr1,ss1,sk1)
Proof
  rw [] \\ drule_all step_n_forward
  \\ rw [] \\ Cases_on ‘~is_halt (sr1,ss1,sk1)’ \\ fs []
  >-
   (first_assum $ irule_at $ Pos hd \\ fs []
    \\ gvs [step_res_rel_cases]
    \\ imp_res_tac cont_rel_not_nil \\ gvs [])
  \\ Cases_on ‘is_halt (tr1,ts1,tk1)’
  >-
   (pop_assum $ irule_at Any \\ fs []
    \\ first_assum $ irule_at Any)
  \\ Q.REFINE_EXISTS_TAC ‘ck+m’
  \\ rewrite_tac [GSYM ADD_ASSOC]
  \\ simp [Once step_n_add]
  \\ qpat_x_assum ‘step_res_rel tr1 tk1 sr1 sk1’ mp_tac
  \\ simp [Once step_res_rel_cases]
  \\ rw [] \\ gvs []
  \\ TRY (irule_at Any cont_rel_is_halt_Val)
  \\ TRY (irule_at Any cont_rel_is_halt_Exn)
  \\ fs [Once step_res_rel_cases]
  \\ simp [Once cont_rel_cases]
QED

Theorem step_until_halt_thm:
  step_res_rel tr tk sr sk ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ⇒
  snext_res_rel (step_until_halt (tr,ts,tk))
                (step_until_halt (sr,ss,sk))
Proof
  fs [step_until_halt_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
  \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
  \\ TRY (simp [Once snext_res_rel_cases] \\ NO_TAC)
  >-
   (‘∃b. step_n x' (sr,ss,sk) = b’ by fs []
    \\ PairCases_on ‘b’ \\ gvs []
    \\ ‘∃a. step_n x (tr,ts,tk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ gvs []
    \\ ‘step_n (x+x') (tr,ts,tk) = (a0,a1,a2)’ by
          metis_tac [is_halt_step,ADD_COMM,step_n_add,PAIR]
    \\ ‘step_n (x+x') (sr,ss,sk) = (b0,b1,b2)’ by
          metis_tac [is_halt_step,ADD_COMM,step_n_add,PAIR]
    \\ drule step_n_forward_thm
    \\ disch_then drule_all \\ rw [] \\ gvs []
    \\ qpat_x_assum ‘step_n _ _ = _’ mp_tac
    \\ simp [Once step_n_add,is_halt_step]
    \\ strip_tac \\ gvs []
    \\ qpat_x_assum ‘step_res_rel _ _ _ _’ mp_tac
    \\ simp [Once step_res_rel_cases] \\ strip_tac \\ gvs []
    \\ simp [Once snext_res_rel_cases] \\ gvs [])
  >-
   (‘∃a. step_n x (sr,ss,sk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ gvs []
    \\ drule step_n_forward_thm
    \\ disch_then drule_all \\ rw [] \\ gvs []
    \\ gvs [step_n_add]
    \\ gvs [is_halt_step]
    \\ metis_tac [])
  >-
   (‘∃a. step_n x (sr,ss,sk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ gvs []
    \\ drule step_n_forward_thm
    \\ disch_then drule_all \\ rw [] \\ gvs []
    \\ first_x_assum $ qspec_then ‘m+x’ mp_tac
    \\ gvs [is_halt_step])
QED

Theorem itree_eq:
  ∀P.
     (∀x y.
        P x y ⇒
        (x = Div ∧ y = Div) ∨ (∃v. x = Ret v ∧ y = Ret v) ∨
        ∃a f g. x = Vis a f ∧ y = Vis a g ∧ ∀v. f v ≠ g v ⇒ P (f v) (g v)) ⇒
     ∀x y. P x y ⇒ x = y
Proof
  rw []
  \\ simp [Once itreeTheory.itree_bisimulation]
  \\ qexists_tac ‘λx y. x ≠ y ⇒ P x y’ \\ fs [] \\ rw []
  >~ [‘Ret v’] >-
   (Cases_on ‘t = Ret v’ \\ fs []
    \\ first_x_assum drule \\ fs [])
  >~ [‘Div’] >-
   (Cases_on ‘t = Div’ \\ fs []
    \\ first_x_assum drule \\ fs [])
  \\ Cases_on ‘t = Vis a f’ \\ fs []
  \\ first_x_assum drule \\ fs []
QED

Theorem semantics_thm:
  compile_rel e1 e2 ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
  env_rel tenv senv ∧
  cont_rel tk sk ⇒
  semantics e1 tenv ts tk =
  semantics e2 senv ss sk
Proof
  qsuff_tac ‘
    ∀t1 t2.
      (∃e1 e2 ts ss tenv senv tk sk.
        compile_rel e1 e2 ∧
        OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
        env_rel tenv senv ∧
        cont_rel tk sk ∧
        t1 = semantics e1 tenv ts tk ∧
        t2 = semantics e2 senv ss sk) ⇒
      t1 = t2’
  >- (rw [PULL_EXISTS])
  \\ ho_match_mp_tac itree_eq
  \\ rpt gen_tac \\ strip_tac
  \\ ntac 2 (pop_assum $ mp_tac o GSYM)
  \\ simp [stateLangTheory.semantics_def]
  \\ simp [Once sinterp_def] \\ strip_tac
  \\ simp [Once sinterp_def] \\ strip_tac
  \\ ntac 2 $ pop_assum mp_tac
  \\ once_rewrite_tac [itreeTheory.itree_unfold_err]
  \\ fs []
  \\ simp [GSYM sinterp_def]
  \\ drule_at (Pos last) step_until_halt_thm
  \\ rpt (disch_then $ drule_at $ Pos last)
  \\ disch_then $ qspecl_then [‘Exp tenv e1’,‘tk’] mp_tac
  \\ disch_then $ qspecl_then [‘Exp senv e2’,‘sk’] mp_tac
  \\ impl_tac >- simp [Once step_res_rel_cases]
  \\ rename [‘snext_res_rel xx yy’]
  \\ simp [snext_res_rel_cases]
  \\ strip_tac \\ fs []
  \\ rw [] \\ gvs []
  \\ Cases \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ fs [] \\ fs [value_def] \\ rw []
  \\ simp [sinterp_def]
  \\ ‘compile_rel (Lit (Str y)) (Lit (Str y))’ by simp [Once compile_rel_cases]
  \\ pop_assum $ irule_at Any
  \\ qpat_x_assum ‘cont_rel _ _’ $ irule_at Any
  \\ ‘env_rel [] []’ by fs [env_rel_def]
  \\ pop_assum $ irule_at Any
  \\ first_assum $ irule_at Any
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
  compile_rel e1 e2 ⇒
  itree_of e1 = itree_of e2
Proof
  fs [stateLangTheory.itree_of_def] \\ rw []
  \\ irule semantics_thm
  \\ simp [Once cont_rel_cases]
  \\ fs [env_rel_def]
QED

val _ = export_theory ();
