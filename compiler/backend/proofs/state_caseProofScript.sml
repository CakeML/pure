(*
  Correctness for expansion of Case to If/Let/Proj combinations.
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     stateLangTheory;
local open pure_semanticsTheory in end

val _ = new_theory "state_caseProof";

val _ = set_grammar_ancestry ["stateLang"];

Overload Fail = “App AppOp [] :stateLang$exp”
Overload Proj = “λn i x. App (Proj n i) [x:stateLang$exp]”
Overload IsEq = “λn i x. App (IsEq n i) [x:stateLang$exp]”

Definition lets_for_def:
  lets_for cn v [] b = b:stateLang$exp ∧
  lets_for cn v ((n,w)::ws) b = Let (SOME w) (Proj cn n (Var v)) (lets_for cn v ws b)
End

Definition rows_of_def:
  rows_of v [] = Fail ∧
  rows_of v ((cn,vs,b)::rest) =
    If (IsEq cn (LENGTH vs) (Var v))
      (lets_for cn v (MAPi (λi v. (i,v)) vs) b)
      (Let (SOME v) (Var v) (rows_of v rest))
End

Definition expand_Case_def:
  expand_Case x v rs =
    if MEM v (FLAT (MAP (FST o SND) rs)) then
      Fail
    else
      Let (SOME v) x (rows_of v rs)
End

Inductive compile_rel:

[~Var:]
  compile_rel (stateLang$Var v) (stateLang$Var v) ∧

[~Lam:]
  (compile_rel x y ⇒
  compile_rel (Lam v_opt x) (Lam v_opt y)) ∧

[~Raise:]
  (compile_rel x y ⇒
  compile_rel (Raise x) (Raise y)) ∧

[~Handle:]
  (compile_rel x1 y1 ∧ compile_rel x2 y2 ⇒
  compile_rel (Handle x1 v x2) (Handle y1 v y2)) ∧

[~HandleApp:]
  (compile_rel x1 y1 ∧ compile_rel x2 y2 ⇒
  compile_rel (HandleApp x1 x2) (HandleApp y1 y2)) ∧

[~App:]
  (LIST_REL compile_rel xs ys ⇒
  compile_rel (App op xs) (App op ys)) ∧

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
    EVERY (λ(n,x). ∃v y. x = Lam v y) tfns ∧
    compile_rel te se ⇒
    compile_rel (Letrec tfns te) (Letrec sfns se)) ∧

[~Let:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (Let x_opt te1 te2) (Let x_opt se1 se2)) ∧

[~If:]
  (compile_rel te se ∧
   compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (If te te1 te2) (If se se1 se2)) ∧

[~Case:]
  (∀v te se tes ses.
     compile_rel te se ∧
     MAP FST tes = MAP FST ses ∧ ALL_DISTINCT (MAP FST tes) ∧
     MAP (FST o SND) tes = MAP (FST o SND) ses ∧
     LIST_REL compile_rel (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
  compile_rel (Case te v tes) (expand_Case se v ses))

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
     env_rel tenv senv ∧ compile_rel te se ⇒
     v_rel (Closure n tenv te) (Closure n senv se)) ∧

[~Recclosure:]
  (∀tfns sfns tenv senv n.
     env_rel tenv senv ∧
     LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
     EVERY (λ(n,x). ∃v y. x = Lam v y) tfns ∧
     MAP FST tfns = MAP FST sfns ⇒
     v_rel (Recclosure tfns tenv n)
           (Recclosure sfns senv n)) ∧

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

Definition env_rel_ignore_def:
  env_rel_ignore tenv senv m ⇔
     (∀n. n ≠ m ⇒ (ALOOKUP tenv n = NONE ⇔ ALOOKUP senv n = NONE)) ∧
     (∀(n:string) tv.
       ALOOKUP tenv n = SOME tv ∧ n ≠ m ⇒
       ∃sv. ALOOKUP senv n = SOME sv ∧ v_rel tv sv)
End

Inductive step_res_rel:
  (v_rel v1 v2 ⇒
   step_res_rel (Val v1) (Val v2)) ∧
  (v_rel v1 v2 ⇒
   step_res_rel (Exn v1) (Exn v2)) ∧
  (step_res_rel Error Error) ∧
  (compile_rel e1 e2 ∧ env_rel env1 env2 ⇒
   step_res_rel (Exp env1 e1) (Exp env2 e2)) ∧
  (step_res_rel (Action a b) (Action a b))
End

Inductive cont_rel:
  (cont_rel [] []) ∧
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
  (∀tenv senv te1 se1 te2 se2 sk tk.
    cont_rel tk sk ∧ env_rel tenv senv ∧
    compile_rel te1 se1 ∧ compile_rel te2 se2 ⇒
    cont_rel (IfK tenv te1 te2 :: tk)
             (IfK senv se1 se2 :: sk)) ∧
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
             (RaiseK :: sk)) ∧
  (∀sk tk v tenv senv.
    cont_rel tk sk ∧ env_rel_ignore tenv senv v ∧
    MAP FST tes = MAP FST ses ∧ ALL_DISTINCT (MAP FST tes) ∧
    ~MEM v (FLAT (MAP (FST o SND) tes)) ∧
    MAP (FST o SND) tes = MAP (FST o SND) ses ∧
    LIST_REL compile_rel (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
    cont_rel (CaseK tenv v tes :: tk)
             (LetK senv (SOME v) (rows_of v ses) :: sk))
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

Theorem cont_rel_nil[simp]:
  (cont_rel [] ys ⇔ ys = []) ∧
  (cont_rel xs [] ⇔ xs = [])
Proof
  Cases_on ‘xs’ \\ Cases_on ‘ys’ \\ fs []
  \\ simp [Once cont_rel_cases]
  \\ simp [Once cont_rel_cases]
QED

Theorem env_rel_cons:
  env_rel xs ys ∧ v_rel x y ⇒
  env_rel ((n,x)::xs) ((n,y)::ys)
Proof
  rw [env_rel_def] \\ rw [] \\ fs [SUBSET_DEF]
QED

Theorem env_rel_zip:
  ∀n x y xs ys.
    env_rel xs ys ∧ LIST_REL v_rel x y ∧
    LENGTH n = LENGTH x ⇒
    env_rel (ZIP(n,x)++xs) (ZIP(n,y)++ys)
Proof
  Induct \\ fs []
  \\ Cases_on ‘x’ \\ fs [PULL_EXISTS] \\ rw []
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

Theorem application_thm:
  application op tenv tvs ts tk = (tr1,ts1,tk1) ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧ cont_rel tk sk ∧
  LIST_REL v_rel tvs svs ∧ env_rel tenv senv ∧
  num_args_ok op (LENGTH svs) ⇒
  ∃sr1 ss1 sk1.
    application op senv svs ss sk = (sr1,ss1,sk1) ∧
    cont_rel tk1 sk1 ∧ OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
    step_res_rel tr1 sr1
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
     (Cases_on ‘n’ \\ fs [opt_bind_def]
      \\ irule env_rel_cons \\ fs []
      \\ first_assum $ irule_at Any \\ fs [])
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
    \\ Cases_on ‘arg’
    \\ gvs [opt_bind_def]
    \\ TRY (irule env_rel_cons)
    \\ rw []
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
    \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs [])
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
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs [])
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

(*
  ∃ck1.
    step_n ck1 (Exp ((v,Constructor s svs)::senv)
                 (lets_for s v (MAPi (λi v. (i,v)) h1) h2'),ss,sk) =
      (Exp (REVERSE (ZIP (h1,svs)) ++ senv) h2',ss,sk)
*)

Theorem step_1_forward:
  ∀tr ts tk tr1 ts1 tk1 ss sr sk.
    step_n 1 (tr,ts,tk) = (tr1,ts1,tk1) ∧
    cont_rel tk sk ∧ OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    step_res_rel tr sr ⇒
    ∃m sr1 ss1 sk1.
      step_n (m+1) (sr,ss,sk) = (sr1,ss1,sk1) ∧
      (tr1 ≠ Error ⇒ cont_rel tk1 sk1) ∧
      OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
      step_res_rel tr1 sr1
Proof

  rpt strip_tac
  \\ Cases_on ‘is_halt (tr,ts,tk)’
  >-
   (‘is_halt (sr,ss,sk)’ by
        (gvs [step_res_rel_cases] \\ Cases_on ‘tk’ \\ gvs [cont_rel_nil])
    \\ full_simp_tac std_ss [is_halt_step] \\ gvs [])
  \\ qpat_x_assum ‘step_res_rel tr sr’ mp_tac
  \\ simp [Once step_res_rel_cases]
  \\ strip_tac \\ gvs []
  >~ [‘Exn’] >-
   (Cases_on ‘tk’ \\ gvs []
    \\ Cases_on ‘sk’ \\ gvs []
    \\ rename [‘cont_rel (tk1::tk) (sk1::sk)’]
    \\ qpat_x_assum ‘cont_rel _ _’ mp_tac
    \\ simp [Once cont_rel_cases]
    \\ rw [] \\ fs [step] \\ gvs []
    \\ qexists_tac ‘0’ \\ fs [step,step_res_rel_cases]
    >- (irule env_rel_cons \\ fs []
        \\ first_assum $ irule_at $ Pos last \\ fs [])
    \\ simp [Once cont_rel_cases])
  >~ [‘Exp’] >-
   (qexists_tac ‘0’
    \\ qpat_x_assum ‘compile_rel e1 e2’ mp_tac
    \\ simp [Once compile_rel_cases] \\ rw []
    >~ [‘Case’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ fs [expand_Case_def] \\ fs [step]
      \\ simp [Once cont_rel_cases]
      \\ pop_assum $ irule_at Any \\ fs []
      \\ fs [env_rel_def,env_rel_ignore_def])
    >~ [‘Var v’] >-
     (gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
      \\ Cases_on ‘ALOOKUP env2 v’ \\ fs []
      \\ res_tac \\ fs [] \\ gvs [])
    >~ [‘Lam’] >-
     (gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
      \\ once_rewrite_tac [Once v_rel_cases] \\ fs [env_rel_def])
    >~ [‘Raise’] >-
     (gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs [])
    >~ [‘Handle’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs []
      \\ first_assum $ irule_at Any \\ fs [env_rel_def])
    >~ [‘HandleApp’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs [])
    >~ [‘Let’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs [])
    >~ [‘If’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs [])
    >~ [‘Letrec’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ gvs [env_rel_def,ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE]
      \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO,ALOOKUP_rec]
      \\ strip_tac \\ Cases_on ‘MEM n (MAP FST sfns)’ \\ fs []
      \\ rw [Once v_rel_cases] \\ fs [env_rel_def,ALOOKUP_NONE])
    \\ fs [step]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ IF_CASES_TAC >- gvs [step_res_rel_cases]
    \\ Cases_on ‘REVERSE xs’
    >- (gvs [] \\ drule application_thm \\ fs []
        \\ rpt $ disch_then drule \\ rw [] \\ fs [])
    \\ gvs []
    \\ Cases_on ‘REVERSE ys’ \\ gvs []
    \\ gvs [SWAP_REVERSE_SYM,MAP_REVERSE]
    \\ simp [step_res_rel_cases,Once cont_rel_cases])
  \\ Cases_on ‘tk’ \\ fs []
  \\ Cases_on ‘sk’ \\ fs []
  \\ rename [‘cont_rel (tk1::tk) (sk1::sk)’]
  \\ qpat_x_assum ‘cont_rel _ _’ mp_tac
  \\ simp [Once cont_rel_cases] \\ rw []
  >~ [‘CaseK _ v’] >-

   (Cases_on ‘tes’ \\ gvs [step,return_def]
    >-
     (fs [GSYM ADD1,step_n_SUC,step,rows_of_def]
      \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
      \\ qexists_tac ‘0’ \\ gvs [step_res_rel_cases])
    \\ PairCases_on ‘h’ \\ fs [step]
    \\ Cases_on ‘ses’ \\ gvs []
    \\ PairCases_on ‘h’ \\ fs [step]
    \\ fs [rows_of_def]
    \\ qpat_x_assum ‘v_rel v1 v2’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac
    \\ TRY
     (gvs []
      \\ qexists_tac ‘1+1+1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ fs [step_res_rel_cases] \\ NO_TAC)
    \\ fs [GSYM ADD1,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ reverse (Cases_on ‘s = h0’) \\ gvs []
    >-
     (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
      \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
      \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
      \\ qexists_tac ‘0’ \\ fs []
      \\ simp [Once step_res_rel_cases,Once v_rel_cases]
      \\ simp [Once cont_rel_cases]
      \\ first_x_assum $ irule_at $ Pos last \\ fs []
      \\ fs [env_rel_ignore_def])
    \\ reverse IF_CASES_TAC \\ gvs []
    >- (qexists_tac ‘0’ \\ fs [step_res_rel_cases])
    \\ simp [Once step_res_rel_cases,PULL_EXISTS]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
    \\ rpt $ first_assum $ irule_at Any

    \\ cheat)
  \\ qexists_tac ‘0’ \\ fs []
  >~ [‘HandleK’] >-
   (gvs [step] \\ fs [step_res_rel_cases])
  >~ [‘HandleAppK’] >-
   (gvs [step] \\ fs [step_res_rel_cases])
  >~ [‘RaiseK’] >-
   (gvs [step] \\ fs [step_res_rel_cases])
  >~ [‘IfK’] >-
   (gvs [step]
    \\ Cases_on ‘v1 = Constructor "True" [] ∨ v1 = Constructor "False" []’ \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    \\ fs [step_res_rel_cases]
    \\ gvs [env_rel_def,SUBSET_DEF])
  >~ [‘LetK _ n’] >-
   (Cases_on ‘n’ \\ gvs [step,step_res_rel_cases]
    \\ irule env_rel_cons \\ simp []
    \\ first_assum $ irule_at Any \\ fs [])
  \\ rename [‘AppK’]
  \\ reverse (Cases_on ‘tes’) \\ gvs [] \\ gvs [step]
  >- (simp [Once cont_rel_cases, step_res_rel_cases] \\ rw [])
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ IF_CASES_TAC >- gs[step_res_rel_cases]
  \\ fs []
  \\ drule application_thm \\ fs [PULL_EXISTS]
  \\ disch_then drule_all \\ strip_tac \\ fs []
QED

Theorem step_n_forward:
  ∀n tr ts tk tr1 ts1 tk1 ss sr sk.
    step_n n (tr,ts,tk) = (tr1,ts1,tk1) ∧
    cont_rel tk sk ∧ OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    step_res_rel tr sr ⇒
    ∃m sr1 ss1 sk1.
      step_n (m+n) (sr,ss,sk) = (sr1,ss1,sk1) ∧
      (tr1 ≠ Error ⇒ cont_rel tk1 sk1) ∧
      OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
      step_res_rel tr1 sr1
Proof
  Induct \\ fs [] \\ rw []
  >- (qexists_tac ‘0’ \\ fs [])
  \\ full_simp_tac std_ss [ADD_CLAUSES,step_n_SUC]
  \\ ‘∃a. step_n 1 (tr,ts,tk) = a’ by fs []
  \\ PairCases_on ‘a’
  \\ drule_all step_1_forward
  \\ strip_tac \\ fs []
  \\ Q.REFINE_EXISTS_TAC ‘ck1+m’
  \\ once_rewrite_tac [DECIDE “m' + m + n = (m' + n) + m:num”]
  \\ full_simp_tac std_ss [step_n_add] \\ fs []
  \\ Cases_on ‘a0 = Error’ \\ gvs []
  >-
   (‘sr1 = Error’ by fs [step_res_rel_cases] \\ gvs []
    \\ ‘is_halt (Error,ss1,sk1)’ by fs []
    \\ full_simp_tac std_ss [is_halt_step_n_same]
    \\ ‘is_halt (Error,a1,a2)’ by fs []
    \\ full_simp_tac std_ss [is_halt_step_n_same]
    \\ gvs [])
  \\ last_x_assum drule_all
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM ADD1,step_n_SUC] \\ fs []
  \\ rpt $ first_assum $ irule_at Any
  \\ fs []
QED

Theorem step_until_halt_thm:
  step_res_rel tr sr ∧ cont_rel tk sk ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ⇒
  snext_res_rel (step_until_halt (tr,ts,tk))
                (step_until_halt (sr,ss,sk))
Proof
  fs [step_until_halt_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
  >-
   (‘∃a. step_n x (tr,ts,tk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ gvs []
    \\ drule_all step_n_forward \\ rw []
    \\ ‘is_halt (sr1,ss1,sk1)’ by gvs [step_res_rel_cases]
    \\ reverse (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw [])
    >- metis_tac []
    \\ ‘step_n x' (sr,ss,sk) = step_n (m+x) (sr,ss,sk)’
      by metis_tac [is_halt_imp_eq]
    \\ gvs []
    \\ qpat_x_assum ‘step_res_rel _ _’ mp_tac
    \\ simp [Once step_res_rel_cases] \\ strip_tac \\ gvs []
    \\ simp [Once snext_res_rel_cases] \\ gvs [])
  \\ reverse (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw [])
  >- simp [Once snext_res_rel_cases]
  \\ ‘∃a. step_n x (sr,ss,sk) = a’ by fs []
  \\ PairCases_on ‘a’ \\ gvs []
  \\ ‘∃b. step_n x (tr,ts,tk) = b’ by fs []
  \\ PairCases_on ‘b’ \\ gvs []
  \\ last_x_assum $ qspec_then ‘x’ assume_tac
  \\ drule_all step_n_forward \\ rw []
  \\ ‘step_n (m + x) (sr,ss,sk) = (a0,a1,a2)’ by
    (rewrite_tac [step_n_add] \\ fs [is_halt_step])
  \\ gvs [] \\ gvs [step_res_rel_cases]
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
  \\ disch_then $ qspec_then ‘Exp tenv e1’ mp_tac
  \\ disch_then $ qspec_then ‘Exp senv e2’ mp_tac
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
