(*
  Correctness for compilation that replaces Delay, Box, Force
  with stateful operations
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     stateLangTheory;
local open pure_semanticsTheory in end

val _ = new_theory "state_namesProof";

val _ = set_grammar_ancestry ["stateLang"];

Inductive compile_rel:

[~Var:]
  compile_rel (stateLang$Var v) (stateLang$Var v) ∧

[~Lam_NONE:]
  (compile_rel x y ∧ ~(v IN freevars x) ⇒
  compile_rel (Lam NONE x) (Lam (SOME v) y)) ∧

[~Lam_SOME:]
  (compile_rel x y ⇒
  compile_rel (Lam (SOME v) x) (Lam (SOME v) y)) ∧

[~Raise:]
  (compile_rel x y ⇒
  compile_rel (Raise x) (Raise y)) ∧

[~Handle:]
  (compile_rel x1 y1 ∧ compile_rel x2 y2 ⇒
  compile_rel (Handle x1 v x2) (Handle y1 v y2)) ∧

[~HandleApp:]
  (compile_rel x1 y1 ∧ compile_rel x2 y2 ∧ ~(v IN freevars x1) ⇒
  compile_rel (HandleApp x1 x2) (Handle y2 v (App AppOp [y1; Var v]))) ∧

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
  compile_rel (If te te1 te2) (If se se1 se2))

End

Inductive v_rel:

[~Atom:]
  (∀a.
     v_rel (Atom a) (Atom a)) ∧

[~Constructor:]
  (∀s tvs svs.
     LIST_REL v_rel tvs svs ⇒
     v_rel (Constructor s tvs) (Constructor s svs)) ∧

[~Closure_NONE:]
  (∀tenv senv te se v.
     env_rel (freevars te) tenv senv ∧ compile_rel te se ∧
     ~(v IN freevars te) ⇒
     v_rel (Closure NONE tenv te) (Closure (SOME v) senv se)) ∧

[~Closure:]
  (∀tenv senv te se n.
     env_rel (freevars (Lam n te)) tenv senv ∧ compile_rel te se ⇒
     v_rel (Closure n tenv te) (Closure n senv se)) ∧

[~Recclosure:]
  (∀tfns sfns tenv senv n.
     env_rel (freevars (Letrec tfns (Lit ARB))) tenv senv ∧
     LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
     MAP FST tfns = MAP FST sfns ∧
     EVERY (λ(n,x). ∃v y. x = Lam v y) tfns  ⇒
     v_rel (Recclosure tfns tenv n)
           (Recclosure sfns senv n)) ∧

[env_rel:]
  (∀s tenv senv.
     (∀(n:string) tv.
       ALOOKUP tenv n = SOME tv ∧ n IN s ⇒
       ∃sv. ALOOKUP senv n = SOME sv ∧ v_rel tv sv) ⇒
     env_rel s tenv senv)

End

Theorem env_rel_def = “env_rel s tenv senv”
  |> SIMP_CONV (srw_ss()) [Once v_rel_cases];

Inductive step_res_rel:
  (v_rel v1 v2 ⇒
   step_res_rel (Val v1) (Val v2)) ∧
  (v_rel v1 v2 ⇒
   step_res_rel (Exn v1) (Exn v2)) ∧
  (step_res_rel Error Error) ∧
  (compile_rel e1 e2 ∧ env_rel (freevars e1) env1 env2 ⇒
   step_res_rel (Exp env1 e1) (Exp env2 e2)) ∧
  (step_res_rel (Action a b) (Action a b))
End

Inductive cont_rel:
  (cont_rel [] []) ∧
  (∀tenv senv op tvs svs tes ses sk tk s.
    cont_rel tk sk ∧ env_rel s tenv senv ∧ freevars (App ARB tes) SUBSET s ∧
    LIST_REL v_rel tvs svs ∧ LIST_REL compile_rel tes ses ⇒
    cont_rel (AppK tenv op tvs tes :: tk)
             (AppK senv op svs ses :: sk)) ∧
  (∀tenv senv n te se sk tk s.
    cont_rel tk sk ∧ env_rel s tenv senv ∧ freevars (Lam n te) SUBSET s ∧
    compile_rel te se ⇒
    cont_rel (LetK tenv n te :: tk)
             (LetK senv n se :: sk)) ∧
  (∀tenv senv te1 se1 te2 se2 sk tk s.
    cont_rel tk sk ∧ env_rel s tenv senv ∧ freevars (App ARB [te1;te2]) SUBSET s ∧
    compile_rel te1 se1 ∧ compile_rel te2 se2 ⇒
    cont_rel (IfK tenv te1 te2 :: tk)
             (IfK senv se1 se2 :: sk)) ∧
  (∀tenv senv n te se sk tk s.
    cont_rel tk sk ∧ env_rel s tenv senv ∧ freevars (Lam (SOME n) te) SUBSET s ∧
    compile_rel te se ⇒
    cont_rel (HandleK tenv n te :: tk)
             (HandleK senv n se :: sk)) ∧
  (∀tenv senv te se sk tk s v.
    cont_rel tk sk ∧ env_rel s tenv senv ∧ freevars te SUBSET s ∧
    compile_rel te se ∧ v ∉ freevars te ⇒
    cont_rel (HandleAppK tenv te :: tk)
             (HandleK senv v (App AppOp [se; Var v]) :: sk)) ∧
  (∀sk tk.
    cont_rel tk sk ⇒
    cont_rel (RaiseK :: tk)
             (RaiseK :: sk))
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

Theorem is_halt_step:
  ∀n x. is_halt x ⇒ step_n n x = x
Proof
  Induct \\ simp [ADD1,step_n_add,FORALL_PROD] \\ Cases \\ fs []
  >- (rw [] \\ rename [‘(Val _,x,y)’] \\ Cases_on ‘y’ \\ fs [step])
  >- (rw [] \\ rename [‘(Exn _,x,y)’] \\ Cases_on ‘y’ \\ fs [step])
  \\ rw [] \\ fs [step]
QED

Theorem step_n_SUC:
  step_n (SUC n) x = step_n n (step_n 1 x)
Proof
  fs [ADD1,step_n_add]
QED

Theorem env_rel_cons:
  env_rel s1 xs ys ∧ v_rel x y ∧ s2 DELETE n SUBSET s1 ⇒
  env_rel s2 ((n,x)::xs) ((n,y)::ys)
Proof
  rw [env_rel_def] \\ rw [] \\ fs [SUBSET_DEF]
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

Theorem application_thm:
  application op tenv tvs ts tk = (tr1,ts1,tk1) ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧ cont_rel tk sk ∧
  LIST_REL v_rel tvs svs ∧ env_rel s tenv senv ∧
  num_args_ok op (LENGTH svs) ⇒
  ∃sr1 ss1 sk1.
    application op senv svs ss sk = (sr1,ss1,sk1) ∧
    cont_rel tk1 sk1 ∧ OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
    step_res_rel tr1 sr1
Proof
  cheat
QED

Theorem step_1_forward:
  ∀tr ts tk tr1 ts1 tk1 ss sr sk.
    step_n 1 (tr,ts,tk) = (tr1,ts1,tk1) ∧
    cont_rel tk sk ∧ OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    step_res_rel tr sr ∧ tr1 ≠ Error ⇒
    ∃m sr1 ss1 sk1.
      step_n (m+1) (sr,ss,sk) = (sr1,ss1,sk1) ∧
      cont_rel tk1 sk1 ∧ OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
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
    \\ TRY (qexists_tac ‘0’ \\ fs [step,step_res_rel_cases]
            \\ irule env_rel_cons \\ fs []
            \\ first_assum $ irule_at $ Pos last \\ fs [] \\ NO_TAC)
    \\ fs [GSYM ADD1]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ qexists_tac ‘0’ \\ fs []
    \\ conj_tac >~ [‘cont_rel’]
    >-
     (simp [Once cont_rel_cases]
      \\ qexists_tac ‘freevars te’ \\ fs []
      \\ fs [env_rel_def] \\ rw [] \\ fs []
      \\ res_tac \\ fs [SUBSET_DEF])
    \\ fs [env_rel_def,step_res_rel_cases] \\ rw [] \\ fs []
    \\ res_tac \\ fs [SUBSET_DEF])
  \\ qexists_tac ‘0’ \\ simp []
  >~ [‘Exp’] >-
   (qpat_x_assum ‘compile_rel e1 e2’ mp_tac
    \\ simp [Once compile_rel_cases] \\ rw []
    >~ [‘Var v’] >-
     (gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases])
    >~ [‘Lam NONE’] >-
     (gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
      \\ once_rewrite_tac [Once v_rel_cases] \\ fs [env_rel_def])
    >~ [‘Lam’] >-
     (gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
      \\ once_rewrite_tac [Once v_rel_cases] \\ fs [env_rel_def])
    >~ [‘Raise’] >-
     (gvs [step,AllCaseEqs(),env_rel_def,step_res_rel_cases]
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs [])
    >~ [‘HandleApp’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs []
      \\ first_assum $ irule_at Any \\ fs [env_rel_def])
    >~ [‘Handle’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs []
      \\ first_assum $ irule_at Any \\ fs [env_rel_def])
    >~ [‘Let’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs []
      \\ first_assum $ irule_at Any \\ fs [env_rel_def,freevars_def]
      \\ Cases_on ‘x_opt’ \\ fs [freevars_def])
    >~ [‘If’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ once_rewrite_tac [Once cont_rel_cases] \\ fs []
      \\ first_assum $ irule_at Any \\ fs []
      \\ fs [SUBSET_DEF] \\ fs [env_rel_def,freevars_def])
    >~ [‘Letrec’] >-
     (gvs [step,AllCaseEqs(),step_res_rel_cases]
      \\ gvs [env_rel_def,ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE]
      \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO,ALOOKUP_rec]
      \\ strip_tac \\ Cases_on ‘MEM n (MAP FST sfns)’ \\ fs []
      \\ rw [Once v_rel_cases] \\ fs [env_rel_def])
    \\ fs [step]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ rw [] \\ fs []
    \\ Cases_on ‘REVERSE xs’
    >-
     (gvs [] \\ irule application_thm \\ fs []
      \\ last_x_assum $ irule_at Any \\ fs []
      \\ last_x_assum $ irule_at Any \\ fs [])
    \\ gvs []
    \\ Cases_on ‘REVERSE ys’ \\ gvs []
    \\ simp [step_res_rel_cases,Once cont_rel_cases]
    \\ last_assum $ irule_at Any \\ fs []
    \\ gvs [SWAP_REVERSE_SYM,MAP_REVERSE]
    \\ gvs [env_rel_def])
  \\ Cases_on ‘tk’ \\ fs []
  \\ Cases_on ‘sk’ \\ fs []
  \\ rename [‘cont_rel (tk1::tk) (sk1::sk)’]
  \\ qpat_x_assum ‘cont_rel _ _’ mp_tac
  \\ simp [Once cont_rel_cases] \\ rw []
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
    >- gvs [env_rel_def,SUBSET_DEF]
    \\ irule env_rel_cons \\ simp []
    \\ first_assum $ irule_at Any \\ fs [])
  \\ rename [‘AppK’]
  \\ reverse (Cases_on ‘tes’) \\ gvs [] \\ gvs [step]
  >-
   (simp [Once cont_rel_cases, step_res_rel_cases] \\ rw []
    >- (first_assum $ irule_at Any \\ fs [])
    \\ fs [env_rel_def,SUBSET_DEF])
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ IF_CASES_TAC \\ gs[]
  \\ drule application_thm \\ fs [PULL_EXISTS]
  \\ disch_then drule_all \\ strip_tac \\ fs []
QED

Theorem step_n_forward:
  ∀n tr ts tk tr1 ts1 tk1 ss sr sk.
    step_n n (tr,ts,tk) = (tr1,ts1,tk1) ∧
    cont_rel tk sk ∧ OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
    step_res_rel tr sr ∧ tr1 ≠ Error ⇒
    ∃m sr1 ss1 sk1.
      step_n (m+n) (sr,ss,sk) = (sr1,ss1,sk1) ∧
      cont_rel tk1 sk1 ∧ OPTREL (LIST_REL (LIST_REL v_rel)) ts1 ss1 ∧
      step_res_rel tr1 sr1
Proof
  Induct \\ fs [] \\ rw []
  >- (qexists_tac ‘0’ \\ fs [])
  \\ full_simp_tac std_ss [ADD_CLAUSES,step_n_SUC]
  \\ ‘∃a. step_n 1 (tr,ts,tk) = a’ by fs []
  \\ PairCases_on ‘a’
  \\ Cases_on ‘a0 = Error’ >- gvs []
  \\ drule_all step_1_forward
  \\ strip_tac \\ fs []
  \\ last_x_assum drule_all
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM ADD1,step_n_SUC] \\ fs []
  \\ qexists_tac ‘m+m'’
  \\ rpt $ first_assum $ irule_at Any
  \\ once_rewrite_tac [DECIDE “m + m' + n = (m' + n) + m:num”]
  \\ full_simp_tac std_ss [step_n_add]
QED

Theorem is_halt_simp[simp]:
  (is_halt (Exn v,s,k) ⇔ k = []) ∧
  (is_halt (Val v,s,k) ⇔ k = [])
Proof
  Cases_on ‘k’ \\ fs []
QED

Theorem step_until_halt_thm:
  step_res_rel tr sr ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
  cont_rel tk sk ∧
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
  \\ Cases_on ‘b0 = Error’ \\ gvs []
  \\ drule_all step_n_forward \\ rw []
  \\ ‘step_n (m + x) (sr,ss,sk) = (a0,a1,a2)’ by
    (rewrite_tac [step_n_add] \\ fs [is_halt_step])
  \\ gvs [] \\ gvs [step_res_rel_cases]
QED

Theorem semantics_thm:
  compile_rel e1 e2 ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
  env_rel (freevars e1) tenv senv ∧
  cont_rel tk sk ⇒
  semantics e1 tenv ts tk --->
  semantics e2 senv ss sk
Proof
  qsuff_tac ‘
    ∀t1 t2.
      (∃e1 e2 ts ss tenv senv tk sk.
        compile_rel e1 e2 ∧
        OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧
        env_rel (freevars e1) tenv senv ∧
        cont_rel tk sk ∧
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
  \\ impl_tac
  >- simp [Once step_res_rel_cases]
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
  \\ qpat_x_assum ‘cont_rel _ _’ $ irule_at Any \\ fs []
  \\ ‘env_rel {} [] []’ by fs [env_rel_def]
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
  compile_rel e1 e2 ⇒
  itree_of e1 ---> itree_of e2
Proof
  fs [stateLangTheory.itree_of_def] \\ rw []
  \\ irule semantics_thm
  \\ simp [Once cont_rel_cases]
  \\ fs [env_rel_def]
QED

val _ = export_theory ();
