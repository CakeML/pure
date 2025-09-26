(*
  Correctness for compilation that pushes applications to Unit as far in as possible,
  e.g. ‘(Let x = ... in foo) Unit’ becomes ‘Let x = ... in (foo Unit)’.
 *)
Theory state_app_unit_2Proof
Ancestors
  string option sum pair list alist finite_map pred_set
  rich_list arithmetic pure_exp_lemmas pure_misc pure_config
  pure_semantics[qualified]
  stateLang
Libs
  BasicProvers dep_rewrite


Overload "app" = “λe1 e2. App AppOp [e1;(e2:exp)]”;
Overload "wrap" = “λe. app (Lam NONE e) (Unit:exp)”;
Overload "cont" = “λe. Let (SOME "a") (e:exp) (Var "a")”;

Inductive compile_rel:

[~App_Let:]
  (compile_rel x x1 ∧ compile_rel y y1 ⇒
   compile_rel (app (Let x_opt x y) Unit)
               (Let x_opt (cont (wrap x1)) (app y1 Unit)))

[~App_If:]
  (compile_rel x x1 ∧ compile_rel y y1 ∧ compile_rel z z1 ⇒
   compile_rel (app (If x y z) Unit)
               (If (cont (wrap x1)) (app y1 Unit) (app z1 Unit)))

[~App_Letrec:]
  (compile_rel y y1 ∧
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
    EVERY (λ(n,x). ∃v y. x = Lam v y) tfns ⇒
   compile_rel (app (Letrec tfns y) Unit)
               (Letrec sfns (app y1 Unit)))

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
  (LIST_REL (compile_rel) xs ys ⇒
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
  (∀v te se tes ses.
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
     LIST_REL (compile_rel) (MAP SND tfns) (MAP SND sfns) ∧
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

Definition store_rel_def:
  store_rel (Array vs1) (Array vs2) = LIST_REL v_rel vs1 vs2 ∧
  store_rel (ThunkMem m1 v1) (ThunkMem m2 v2) =
    (m1 = m2 ∧ v_rel v1 v2) ∧
  store_rel _ _ = F
End

Definition state_rel_def:
  state_rel st1 st2 = LIST_REL store_rel st1 st2
End

Inductive cont_rel:
  (cont_rel [] []) ∧
  (∀tk sk e1 e2 x_opt.
    compile_rel e1 e2 ∧ cont_rel tk sk ∧ env_rel env1 env2 ⇒
    cont_rel (LetK env1 x_opt e1::AppK env1 AppOp [Constructor "" []] []::tk)
             (LetK env2 (SOME "a") (Var "a")::LetK env2 x_opt (app e2 Unit)::sk)) ∧
  (∀tk sk e1 e2 e1' e2'.
    compile_rel e1 e2 ∧ compile_rel e1' e2' ∧ cont_rel tk sk ∧ env_rel env1 env2 ⇒
    cont_rel (IfK env1 e1 e1'::AppK env1 AppOp [Constructor "" []] []::tk)
             (LetK env2 (SOME "a") (Var "a")::
               IfK env2 (app e2 Unit) (app e2' Unit)::sk)) ∧
  (∀tk sk.
    cont_rel tk sk ∧ env_rel tenv senv ∧
    compile_rel te1 se1 ∧ compile_rel te2 se2 ⇒
    cont_rel (IfK tenv te1 te2 :: tk)
             (IfK senv se1 se2 :: sk)) ∧
  (∀tenv senv op tvs svs tes ses sk tk.
    cont_rel tk sk ∧ (tes ≠ [] ⇒ env_rel tenv senv) ∧
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
             (RaiseK :: sk)) ∧
  (∀sk tk s1 s2 n.
    cont_rel tk sk ∧
    state_rel s1 s2 ∧
    n < LENGTH s1 ⇒
    cont_rel (ForceMutK n::tk) (ForceMutK n::sk))
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
  (OPTREL state_rel ts ss ∧ cont_rel tk sk ⇒
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
    LIST_REL (compile_rel) (MAP SND tfns) (MAP SND sfns) ∧
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
  ∀op tvs ts tk tr1 ts1 tk1 ss sk svs.
    application op tvs ts tk = (tr1,ts1,tk1) ∧
    OPTREL state_rel ts ss ∧ cont_rel tk sk ∧
    LIST_REL v_rel tvs svs ∧
    num_args_ok op (LENGTH svs) ⇒
    ∃sr1 ss1 sk1.
      application op svs ss sk = (sr1,ss1,sk1) ∧
      OPTREL state_rel ts1 ss1 ∧
      step_res_rel tr1 tk1 sr1 sk1
Proof
  Cases \\ rw []
  \\ fs [num_args_ok_def,LENGTH_EQ_NUM_compute,PULL_EXISTS]
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
    \\ fs [state_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ simp [Once v_rel_cases]
    \\ fs [LIST_REL_SNOC,store_rel_def]
    \\ simp [LIST_REL_EL_EQN,EL_REPLICATE])
  >~ [‘Length’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [oEL_THM]
    \\ IF_CASES_TAC \\ gvs []
    \\ gvs [LIST_REL_EL_EQN,state_rel_def]
    \\ Cases_on ‘EL n x’ \\ Cases_on ‘EL n x'’ \\ gvs [store_rel_def]
    \\ res_tac \\ Cases_on ‘EL n x’ \\ gvs [store_rel_def]
    \\ simp [Once v_rel_cases]
    \\ gvs [LIST_REL_EL_EQN,state_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
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
    \\ gvs [state_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs [state_rel_def]
    \\ Cases_on ‘EL n x’ \\ Cases_on ‘EL n x'’ \\ gvs [LIST_REL_EL_EQN]
    \\ res_tac \\ Cases_on ‘EL n x’ \\ gvs [store_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ gvs [LIST_REL_EL_EQN]
    \\ Cases_on ‘0 ≤ i’ \\ gvs []
    >-
      (imp_res_tac integerTheory.NUM_POSINT_EXISTS
       \\ first_x_assum $ qspec_then ‘&n'’ assume_tac
       \\ gvs []
       \\ Cases_on ‘n' < LENGTH l'’ \\ gvs []
       \\ gvs [Once v_rel_cases,LIST_REL_EL_EQN,state_rel_def])
    \\ simp [Once v_rel_cases,LIST_REL_EL_EQN,state_rel_def]) 
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
    \\ gvs [state_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs [state_rel_def]
    \\ Cases_on ‘EL n x’ \\ Cases_on ‘EL n x'’ \\ gvs [LIST_REL_EL_EQN]
    \\ res_tac \\ Cases_on ‘EL n x’ \\ gvs [store_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ gvs [LIST_REL_EL_EQN]
    \\ Cases_on ‘0 ≤ i’ \\ gvs []
    >-
      (imp_res_tac integerTheory.NUM_POSINT_EXISTS
       \\ first_x_assum $ qspec_then ‘&n'’ assume_tac \\ gvs []
       \\ Cases_on ‘n' < LENGTH l'’ \\ gvs []
       \\ simp [Once v_rel_cases,LIST_REL_EL_EQN,state_rel_def]
       \\ rpt strip_tac
       \\ gvs [EL_LUPDATE]
       \\ Cases_on ‘n'' = n’ \\ gvs []
       \\ rw [LIST_REL_EL_EQN,store_rel_def]
       \\ gvs [EL_LUPDATE]
       \\ Cases_on ‘n'' = n'’ \\ gvs []
       \\ res_tac \\ Cases_on ‘EL n x’ \\ gvs [store_rel_def]
       \\ gvs [LIST_REL_EL_EQN])
    \\ simp [Once v_rel_cases,LIST_REL_EL_EQN,state_rel_def])
  >~ [‘AllocMutThunk’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘ss’ \\ gvs []
    \\ fs [state_rel_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ simp [Once v_rel_cases]
    \\ fs [LIST_REL_SNOC,store_rel_def]
    \\ simp [Once v_rel_cases,LIST_REL_EL_EQN,EL_REPLICATE]
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘UpdateMutThunk’] >-
   (gvs [application_def,step,step_res_rel_cases]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs []
    \\ gvs [AllCaseEqs(),oEL_THM,state_rel_def,LIST_REL_EL_EQN]
    \\ first_assum drule \\ asm_rewrite_tac [store_rel_def] \\ strip_tac
    \\ Cases_on ‘EL n x''’ \\ gvs [state_rel_def,store_rel_def,LIST_REL_EL_EQN]
    \\ simp [Once v_rel_cases] \\ strip_tac
    \\ gvs [EL_LUPDATE]
    \\ IF_CASES_TAC \\ rw [store_rel_def])
  >~ [‘ForceMutThunk’] >-
   (once_rewrite_tac [application_def]
    \\ rgs [Once application_def]
    \\ qpat_x_assum ‘v_rel x h’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac
    \\ gvs [error_def,step_res_rel_cases]
    \\ Cases_on ‘a’ \\ gvs []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs [] >>
       gvs[oEL_THM] >> imp_res_tac state_rel_def >> gvs[LIST_REL_EL_EQN] >>
       last_x_assum mp_tac >>
       reverse $ IF_CASES_TAC >> gvs[] >- (rw[] >> gvs[]) >>
       first_x_assum drule >> CASE_TAC >> simp[oneline store_rel_def] >>
       rw[] >> gvs[] >> FULL_CASE_TAC >> gvs[] >>
       CASE_TAC >> gvs[value_def] >>
       ntac 2 $ simp[Once cont_rel_cases] >>
       simp[Once v_rel_cases] >> goal_assum drule >> simp[])
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

Definition step_1_ind_hyp_def:
  step_1_ind_hyp k =
  (∀m tr' ts' tk' tr1' ts1' tk1' ss' sr' sk'.
     m < k ∧ step_n m (tr',ts',tk') = (tr1',ts1',tk1') ∧
     OPTREL state_rel ts' ss' ∧
     step_res_rel tr' tk' sr' sk' ⇒
     ∃m' sr1 ss1 sk1.
       step_n m' (sr',ss',sk') = (sr1,ss1,sk1) ∧ m ≤ m' ∧
       (is_halt (tr1',ts1',tk1') ⇔ is_halt (sr1,ss1,sk1)) ∧
       (is_halt (tr1',ts1',tk1') ⇒
        OPTREL state_rel ts1' ss1 ∧
        step_res_rel tr1' tk1' sr1 sk1))
End

Theorem step_1_ind_hyp_add:
  step_1_ind_hyp (n + k) ⇒ step_1_ind_hyp n
Proof
  fs [step_1_ind_hyp_def] \\ rw []
  \\ first_x_assum irule \\ fs []
  \\ rpt $ first_x_assum $ irule_at Any
QED

Theorem step_1_ind_hyp_SUC:
  step_1_ind_hyp (SUC n) ⇒ step_1_ind_hyp n
Proof
  fs [step_1_ind_hyp_def] \\ rw []
  \\ first_x_assum irule \\ fs []
  \\ rpt $ first_x_assum $ irule_at Any
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
    OPTREL (λ(a,x) (b,y). a = b ∧ compile_rel x y ∧ RR x y) te se ∧
    LIST_REL (λa b. compile_rel (SND (SND a)) (SND (SND b))) tes ses ∧
    LIST_REL RR (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
    ∃env2' e2.
      find_match_list s svs env2 ses se = SOME (env2',e2) ∧
      env_rel env1' env2' ∧ compile_rel e1 e2 ∧ RR e1 e2
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
  ∀e1 e2.
    compile_rel e1 e2 ⇒
    ∀k ts tk tr1 ts1 tk1 ss sk env1 env2.
      step_n k (Exp env1 e1,ts,tk) = (tr1,ts1,tk1) ∧
      step_1_ind_hyp k ∧
      cont_rel tk sk ∧ compile_rel e1 e2 ∧
      OPTREL state_rel ts ss ∧
      env_rel env1 env2 ⇒
      ∃m sr1 ss1 sk1.
        step_n m (Exp env2 e2,ss,sk) = (sr1,ss1,sk1) ∧ k ≤ m ∧
        ((is_halt (sr1,ss1,sk1) ⇔ is_halt (tr1,ts1,tk1)) ∧
         (is_halt (sr1,ss1,sk1) ⇒
          OPTREL state_rel ts1 ss1 ∧
          step_res_rel tr1 tk1 sr1 sk1))
Proof
  ho_match_mp_tac compile_rel_strongind \\ rpt strip_tac
  >-
   (Cases_on ‘k’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Cases_on ‘n’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Cases_on ‘n'’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Cases_on ‘n’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ last_x_assum drule
    \\ disch_then $ drule_at Any
    \\ disch_then $ drule_at Any
    \\ disch_then $ qspec_then
         ‘LetK env2 (SOME "a") (Var "a")::LetK env2 x_opt (app e2' Unit)::sk’ mp_tac
    \\ impl_tac
    >-
     (fs [ADD1] \\ imp_res_tac step_1_ind_hyp_add \\ fs []
      \\ simp [Once cont_rel_cases])
    \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  >-
   (Cases_on ‘k’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Cases_on ‘n’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Cases_on ‘n'’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Cases_on ‘n’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ last_x_assum drule
    \\ disch_then $ drule_at Any
    \\ disch_then $ drule_at Any
    \\ disch_then $ qspec_then
         ‘LetK env2 (SOME "a") (Var "a")::
               IfK env2 (app e2' Unit) (app e2'' Unit)::sk’ mp_tac
    \\ impl_tac
    >-
     (fs [ADD1] \\ imp_res_tac step_1_ind_hyp_add \\ fs []
      \\ simp [Once cont_rel_cases])
    \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  >-
   (Cases_on ‘k’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Cases_on ‘n’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Cases_on ‘n'’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ Cases_on ‘n’ \\ gvs [step_n_SUC,step]
    >- (qexists_tac ‘0’ \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ last_x_assum drule
    \\ disch_then $ drule_at Any
    \\ disch_then irule
    \\ fs [ADD1]
    \\ imp_res_tac step_1_ind_hyp_add \\ fs []
    \\ conj_tac
    >- (simp [Once cont_rel_cases] \\ simp [Once v_rel_cases])
    \\ gvs [env_rel_def,ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE]
    \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO,ALOOKUP_rec]
    \\ rpt strip_tac \\ Cases_on ‘MEM n'' (MAP FST sfns)’ \\ fs []
    \\ rw [Once v_rel_cases] \\ fs [env_rel_def,ALOOKUP_NONE]
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ fs [])
  \\ (Cases_on ‘k’ \\ gvs [step_n_SUC,step] >- (qexists_tac ‘0’ \\ fs []))
  \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
  >~ [‘Var v’] >-
   (Cases_on ‘ALOOKUP env1 v’ \\ fs [] \\ fs [env_rel_def]
    \\ gvs [is_halt_step]
    >- (qexists_tac ‘n’ \\ fs [step_res_rel_cases])
    \\ res_tac \\ fs [step_1_ind_hyp_def]
    \\ first_x_assum $ drule_at $ Pos $ el 2
    \\ rpt $ disch_then $ drule_at $ Pos $ el 2
    \\ simp [Once step_res_rel_cases,PULL_EXISTS]
    \\ rpt $ disch_then $ drule_at $ Any
    \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  >~ [‘Lam’] >-
   (fs [step_1_ind_hyp_def]
    \\ first_x_assum $ drule_at $ Pos $ el 2
    \\ rpt $ disch_then $ drule_at $ Pos $ el 2 \\ simp []
    \\ simp [Once step_res_rel_cases,PULL_EXISTS]
    \\ simp [Once v_rel_cases,PULL_EXISTS]
    \\ disch_then drule_all \\ strip_tac
    \\ rpt $ first_x_assum $ irule_at $ Pos hd
    \\ simp [])
  >~ [‘RaiseK’] >-
   (first_x_assum irule \\ fs []
    \\ rpt $ first_x_assum $ irule_at $ Any
    \\ imp_res_tac step_1_ind_hyp_SUC
    \\ simp [Once cont_rel_cases])
  >~ [‘HandleK’] >-
   (first_x_assum irule \\ fs [step_1_ind_hyp_SUC]
    \\ rpt $ first_assum $ irule_at $ Any
    \\ simp [Once cont_rel_cases])
  >~ [‘HandleApp’] >-
   (first_x_assum irule \\ fs [step_1_ind_hyp_SUC]
    \\ rpt $ first_assum $ irule_at $ Any
    \\ simp [Once cont_rel_cases])
  >~ [‘Recclosure’] >-
   (first_x_assum irule \\ fs [step_1_ind_hyp_SUC]
    \\ rpt $ first_assum $ irule_at $ Any
    \\ simp [Once cont_rel_cases]
    \\ gvs [env_rel_def,ALOOKUP_APPEND,AllCaseEqs(),ALOOKUP_NONE]
    \\ gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO,ALOOKUP_rec]
    \\ rpt strip_tac \\ Cases_on ‘MEM n' (MAP FST sfns)’ \\ fs []
    \\ rw [Once v_rel_cases] \\ fs [env_rel_def,ALOOKUP_NONE]
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ fs [])
  >~ [‘Let’] >-
   (first_x_assum irule \\ fs [step_1_ind_hyp_SUC]
    \\ rpt $ first_assum $ irule_at $ Any
    \\ simp [Once cont_rel_cases])
  >~ [‘If’] >-
   (first_x_assum irule \\ fs [step_1_ind_hyp_SUC]
    \\ rpt $ first_assum $ irule_at $ Any
    \\ simp [Once cont_rel_cases])
  >~ [‘Case’] >-
   (Q.REFINE_EXISTS_TAC ‘ck+n’ \\ gvs [step]
    \\ Cases_on ‘ALOOKUP env1 v’ \\ fs []
    >-
     (fs [env_rel_def,AllCaseEqs()]
      \\ res_tac \\ gvs [step_n_Error]
      \\ simp [Once step_res_rel_cases])
    \\ rename [‘ALOOKUP env1 v = SOME v1’]
    \\ ‘∃v2. ALOOKUP env2 v = SOME v2 ∧ v_rel v1 v2’ by
      (fs [env_rel_def] \\ res_tac \\ fs [])
    \\ gvs []
    \\ gvs [find_match_def]
    \\ ‘ses = [] ⇔ tes = []’ by (Cases_on ‘ses’ \\ Cases_on ‘tes’ \\ gvs [])
    \\ gvs [] \\ IF_CASES_TAC
    >- (gvs [step_n_Error] \\ simp [Once step_res_rel_cases])
    \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs [step_n_Error]
    \\ TRY (simp [Once step_res_rel_cases] \\ NO_TAC)
    \\ Cases_on ‘find_match_list s tvs env1 tes te’ \\ fs []
    >-
     (qsuff_tac ‘find_match_list s svs env2 ses se = NONE’
      >- (rw [] \\ gvs [step_n_Error] \\ simp [Once step_res_rel_cases])
      \\ drule_then irule find_match_list_NONE
      \\ gvs []
      \\ Cases_on ‘te’ \\ Cases_on ‘se’ \\ gvs []
      \\ fs [UNCURRY])
    \\ PairCases_on ‘x’ \\ fs []
    \\ drule_then drule find_match_list_SOME \\ fs []
    \\ disch_then $ drule_then drule
    \\ disch_then $ drule_at $ Pos last
    \\ disch_then $ qspec_then ‘se’ mp_tac
    \\ reverse impl_tac
    >- (rw [] \\ gvs []
        \\ imp_res_tac step_1_ind_hyp_SUC
        \\ first_x_assum drule_all \\ strip_tac \\ fs []
        \\ qexists_tac ‘m - n’ \\ fs [])
    \\ conj_tac
    >- (Cases_on ‘te’ \\ Cases_on ‘se’ \\ gvs [] \\ gvs [UNCURRY]
        \\ Cases_on ‘x’ \\ Cases_on ‘x'’ \\ gvs []
        \\ rw [] \\ first_x_assum irule \\ fs []
        \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ fs [LIST_REL_MAP_MAP]
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ fs [])
  >~ [‘App’] >-
   (imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [is_halt_step]
    >- (qexists_tac ‘n’ \\ fs [step_res_rel_cases])
    \\ Cases_on ‘REVERSE xs’ \\ gvs []
    >-
     (‘∃a. application op [] ts tk = a’ by fs [] \\ PairCases_on ‘a’
      \\ drule application_thm \\ fs []
      \\ disch_then drule_all \\ strip_tac \\ gvs[]
      \\ fs [step_1_ind_hyp_def]
      \\ first_x_assum $ drule_at $ Pos $ el 2 \\ fs []
      \\ rpt $ disch_then $ drule_at $ Pos $ last
      \\ strip_tac \\ fs []
      \\ rpt $ first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ gvs [SWAP_REVERSE_SYM]
    \\ Cases_on ‘ys’ using SNOC_CASES \\ fs [PULL_EXISTS]
    \\ gvs [GSYM SWAP_REVERSE_SYM]
    \\ full_simp_tac std_ss [GSYM SNOC_APPEND,LIST_REL_SNOC]
    \\ gvs []
    \\ full_simp_tac std_ss [REVERSE_SNOC] \\ fs []
    \\ drule EVERY2_REVERSE \\ simp_tac std_ss [REVERSE_REVERSE] \\ strip_tac
    \\ first_x_assum $ qspec_then ‘n’ mp_tac \\ fs []
    \\ rpt $ disch_then drule
    \\ simp [Once cont_rel_cases,PULL_EXISTS]
    \\ rpt $ disch_then drule \\ fs [step_1_ind_hyp_SUC]
    \\ rpt $ disch_then $ drule_at Any
    \\ disch_then irule \\ fs []
    \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
    \\ fs [])
QED

Definition dest_thunk_ptr_res_rel_def[simp]:
  dest_thunk_ptr_res_rel BadRef BadRef = T ∧
  dest_thunk_ptr_res_rel NotThunk NotThunk = T ∧
  dest_thunk_ptr_res_rel (IsThunk m1 v1) (IsThunk m2 v2) =
    (m1 = m2 ∧ v_rel v1 v2) ∧
  dest_thunk_ptr_res_rel _ _ = F
End

Theorem dest_thunk_ptr_rel:
  state_rel s1 s2 ∧
  v_rel v1 v2 ∧
  dest_thunk_ptr v1 s1 = res1 ⇒
    ∃res2.
      dest_thunk_ptr v2 s2 = res2 ∧
      dest_thunk_ptr_res_rel res1 res2
Proof
  rw [oneline dest_thunk_ptr_def, AllCaseEqs()]
  \\ gvs [Once v_rel_cases]
  \\ rpt (TOP_CASE_TAC \\ gvs [])
  \\ gvs [state_rel_def, LIST_REL_EL_EQN, oEL_THM]
  \\ first_x_assum drule \\ simp [store_rel_def]
QED

Theorem step_1_forward:
  ∀k tr ts tk tr1 ts1 tk1 ss sr sk.
    step_n k (tr,ts,tk) = (tr1,ts1,tk1) ∧
    OPTREL state_rel ts ss ∧
    step_res_rel tr tk sr sk ⇒
    ∃m sr1 ss1 sk1.
      step_n m (sr,ss,sk) = (sr1,ss1,sk1) ∧ k ≤ m ∧
      (is_halt (tr1,ts1,tk1) = is_halt (sr1,ss1,sk1) ∧
       (is_halt (tr1,ts1,tk1) ⇒
        OPTREL state_rel ts1 ss1 ∧
        step_res_rel tr1 tk1 sr1 sk1))
Proof
  gen_tac
  \\ completeInduct_on ‘k’ \\ rpt strip_tac
  \\ fs [PULL_FORALL, AND_IMP_INTRO, GSYM CONJ_ASSOC]
  \\ rpt strip_tac
  \\ Cases_on ‘is_halt (tr,ts,tk)’
  >-
   (‘is_halt (sr,ss,sk)’ by
     (qpat_x_assum ‘step_res_rel _ _ _ _’ mp_tac
      \\ simp [step_res_rel_cases,Once cont_rel_cases]
      \\ rw [] \\ fs [] \\ gvs [Once cont_rel_cases])
    \\ full_simp_tac std_ss [is_halt_step] \\ gvs []
    \\ qexists_tac ‘k’ \\ fs [])
  \\ qpat_x_assum ‘step_res_rel tr tk sr sk’ mp_tac
  \\ simp [Once step_res_rel_cases]
  \\ strip_tac \\ gvs []
  >~ [‘Exp’] >-
   (drule step_1_Exp_forward
    \\ rpt $ disch_then $ drule_at Any
    \\ fs [GSYM step_1_ind_hyp_def]
    \\ strip_tac \\ fs []
    \\ first_assum $ irule_at $ Pos hd \\ fs [])
  >~ [‘Exn’] >-
   (Cases_on ‘tk’ \\ gvs []
    \\ Cases_on ‘sk’ \\ gvs []
    >- fs [Once cont_rel_cases]
    \\ rename [‘cont_rel (tk1::tk) (sk1::sk)’]
    \\ qpat_x_assum ‘cont_rel _ _’ mp_tac
    \\ simp [Once cont_rel_cases]
    \\ rw [] \\ fs [step] \\ gvs []
    \\ (Cases_on ‘k’ >- (qexists_tac ‘0’ \\ gvs []))
    \\ TRY (Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
      \\ Cases_on ‘n’ \\ gvs [ADD_CLAUSES,step_n_SUC,step]
      >- (qexists_tac ‘0’ \\ fs [])
      \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
      \\ last_x_assum $ qspec_then ‘n'’ mp_tac \\ simp []
      \\ disch_then drule \\ fs []
      \\ disch_then drule \\ fs []
      \\ simp [Once step_res_rel_cases] \\ NO_TAC)
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ first_x_assum irule \\ fs []
    \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ rpt $ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ fs [step,step_res_rel_cases]
    \\ simp [Once cont_rel_cases]
    \\ irule env_rel_cons \\ fs [])
  \\ Cases_on ‘tk’ \\ fs []
  \\ Cases_on ‘sk’ \\ fs []
  >- fs [Once cont_rel_cases]
  \\ (Cases_on ‘k’ >- (qexists_tac ‘0’ \\ gvs []))
  \\ rename [‘cont_rel (tk1::tk) (sk1::sk)’]
  \\ qpat_x_assum ‘cont_rel _ _’ mp_tac
  \\ simp [Once cont_rel_cases] \\ rw []
  >-
   (Cases_on ‘x_opt’
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ last_x_assum $ qspec_then ‘n’ mp_tac \\ fs []
    \\ disch_then drule
    \\ disch_then drule
    \\ simp [Once step_res_rel_cases,PULL_EXISTS]
    \\ disch_then drule
    \\ ‘env_rel ((x,v1)::env1) ((x,v2)::env2)’ by (irule env_rel_cons \\ fs [])
    \\ disch_then drule
    \\ qmatch_goalsub_abbrev_tac ‘(Exp _ _,ss,sk1::_)’
    \\ disch_then $ qspec_then ‘sk1::sk'’ mp_tac
    \\ (impl_tac >-
          (fs [Abbr‘sk1’] \\ simp [Once cont_rel_cases]
           \\ simp [Once v_rel_cases]))
    \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  >-
   (Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ last_x_assum $ qspec_then ‘n’ mp_tac \\ fs []
    \\ rw []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ fs []
    \\ strip_tac \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ gvs [is_halt_step]
    \\ TRY (simp [Once step_res_rel_cases,ADD1] \\ qexists_tac ‘n’ \\ fs [] \\ NO_TAC)
    \\ TRY
     (every_case_tac \\ gvs [is_halt_step]
      \\ simp [Once step_res_rel_cases,ADD1] \\ qexists_tac ‘n’ \\ fs [] \\ NO_TAC)
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ first_x_assum drule
    \\ disch_then drule
    \\ simp [Once step_res_rel_cases,PULL_EXISTS]
    \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac ‘(Exp _ _,ss,sk1::_)’
    \\ first_x_assum $ qspec_then ‘sk1::sk'’ mp_tac
    \\ (impl_tac >-
          (fs [Abbr‘sk1’] \\ simp [Once cont_rel_cases]
           \\ simp [Once v_rel_cases]))
    \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  >~ [‘IfK’] >-
   (gvs [step,step_n_SUC]
    \\ Cases_on ‘v1 = Constructor "True" [] ∨ v1 = Constructor "False" []’ \\ gvs []
    \\ gvs [step]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ TRY (first_x_assum $ irule \\ fs []
            \\ rpt $ first_assum $ irule_at Any \\ fs []
            \\ simp [Once step_res_rel_cases] \\ NO_TAC)
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ gvs [is_halt_step]
    \\ qexists_tac ‘n’ \\ fs [step_res_rel_cases])
  >~ [‘LetK _ nn’] >-
   (Cases_on ‘nn’ \\ gvs [step_n_SUC,step]
    \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ simp [ADD_CLAUSES,step_n_SUC,step]
    \\ first_assum $ irule_at Any \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ simp [Once step_res_rel_cases]
    \\ irule env_rel_cons \\ fs [])
  >~ [‘HandleK’] >-
   (Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ first_assum $ irule_at Any \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ simp [Once step_res_rel_cases])
  >~ [‘HandleAppK’] >-
   (Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ first_assum $ irule_at Any \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ simp [Once step_res_rel_cases])
  >~ [‘RaiseK’] >-
   (Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
    \\ ‘ts = NONE ⇔ ss = NONE’ by (Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ fs [])
    \\ fs [] \\ IF_CASES_TAC
    \\ gvs [is_halt_step]
    >- (qexists_tac ‘n’ \\ fs [step_res_rel_cases])
    \\ first_assum $ irule_at Any \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ simp [Once step_res_rel_cases])
  >~ [‘ForceMutK’] >-
   (qrefine ‘SUC ck’ \\ gvs [ADD_CLAUSES, step_n_SUC, step]
    \\ qpat_x_assum ‘_ = (tr1,ts1,tk1')’ mp_tac
    \\ TOP_CASE_TAC \\ gvs [OPTREL_def]
    >- (
      strip_tac
      \\ last_x_assum irule \\ gvs []
      \\ metis_tac [step_res_rel_cases])
    \\ TOP_CASE_TAC \\ gvs []
    \\ drule_all dest_thunk_ptr_rel \\ gvs []
    \\ TOP_CASE_TAC \\ gvs []
    >~ [‘BadRef’]
    >- (
      strip_tac
      \\ last_x_assum irule \\ gvs [PULL_EXISTS]
      \\ metis_tac [step_res_rel_cases])
    >~ [‘IsThunk’]
    >- (
      rpt strip_tac
      \\ last_x_assum irule \\ gvs [PULL_EXISTS]
      \\ metis_tac [step_res_rel_cases])
    \\ (
      rpt strip_tac \\ gvs []
      \\ ntac 2 (TOP_CASE_TAC \\ gvs [])
      \\ last_x_assum irule \\ gvs [PULL_EXISTS]
      \\ goal_assum drule \\ gvs [step_res_rel_cases]
      \\ gvs [state_rel_def, LIST_REL_EL_EQN, EL_LUPDATE] \\ rw [store_rel_def]
      \\ qpat_x_assum ‘store_same_type _ _’ mp_tac
      \\ qpat_x_assum ‘¬store_same_type _ _’ mp_tac
      \\ simp [store_same_type_def]
      \\ rpt (TOP_CASE_TAC \\ gvs [])
      \\ first_x_assum drule \\ gvs [store_rel_def]))
  \\ rename [‘AppK’]
  \\ Q.REFINE_EXISTS_TAC ‘SUC ck’ \\ fs [ADD_CLAUSES,step_n_SUC,step]
  \\ reverse (Cases_on ‘tes’) \\ gvs [] \\ gvs [step]
  >-
   (first_assum $ irule_at Any \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ simp [Once step_res_rel_cases]
    \\ simp [Once cont_rel_cases])
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ IF_CASES_TAC \\ gs[]
  \\ TRY (first_assum $ irule_at Any \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ simp [Once step_res_rel_cases]
    \\ simp [Once cont_rel_cases] \\ NO_TAC)
  \\ ‘∃x. application op (v1::tvs) ts tk = x’ by fs []
  \\ PairCases_on ‘x’
  \\ drule application_thm \\ fs [PULL_EXISTS]
  \\ rpt $ disch_then drule \\ simp [] \\ strip_tac \\ gvs[]
  \\ first_assum $ irule_at Any \\ fs []
  \\ first_x_assum $ irule_at $ Pos hd \\ fs []
QED

Theorem step_until_halt_thm:
  step_res_rel tr tk sr sk ∧
  OPTREL state_rel ts ss ⇒
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
    \\ ‘step_n (x+x') (sr,ss,sk) = (b0,b1,b2)’ by
          metis_tac [is_halt_step,ADD_COMM,step_n_add,PAIR]
    \\ ‘step_n (x+x') (tr,ts,tk) = (a0,a1,a2)’ by
          metis_tac [is_halt_step,ADD_COMM,step_n_add,PAIR]
    \\ drule step_1_forward
    \\ disch_then drule_all \\ rw [] \\ gvs []
    \\ gvs [LESS_EQ_EXISTS]
    \\ ‘step_n x' (sr,ss,sk) = step_n (p+(x+x')) (sr,ss,sk)’ by
          metis_tac [is_halt_step,ADD_COMM,step_n_add,PAIR]
    \\ gvs []
    \\ qpat_x_assum ‘step_res_rel _ _ _ _’ mp_tac
    \\ simp [Once step_res_rel_cases] \\ strip_tac \\ gvs []
    \\ simp [Once snext_res_rel_cases] \\ gvs [])
  >-
   (‘∃a. step_n x (tr,ts,tk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ gvs []
    \\ drule_all step_1_forward \\ strip_tac
    \\ first_x_assum $ qspec_then ‘m’ mp_tac \\ gvs [])
  >-
   (‘∃a. step_n x (tr,ts,tk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ gvs []
    \\ first_x_assum $ qspec_then ‘x’ mp_tac
    \\ drule_all step_1_forward
    \\ strip_tac \\ rfs []
    \\ simp [Once step_res_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [LESS_EQ_EXISTS,step_n_add]
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
  OPTREL state_rel ts ss ∧
  env_rel tenv senv ∧
  cont_rel tk sk ⇒
  semantics e1 tenv ts tk =
  semantics e2 senv ss sk
Proof
  qsuff_tac ‘
    ∀t1 t2.
      (∃e1 e2 ts ss tenv senv tk sk.
        compile_rel e1 e2 ∧
        OPTREL state_rel ts ss ∧
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
  \\ fs [env_rel_def,state_rel_def]
QED

(*

(* -- cexp version -- *)

Overload "app" = “λe1 e2. App AppOp [e1;(e2:cexp)]”;
Overload "wrap" = “λe. app (Lam NONE (e:cexp) Unit”;
Overload "cont" = “λe. Let (SOME "a") (e:cexp) (Var "a")”;

*)
