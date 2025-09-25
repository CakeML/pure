(*
  Correctness for expansion of Case to If/Let/Proj combinations.
 *)
Theory state_caseProof
Ancestors
  string option sum pair list alist finite_map pred_set
  rich_list arithmetic pure_exp_lemmas pure_misc pure_config
  pure_semantics[qualified]
  stateLang
Libs
  BasicProvers dep_rewrite


Overload True[local] = “App (Cons "True") [] :stateLang$exp”
Overload False[local] = “App (Cons "False") [] :stateLang$exp”
Overload Fail = “App (AtomOp Add) [] :stateLang$exp”
Overload Proj = “λn i x. App (Proj n i) [x:stateLang$exp]”
Overload IsEq = “λn i x. App (IsEq n i) [x:stateLang$exp]”

Definition lets_for_def:
  lets_for l cn v [] b = b:stateLang$exp ∧
  lets_for l cn v ((n,w)::ws) b =
    Let NONE (If (IsEq cn l (Var v)) Unit Fail) $
      Let (SOME w) (Proj cn n (Var v)) (lets_for l cn v ws b)
End

Definition Disj_def:
  Disj v [] = False ∧
  Disj v ((cn,l)::xs) = If (IsEq cn l (Var v)) True (Disj v xs)
End

Definition rows_of_def:
  rows_of v [] d =
    (case d of
     | NONE => Fail
     | SOME (alts,e) => If (Disj v alts) e Fail) ∧
  rows_of v ((cn,vs,b)::rest) d =
    If (IsEq cn (LENGTH vs) (Var v))
       (lets_for (LENGTH vs) cn v (MAPi (λi v. (i,v)) vs) b)
       (rows_of v rest d)
End

Definition expand_Case_def:
  expand_Case v rs d =
    if MEM v (FLAT (MAP (FST o SND) rs)) ∨ rs = [] then
      Fail
    else
      rows_of v rs d
End

Inductive compile_rel:

[~Var:]
  compile_rel (stateLang$Var v) (stateLang$Var v)

[~Lam:]
  (compile_rel x y ⇒
  compile_rel (Lam v_opt x) (Lam v_opt y))

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
  (∀v tes ses td sd.
     OPTREL (λ(a,x) (b,y). a = b ∧ compile_rel x y) td sd ∧
     MAP FST tes = MAP FST ses ∧ ALL_DISTINCT (MAP FST tes) ∧
     MAP (FST o SND) tes = MAP (FST o SND) ses ∧
     LIST_REL compile_rel (MAP (SND o SND) tes) (MAP (SND o SND) ses) ⇒
  compile_rel (Case v tes td) (expand_Case v ses sd))

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
     EVERY (λ(n,x). ∃v y. x = Lam v y) tfns ∧
     MAP FST tfns = MAP FST sfns ⇒
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

Theorem env_rel_cons:
  env_rel xs ys ∧ v_rel x y ⇒
  env_rel ((n,x)::xs) ((n,y)::ys)
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
  application op tvs ts tk = (tr1,ts1,tk1) ∧
  OPTREL (LIST_REL (LIST_REL v_rel)) ts ss ∧ cont_rel tk sk ∧
  LIST_REL v_rel tvs svs ∧
  num_args_ok op (LENGTH svs) ⇒
  ∃sr1 ss1 sk1.
    application op svs ss sk = (sr1,ss1,sk1) ∧
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
    \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs []
    \\ simp[Once v_rel_cases])
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

Theorem step_n_lets_for:
  ∀svs1 svs0 n senv h1 h2.
    ALOOKUP senv v = SOME (Constructor h0 (svs0 ++ svs1)) ∧
    LENGTH svs0 = n ∧ ~MEM v h1 ∧ LENGTH h1 = LENGTH svs1 ⇒
    ∃ck.
      step_n ck
        (Exp senv (lets_for (LENGTH svs0 + LENGTH svs1) h0 v
             (MAPi (λi v. (i+n,v)) h1) h2),ss,sk) =
          (Exp (REVERSE (ZIP (h1,svs1)) ++ senv) h2,ss,sk)
Proof
  Induct \\ fs [lets_for_def]
  >- (rw [] \\ qexists_tac ‘0’ \\ fs [])
  \\ Cases_on ‘h1’ \\ fs [] \\ rw []
  \\ fs [lets_for_def]
  \\ ntac 13 (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
  \\ fs [EL_APPEND2]
  \\ last_x_assum $ drule_at $ Pos last \\ fs [combinTheory.o_DEF]
  \\ rename [‘Exp ((a1,a2)::_)’]
  \\ disch_then $ qspecl_then [‘svs0 ++ [a2]’,‘((a1,a2)::senv)’] mp_tac
  \\ impl_tac >- fs [ALOOKUP_def]
  \\ fs [ADD_CLAUSES,LENGTH_APPEND,GSYM ADD1]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
QED

Triviality step_n_lets_for_lemma =
  step_n_lets_for |> Q.SPECL [‘xs’,‘[]’,‘0’] |> SIMP_RULE std_ss [LENGTH,APPEND]

Theorem env_rel_zip:
  ∀n x y xs ys.
    env_rel xs ys ∧ LIST_REL v_rel x y ∧
    LENGTH n = LENGTH x ⇒
    env_rel (REVERSE(ZIP(n,x))++xs) (REVERSE(ZIP(n,y))++ys)
Proof
  Induct \\ fs []
  \\ Cases_on ‘x’ \\ fs [PULL_EXISTS] \\ rw []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ last_x_assum irule \\ fs []
  \\ irule env_rel_cons \\ fs []
QED

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
   (qpat_x_assum ‘compile_rel e1 e2’ mp_tac
    \\ simp [Once compile_rel_cases] \\ rw []
    >~ [‘Case’] >-
     (gvs [step,CaseEq "bool",step_res_rel_cases]
      \\ Cases_on ‘ALOOKUP env1 v’ \\ gvs []
      >-
       (full_simp_tac std_ss [GSYM ADD1,step_n_SUC]
        \\ fs [step,expand_Case_def]
        \\ IF_CASES_TAC \\ fs []
        >- (qexists_tac ‘0’ \\ fs [step,get_atoms_def,expand_Case_def])
        >- (qexists_tac ‘0’ \\ fs [step,get_atoms_def,expand_Case_def])
        \\ Cases_on ‘tes’ \\ Cases_on ‘ses’ \\ gvs []
        \\ PairCases_on ‘h’ \\ fs []
        \\ PairCases_on ‘h'’ \\ fs []
        \\ fs [rows_of_def,step]
        \\ ntac 2 (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
        \\ fs [env_rel_def] \\ res_tac \\ fs []
        \\ qexists_tac ‘0’ \\ fs [step])
      \\ gs [find_match_def,expand_Case_def]
      \\ IF_CASES_TAC
      >- (gvs [] \\ qexists_tac ‘0’ \\ fs [step,get_atoms_def,expand_Case_def])
      \\ gvs []
      \\ Cases_on ‘tes = []’ \\ gvs []
      \\ ‘∃y. ALOOKUP env2 v = SOME y ∧ v_rel x y’ by
         (fs [env_rel_def] \\ res_tac \\ fs [])
      \\ reverse (Cases_on ‘∃c1 ws1. x = Constructor c1 ws1’)
      >-
       (full_simp_tac std_ss [GSYM ADD1,step_n_SUC]
        \\ fs [step,expand_Case_def]
        \\ Cases_on ‘tes’ \\ Cases_on ‘ses’ \\ gvs []
        \\ PairCases_on ‘h’ \\ fs []
        \\ PairCases_on ‘h'’ \\ fs []
        \\ fs [rows_of_def,step]
        \\ ntac 3 (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
        \\ qpat_x_assum ‘v_rel x y’ mp_tac
        \\ simp [Once v_rel_cases] \\ rw [] \\ fs []
        \\ qexists_tac ‘0’ \\ gvs [step])
      \\ gvs []
      \\ qpat_x_assum ‘v_rel _ y’ mp_tac
      \\ simp [Once v_rel_cases] \\ rw [] \\ fs []
      \\ rename [‘LIST_REL v_rel ws1 ws2’]
      \\ rpt $ qpat_x_assum ‘_ ≠ []’ kall_tac
      \\ rpt $ pop_assum mp_tac
      \\ qid_spec_tac ‘ses’
      \\ qid_spec_tac ‘tes’
      \\ Induct \\ fs [PULL_EXISTS]
      \\ fs [find_match_list_def]
      >-
       (Cases_on ‘td’ \\ Cases_on ‘sd’ \\ fs []
        >- (rw [rows_of_def] \\ qexists_tac ‘0’ \\ fs [step,get_atoms_def])
        \\ rename [‘rows_of v [] (SOME y)’]
        \\ PairCases_on ‘x’
        \\ PairCases_on ‘y’ \\ gvs []
        \\ fs [rows_of_def]
        \\ fs [step_n_SUC,step,GSYM ADD1]
        \\ rpt strip_tac \\ gvs []
        \\ Induct_on ‘x0’ \\ gvs []
        >-
         (fs [Disj_def] \\ rw []
          \\ ntac 3 (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
          \\ qexists_tac ‘0’ \\ fs [get_atoms_def])
        \\ PairCases \\ fs []
        \\ Cases_on ‘h0 = c1’ \\ fs []
        >-
         (rw [Disj_def] \\ pop_assum kall_tac
          \\ imp_res_tac LIST_REL_LENGTH
          \\ ntac 7 (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
          \\ qexists_tac ‘0’ \\ fs [get_atoms_def])
        \\ strip_tac
        \\ first_x_assum dxrule
        \\ rewrite_tac [METIS_PROVE [] “b ∨ c ⇔ (~b ⇒ c)”]
        \\ strip_tac \\ gvs []
        \\ rw [] \\ fs []
        \\ fs [Disj_def] \\ rw []
        \\ ntac 4 (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
        \\ imp_res_tac LIST_REL_LENGTH \\ fs []
        \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step]
        \\ first_x_assum $ irule_at $ Pos hd
        \\ fs [])
      \\ PairCases
      \\ fs [find_match_list_def]
      \\ Cases \\ fs []
      \\ rename [‘rows_of v (f::t)’] \\ PairCases_on ‘f’ \\ fs []
      \\ reverse IF_CASES_TAC
      >-
       (rpt strip_tac \\ fs []
        \\ fs [step,GSYM ADD1,step_n_SUC,rows_of_def]
        \\ ntac 4 (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
        \\ Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
      \\ gvs [] \\ pop_assum kall_tac
      \\ reverse IF_CASES_TAC
      >-
       (fs [] \\ rpt strip_tac \\ gvs []
        \\ fs [step,GSYM ADD1,step_n_SUC,rows_of_def]
        \\ imp_res_tac LIST_REL_LENGTH \\ fs []
        \\ ntac 3 (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
        \\ qexists_tac ‘0’ \\ fs [get_atoms_def])
      \\ fs [] \\ strip_tac \\ gvs []
      \\ fs [] \\ rpt strip_tac \\ gvs []
      \\ fs [step,GSYM ADD1,step_n_SUC,rows_of_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ ntac 4 (Q.REFINE_EXISTS_TAC ‘SUC ck1’ \\ fs [step_n_SUC,step])
      \\ drule_all step_n_lets_for_lemma
      \\ disch_then $ qspecl_then [‘ss’,‘sk’,‘f2’] strip_assume_tac
      \\ pop_assum $ irule_at Any \\ fs []
      \\ irule env_rel_zip \\ fs [])
    \\ qexists_tac ‘0’
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
  \\ qexists_tac ‘0’ \\ fs []
  >~ [‘HandleK’] >-
   (gvs [step] \\ fs [step_res_rel_cases])
  >~ [‘HandleAppK’] >-
   (gvs [step] \\ fs [step_res_rel_cases])
  >~ [‘RaiseK’] >-
   (Cases_on ‘ts’ \\ Cases_on ‘ss’ \\ gvs [step,step_res_rel_cases])
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
