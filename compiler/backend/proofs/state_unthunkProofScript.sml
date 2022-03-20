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

val _ = new_theory "state_unthunkProof";

val _ = set_grammar_ancestry ["stateLang"];

Overload "app" = “λe1 e2. App AppOp [e1;e2]”;

Overload True  = “App (Cons "True")  []”;
Overload False = “App (Cons "False") []”;

Overload True_v  = “stateLang$Constructor "True"  []”;
Overload False_v = “stateLang$Constructor "False" []”;

(****************************************)

Overload "box" = “λx. App Ref [True; x]”

Overload "delay" = “λx. App Ref [False; Lam NONE x]”

Overload "force_lets" = “
  Let (SOME "v1") (App UnsafeSub [IntLit 0; Var "v"]) $
  Let (SOME "v2") (App UnsafeSub [IntLit 1; Var "v"]) $
    If (Var "v1") (Var "v2") $
      Let (SOME "wh") (app (Var "v2") Unit) $
      Let NONE (App UnsafeUpdate [IntLit 0; Var "v"; True]) $
      Let NONE (App UnsafeUpdate [IntLit 1; Var "v"; Var "wh"]) $
        Var "wh"”

Overload "force" = “λx. Let (SOME "v") x force_lets”

Definition dest_Delay_def:
  dest_Delay (Delay x) = SOME x ∧
  dest_Delay _ = NONE
End

Definition dest_Lam_def:
  dest_Lam (Lam v x) = SOME (v,x) ∧
  dest_Lam _ = NONE
End

Overload is_Delay = “λx. IS_SOME (dest_Delay x)”
Overload is_Lam = “λx. IS_SOME (dest_Lam x)”

Definition Lets_def:
  Lets [] x = x ∧
  Lets ((v,y)::ys) x = Let v y (Lets ys x)
End

Definition Letrec_imm_def:
  (Letrec_imm vs (Var v) ⇔ MEM v vs) ∧
  (Letrec_imm vs (Lam _ _) ⇔ T) ∧
  (Letrec_imm vs (Lit _) ⇔ T) ∧
  (Letrec_imm vs _ ⇔ F)
End

Definition Letrec_split_def:
  Letrec_split vs [] = ([],[],[]) ∧
  Letrec_split vs ((v:string,x)::fns) =
    let (xs,ys,zs) = Letrec_split vs fns in
      case dest_Delay x of
      | NONE => (xs,(v,x)::ys,zs)
      | SOME y =>
        if Letrec_imm vs y then
          ((SOME v,App Ref [True; True])::xs,ys,
           (NONE,App UnsafeUpdate [IntLit 1; Var v; y])::zs)
        else
          ((SOME v,App Ref [False; False])::xs,ys,
           (NONE,App UnsafeUpdate [IntLit 1; Var v; Lam NONE y])::zs)
End

Definition comp_Letrec_def:
  comp_Letrec fns y =
    let (xs,ys,zs) = Letrec_split (MAP FST fns) fns in
      Lets xs $ Letrec ys $ Lets zs y
End

Inductive compile_rel:

[~Var:]
  compile_rel (stateLang$Var v) (stateLang$Var v) ∧

[~Lam:]
  (compile_rel x y ⇒
  compile_rel (Lam z x) (Lam z y)) ∧

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
  (LIST_REL compile_rel xs ys ∧ (∀l. op ≠ AtomOp (Lit (Loc l))) ⇒
  compile_rel (App op xs) (App op ys)) ∧

[~Letrec:]
  (∀tfns sfns te se.
    EVERY (λ(_,x). is_Lam x ∨ is_Delay x) tfns ∧
    MAP FST tfns = MAP FST sfns ∧ ALL_DISTINCT (MAP FST tfns) ∧
    LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
    compile_rel te se ⇒
    compile_rel (Letrec tfns te) (comp_Letrec sfns se)) ∧

[~Let:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (Let x_opt te1 te2) (Let x_opt se1 se2)) ∧

[~If:]
  (compile_rel te se ∧
   compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (If te te1 te2) (If se se1 se2)) ∧

[~Box:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Box te) (box se)) ∧

[~Delay:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Delay te) (delay se)) ∧

[~Force:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Force te) (force se))

End

Definition find_loc_def:
  find_loc n [] = NONE ∧
  find_loc n (x::xs) =
    case x of
    | NONE => if n = 0:num then SOME (0:num) else
                OPTION_MAP (λn. n + 1:num) (find_loc (n-1) xs)
    | SOME _ => OPTION_MAP (λn. n + 1:num) (find_loc n xs)
End

Inductive v_rel:

[~Loc:]
  (∀p n1 n2.
     find_loc n1 p = SOME n2 ⇒
     v_rel p (Atom (Loc n1)) (Atom (Loc n2))) ∧

[~Atom:]
  (∀p a.
     (∀l. a ≠ Loc l) ⇒
     v_rel p (Atom a) (Atom a)) ∧

[~Constructor:]
  (∀p s tvs svs.
     LIST_REL (v_rel p) tvs svs ⇒
     v_rel p (Constructor s tvs) (Constructor s svs)) ∧

[~Closure:]
  (∀p tv sv tenv senv te se n.
     env_rel p tenv senv ∧ compile_rel te se ∧
     dest_anyClosure tv = SOME (n,tenv,te) ∧
     dest_anyClosure sv = SOME (n,senv,se) ⇒
     v_rel p tv sv) ∧

[~Thunk:]
  (∀p v n r.
     oEL n p = SOME (SOME r) ∧
     dest_anyThunk v = SOME r ⇒
     v_rel p v (Atom (Loc n))) ∧

[env_rel:]
  (∀p tenv senv.
     (∀(n:string) tv.
       ALOOKUP tenv n = SOME tv ⇒
       ∃sv. ALOOKUP senv n = SOME sv ∧ v_rel p tv sv) ⇒
     env_rel p tenv senv)

End

Theorem dest_anyThunk_simp[simp]:
  dest_anyThunk (Atom a) = NONE ∧
  dest_anyThunk (Constructor s vs) = NONE ∧
  dest_anyThunk (Closure x env e) = NONE
Proof
  fs [AllCaseEqs(),dest_Thunk_def,dest_anyThunk_def]
QED

Theorem dest_anyClosure_simp[simp]:
  dest_anyClosure (Atom a) = NONE ∧
  dest_anyClosure (Constructor s vs) = NONE ∧
  dest_anyClosure (Thunk d) = NONE
Proof
  fs [AllCaseEqs(),dest_Closure_def,dest_anyClosure_def]
QED

Theorem env_rel_def = “env_rel p tenv senv”
  |> SIMP_CONV (srw_ss()) [Once v_rel_cases];

Inductive step_res_rel:
  (v_rel p v1 v2 ⇒
   step_res_rel p (Val v1) (Val v2)) ∧
  (v_rel p v1 v2 ⇒
   step_res_rel p (Exn v1) (Exn v2)) ∧
  (step_res_rel p Error Error) ∧
  (compile_rel e1 e2 ∧ env_rel p env1 env2 ⇒
   step_res_rel p (Exp env1 e1) (Exp env2 e2)) ∧
  (step_res_rel p (Action a b) (Action a b))
End

Inductive cont_rel:
  (∀p. cont_rel p [] []) ∧
  (∀p tenv senv op tvs svs tes ses sk tk.
    cont_rel p tk sk ∧ env_rel p tenv senv ∧
    LIST_REL (v_rel p) tvs svs ∧ LIST_REL compile_rel tes ses ⇒
    cont_rel p (AppK tenv op tvs tes :: tk)
               (AppK senv op svs ses :: sk)) ∧
  (∀p tenv senv n te se sk tk.
    cont_rel p tk sk ∧ env_rel p tenv senv ∧
    compile_rel te se ⇒
    cont_rel p (LetK tenv n te :: tk)
               (LetK senv n se :: sk)) ∧
  (∀p tenv senv te1 se1 te2 se2 sk tk.
    cont_rel p tk sk ∧ env_rel p tenv senv ∧
    compile_rel te1 se1 ∧ compile_rel te2 se2 ⇒
    cont_rel p (IfK tenv te1 te2 :: tk)
               (IfK senv se1 se2 :: sk)) ∧
  (∀p tenv senv n te se sk tk.
    cont_rel p tk sk ∧ env_rel p tenv senv ∧
    compile_rel te se ⇒
    cont_rel p (HandleK tenv n te :: tk)
               (HandleK senv n se :: sk)) ∧
  (∀p tenv senv te se sk tk.
    cont_rel p tk sk ∧ env_rel p tenv senv ∧
    compile_rel te se ⇒
    cont_rel p (HandleAppK tenv te :: tk)
               (HandleAppK senv se :: sk)) ∧
  (∀p sk tk senv.
    cont_rel p tk sk ⇒
    cont_rel p (BoxK :: tk)
               (AppK senv Ref [] [True] :: sk)) ∧
  (∀p sk tk.
    cont_rel p tk sk ⇒
    cont_rel p (RaiseK :: tk)
               (RaiseK :: sk)) ∧
  (∀p sk tk senv.
    cont_rel p tk sk ⇒
    cont_rel p (ForceK1 :: tk)
               (LetK senv (SOME "v") force_lets :: sk))
End

Definition rec_env_def:
  rec_env f env =
    MAP (λ(fn,_). (fn,Recclosure f env fn)) f ++ env
End

Definition thunk_rel_def:
  thunk_rel p NONE _ = T ∧
  thunk_rel p (SOME (x,f)) vs =
    case x of
    | INL tv => (∃sv. v_rel p tv sv ∧ vs = [True_v; sv])
    | INR (tenv,te) =>
        (∃senv se.
           env_rel p (rec_env f tenv) senv ∧ compile_rel te se ∧
           vs = [False_v; Closure NONE senv se]) ∨
        (∃tv sv ck.
           step_n ck (Exp (rec_env f tenv) te,NONE,[]) = (Val tv,NONE,[]) ∧
           vs = [True_v; sv] ∧ v_rel p tv sv)
End

Definition state_rel_def:
  state_rel p (ts:state option) (ss:state option) =
    ∃t1 s1.
      ts = SOME t1 ∧ ss = SOME s1 ∧
      LIST_REL (thunk_rel p) p s1 ∧
      LIST_REL (LIST_REL (v_rel p)) t1 (MAP SND (FILTER (λx. FST x = NONE) (ZIP (p,s1))))
End

Inductive snext_res_rel:
  (state_rel p (SOME ts) (SOME ss) ∧ cont_rel p tk sk ⇒
   snext_res_rel p (Act x tk (SOME ts)) (Act x sk (SOME ss))) ∧
  (snext_res_rel p Ret Ret) ∧
  (snext_res_rel p Div Div) ∧
  (snext_res_rel p Err Err)
End

Theorem step_n_is_halt_SOME:
  step_n n (tr,SOME ts,tk) = (tr1,ts1,tk1) ∧ is_halt (tr1,ts1,tk1) ∧ tr1 ≠ Error ⇒
  ∃ts2. ts1 = SOME ts2
Proof
  cheat
QED

Definition pick_opt_def[simp]:
  pick_opt zs NONE = SOME zs ∧
  pick_opt zs (SOME xs) = SOME xs
End

Triviality cont_rel_nil_cons:
  ~(cont_rel p [] (y::ys)) ∧
  ~(cont_rel p (x::xs) [])
Proof
  once_rewrite_tac [cont_rel_cases] \\ fs []
QED

Theorem cont_rel_nil:
  (cont_rel p [] ys ⇔ ys = []) ∧
  (cont_rel p xs [] ⇔ xs = [])
Proof
  Cases_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [cont_rel_nil_cons]
  \\ simp [Once cont_rel_cases]
QED

Theorem v_rel_new_Thunk:
  loc = LENGTH p ⇒
  v_rel (p ++ [SOME (r,[])]) (Thunk r) (Atom (Loc loc))
Proof
  cheat
QED

Theorem v_rel_ext:
  ∀q p k1 k2.
    v_rel p k1 k2 ⇒
    v_rel (p ++ q) k1 k2
Proof
  cheat
QED

Theorem cont_rel_ext:
  ∀q p k1 k2.
    cont_rel p k1 k2 ⇒
    cont_rel (p ++ q) k1 k2
Proof
  cheat
QED

Theorem state_rel_INR:
  state_rel p ts (SOME ss) ∧
  env_rel p env1 env2 ∧
  compile_rel te se ⇒
  state_rel (p ++ [SOME (INR (env1,te),f)]) ts
     (SOME (SNOC [False_v; Closure NONE env2 se] ss))
Proof
  cheat
QED

Theorem state_rel_INL:
  state_rel p ts (SOME ss) ∧ v_rel p v1 v2 ⇒
  state_rel (p ++ [SOME (INL v1,f)]) ts (SOME (SNOC [True_v; v2] ss))
Proof
  cheat
QED

Theorem v_rel_Ref:
  state_rel p (SOME x) (SOME ss) ⇒
  v_rel (p ++ [NONE]) (Atom (Loc (LENGTH x))) (Atom (Loc (LENGTH ss)))
Proof
  cheat
QED

Theorem state_rel_Ref:
  LIST_REL (v_rel p) xs ys ∧ state_rel p (SOME ts) (SOME ss) ⇒
  state_rel (p ++ [NONE]) (SOME (SNOC xs ts)) (SOME (SNOC ys ss))
Proof
  cheat
QED

Theorem dest_anyThunk_INL:
  v_rel p v1 v2 ∧ state_rel p zs (SOME ss) ∧
  dest_anyThunk v1 = SOME (INL x, f) ⇒
  ∃loc y.
    v2 = Atom (Loc loc) ∧ v_rel p x y ∧
    oEL loc ss = SOME [True_v; y]
Proof
  Cases_on ‘v1’ \\ fs [dest_anyThunk_def,dest_Thunk_def,AllCaseEqs()]
  \\ simp [Once v_rel_cases]
  \\ fs [dest_anyThunk_def,dest_Thunk_def,AllCaseEqs()]
  \\ rw [] \\ gvs []
  \\ gvs [state_rel_def]
  \\ gvs [oEL_THM]
  \\ gvs [LIST_REL_EL_EQN]
  \\ last_x_assum drule
  \\ fs [thunk_rel_def]
QED

Theorem dest_anyThunk_INR:
  v_rel p v1 v2 ∧ state_rel p zs (SOME ss) ∧
  dest_anyThunk v1 = SOME (INR (x1,x2), f) ⇒
  ∃loc.
    v2 = Atom (Loc loc) ∧
    ((∃senv se.
       env_rel p (rec_env f x1) senv ∧ compile_rel x2 se ∧
       oEL loc ss = SOME [False_v; Closure NONE senv se]) ∨
     ∃tv sv ck. step_n ck (Exp (rec_env f x1) x2,NONE,[]) = (Val tv,NONE,[]) ∧
                oEL loc ss = SOME [True_v; sv] ∧ v_rel p tv sv)
Proof
  Cases_on ‘v1’ \\ fs [dest_anyThunk_def,dest_Thunk_def,AllCaseEqs()]
  \\ simp [Once v_rel_cases]
  \\ fs [dest_anyThunk_def,dest_Thunk_def,
         dest_anyClosure_def,dest_Closure_def,AllCaseEqs()]
  \\ rw [] \\ gvs []
  \\ gvs [state_rel_def]
  \\ gvs [oEL_THM]
  \\ gvs [LIST_REL_EL_EQN]
  \\ last_x_assum drule
  \\ fs [thunk_rel_def]
  \\ strip_tac \\ fs []
  \\ rpt (first_x_assum $ irule_at Any)
QED

Theorem dest_anyThunk_INR_abs:
  v_rel p v1 (Atom (Loc loc)) ∧ state_rel p zs (SOME ss) ∧
  dest_anyThunk v1 = SOME (INR (x1,x2), f) ⇒
  ∃i1 i2. oEL loc ss = SOME [i1;i2]
Proof
  strip_tac
  \\ drule_all dest_anyThunk_INR \\ fs []
  \\ rw [] \\ fs []
QED

Theorem step_n_cut_cont:
  step_n n (x,s,k) = y ∧ is_halt y ⇒
  ∃m z. m ≤ n ∧ step_n m (x,s,[]) = z ∧ is_halt z
Proof
  cheat
QED

Theorem step_n_NONE:
  step_n n (Exp tenv1 te,ts,[]) = (tr1,ts1,tk1) ∧ is_halt (tr1,ts1,tk1) ⇒
  step_n n (Exp tenv1 te,NONE,[]) = (tr1,NONE,tk1) ∧ (∃res. tr1 = Val res) ∨
  ∀k. ∃ts2 tk2. step_n n (Exp tenv1 te,NONE,k) = (Error,ts2,tk2)
Proof
  cheat
QED

Theorem step_n_set_cont:
  step_n n (Exp tenv1 te,NONE,[]) = (Val res,ts1,[]) ⇒
  ∀k. step_n n (Exp tenv1 te,NONE,k) = (Val res,ts1,k)
Proof
  cheat
QED

Theorem step_n_fast_forward:
  step_n n (sr,ss,k::ks) = (sr1,ss1,sk1) ∧ is_halt (sr1,ss1,sk1) ∧
  step_n m2 (sr,ss,[]) = (Val v2,ss2,[]) ⇒
  ∃m3. m3 ≤ n ∧ step_n m3 (Val v2,ss2,k::ks) = (sr1,ss1,sk1)
Proof
  cheat
QED

Theorem SOME_THE_pick_opt:
  SOME (THE (pick_opt zs ts)) = pick_opt zs ts
Proof
  Cases_on ‘ts’ \\ fs []
QED

Theorem LUPDATE_LUPDATE:
  ∀xs n x y. LUPDATE x n (LUPDATE y n xs) = LUPDATE x n xs
Proof
  Induct \\ fs [LUPDATE_DEF] \\ rw [] \\ fs [LUPDATE_DEF]
QED

Theorem state_rel_LUPDATE_anyThunk:
  v_rel p res v2 ∧ state_rel p ts (SOME ss2) ∧
  v_rel p v1 (Atom (Loc loc)) ∧
  dest_anyThunk v1 = SOME (INR (tenv1,te),f) ∧
  step_n n (Exp (rec_env f tenv1) te,NONE,[]) = (Val res,NONE,[]) ⇒
  state_rel p ts (SOME (LUPDATE [True_v; v2] loc ss2))
Proof
  fs [state_rel_def] \\ rw [] \\ fs []
  \\ qpat_x_assum ‘v_rel p v1 (Atom (Loc loc))’ mp_tac
  \\ simp [Once v_rel_cases]
  \\ strip_tac \\ gvs []
  \\ gvs [state_rel_def]
  \\ gvs [oEL_THM]
  \\ reverse conj_tac
  >-
   (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ match_mp_tac (METIS_PROVE [] “p = q ⇒ x p ⇒ x q”)
    \\ AP_TERM_TAC
    \\ pop_assum mp_tac
    \\ imp_res_tac LIST_REL_LENGTH
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘loc’
    \\ qid_spec_tac ‘ss2’
    \\ qid_spec_tac ‘p’
    \\ rpt (pop_assum kall_tac)
    \\ Induct \\ fs [] \\ Cases_on ‘ss2’ \\ fs []
    \\ Cases_on ‘loc’ \\ fs [LUPDATE_DEF]
    \\ rw [] \\ fs [])
  \\ qpat_x_assum ‘LIST_REL _ _ _’ kall_tac
  \\ fs [LIST_REL_EL_EQN]
  \\ gvs [EL_LUPDATE]
  \\ rw [] \\ gvs []
  \\ fs [thunk_rel_def]
  \\ rpt (first_x_assum $ irule_at Any)
QED

Theorem step_forward:
  ∀n zs p tr ts tk tr1 ts1 tk1 ss sr sk.
    step_n n (tr,ts,tk) = (tr1,ts1,tk1) ∧ is_halt (tr1,ts1,tk1) ∧
    cont_rel p tk sk ∧
    state_rel p (pick_opt zs ts) (SOME ss) ∧
    step_res_rel p tr sr ∧ tr1 ≠ Error ⇒
    ∃m q sr1 ss1 sk1.
      step_n m (sr,SOME ss,sk) = (sr1,SOME ss1,sk1) ∧
      is_halt (sr1,SOME ss1,sk1) ∧
      cont_rel (p++q) tk1 sk1 ∧
      state_rel (p++q) (pick_opt zs ts1) (SOME ss1) ∧
      step_res_rel (p++q) tr1 sr1
Proof
  gen_tac \\ completeInduct_on ‘n’
  \\ rpt strip_tac \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ Cases_on ‘n = 0’
  >-
   (gvs [] \\ qexists_tac ‘0’ \\ qexists_tac ‘[]’ \\ gvs []
    \\ TRY (first_assum $ irule_at Any) \\ fs []
    \\ Cases_on ‘sr’ \\ fs [is_halt_def]
    \\ gvs [step_res_rel_cases,is_halt_def]
    \\ Cases_on ‘tk’ \\ Cases_on ‘sk’ \\ gvs [is_halt_def,cont_rel_nil_cons])
  \\ cheat
  (*
  \\ Cases_on ‘∃tenv te. tr = Exp tenv te’ \\ rw []
    qpat_x_assum ‘step_res_rel _ _ _’ mp_tac
    \\ simp [Once step_res_rel_cases] \\ rw []
    \\ Cases_on ‘∃te1. te = Force te1’ \\ rw []
      fs [Once compile_rel_cases] \\ rw []
  \\ Cases_on ‘tr’
  *)
QED

Theorem step_backward:
  ∀m zs p sr ss sk sr1 ss1 sk1 tr ts tk.
    step_n m (sr,SOME ss,sk) = (sr1,ss1,sk1) ∧
    is_halt (sr1,ss1,sk1) ∧
    cont_rel p tk sk ∧
    state_rel p (pick_opt zs ts) (SOME ss) ∧
    step_res_rel p tr sr ⇒
    ∃n q tr1 ts1 tk1.
      step_n n (tr,ts,tk) = (tr1,ts1,tk1) ∧
      is_halt (tr1,ts1,tk1)
Proof
  gen_tac \\ completeInduct_on ‘m’
  \\ rpt strip_tac \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ Cases_on ‘m = 0’
  >-
   (gvs [] \\ qexists_tac ‘0’ \\ gvs []
    \\ Cases_on ‘sr’ \\ fs [is_halt_def]
    \\ gvs [step_res_rel_cases,is_halt_def]
    \\ Cases_on ‘tk’ \\ Cases_on ‘sk’ \\ gvs [is_halt_def,cont_rel_nil_cons])
  \\ Cases_on ‘is_halt (tr,ts,tk)’
  >- (qexists_tac ‘0’ \\ fs [])
  \\ qpat_x_assum ‘step_res_rel p tr sr’ mp_tac
  \\ once_rewrite_tac [step_res_rel_cases]
  \\ strip_tac \\ gvs [is_halt_def]
  >-
   (Cases_on ‘tk’ \\ gvs [is_halt_def]
    \\ Cases_on ‘sk’ \\ gvs [is_halt_def,cont_rel_nil_cons]
    \\ rename [‘cont_rel p (tk'::tk) (sk'::sk)’]
    \\ qpat_x_assum ‘cont_rel _ _ _’ mp_tac
    \\ once_rewrite_tac [cont_rel_cases]
    \\ strip_tac \\ gvs []
    >~ [‘ForceK1’] >-
     (Q.REFINE_EXISTS_TAC ‘ck+1:num’
      \\ qpat_x_assum ‘step_n m _ = _’ mp_tac
      \\ (Cases_on ‘m’ >- fs [])
      \\ rewrite_tac [step_n_add,ADD1]
      \\ fs [] \\ simp [step,error_def]
      \\ rename [‘v_rel p v1 v2’]
      \\ Cases_on ‘dest_anyThunk v1’ \\ simp []
      >- (rw [] \\ qexists_tac ‘0’ \\ fs [is_halt_def])
      \\ PairCases_on ‘x’ \\ gvs []
      \\ rename [‘_ = SOME (yy,_)’] \\ Cases_on ‘yy’ \\ simp []
      >-
       (rename [‘step_n n’] \\ Cases_on ‘n’ \\ fs []
        >- (rw [] \\ fs [is_halt_def])
        \\ rewrite_tac [step_n_add,ADD1] \\ simp [step]
        \\ rename [‘step_n n’] \\ Cases_on ‘n’ \\ fs []
        >- (rw [] \\ fs [is_halt_def])
        \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def]
        \\ drule_all dest_anyThunk_INL
        \\ strip_tac \\ gvs []
        \\ ntac 16 (rename [‘step_n n’] \\ Cases_on ‘n’ \\ fs []
                    >- (rw [] \\ fs [is_halt_def])
                    \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
        \\ gvs [ADD1]
        \\ strip_tac \\ last_x_assum irule
        \\ pop_assum $ irule_at Any \\ fs []
        \\ simp [Once step_res_rel_cases]
        \\ rpt (first_x_assum $ irule_at Any))
      \\ PairCases_on ‘y’
      \\ drule_all dest_anyThunk_INR \\ reverse strip_tac \\ gvs []
      >-
       (ntac 18 (rename [‘step_n nn’] \\ Cases_on ‘nn’ \\ fs []
                 >- (rw [] \\ fs [is_halt_def])
                 \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
        \\ gvs [ADD1,GSYM rec_env_def] \\ strip_tac
        \\ drule step_n_set_cont
        \\ disch_then $ qspec_then ‘ForceK2 ts::tk’ assume_tac
        \\ Q.REFINE_EXISTS_TAC ‘ck1+(1+ck)’
        \\ rewrite_tac [step_n_add,ADD1]
        \\ fs [] \\ simp [step]
        \\ pop_assum kall_tac
        \\ last_x_assum $ irule
        \\ pop_assum $ irule_at Any \\ fs []
        \\ rpt (first_assum $ irule_at Any)
        \\ simp [step_res_rel_cases])
      \\ ntac 23 (rename [‘step_n n’] \\ Cases_on ‘n’ \\ fs []
                  >- (rw [] \\ fs [is_halt_def])
                  \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
      \\ gvs [ADD1]
      \\ strip_tac
      \\ drule_all step_n_cut_cont
      \\ strip_tac \\ PairCases_on ‘z’ \\ fs []
      \\ last_assum $ qspec_then ‘m’ mp_tac \\ simp []
      \\ disch_then drule \\ simp []
      \\ simp [Once cont_rel_cases,GSYM rec_env_def]
      \\ rpt (disch_then drule \\ simp [])
      \\ rename [‘env_rel p (rec_env f tenv1) senv1’,‘compile_rel te se’]
      \\ disch_then $ qspec_then ‘Exp (rec_env f tenv1) te’ mp_tac
      \\ impl_tac >- simp [Once step_res_rel_cases]
      \\ strip_tac
      \\ drule_all step_n_NONE
      \\ reverse strip_tac
      >-
       (pop_assum $ qspec_then ‘ForceK2 ts::tk’ strip_assume_tac
        \\ pop_assum $ irule_at Any \\ fs [is_halt_def])
      \\ gvs []
      \\ Cases_on ‘tk1’ \\ fs [is_halt_def]
      \\ drule step_n_set_cont
      \\ disch_then $ qspec_then ‘ForceK2 ts::tk’ assume_tac
      \\ Q.REFINE_EXISTS_TAC ‘ck+(1+n)’
      \\ qpat_x_assum ‘step_n m _ = _’ mp_tac
      \\ rewrite_tac [step_n_add,ADD1] \\ simp []
      \\ simp [step] \\ gvs []
      \\ pop_assum mp_tac
      \\ drule step_forward
      \\ simp [cont_rel_nil,is_halt_def]
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ ‘state_rel p (SOME (THE (pick_opt zs ts))) (SOME ss)’
        by (Cases_on ‘ts’ \\ fs [])
      \\ rpt (disch_then $ drule_at Any)
      \\ fs [is_halt_def]
      \\ simp [Once step_res_rel_cases]
      \\ strip_tac \\ gvs [is_halt_def]
      \\ rename [‘step_n m2 (Exp senv1 se,SOME ss,[]) = (Val v2,SOME ss2,[])’]
      \\ drule_all step_n_fast_forward \\ strip_tac
      \\ pop_assum mp_tac
      \\ ntac 9 (rename [‘step_n nn’] \\ Cases_on ‘nn’ \\ fs []
                 >- (rw [] \\ fs [is_halt_def])
                 \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
      \\ gvs [ADD1,SOME_THE_pick_opt]
      \\ qpat_x_assum ‘_ = (sr1,ss1,sk1)’ kall_tac
      \\ ‘v_rel (p++q) v1 (Atom (Loc loc))’ by (irule v_rel_ext \\ fs [])
      \\ drule dest_anyThunk_INR_abs
      \\ disch_then drule_all
      \\ strip_tac \\ fs []
      \\ ntac 9 (rename [‘step_n nn’] \\ Cases_on ‘nn’ \\ fs []
                 >- (rw [] \\ fs [is_halt_def])
                 \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
      \\ fs [oEL_THM,EL_LUPDATE]
      \\ ntac 2 (rename [‘step_n nn’] \\ Cases_on ‘nn’ \\ fs []
                 >- (rw [] \\ fs [is_halt_def])
                 \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
      \\ qmatch_goalsub_abbrev_tac ‘SOME ss3’
      \\ rename [‘step_n nn’] \\ gvs [ADD1]
      \\ strip_tac
      \\ rpt (disch_then kall_tac)
      \\ last_x_assum irule
      \\ pop_assum $ irule_at Any \\ fs []
      \\ qexists_tac ‘zs’ \\ qexists_tac ‘p++q’ \\ fs [step_res_rel_cases]
      \\ irule_at Any cont_rel_ext \\ fs [LUPDATE_DEF,LUPDATE_LUPDATE]
      \\ simp [Abbr‘ss3’]
      \\ drule_all state_rel_LUPDATE_anyThunk \\ fs [])
    >~ [‘BoxK’] >-
     (Q.REFINE_EXISTS_TAC ‘ck1+1’
      \\ rewrite_tac [step_n_add,ADD1] \\ simp [step]
      \\ qpat_x_assum ‘step_n _ _ = _’ mp_tac
      \\ ntac 3 (rename [‘step_n nn’] \\ Cases_on ‘nn’
                 >- (rw [] \\ fs [is_halt_def]) \\ fs []
                 \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
      \\ strip_tac
      \\ first_x_assum irule
      \\ pop_assum $ irule_at Any \\ fs [ADD1]
      \\ qexists_tac ‘zs’
      \\ simp [step_res_rel_cases]
      \\ irule_at Any v_rel_new_Thunk
      \\ irule_at Any cont_rel_ext
      \\ pop_assum $ irule_at Any
      \\ irule_at Any state_rel_INL \\ gvs []
      \\ fs [state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
    >~ [‘LetK tenv n te’] >- cheat
    >~ [‘IfK tenv te1 te2’] >- cheat
    >~ [‘HandleK tenv n te’] >- cheat
    >~ [‘HandleAppK tenv te’] >- cheat
    >~ [‘RaiseK’] >- cheat
    \\ rename [‘AppK tenv op tvs tes’]
    \\ cheat)
  >-
   (Cases_on ‘tk’ \\ gvs [is_halt_def]
    \\ Cases_on ‘sk’ \\ gvs [is_halt_def,cont_rel_nil_cons]
    \\ rename [‘cont_rel p (tk'::tk) (sk'::sk)’]
    \\ qpat_x_assum ‘cont_rel _ _ _’ mp_tac
    \\ once_rewrite_tac [cont_rel_cases]
    \\ strip_tac \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘ck+1:num’
    \\ qpat_x_assum ‘step_n m _ = _’ mp_tac
    \\ (Cases_on ‘m’ >- fs [])
    \\ rewrite_tac [step_n_add,ADD1]
    \\ fs [] \\ simp [step_def,continue_def,push_def]
    \\ strip_tac
    \\ last_x_assum irule
    \\ pop_assum $ irule_at Any \\ fs []
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ rpt (first_assum $ irule_at $ Any \\ fs [])
    \\ once_rewrite_tac [cont_rel_cases] \\ fs []
    \\ fs [env_rel_def] \\ rw [] \\ fs [])
  \\ qpat_x_assum ‘compile_rel e1 e2’ mp_tac
  \\ simp [Once compile_rel_cases] \\ rw []
  \\ Q.REFINE_EXISTS_TAC ‘ck+1:num’
  \\ qpat_x_assum ‘step_n m _ = _’ mp_tac
  \\ (Cases_on ‘m’ >- fs [])
  \\ rewrite_tac [step_n_add,ADD1]
  \\ TRY
     (simp [step]
      \\ strip_tac
      \\ last_x_assum irule
      \\ pop_assum $ irule_at Any \\ fs []
      \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
      \\ rpt (first_assum $ irule_at $ Any \\ fs [])
      \\ once_rewrite_tac [cont_rel_cases] \\ fs []
      \\ once_rewrite_tac [v_rel_cases] \\ fs [dest_anyClosure_def] \\ NO_TAC)
  >~ [‘Var vname’] >-
   (fs [step,error_def]
    \\ Cases_on ‘ALOOKUP env1 vname’ \\ fs [is_halt_def]
    >- (rw [] \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs [env_rel_def] \\ fs []
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ gvs []
    \\ last_x_assum irule
    \\ pop_assum $ irule_at Any \\ fs []
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ rpt (first_assum $ irule_at $ Any \\ fs []))
  >~ [‘Delay te’] >-
   (simp [step]
    \\ Cases_on ‘n’ \\ fs []
    >- (rw [] \\ fs [is_halt_def])
    \\ rewrite_tac [step_n_add,ADD1]
    \\ simp [step]
    \\ rename [‘step_n n’]
    \\ Cases_on ‘n’ \\ fs []
    >- (rw [] \\ fs [is_halt_def])
    \\ rewrite_tac [step_n_add,ADD1]
    \\ simp [step]
    \\ rename [‘step_n n’]
    \\ Cases_on ‘n’ \\ fs []
    >- (rw [] \\ fs [is_halt_def])
    \\ rewrite_tac [step_n_add,ADD1]
    \\ simp [step]
    \\ rename [‘step_n n’]
    \\ Cases_on ‘n’ \\ fs []
    >- (rw [] \\ fs [is_halt_def])
    \\ rewrite_tac [step_n_add,ADD1]
    \\ simp [step]
    \\ rename [‘step_n n’]
    \\ strip_tac
    \\ last_x_assum irule
    \\ pop_assum $ irule_at Any \\ fs []
    \\ qexists_tac ‘zs’ \\ fs []
    \\ qexists_tac ‘p ++ [SOME (INR (env1,te),[])]’ \\ fs []
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ irule_at Any v_rel_new_Thunk
    \\ irule_at Any cont_rel_ext \\ simp []
    \\ irule_at Any state_rel_INR \\ fs []
    \\ fs [state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  >~ [‘App op ys’] >-
   (fs [step,error_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC
    >- (rw [] \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs []
    \\ reverse CASE_TAC \\ gvs []
    >-
     (Cases_on ‘REVERSE xs’ >- gvs []
      \\ gvs [SWAP_REVERSE_SYM]
      \\ strip_tac
      \\ last_x_assum irule
      \\ pop_assum $ irule_at Any \\ fs []
      \\ qexists_tac ‘zs’ \\ fs []
      \\ rpt (first_assum $ irule_at $ Any \\ fs [])
      \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
      \\ once_rewrite_tac [cont_rel_cases] \\ fs [])
    \\ Cases_on ‘∃aop. op = AtomOp aop’
    >-
     (gvs [application_def,get_atoms_def]
      \\ fs [value_def,error_def]
      \\ every_case_tac
      \\ TRY (strip_tac \\ qexists_tac ‘0’ \\ fs [is_halt_def] \\ NO_TAC)
      \\ strip_tac
      \\ last_x_assum irule
      \\ pop_assum $ irule_at Any \\ fs []
      \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
      \\ rpt (first_assum $ irule_at $ Any \\ fs [])
      \\ once_rewrite_tac [cont_rel_cases] \\ fs []
      \\ once_rewrite_tac [v_rel_cases] \\ fs []
      \\ Cases_on ‘aop’ \\ fs [])
    \\ Cases_on ‘∃k. op = Cons k’
    >-
     (gvs [application_def,get_atoms_def]
      \\ fs [value_def,error_def]
      \\ strip_tac
      \\ last_x_assum irule
      \\ pop_assum $ irule_at Any \\ fs []
      \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
      \\ rpt (first_assum $ irule_at $ Any \\ fs [])
      \\ once_rewrite_tac [v_rel_cases] \\ fs [])
    \\ Cases_on ‘op’ \\ fs []
    \\ rename [‘application Ref’]
    \\ gvs [application_def,get_atoms_def]
    \\ fs [value_def,error_def]
    \\ Cases_on ‘ts’ \\ fs []
    >- (strip_tac \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ strip_tac
    \\ last_x_assum irule
    \\ pop_assum $ irule_at Any \\ fs []
    \\ qexists_tac ‘p ++ [NONE]’
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ irule_at Any cont_rel_ext \\ simp []
    \\ irule_at Any v_rel_Ref \\ simp []
    \\ irule_at Any state_rel_Ref \\ simp [])
  \\ rename [‘Letrec tfns te’]
  \\ cheat
QED

(* step_until_halt *)

Theorem step_until_halt_thm:
  step_res_rel p tr sr ∧
  state_rel p (SOME ts) (SOME ss) ∧
  cont_rel p tk sk ∧
  step_until_halt (tr,SOME ts,tk) ≠ Err ⇒
  ∃q. snext_res_rel q (step_until_halt (tr,SOME ts,tk))
                      (step_until_halt (sr,SOME ss,sk))
Proof
  fs [step_until_halt_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
  >-
   (‘∃a. step_n x (tr,SOME ts,tk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ gvs []
    \\ ‘a0 ≠ Error’ by (strip_tac \\ gvs [])
    \\ ‘state_rel p (pick_opt zs (SOME ts)) (SOME ss)’ by fs []
    \\ drule_all step_forward \\ rw []
    \\ reverse (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw [])
    >- metis_tac []
    \\ ‘step_n x' (sr,SOME ss,sk) = step_n m (sr,SOME ss,sk)’
      by metis_tac [is_halt_imp_eq]
    \\ gvs []
    \\ qpat_x_assum ‘step_res_rel _ _ _’ mp_tac
    \\ simp [Once step_res_rel_cases] \\ strip_tac \\ gvs []
    \\ simp [Once snext_res_rel_cases] \\ gvs []
    \\ rpt (first_assum $ irule_at Any)
    \\ qpat_x_assum ‘step_n x _ = _’ assume_tac
    \\ drule step_n_is_halt_SOME \\ gvs []
    \\ strip_tac \\ gvs [])
  \\ reverse (DEEP_INTRO_TAC some_intro \\ fs [] \\ rw [])
  >- simp [Once snext_res_rel_cases]
  \\ ‘∃a. step_n x (sr,SOME ss,sk) = a’ by fs []
  \\ PairCases_on ‘a’ \\ gvs []
  \\ ‘state_rel p (pick_opt zs (SOME ts)) (SOME ss)’ by fs []
  \\ drule_all step_backward
  \\ metis_tac []
QED

(* unfold *)

Theorem semantics_thm:
  compile_rel e1 e2 ∧
  state_rel p (SOME ts) (SOME ss) ∧
  env_rel p tenv senv ∧
  cont_rel p tk sk ⇒
  semantics e1 tenv (SOME ts) tk --->
  semantics e2 senv (SOME ss) sk
Proof
  qsuff_tac ‘
    ∀t1 t2.
      (∃p e1 e2 ts ss tenv senv tk sk.
        compile_rel e1 e2 ∧
        state_rel p (SOME ts) (SOME ss) ∧
        env_rel p tenv senv ∧
        cont_rel p tk sk ∧
        t1 = semantics e1 tenv (SOME ts) tk ∧
        t2 = semantics e2 senv (SOME ss) sk) ⇒
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
  \\ once_rewrite_tac [io_treeTheory.io_unfold_err]
  \\ fs []
  \\ simp [GSYM sinterp_def]
  \\ Cases_on ‘step_until_halt (Exp tenv e1,SOME ts,tk) = Err’ >- fs []
  \\ drule_at (Pos last) step_until_halt_thm
  \\ rpt (disch_then $ drule_at $ Pos last)
  \\ disch_then $ qspec_then ‘Exp senv e2’ mp_tac
  \\ impl_tac
  >- simp [Once step_res_rel_cases]
  \\ rename [‘snext_res_rel _ xx yy’]
  \\ simp [snext_res_rel_cases]
  \\ strip_tac \\ fs []
  \\ rw [] \\ gvs []
  \\ Cases \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ fs [] \\ fs [value_def] \\ rw []
  \\ simp [sinterp_def]
  \\ ‘compile_rel (Lit (Str y)) (Lit (Str y))’ by simp [Once compile_rel_cases]
  \\ pop_assum $ irule_at Any
  \\ qpat_x_assum ‘cont_rel _ _ _’ $ irule_at Any
  \\ ‘env_rel q [] []’ by fs [env_rel_def]
  \\ pop_assum $ irule_at Any
  \\ qpat_x_assum ‘state_rel q _ _’ $ irule_at Any
  \\ simp [value_def]
  \\ once_rewrite_tac [io_treeTheory.io_unfold_err]
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
  \\ qexists_tac ‘[]’ \\ fs [state_rel_def]
QED

val _ = export_theory ();
