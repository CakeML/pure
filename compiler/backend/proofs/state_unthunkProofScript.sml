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
  Let (SOME "v1") (App UnsafeSub [Var "v"; IntLit 0]) $
  Let (SOME "v2") (App UnsafeSub [Var "v"; IntLit 1]) $
    If (Var "v1") (Var "v2") $
      Let (SOME "wh") (app (Var "v2") Unit) $
      Let NONE (App UnsafeUpdate [Var "v"; IntLit 0; True]) $
      Let NONE (App UnsafeUpdate [Var "v"; IntLit 1; Var "wh"]) $
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
  (Letrec_imm vs _ ⇔ F)
End

Definition Letrec_split_def:
  Letrec_split vs [] = ([],[]) ∧
  Letrec_split vs ((v:string,x)::fns) =
    let (xs,ys) = Letrec_split vs fns in
      case dest_Delay x of
      | NONE => (xs,(v,x)::ys)
      | SOME y => ((v,Letrec_imm vs y,y)::xs,ys)
End

Definition Bool_def[simp]:
  Bool T = True ∧
  Bool F = False
End

Definition Bool_v_def[simp]:
  Bool_v T = True_v ∧
  Bool_v F = False_v
End

Definition some_ref_bool_def:
  some_ref_bool (v:string,b,y:exp) = (SOME v, App Ref [Bool b; Bool b])
End

Definition unsafe_update_def:
  unsafe_update (v,b,y) =
    (NONE:string option, App UnsafeUpdate [Var v; IntLit 1; if b then y else Lam NONE y])
End

Definition comp_Letrec_def:
  comp_Letrec xs y =
    let (delays,funs) = Letrec_split (MAP FST xs) xs in
      Lets (MAP some_ref_bool delays) $
      Letrec funs $
      Lets (MAP unsafe_update delays) y
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
    MAP FST tfns = MAP FST sfns ∧ ALL_DISTINCT (MAP FST tfns) ∧
    LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ∧
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
    compile_rel (Force te) (force se)) ∧

[letrec_rel_Delay:]
  (∀te se.
    compile_rel te se ⇒
    letrec_rel (Delay te) (Delay se)) ∧

[letrec_rel_Lam:]
  (∀te se n.
    compile_rel te se ⇒
    letrec_rel (Lam n te) (Lam n se))

End

Definition find_loc_def:
  find_loc n [] = NONE ∧
  find_loc n (x::xs) =
    case x of
    | NONE => if n = 0:num then SOME (0:num) else
                OPTION_MAP (λn. n + 1:num) (find_loc (n-1) xs)
    | SOME _ => OPTION_MAP (λn. n + 1:num) (find_loc n xs)
End

Definition loc_rel_def[simp]:
  loc_rel p tenv tfns (tn,te:exp) (sn,sv) ⇔
  ∃r n.
    tn = sn ∧
    dest_anyThunk (Recclosure tfns tenv tn) = SOME r ∧
    sv = Atom (Loc n) ∧
    oEL n p = SOME (SOME r)
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
  (∀p tenv senv te se n.
     env_rel p tenv senv ∧ compile_rel te se ⇒
     v_rel p (Closure n tenv te) (Closure n senv se)) ∧

[~Recclosure:]
  (∀p tfns tfns1 sfns1 tfns2 sfns tenv senv n v e.
     env_rel p tenv senv ∧
     ALL_DISTINCT (MAP FST tfns) ∧
     LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ∧
     MAP FST tfns = MAP FST sfns ∧
     tfns1 = FILTER (is_Lam o SND) tfns ∧
     tfns2 = FILTER (is_Delay o SND) tfns ∧
     sfns1 = FILTER (is_Lam o SND) sfns ∧
     LIST_REL (loc_rel p tenv tfns) tfns2 locs ∧
     MEM (n,Lam v e) tfns ⇒
     v_rel p (Recclosure tfns tenv n)
             (Recclosure sfns1 (REVERSE locs ++ senv) n)) ∧

[~Recthunk:]
  (∀p tfns tfns1 sfns1 tfns2 sfns tenv senv n loc.
     env_rel p tenv senv ∧
     ALL_DISTINCT (MAP FST tfns) ∧
     LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ∧
     MAP FST tfns = MAP FST sfns ∧
     tfns1 = FILTER (is_Lam o SND) tfns ∧
     tfns2 = FILTER (is_Delay o SND) tfns ∧
     sfns1 = FILTER (is_Lam o SND) sfns ∧
     LIST_REL (loc_rel p tenv tfns) tfns2 locs ∧
     ALOOKUP locs n = SOME loc ⇒
     v_rel p (Recclosure tfns tenv n) loc) ∧

[~Thunk:]
  (∀p n r.
     oEL n p = SOME (SOME (r,[])) ⇒
     v_rel p (Thunk r) (Atom (Loc n))) ∧

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
    cont_rel p tk sk ∧ env_rel p tenv senv ∧ (∀l. op ≠ AtomOp (Lit (Loc l))) ∧
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
  simp [Once v_rel_cases,oEL_THM,rich_listTheory.EL_LENGTH_APPEND]
  \\ EVAL_TAC
QED

Theorem v_rel_env_rel_ext:
  (∀p k1 k2.
     v_rel p k1 k2 ⇒
     v_rel (p ++ q) k1 k2) ∧
  (∀p k1 k2.
     env_rel p k1 k2 ⇒
     env_rel (p ++ q) k1 k2)
Proof
  ho_match_mp_tac v_rel_ind \\ rw []
  \\ simp [Once v_rel_cases]
  \\ gvs [SF ETA_ss]
  \\ gvs [oEL_THM,EL_APPEND1]
  >-
   (pop_assum mp_tac
    \\ qid_spec_tac ‘n2’
    \\ qid_spec_tac ‘n1’
    \\ qid_spec_tac ‘p’
    \\ Induct \\ fs [find_loc_def]
    \\ Cases \\ fs []
    \\ rw [] \\ res_tac \\ gvs [])
  THENL [disj1_tac,disj2_tac]
  \\ last_x_assum $ irule_at $ Pos last
  \\ rpt (first_x_assum $ irule_at Any) \\ fs []
  \\ pop_assum mp_tac
  \\ match_mp_tac LIST_REL_mono
  \\ fs [FORALL_PROD]
  \\ rw [loc_rel_def]
  \\ gvs [oEL_THM,EL_APPEND1]
QED

Theorem v_rel_ext:
  ∀q p k1 k2.
    v_rel p k1 k2 ⇒
    v_rel (p ++ q) k1 k2
Proof
  metis_tac [v_rel_env_rel_ext]
QED

Theorem env_rel_ext:
  ∀q p k1 k2.
    env_rel p k1 k2 ⇒
    env_rel (p ++ q) k1 k2
Proof
  metis_tac [v_rel_env_rel_ext]
QED

Theorem cont_rel_ext:
  ∀q p k1 k2.
    cont_rel p k1 k2 ⇒
    cont_rel (p ++ q) k1 k2
Proof
  gen_tac \\ Induct_on ‘cont_rel’ \\ rw []
  \\ simp [Once cont_rel_cases]
  \\ rpt (irule_at Any env_rel_ext \\ fs [])
  \\ gvs [LIST_REL_EL_EQN]
  \\ rw [] \\ res_tac
  \\ rpt (irule_at Any v_rel_ext \\ fs [])
QED

Theorem thunk_rel_ext:
  ∀q p k1 k2.
    thunk_rel p k1 k2 ⇒
    thunk_rel (p ++ q) k1 k2
Proof
  rw [] \\ Cases_on ‘k1’ \\ fs [thunk_rel_def]
  \\ PairCases_on ‘x’ \\ fs [thunk_rel_def]
  \\ Cases_on ‘x0’ \\ fs []
  \\ TRY (Cases_on ‘y’ \\ fs [])
  \\ TRY (irule_at Any v_rel_ext \\ fs [])
  \\ TRY (irule_at Any env_rel_ext \\ fs [])
  \\ first_x_assum $ irule_at Any
  \\ first_x_assum $ irule_at Any
QED

Theorem state_rel_INR:
  state_rel p ts (SOME ss) ∧
  env_rel p (rec_env f env1) env2 ∧
  compile_rel te se ⇒
  state_rel (p ++ [SOME (INR (env1,te),f)]) ts
     (SOME (SNOC [False_v; Closure NONE env2 se] ss))
Proof
  fs [state_rel_def] \\ rw [] \\ gvs []
  \\ gvs [thunk_rel_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ gvs [GSYM ZIP_APPEND,FILTER_APPEND]
  \\ gvs [LIST_REL_EL_EQN] \\ rw []
  \\ TRY (irule_at Any thunk_rel_ext \\ fs [])
  \\ TRY (irule_at Any env_rel_ext \\ fs [])
  \\ irule_at Any v_rel_ext \\ fs []
QED

Theorem state_rel_INL:
  state_rel p ts (SOME ss) ∧ v_rel p v1 v2 ⇒
  state_rel (p ++ [SOME (INL v1,f)]) ts (SOME (SNOC [True_v; v2] ss))
Proof
  fs [state_rel_def] \\ rw [] \\ gvs []
  \\ gvs [thunk_rel_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ gvs [GSYM ZIP_APPEND,FILTER_APPEND]
  \\ gvs [LIST_REL_EL_EQN] \\ rw []
  \\ TRY (irule_at Any thunk_rel_ext \\ fs [])
  \\ irule_at Any v_rel_ext \\ fs []
QED

Theorem v_rel_Ref:
  state_rel p (SOME x) (SOME ss) ⇒
  v_rel (p ++ [NONE]) (Atom (Loc (LENGTH x))) (Atom (Loc (LENGTH ss)))
Proof
  fs [Once v_rel_cases,state_rel_def]
  \\ rename [‘LIST_REL r p ss’]
  \\ rename [‘LIST_REL (LIST_REL qq) x’]
  \\ qid_spec_tac ‘x’
  \\ qid_spec_tac ‘ss’
  \\ qid_spec_tac ‘p’
  \\ Induct \\ fs [find_loc_def,PULL_EXISTS]
  \\ Cases \\ fs [PULL_EXISTS] \\ rw []
  \\ res_tac \\ fs []
QED

Theorem state_rel_Ref:
  LIST_REL (v_rel p) xs ys ∧ state_rel p (SOME ts) (SOME ss) ⇒
  state_rel (p ++ [NONE]) (SOME (SNOC xs ts)) (SOME (SNOC ys ss))
Proof
  gvs [state_rel_def,thunk_rel_def] \\ rpt strip_tac
  >-
   (gvs [LIST_REL_EL_EQN] \\ rw []
    \\ irule_at Any thunk_rel_ext \\ fs [])
  \\ imp_res_tac LIST_REL_LENGTH
  \\ ‘ZIP (p ++ [NONE],ss ++ [ys]) = ZIP (p,ss) ++ ZIP ([NONE],[ys])’ by
       (irule $ GSYM ZIP_APPEND \\ fs [])
  \\ fs [FILTER_APPEND]
  \\ gvs [LIST_REL_EL_EQN] \\ rw []
  \\ irule_at Any v_rel_ext \\ fs []
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

Triviality ALOOKUP_LIST_REL_loc_rel:
  ∀tfns locs x1 x2 x3 n y.
    LIST_REL (loc_rel x1 x2 x3) tfns locs ∧
    ALOOKUP locs n = SOME y ⇒
    MEM n (MAP FST tfns)
Proof
  Induct \\ fs [FORALL_PROD] \\ rw [] \\ gvs []
  \\ PairCases_on ‘y'’ \\ gvs []
  \\ CCONTR_TAC \\ gvs []
  \\ first_x_assum drule_all \\ fs []
QED

Triviality LIST_REL_loc_rel_alt_lemma:
  ∀f locs f1.
    ALL_DISTINCT (MAP FST f) ∧
    LIST_REL (loc_rel p l (f1 ++ f)) (FILTER ((λx. is_Delay x) ∘ SND) f) locs ∧
    ALOOKUP locs s = SOME v2 ⇒
    ∃x2. ALOOKUP f s = SOME (Delay x2) ∧
         loc_rel p l (f1 ++ f) (s,x2) (s,v2)
Proof
  Induct \\ fs [FORALL_PROD]
  \\ rpt strip_tac
  \\ Cases_on ‘p_1 = s’ \\ gvs []
  >-
   (drule_all ALOOKUP_LIST_REL_loc_rel
    \\ fs [MEM_MAP] \\ reverse (rw [])
    \\ fs [MEM_FILTER] >- metis_tac []
    \\ Cases_on ‘p_2’ \\ fs [dest_Delay_def]
    \\ PairCases_on ‘y’
    \\ gvs [dest_anyThunk_def])
  \\ Cases_on ‘~is_Delay p_2’ \\ gvs []
  >-
   (‘f1 ++ (p_1,p_2)::f = (f1 ++ [(p_1,p_2)]) ++ f’ by fs [APPEND_ASSOC]
    \\ full_simp_tac std_ss []
    \\ last_x_assum irule
    \\ last_x_assum $ irule_at Any \\ fs [])
  \\ PairCases_on ‘y’ \\ gvs []
  \\ ‘f1 ++ (p_1,p_2)::f = (f1 ++ [(p_1,p_2)]) ++ f’ by fs [APPEND_ASSOC]
  \\ full_simp_tac std_ss []
  \\ last_x_assum irule
  \\ last_x_assum $ irule_at Any \\ fs []
QED

Triviality LIST_REL_loc_rel_alt =
  Q.SPECL [‘f’,‘locs’,‘[]’] LIST_REL_loc_rel_alt_lemma |> REWRITE_RULE [APPEND];

Triviality LIST_REL_loc_rel:
  ALL_DISTINCT (MAP FST f) ∧
  LIST_REL (loc_rel p l f) (FILTER ((λx. is_Delay x) ∘ SND) f) locs ∧
  ALOOKUP locs s = SOME v2 ∧
  ALOOKUP f s = SOME (Delay x2) ⇒
  loc_rel p l f (s,x2) (s,v2)
Proof
  strip_tac
  \\ drule_all LIST_REL_loc_rel_alt
  \\ fs []
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
  reverse (Cases_on ‘v1’
           \\ fs [dest_anyThunk_def,dest_Thunk_def,AllCaseEqs()])
  >-
   (simp [Once v_rel_cases]
    \\ fs [dest_anyThunk_def,dest_Thunk_def,
           dest_anyClosure_def,dest_Closure_def,AllCaseEqs()]
    \\ rw [] \\ gvs []
    \\ gvs [state_rel_def]
    \\ gvs [oEL_THM]
    \\ gvs [LIST_REL_EL_EQN]
    \\ last_x_assum drule
    \\ fs [thunk_rel_def]
    \\ strip_tac \\ fs []
    \\ rpt (first_x_assum $ irule_at Any))
  \\ simp [Once v_rel_cases] \\ rw []
  >- (drule_all alistTheory.ALOOKUP_ALL_DISTINCT_MEM \\ fs [])
  \\ drule_all LIST_REL_loc_rel
  \\ strip_tac \\ gvs []
  \\ gvs [state_rel_def]
  \\ gvs [oEL_THM]
  \\ qpat_x_assum ‘LIST_REL (thunk_rel p) p ss’ mp_tac
  \\ simp [LIST_REL_EL_EQN]
  \\ strip_tac
  \\ first_x_assum drule \\ fs []
  \\ PairCases_on ‘r’
  \\ fs [thunk_rel_def]
  \\ gvs [dest_anyThunk_def]
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

Triviality IMP_ALOOKUP_FILTER:
  ∀xs x y P.
    ALOOKUP xs x = SOME y ∧ P (x,y) ⇒
    ALOOKUP (FILTER P xs) x = SOME y
Proof
  Induct \\ fs [FORALL_PROD] \\ rw [] \\ gvs []
QED

Triviality ALOOKUP_LIST_REL:
  ∀tfns n x r sfns.
    ALOOKUP tfns n = SOME x ∧ ALL_DISTINCT (MAP FST sfns) ∧
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL r (MAP SND tfns) (MAP SND sfns) ⇒
    ∃y. r x y ∧ ALOOKUP sfns n = SOME y
Proof
  Induct \\ fs [FORALL_PROD]
  \\ rw [] \\ gvs []
  \\ Cases_on ‘sfns’ \\ gvs [] \\ PairCases_on ‘h’ \\ gvs []
QED

Triviality ALOOKUP_LIST_REL_loc_rel:
  ∀tfns locs x1 x2 x3 n x y.
    LIST_REL (loc_rel x1 x2 x3) tfns locs ∧
    ALOOKUP tfns n = SOME x ∧
    ALOOKUP locs n = SOME y ⇒
    loc_rel x1 x2 x3 (n,x) (n,y)
Proof
  Induct \\ fs [FORALL_PROD] \\ rw [] \\ gvs []
  \\ PairCases_on ‘y'’ \\ gvs []
  \\ first_x_assum drule_all
  \\ strip_tac \\ fs []
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
  \\ rpt conj_tac
  >~ [‘LIST_REL (thunk_rel p) p (LUPDATE [True_v; v2] loc ss2)’,‘Thunk’]
  >- (qpat_x_assum ‘LIST_REL _ _ _’ kall_tac
      \\ fs [LIST_REL_EL_EQN]
      \\ gvs [EL_LUPDATE,dest_anyThunk_def]
      \\ rw [] \\ gvs []
      \\ fs [thunk_rel_def]
      \\ rpt (first_x_assum $ irule_at Any))
  >~ [‘Thunk’]
  >- (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
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
      \\ Induct \\ fs [LUPDATE_DEF] \\ Cases_on ‘ss2’ \\ fs []
      \\ Cases_on ‘loc’ \\ fs [LUPDATE_DEF]
      \\ rw [] \\ fs [])
  >~ [‘LIST_REL (thunk_rel p) p (LUPDATE [True_v; v2] loc ss2)’]
  >- (qpat_x_assum ‘LIST_REL (thunk_rel p) p ss2’ mp_tac
      \\ simp [LIST_REL_EL_EQN] \\ rw []
      \\ gvs [EL_LUPDATE,dest_anyThunk_def,AllCaseEqs()]
      \\ rw [] \\ gvs []
      \\ first_x_assum drule
      \\ Cases_on ‘EL loc p’ \\ fs [thunk_rel_def]
      \\ PairCases_on ‘x’ \\ fs [thunk_rel_def]
      \\ qpat_x_assum ‘ALOOKUP f n' = SOME (Delay te)’ assume_tac
      \\ drule IMP_ALOOKUP_FILTER
      \\ disch_then $ qspec_then ‘((λx. is_Delay x) ∘ SND)’ mp_tac
      \\ impl_tac >- fs [dest_Delay_def]
      \\ strip_tac
      \\ drule_all ALOOKUP_LIST_REL_loc_rel
      \\ simp [dest_anyThunk_def,oEL_THM]
      \\ reverse (rpt strip_tac) \\ gvs []
      \\ last_x_assum $ irule_at $ Pos hd \\ fs [])
  \\ qpat_x_assum ‘LIST_REL (thunk_rel p) p ss2’ mp_tac
  \\ simp [Once LIST_REL_EL_EQN] \\ rw []
  \\ gvs [EL_LUPDATE,dest_anyThunk_def,AllCaseEqs()]
  \\ rw [] \\ gvs []
  \\ qpat_x_assum ‘ALOOKUP f n' = SOME (Delay te)’ assume_tac
  \\ drule IMP_ALOOKUP_FILTER
  \\ disch_then $ qspec_then ‘((λx. is_Delay x) ∘ SND)’ mp_tac
  \\ impl_tac >- fs [dest_Delay_def]
  \\ strip_tac
  \\ drule_all ALOOKUP_LIST_REL_loc_rel
  \\ gvs [oEL_THM] \\ strip_tac
  \\ qpat_x_assum ‘LIST_REL (LIST_REL _) _ _’ mp_tac
  \\ match_mp_tac (METIS_PROVE [] “p = q ⇒ x p ⇒ x q”)
  \\ AP_TERM_TAC
  \\ pop_assum mp_tac
  \\ qpat_x_assum ‘LENGTH p = LENGTH ss2’ mp_tac
  \\ qid_spec_tac ‘loc’
  \\ qid_spec_tac ‘ss2’
  \\ qid_spec_tac ‘p’
  \\ rpt (pop_assum kall_tac)
  \\ Induct \\ fs [LUPDATE_DEF] \\ Cases_on ‘ss2’ \\ fs []
  \\ Cases_on ‘loc’ \\ fs [LUPDATE_DEF]
  \\ rw [] \\ fs []
QED

Theorem imp_env_rel_cons:
  v_rel p x y ∧ env_rel p x1 y1 ⇒
  env_rel p ((m,x)::x1) ((m,y)::y1)
Proof
  fs [env_rel_def] \\ rw [] \\ rw [] \\ fs []
QED

Theorem imp_env_rel_opt_bind:
  v_rel p x y ∧ m = n ∧ env_rel p x1 y1 ⇒
  env_rel p (opt_bind m x x1) (opt_bind n y y1)
Proof
  Cases_on ‘m’ \\ rw [] \\ gvs [opt_bind_def]
  \\ irule imp_env_rel_cons \\ fs []
QED

Theorem state_rel_array:
  state_rel p (SOME ts) (SOME ss) ∧
  find_loc n p = SOME n1 ∧ oEL n ts = SOME ta ⇒
  ∃sa.
    oEL n1 ss = SOME sa ∧ LIST_REL (v_rel p) ta sa ∧
    ∀i x y.
      i < LENGTH ta ∧ v_rel p x y ⇒
      state_rel p (SOME (LUPDATE (LUPDATE x i ta) n ts))
                  (SOME (LUPDATE (LUPDATE y i sa) n1 ss))
Proof
  fs [state_rel_def,GSYM CONJ_ASSOC]
  \\ qsuff_tac ‘∀q p ss ts n n1 ta.
   LIST_REL (thunk_rel q) p ss ∧
   LIST_REL (LIST_REL (v_rel q)) ts
     (MAP SND (FILTER (λx. FST x = NONE) (ZIP (p,ss)))) ∧
   find_loc n p = SOME n1 ∧ oEL n ts = SOME ta ⇒
   ∃sa.
     oEL n1 ss = SOME sa ∧ LIST_REL (v_rel q) ta sa ∧
     ∀i x y.
       i < LENGTH ta ∧ v_rel q x y ⇒
       LIST_REL (thunk_rel q) p (LUPDATE (LUPDATE y i sa) n1 ss) ∧
       LIST_REL (LIST_REL (v_rel q)) (LUPDATE (LUPDATE x i ta) n ts)
         (MAP SND
            (FILTER (λx. FST x = NONE)
               (ZIP (p,LUPDATE (LUPDATE y i sa) n1 ss))))’
  THEN1 (metis_tac [])
  \\ gen_tac
  \\ Induct \\ Cases_on ‘ss’ \\ fs [find_loc_def]
  \\ reverse Cases \\ fs [] \\ rpt gen_tac \\ strip_tac \\ gvs []
  THEN1
   (last_x_assum drule_all \\ strip_tac
    \\ fs [GSYM ADD1,oEL_def,LUPDATE_DEF]
    \\ metis_tac [])
  \\ reverse (Cases_on ‘n’) \\ gvs [oEL_def]
  >- fs [GSYM ADD1,oEL_def,LUPDATE_DEF]
  \\ fs [thunk_rel_def,LUPDATE_DEF]
  \\ rw []
  \\ irule_at Any listTheory.EVERY2_LUPDATE_same \\ fs []
QED

Theorem get_atoms_imp:
  ∀a x. get_atoms a = SOME x ⇒ a = MAP Atom x
Proof
  Induct \\ fs [get_atoms_def]
  \\ Cases \\ fs [get_atoms_def] \\ rw [] \\ gvs []
QED

Theorem eval_op_Loc:
  eval_op a x = SOME y ∧ (∀l. a ≠ Lit (Loc l)) ⇒
  EVERY (λv. ∀l. v ≠ Loc l) x ∧ ∀v l. y = INL v ⇒ v ≠ Loc l
Proof
  simp [DefnBase.one_line_ify NONE eval_op_def, AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘z’
  \\ qid_spec_tac ‘x’
  \\ Induct \\ fs []
  \\ Cases \\ fs [concat_def,implode_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem v_rel_Atom[local]:
  ∀x svs.
    LIST_REL (v_rel p) (MAP Atom x) svs ∧ EVERY (λv. ∀l. v ≠ Loc l) x ⇒
    svs = MAP Atom x
Proof
   Induct \\ fs [PULL_EXISTS] \\ Cases \\ fs []
   \\ simp [Once v_rel_cases] \\ fs []
QED

Theorem application_thm:
  application op tenv tvs ts tk = (t_0,t_1,t_2) ∧
  application op senv svs (SOME ss) sk = (s_0,s_1,s_2) ∧
  state_rel p (pick_opt zs ts) (SOME ss) ∧
  op ≠ AppOp ∧ (∀l. op ≠ AtomOp (Lit (Loc l))) ∧
  LIST_REL (v_rel p) tvs svs ∧ env_rel p tenv senv ∧
  num_args_ok op (LENGTH svs) ∧ cont_rel p tk sk ⇒
  t_0 = Error ∨
  ∃q ss1.
    s_1 = SOME ss1 ∧
    cont_rel (p++q) t_2 s_2 ∧
    state_rel (p++q) (pick_opt zs t_1) (SOME ss1) ∧
    step_res_rel (p++q) t_0 s_0
Proof
  Cases_on ‘t_0 = Error’ \\ asm_rewrite_tac []
  \\ Cases_on ‘op = Ref’ \\ rw [] THEN1
   (gvs [application_def,get_atoms_def]
    \\ fs [value_def,error_def]
    \\ Cases_on ‘ts’ \\ gvs []
    \\ qexists_tac ‘[NONE]’
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ irule_at Any cont_rel_ext \\ simp []
    \\ irule_at Any v_rel_Ref \\ simp [GSYM SNOC_APPEND]
    \\ simp [Once SNOC_APPEND]
    \\ irule_at Any state_rel_Ref \\ simp [])
  \\ Cases_on ‘op = Alloc’ \\ rw [] THEN1
   (gvs [application_def,LENGTH_EQ_NUM_compute,error_def,value_def]
    \\ ntac 4 $ pop_assum mp_tac \\ simp [Once v_rel_cases]
    \\ gvs [AllCaseEqs(),SNOC_APPEND]
    \\ rpt strip_tac \\ qexists_tac ‘[NONE]’ \\ gvs [step_res_rel_cases]
    \\ irule_at Any cont_rel_ext \\ simp []
    \\ irule_at Any v_rel_Ref \\ simp [GSYM SNOC_APPEND]
    \\ simp [Once SNOC_APPEND]
    \\ irule_at Any state_rel_Ref \\ simp []
    \\ fs [LIST_REL_REPLICATE_same])
  \\ qexists_tac ‘[]’ \\ fs []
  \\ Cases_on ‘∃k. op = Cons k’ \\ rw [] THEN1
   (gvs [application_def,get_atoms_def,value_def,error_def]
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ simp [Once v_rel_cases])
  \\ Cases_on ‘∃s. op = FFI s’ \\ rw [] THEN1
   (gvs [application_def,LENGTH_EQ_NUM_compute,error_def,value_def]
    \\ ntac 4 $ pop_assum mp_tac \\ simp [Once v_rel_cases]
    \\ gvs [AllCaseEqs()] \\ rpt strip_tac
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs [])
  \\ Cases_on ‘op = Sub ∨ op = UnsafeSub ∨ op = Length ∨
               op = Update ∨ op = UnsafeUpdate’ THEN1
   (gvs [application_def,LENGTH_EQ_NUM_compute,error_def,value_def]
    \\ Cases_on ‘x’ \\ gvs []
    \\ Cases_on ‘l’ \\ gvs []
    \\ TRY (Cases_on ‘x'’ \\ gvs [])
    \\ TRY (Cases_on ‘l’ \\ gvs [])
    \\ Cases_on ‘ts’ \\ gvs []
    \\ rpt (qpat_x_assum ‘v_rel _ (Atom _) _’ mp_tac)
    \\ once_rewrite_tac [v_rel_cases] \\ simp []
    \\ rpt strip_tac \\ gvs []
    \\ Cases_on ‘oEL n x’ \\ fs [continue_def]
    \\ drule_all state_rel_array \\ strip_tac \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ gvs [AllCaseEqs(),step_res_rel_cases,LIST_REL_EL_EQN]
    \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs []
    \\ simp [Once v_rel_cases]
    \\ ntac 3 (simp [Once compile_rel_cases]))
  \\ Cases_on ‘∃s n. op = IsEq s n’ \\ rw [] THEN1
   (gvs [application_def,LENGTH_EQ_NUM_compute,error_def,value_def]
    \\ ntac 4 $ pop_assum mp_tac \\ simp [Once v_rel_cases]
    \\ gvs [AllCaseEqs()] \\ rpt strip_tac \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ simp [Once v_rel_cases] \\ rw [])
  \\ Cases_on ‘∃s n. op = Proj s n’ \\ rw [] THEN1
   (gvs [application_def,LENGTH_EQ_NUM_compute,error_def,value_def]
    \\ ntac 4 $ pop_assum mp_tac \\ simp [Once v_rel_cases]
    \\ gvs [AllCaseEqs()] \\ rpt strip_tac \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ gvs [LIST_REL_EL_EQN])
  \\ Cases_on ‘op’ \\ gvs []
  \\ rename [‘AtomOp a’]
  \\ gvs [application_def,error_def]
  \\ Cases_on ‘get_atoms tvs’ \\ gvs []
  \\ Cases_on ‘eval_op a x’ \\ gvs [value_def]
  \\ ‘s_1 = SOME ss ∧ t_1 = ts ∧ t_2 = tk ∧ s_2 = sk’ by gvs [AllCaseEqs()]
  \\ gvs [] \\ imp_res_tac get_atoms_imp \\ gvs []
  \\ drule_all eval_op_Loc
  \\ strip_tac
  \\ drule_all v_rel_Atom \\ strip_tac \\ gvs []
  \\ gvs [AllCaseEqs(),step_res_rel_cases]
  \\ simp [Once v_rel_cases]
QED

Definition make_let_env_def:
  make_let_env [] n env = env ∧
  make_let_env (x::xs) n env = make_let_env xs (n+1) ((FST x,Atom (Loc n))::env)
End

Theorem step_n_Lets_some_ref_bool:
  ∀delays env n ss.
    step_n n (Exp env (Lets (MAP some_ref_bool delays) x),SOME ss,sk) = (sr1,ss1,sk1) ∧
    is_halt (sr1,ss1,sk1) ⇒
    ∃m. m ≤ n ∧
      step_n m (Exp (make_let_env delays (LENGTH ss) env) x,
        SOME (ss ++ MAP (λ(v,b,y). [Bool_v b; Bool_v b]) delays),sk) =
          (sr1,ss1,sk1)
Proof
  Induct \\ fs [Lets_def,make_let_env_def] \\ rw []
  >- (first_x_assum $ irule_at Any \\ fs [])
  \\ PairCases_on ‘h’ \\ gvs [some_ref_bool_def,Lets_def]
  \\ qpat_x_assum ‘step_n _ _ = _’ mp_tac
  \\ Cases_on ‘h1’ \\ fs []
  \\ ntac 7 (rename [‘step_n nn’] \\ Cases_on ‘nn’ \\ fs []
             >- (rw [] \\ fs [is_halt_def])
             \\ rewrite_tac [step_n_add,ADD1] \\ simp [step])
  \\ strip_tac \\ last_x_assum drule
  \\ strip_tac \\ qexists_tac ‘m’ \\ fs []
  \\ gvs [SNOC_APPEND,ADD1]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
QED

Theorem Letrec_split_EVERY:
  ∀xs delays funs.
    Letrec_split vs xs = (delays, funs) ⇒
    EVERY (λ(v,b,x). b = Letrec_imm vs x) delays
Proof
  Induct \\ fs [Letrec_split_def]
  \\ Cases \\ fs [Letrec_split_def]
  \\ pairarg_tac \\ fs []
  \\ CASE_TAC \\ fs []
QED

Theorem Letrec_split_ALL_DISTINCT:
  ∀xs delays funs.
    Letrec_split vs xs = (delays, funs) ∧ ALL_DISTINCT (MAP FST xs) ⇒
    (set (MAP FST delays)) UNION (set (MAP FST funs)) = set (MAP FST xs) ∧
    ALL_DISTINCT (MAP FST delays) ∧
    ALL_DISTINCT (MAP FST funs) ∧
    DISJOINT (set (MAP FST delays)) (set (MAP FST funs))
Proof
  Induct \\ fs [Letrec_split_def]
  \\ Cases \\ fs [Letrec_split_def]
  \\ pairarg_tac \\ fs []
  \\ CASE_TAC \\ fs [ALL_DISTINCT_APPEND]
  \\ rw [] \\ fs [EXTENSION,IN_DISJOINT]
  \\ metis_tac []
QED

Theorem ALOOKUP_make_let_env:
  ∀delays h env n.
    ALOOKUP delays h = NONE ⇒
    ALOOKUP (make_let_env delays n env) h = ALOOKUP env h
Proof
  Induct
  \\ fs [make_let_env_def,FORALL_PROD] \\ rw [] \\ gs []
QED

Definition Letrec_store_def:
  Letrec_store env (v,b,y) =
    if ~b then [False_v; Closure NONE env y] else
      case y of
      | Var w   => [True_v; THE (ALOOKUP env w)]
      | Lam w e => [True_v; Closure w env e]
      | _       => [False_v; Closure NONE env y]
End

Theorem Letrec_store_thm:
  ∀delays ss env2 n.
    EVERY (λ(v,b,x). b ⇔ Letrec_imm (MAP FST (sfns: (string # exp) list)) x) delays ∧
    ALL_DISTINCT (MAP FST delays) ∧ is_halt (sr1,ss1,sk1) ∧
    DISJOINT (set (MAP FST delays)) (set (MAP FST (funs: (string # exp) list))) ∧
    EVERY (λ(n,x). ~MEM n (MAP FST env1)) delays ∧
    EVERY (λn. ALOOKUP (env1 ++ make_let_env delays (LENGTH ss) env2) n ≠ NONE)
      (MAP FST sfns) ∧
    step_n n (Exp (env1 ++ make_let_env delays (LENGTH ss) env2)
                (Lets (MAP unsafe_update delays) se),
              SOME (ss ++ MAP (λ(v,b,y). [Bool_v b; Bool_v b]) delays),sk) =
          (sr1,ss1,sk1) ⇒
    ∃k. k ≤ n ∧
      let env3 = env1 ++ make_let_env delays (LENGTH ss) env2 in
        step_n k (Exp env3 se, SOME (ss ++ MAP (Letrec_store env3) delays),sk) =
              (sr1,ss1,sk1)
Proof
  Induct \\ fs [Lets_def]
  >- (rw [] \\ qexists_tac ‘n’ \\ fs [])
  \\ gen_tac \\ PairCases_on ‘h’ \\ fs []
  \\ gvs [unsafe_update_def,Lets_def,make_let_env_def]
  \\ rpt gen_tac \\ strip_tac
  \\ pop_assum mp_tac
  \\ ntac 2 (rename [‘step_n nn’] \\ Cases_on ‘nn’
             >- (rw [] \\ fs [is_halt_def]) \\ fs []
             \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
  \\ reverse IF_CASES_TAC
  >-
    (ntac 5 (rename [‘step_n nn’] \\ Cases_on ‘nn’
             >- (rw [] \\ fs [is_halt_def]) \\ fs []
             \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
     \\ fs [ALOOKUP_APPEND,GSYM ALOOKUP_NONE,ALOOKUP_make_let_env]
     \\ ntac 1 (rename [‘step_n nn’] \\ Cases_on ‘nn’
                >- (rw [] \\ fs [is_halt_def]) \\ fs []
                \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
     \\ gvs [oEL_THM,EL_APPEND2]
     \\ ntac 1 (rename [‘step_n nn’] \\ Cases_on ‘nn’
                >- (rw [] \\ fs [is_halt_def]) \\ fs []
                \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
     \\ gvs [ADD1,LUPDATE_DEF]
     \\ qmatch_goalsub_abbrev_tac ‘ss ++ s1::_’
     \\ strip_tac \\ last_x_assum $ qspec_then ‘ss ++ [s1]’ mp_tac
     \\ gvs [] \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
     \\ disch_then $ drule_at $ Pos last
     \\ impl_tac >- fs []
     \\ strip_tac \\ qexists_tac ‘k’ \\ fs [Letrec_store_def])
  \\ Cases_on ‘∃v3 e3. h2 = Lam v3 e3’ \\ gvs []
  >-
    (ntac 5 (rename [‘step_n nn’] \\ Cases_on ‘nn’
             >- (rw [] \\ fs [is_halt_def]) \\ fs []
             \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
     \\ fs [ALOOKUP_APPEND,GSYM ALOOKUP_NONE,ALOOKUP_make_let_env]
     \\ ntac 1 (rename [‘step_n nn’] \\ Cases_on ‘nn’
                >- (rw [] \\ fs [is_halt_def]) \\ fs []
                \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
     \\ gvs [oEL_THM,EL_APPEND2]
     \\ ntac 1 (rename [‘step_n nn’] \\ Cases_on ‘nn’
                >- (rw [] \\ fs [is_halt_def]) \\ fs []
                \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
     \\ gvs [ADD1,LUPDATE_DEF]
     \\ qmatch_goalsub_abbrev_tac ‘ss ++ s1::_’
     \\ strip_tac \\ last_x_assum $ qspec_then ‘ss ++ [s1]’ mp_tac
     \\ gvs [] \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
     \\ disch_then $ drule_at $ Pos last
     \\ impl_tac >- fs []
     \\ strip_tac \\ qexists_tac ‘k’ \\ fs [Letrec_store_def])
  \\ Cases_on ‘h2’ \\ gvs [Letrec_imm_def]
  \\ rename [‘Var vv’]
  \\ qpat_assum ‘EVERY _ _’ (fn th => drule (REWRITE_RULE [EVERY_MEM] th))
  \\ simp []
  \\ Cases_on ‘ALOOKUP (env1 ++
           make_let_env delays (LENGTH ss + 1)
             ((h0,Atom (Loc (LENGTH ss)))::env2)) vv’ \\ fs []
  \\ ntac 5 (rename [‘step_n nn’] \\ Cases_on ‘nn’
             >- (rw [] \\ fs [is_halt_def]) \\ fs []
             \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
  \\ fs [ALOOKUP_APPEND,GSYM ALOOKUP_NONE,ALOOKUP_make_let_env]
  \\ ntac 1 (rename [‘step_n nn’] \\ Cases_on ‘nn’
             >- (rw [] \\ fs [is_halt_def]) \\ fs []
             \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
  \\ gvs [oEL_THM,EL_APPEND2]
  \\ ntac 1 (rename [‘step_n nn’] \\ Cases_on ‘nn’
             >- (rw [] \\ fs [is_halt_def]) \\ fs []
             \\ rewrite_tac [step_n_add,ADD1] \\ simp [step,get_atoms_def])
  \\ gvs [ADD1,LUPDATE_DEF]
  \\ qmatch_goalsub_abbrev_tac ‘ss ++ s1::_’
  \\ strip_tac \\ last_x_assum $ qspec_then ‘ss ++ [s1]’ mp_tac
  \\ gvs [] \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ disch_then $ drule_at $ Pos last
  \\ impl_tac >- fs []
  \\ strip_tac \\ qexists_tac ‘k’ \\ fs [Letrec_store_def]
  \\ gvs [ALOOKUP_APPEND]
QED

Triviality step_n_unwind:
  step_n (m+1) s = x ∧ n = m + 1 ⇒ step_n n s = x
Proof
  rw []
QED

Theorem Letrec_store_forward:
  ∀delays ss env2 n k.
    EVERY (λ(v,b,x). b ⇔ Letrec_imm (MAP FST (sfns: (string # exp) list)) x) delays ∧
    ALL_DISTINCT (MAP FST delays) ∧ is_halt (sr1,ss1,sk1) ∧
    DISJOINT (set (MAP FST delays)) (set (MAP FST (funs: (string # exp) list))) ∧
    EVERY (λ(n,x). ~MEM n (MAP FST env1)) delays ∧
    EVERY (λn. ALOOKUP (env1 ++ make_let_env delays (LENGTH ss) env2) n ≠ NONE)
          (MAP FST sfns) ∧
    (let env3 = env1 ++ make_let_env delays (LENGTH ss) env2 in
       step_n k (Exp env3 se, SOME (ss ++ MAP (Letrec_store env3) delays),sk) =
         (sr1,ss1,sk1)) ∧ n = k + 9 * LENGTH delays ⇒
    step_n n (Exp (env1 ++ make_let_env delays (LENGTH ss) env2)
                (Lets (MAP unsafe_update delays) se),
              SOME (ss ++ MAP (λ(v,b,y). [Bool_v b; Bool_v b]) delays),sk) =
          (sr1,ss1,sk1)
Proof
  Induct \\ fs [Lets_def]
  \\ gen_tac \\ PairCases_on ‘h’ \\ fs []
  \\ gvs [unsafe_update_def,Lets_def,make_let_env_def]
  \\ rpt gen_tac \\ strip_tac
  \\ irule_at Any step_n_unwind
  \\ once_rewrite_tac [step_n_add] \\ fs [step]
  \\ irule_at Any step_n_unwind
  \\ once_rewrite_tac [step_n_add] \\ fs [step]
  \\ reverse IF_CASES_TAC
  >- (
    ntac 5 (irule_at Any step_n_unwind
            \\ once_rewrite_tac [step_n_add] \\ fs [step, get_atoms_def])
    \\ fs [ALOOKUP_APPEND,GSYM ALOOKUP_NONE,ALOOKUP_make_let_env]
    \\ ntac 1 (irule_at Any step_n_unwind
               \\ once_rewrite_tac [step_n_add] \\ fs [step,get_atoms_def])
    \\ gvs [oEL_THM,EL_APPEND2]
    \\ ntac 1 (irule_at Any step_n_unwind
               \\ once_rewrite_tac [step_n_add] \\ fs [step,get_atoms_def])
    \\ gvs [ADD1,LUPDATE_DEF]
    \\ qmatch_goalsub_abbrev_tac ‘ss ++ s1::_’
    \\ last_x_assum $ qspec_then ‘ss ++ [s1]’ mp_tac
    \\ gvs [] \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ simp [LEFT_ADD_DISTRIB] \\ simp_tac std_ss [ADD_ASSOC]
    \\ disch_then $ qspecl_then [‘(h0,Atom (Loc (LENGTH ss)))::env2’,‘k’] mp_tac
    \\ impl_tac >- fs [Letrec_store_def]
    \\ strip_tac \\ fs [])
  \\ Cases_on ‘∃v3 e3. h2 = Lam v3 e3’ \\ gvs []
  >- (
    ntac 5 (irule_at Any step_n_unwind
            \\ once_rewrite_tac [step_n_add] \\ fs [step, get_atoms_def])
    \\ fs [ALOOKUP_APPEND,GSYM ALOOKUP_NONE,ALOOKUP_make_let_env]
    \\ ntac 1 (irule_at Any step_n_unwind
               \\ once_rewrite_tac [step_n_add] \\ fs [step,get_atoms_def])
    \\ gvs [oEL_THM,EL_APPEND2]
    \\ ntac 1 (irule_at Any step_n_unwind
               \\ once_rewrite_tac [step_n_add] \\ fs [step,get_atoms_def])
    \\ gvs [ADD1,LUPDATE_DEF]
    \\ qmatch_goalsub_abbrev_tac ‘ss ++ s1::_’
    \\ last_x_assum $ qspec_then ‘ss ++ [s1]’ mp_tac
    \\ gvs [] \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ simp [LEFT_ADD_DISTRIB] \\ simp_tac std_ss [ADD_ASSOC]
    \\ disch_then $ qspecl_then [‘(h0,Atom (Loc (LENGTH ss)))::env2’,‘k’] mp_tac
    \\ impl_tac >- fs [Letrec_store_def]
    \\ strip_tac \\ fs [])
  \\ Cases_on ‘h2’ \\ gvs [Letrec_imm_def]
  \\ rename [‘Var vv’]
  \\ qpat_assum ‘EVERY _ _’ (fn th => drule (REWRITE_RULE [EVERY_MEM] th))
  \\ simp []
  \\ Cases_on ‘ALOOKUP (env1 ++
           make_let_env delays (LENGTH ss + 1)
             ((h0,Atom (Loc (LENGTH ss)))::env2)) vv’ \\ fs []
  \\ ntac 5 (irule_at Any step_n_unwind
             \\ once_rewrite_tac [step_n_add] \\ fs [step, get_atoms_def])
  \\ fs [ALOOKUP_APPEND,GSYM ALOOKUP_NONE,ALOOKUP_make_let_env]
  \\ ntac 1 (irule_at Any step_n_unwind
             \\ once_rewrite_tac [step_n_add] \\ fs [step,get_atoms_def])
  \\ gvs [oEL_THM,EL_APPEND2]
  \\ ntac 1 (irule_at Any step_n_unwind
             \\ once_rewrite_tac [step_n_add] \\ fs [step,get_atoms_def])
  \\ gvs [ADD1,LUPDATE_DEF]
  \\ qmatch_goalsub_abbrev_tac ‘ss ++ s1::_’
  \\ last_x_assum $ qspec_then ‘ss ++ [s1]’ mp_tac
  \\ gvs [] \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ simp [LEFT_ADD_DISTRIB] \\ simp_tac std_ss [ADD_ASSOC]
  \\ disch_then $ qspecl_then [‘(h0,Atom (Loc (LENGTH ss)))::env2’,‘k’] mp_tac
  \\ disch_then irule
  \\ gvs [Letrec_store_def,ALOOKUP_APPEND]
QED

Theorem MEM_make_let_env:
  ∀delays k env x.
    MEM x (MAP FST (make_let_env delays k env)) ⇔
    MEM x (MAP FST delays) ∨ MEM x (MAP FST env)
Proof
  Induct \\ fs [make_let_env_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Triviality EVERY_LAM:
  ∀xs. EVERY (λ(n,x). f n) xs = EVERY f (MAP FST xs)
Proof
  Induct \\ fs [FORALL_PROD]
QED

Triviality FST_INTRO:
  (λ(p1,p2). p1) = FST
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem env_rel_append:
  ∀xs ys xs1 ys1.
    env_rel p xs1 ys1 ∧ env_rel p xs ys ∧ set (MAP FST xs) = set (MAP FST ys) ⇒
    env_rel p (xs ++ xs1) (ys ++ ys1)
Proof
  rw [env_rel_def,ALOOKUP_APPEND]
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  \\ first_x_assum $ irule_at $ Pos last
  \\ gvs [ALOOKUP_NONE,EXTENSION]
QED

Triviality LIST_REL_loc_rel_MAP_FST:
  ∀xs ys. LIST_REL (loc_rel p tenv tfns) xs ys ⇒ MAP FST xs = MAP FST ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs [] \\ Cases \\ Cases_on ‘h’ \\ fs []
  \\ rw [] \\ fs []
QED

Triviality ALOOUKP_MAP_Rec:
  ∀tfns n.
    ALOOKUP (MAP (λ(fn,x). (fn,Recclosure y tenv fn)) tfns) n = SOME tv ⇔
    MEM n (MAP FST tfns) ∧ tv = Recclosure y tenv n
Proof
  Induct \\ fs [FORALL_PROD] \\ rw [] \\ eq_tac \\ rw []
QED

Triviality LIST_REL_letrec_rel_Lam:
  ∀tfns sfns.
    LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ∧
    MEM k (MAP FST (FILTER (λ(p1,p2). is_Lam p2) sfns)) ∧
    MAP FST tfns = MAP FST sfns ⇒
    ∃v' e'. MEM (k,Lam v' e') tfns
Proof
  Induct \\ fs [PULL_EXISTS,FORALL_PROD]
  \\ Cases_on ‘sfns’ \\ fs []
  \\ PairCases_on ‘h’ \\ fs []
  \\ simp [Once compile_rel_cases]
  \\ gen_tac \\ strip_tac \\ gvs [dest_Lam_def]
  >- (first_x_assum drule \\ fs [])
  \\ metis_tac []
QED

Triviality LIST_REL_letrec_rel_Delay:
  ∀tfns sfns.
    LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ∧
    ~MEM k (MAP FST (FILTER (λ(p1,p2). is_Lam p2) sfns)) ∧
    MAP FST tfns = MAP FST sfns ∧ MEM k (MAP FST sfns) ⇒
    ∃e'. MEM (k,Delay e') tfns
Proof
  Induct \\ fs [PULL_EXISTS,FORALL_PROD]
  \\ Cases_on ‘sfns’ \\ fs []
  \\ PairCases_on ‘h’ \\ fs []
  \\ simp [Once compile_rel_cases]
  \\ gen_tac \\ strip_tac \\ gvs [dest_Lam_def]
  \\ metis_tac []
QED

Triviality ALL_DISTINCT_MAP_FILTER:
  ∀xs. ALL_DISTINCT (MAP f xs) ⇒ ALL_DISTINCT (MAP f (FILTER p xs))
Proof
  Induct \\ fs [] \\ rw []
  \\ res_tac \\ fs []
  \\ gvs [MEM_MAP,MEM_FILTER]
QED

Triviality LIST_REL_loc_rel_Delay:
  ∀tfns locs.
    LIST_REL (loc_rel p tenv xx) (FILTER (λ(p1,p2). is_Delay p2) tfns) locs ∧
    MEM (k,Delay e) tfns ⇒
    MEM k (MAP FST locs)
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ TRY (PairCases_on ‘y’ \\ gvs [])
  \\ fs [dest_Delay_def]
QED

Theorem dest_anyClosure_v_rel:
  dest_anyClosure v1 = SOME (x0,x1,x2) ∧
  v_rel p v1 v2 ∧ state_rel p (pick_opt zs ts) (SOME ss) ⇒
  ∃y1 y2.
    dest_anyClosure v2 = SOME (x0,y1,y2) ∧
    compile_rel x2 y2 ∧ env_rel p x1 y1
Proof
  simp [Once v_rel_cases] \\ reverse (rw []) \\ gvs []
  >~ [‘Closure’] >- gvs [dest_anyClosure_def]
  \\ gvs [dest_anyClosure_def,AllCaseEqs()]
  >-
   (drule_at (Pos last) LIST_REL_loc_rel_alt
    \\ disch_then $ drule_at $ Pos last \\ fs [])
  \\ drule_all ALOOKUP_LIST_REL
  \\ strip_tac
  \\ qpat_x_assum ‘letrec_rel _ _’ mp_tac
  \\ simp [Once compile_rel_cases] \\ strip_tac \\ gvs []
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any IMP_ALOOKUP_FILTER
  \\ fs [dest_Lam_def]
  \\ irule env_rel_append \\ simp []
  \\ conj_tac
  >-
   (fs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,EXTENSION,MAP_REVERSE]
    \\ fs [FST_INTRO]
    \\ imp_res_tac (GSYM LIST_REL_loc_rel_MAP_FST) \\ fs []
    \\ qpat_x_assum ‘LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns)’ mp_tac
    \\ qpat_x_assum ‘MAP FST tfns = MAP FST sfns’ mp_tac
    \\ qid_spec_tac ‘sfns’
    \\ qid_spec_tac ‘tfns’
    \\ Induct \\ Cases_on ‘sfns’ \\ fs [FORALL_PROD]
    \\ ntac 2 gen_tac \\ Cases \\ fs []
    \\ rename [‘_ = FST hh’] \\ PairCases_on ‘hh’ \\ fs []
    \\ simp [Once compile_rel_cases] \\ rw []
    \\ gvs [dest_Lam_def,dest_Delay_def]
    \\ fs [AC DISJ_COMM DISJ_ASSOC])
  \\ fs [env_rel_def]
  \\ gvs [ALOOUKP_MAP_Rec]
  \\ simp [ALOOKUP_APPEND,AllCaseEqs()]
  \\ gvs [ALOOUKP_MAP_Rec]
  \\ simp [AllCaseEqs(),ALOOKUP_NONE]
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,EXTENSION,MAP_REVERSE,FST_INTRO]
  \\ rw []
  \\ rename [‘MEM k (MAP FST sfns)’]
  \\ Cases_on ‘MEM k (MAP FST (FILTER (λ(p1,p2). is_Lam p2) sfns))’ \\ fs []
  >-
   (simp [Once v_rel_cases] \\ disj1_tac
    \\ simp [combinTheory.o_DEF,LAMBDA_PROD]
    \\ ‘REVERSE locs ++ senv = REVERSE locs ++ senv’ by fs []
    \\ pop_assum $ irule_at Any \\ fs []
    \\ qpat_assum ‘LIST_REL letrec_rel _ _’ $ irule_at Any
    \\ fs [env_rel_def]
    \\ rpt $ first_assum $ irule_at Any
    \\ irule LIST_REL_letrec_rel_Lam
    \\ rpt $ first_assum $ irule_at Any)
  \\ simp [Once v_rel_cases]
  \\ irule_at Any (METIS_PROVE [] “c ⇒ b ∨ c”)
  \\ simp [PULL_EXISTS]
  \\ ‘env_rel p tenv senv’ by fs [env_rel_def]
  \\ pop_assum $ irule_at Any
  \\ rpt $ first_assum $ irule_at $ Pos hd
  \\ fs [combinTheory.o_DEF,LAMBDA_PROD]
  \\ rpt $ first_assum $ irule_at $ Pos hd
  \\ drule_all LIST_REL_letrec_rel_Delay
  \\ strip_tac
  \\ ‘ALL_DISTINCT (MAP FST locs)’ by
    (drule (GSYM LIST_REL_loc_rel_MAP_FST)
     \\ fs [] \\ rw [] \\ irule ALL_DISTINCT_MAP_FILTER \\ fs [])
  \\ gvs [alookup_distinct_reverse]
  \\ Cases_on ‘ALOOKUP locs k’ \\ fs []
  \\ fs [ALOOKUP_NONE]
  \\ drule_all LIST_REL_loc_rel_Delay
  \\ fs []
QED

Triviality LIST_REL_LIST_REL_lemma:
  (∀x y. r1 x y ⇒ r2 x y) ∧ ys1 = ys2 ⇒
  LIST_REL r1 xs ys1 ⇒ LIST_REL r2 xs ys2
Proof
  metis_tac [LIST_REL_mono]
QED

Triviality FILTER_ZIP_EQ:
  ∀p ss xs ys.
    LENGTH p = LENGTH ss ∧ EVERY (λx. x ≠ NONE) xs ⇒
    FILTER (λx. FST x = NONE) (ZIP (p,ss)) =
    FILTER (λx. FST x = NONE) (ZIP (p ++ xs,ss ++ ys))
Proof
  reverse Induct \\ Cases_on ‘ss’ \\ fs []
  >- rw []
  \\ Induct \\ fs [ZIP_def]
  \\ Cases_on ‘ys’ \\ fs [ZIP_def]
QED

Theorem MEM_IMP_ALOOKUP:
  ∀xs x y.
    MEM (x,y) xs ∧ ALL_DISTINCT (MAP FST xs) ⇒
    ALOOKUP xs x = SOME y
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ res_tac \\ fs [MEM_MAP]
QED

Theorem Letrec_split_compile_rel:
  ∀sfns tfns vs delays funs.
    Letrec_split vs sfns = (delays,funs) ∧ MAP FST tfns = MAP FST sfns ∧
    LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ⇒
    LIST_REL (λ(n,x) (m,b,y). n = m ∧  Letrec_imm vs y = b ∧
         ∃x'. x = Delay x' ∧ compile_rel x' y)
      (FILTER ((λx. is_Delay x) ∘ SND) tfns) delays
Proof
  Induct \\ fs [Letrec_split_def,FORALL_PROD]
  \\ rw [] \\ Cases_on ‘tfns’ \\ fs []
  \\ PairCases_on ‘h’ \\ gvs []
  \\ qpat_x_assum ‘letrec_rel _ _’ mp_tac
  \\ simp [Once compile_rel_cases] \\ rw [] \\ fs [dest_Delay_def]
  \\ pairarg_tac \\ gvs []
QED

Theorem comp_Letrec_not:
  Lam n x ≠ comp_Letrec sfns se ∧
  Var v ≠ comp_Letrec sfns se
Proof
  fs [comp_Letrec_def]
  \\ pairarg_tac \\ fs []
  \\ Cases_on ‘delays’ \\ fs [Lets_def]
  \\ PairCases_on ‘h’
  \\ fs [some_ref_bool_def,Lets_def]
QED

Theorem make_let_env_lemma:
  ∀xs n env.
    make_let_env xs n env = make_let_env xs n [] ++ env
Proof
  Induct
  \\ rewrite_tac [make_let_env_def,APPEND]
  \\ pop_assum $ once_rewrite_tac o single
  \\ fs []
QED

Triviality MAP_FST_make_let_env:
  ∀delays n env.
    MAP FST (make_let_env delays n env) =
    REVERSE (MAP FST delays) ++ MAP FST env
Proof
  Induct \\ fs [make_let_env_def]
QED

Theorem Letrec_split_MAP_FST:
  ∀sfns delays funs.
    Letrec_split vs sfns = (delays,funs) ⇒
    set (MAP FST sfns) = set (MAP FST funs) ∪ set (MAP FST delays)
Proof
  Induct \\ fs [Letrec_split_def,FORALL_PROD]
  \\ rw [] \\ pairarg_tac \\ fs []
  \\ gvs [AllCaseEqs(),EXTENSION,AC DISJ_COMM DISJ_ASSOC]
QED

Theorem Letrec_split_IMP_FILTER:
  ∀sfns delays funs tfns.
    Letrec_split vs sfns = (delays,funs) ∧
    LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ⇒
    funs = FILTER ((λx. is_Lam x) ∘ SND) sfns
Proof
  Induct
  \\ fs [Letrec_split_def,FORALL_PROD] \\ rw []
  \\ pairarg_tac \\ fs []
  \\ Cases_on ‘tfns’ \\ fs []
  \\ fs [Once compile_rel_cases,dest_Lam_def,dest_Delay_def]
  \\ gvs [dest_Lam_def,dest_Delay_def]
  \\ res_tac \\ fs []
QED

Theorem REVERSE_make_let_env:
  ∀delays n.
    REVERSE (make_let_env delays n []) =
    MAPi (λi x. (FST x, Atom (Loc (n+i)))) delays
Proof
  Induct \\ fs [make_let_env_def,FORALL_PROD]
  \\ simp [Once make_let_env_lemma]
  \\ fs [combinTheory.o_DEF,ADD1]
  \\ rw [] \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [FUN_EQ_THM]
QED

Triviality IMP_Lam:
  ∀tfns sfns.
    MAP FST tfns = MAP FST sfns ∧ MEM (y,Lam v e) sfns ∧
    LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ⇒
    ∃v e. MEM (y,Lam v e) tfns
Proof
  Induct \\ fs [FORALL_PROD]
  \\ Cases_on ‘sfns’ \\ fs []
  \\ PairCases_on ‘h’ \\ fs []
  \\ rw [] \\ fs []
  \\ res_tac \\ fs []
  \\ fs [Once compile_rel_cases]
  \\ metis_tac []
QED

Triviality EXISTS_ALOOKUP_ALOOKUP:
  ∀n xs ys.
    MEM n (MAP FST xs) ∧ ALL_DISTINCT (MAP FST ys) ∧ xs = REVERSE ys ⇒
    ∃v. ALOOKUP xs n = SOME v ∧ ALOOKUP ys n = SOME v
Proof
  gen_tac \\ simp [MAP_REVERSE]
  \\ Induct \\ fs [FORALL_PROD]
  \\ rpt gen_tac \\ IF_CASES_TAC \\ gvs []
  \\ fs [ALOOKUP_APPEND] \\ rw []
  \\ TRY (last_x_assum drule_all)
  \\ rw [] \\ fs [AllCaseEqs()]
  \\ fs [ALOOKUP_NONE,MAP_REVERSE]
QED

Theorem MAPi_MAP:
  ∀f xs. MAPi (λi x. f x) xs = MAP f xs
Proof
  Induct_on ‘xs’ \\ fs [combinTheory.o_DEF]
QED

Theorem Letrec_split_FILTER:
  ∀sfns tfns delays funs vs f.
    Letrec_split vs sfns = (delays,funs) ∧
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ⇒
    MAPi (λi x. (FST x,Atom (Loc (f i)))) delays =
    MAPi (λi x. (FST x,Atom (Loc (f i)))) (FILTER (λ(p1,p2). is_Delay p2) tfns)
Proof
  Induct \\ Cases_on ‘tfns’ \\ fs [Letrec_split_def]
  \\ Cases \\ PairCases_on ‘h’ \\ fs [Letrec_split_def]
  \\ simp [Once compile_rel_cases]
  \\ rpt strip_tac
  \\ gvs [dest_Lam_def, dest_Delay_def, combinTheory.o_DEF, ADD1]
  \\ pairarg_tac \\ gvs [combinTheory.o_DEF, ADD1]
  \\ res_tac \\ fs []
QED

Theorem state_rel_Letrec:
  state_rel p (pick_opt zs ts) (SOME ss) ∧
  env_rel p env1 env2 ∧
  MAP FST tfns = MAP FST sfns ∧
  ALL_DISTINCT (MAP FST sfns) ∧
  LIST_REL letrec_rel (MAP SND tfns) (MAP SND sfns) ∧
  Letrec_split (MAP FST sfns) sfns = (delays,funs) ∧
  EVERY (λ(v,b,x). b ⇔ Letrec_imm (MAP FST sfns) x) delays ∧
  set (MAP FST delays) ∪ set (MAP FST funs) = set (MAP FST sfns) ∧
  ALL_DISTINCT (MAP FST delays) ∧
  ALL_DISTINCT (MAP FST funs) ∧
  DISJOINT (set (MAP FST delays)) (set (MAP FST funs)) ⇒
  state_rel
    (p ++ MAP (λ(fn,_). dest_anyThunk (Recclosure tfns env1 fn))
             (FILTER ((λx. is_Delay x) ∘ SND) tfns)) (pick_opt zs ts)
    (SOME (ss ++ MAP
             (Letrec_store (rec_env funs (make_let_env delays (LENGTH ss) env2)))
                delays)) ∧
  env_rel (p ++ MAP (λ(fn,_). dest_anyThunk (Recclosure tfns env1 fn))
                 (FILTER ((λx. is_Delay x) ∘ SND) tfns)) (rec_env tfns env1)
          (rec_env funs (make_let_env delays (LENGTH ss) env2))
Proof
  fs [state_rel_def]
  \\ strip_tac
  \\ reverse conj_asm2_tac
  >-
   (fs [rec_env_def]
    \\ once_rewrite_tac [make_let_env_lemma] \\ simp []
    \\ irule env_rel_append
    \\ irule_at (Pos last) env_rel_ext \\ fs []
    \\ conj_tac
    >-
     (gvs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO,MAP_FST_make_let_env]
      \\ drule Letrec_split_MAP_FST \\ fs [])
    \\ simp [env_rel_def,ALOOKUP_APPEND,ALOOUKP_MAP_Rec,AllCaseEqs()]
    \\ fs [ALOOKUP_NONE,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_INTRO]
    \\ rpt strip_tac
    \\ ‘LIST_REL
            (loc_rel
               (p ++
                MAP (λ(fn,_). dest_anyThunk (Recclosure tfns env1 fn))
                  (FILTER (λ(p1,p2). is_Delay p2) tfns)) env1 tfns)
            (FILTER ((λx. is_Delay x) ∘ SND) tfns)
            (MAPi (λi x. (FST x,Atom (Loc (i + LENGTH ss)))) delays)’ by
     (drule_all Letrec_split_FILTER
      \\ disch_then $ simp o single
      \\ simp [LIST_REL_EL_EQN,combinTheory.o_DEF,LAMBDA_PROD]
      \\ fs [indexedListsTheory.EL_MAPi]
      \\ rw [] \\ rename [‘k < LENGTH _’]
      \\ Cases_on ‘EL k (FILTER (λ(p1,p2). is_Delay p2) tfns)’ \\ fs []
      \\ drule EL_MEM \\ asm_rewrite_tac [MEM_FILTER]
      \\ rw [] \\ fs [oEL_THM]
      \\ ‘LENGTH ss = LENGTH p’ by (imp_res_tac LIST_REL_LENGTH \\ fs [])
      \\ simp [EL_APPEND2,EL_MAP]
      \\ drule MEM_IMP_ALOOKUP
      \\ simp [dest_anyThunk_def,AllCaseEqs()]
      \\ Cases_on ‘r’ \\ gvs [dest_Delay_def])
    \\ Cases_on ‘MEM n (MAP FST funs)’ \\ fs []
    >-
     (simp [Once v_rel_cases] \\ disj1_tac
      \\ ‘make_let_env delays (LENGTH ss) [] ++ env2 =
          REVERSE (REVERSE (make_let_env delays (LENGTH ss) [])) ++ env2’ by fs []
      \\ pop_assum $ irule_at Any
      \\ irule_at Any env_rel_ext \\ fs []
      \\ qpat_assum ‘LIST_REL letrec_rel _ _’ $ irule_at Any \\ fs []
      \\ simp [REVERSE_make_let_env]
      \\ drule_all Letrec_split_IMP_FILTER \\ fs []
      \\ strip_tac \\ gvs []
      \\ gvs [MEM_MAP,MEM_FILTER]
      \\ rename [‘MEM yy _’] \\ PairCases_on ‘yy’ \\ fs []
      \\ Cases_on ‘yy1’ \\ gvs [dest_Lam_def]
      \\ drule_at (Pos last) IMP_Lam \\ fs []
      \\ disch_then irule
      \\ pop_assum $ irule_at Any)
    \\ simp [Once v_rel_cases]
    \\ irule_at Any (METIS_PROVE [] “c ⇒ b ∨ c”) \\ simp [PULL_EXISTS]
    \\ qpat_assum ‘LIST_REL letrec_rel _ _’ $ irule_at Any \\ fs []
    \\ irule_at Any env_rel_ext \\ fs []
    \\ qpat_assum ‘env_rel _ _ _’ $ irule_at Any \\ fs []
    \\ first_assum $ irule_at $ Pos hd
    \\ irule EXISTS_ALOOKUP_ALOOKUP
    \\ simp [REVERSE_make_let_env]
    \\ fs [combinTheory.o_DEF,MAPi_MAP,MAP_FST_make_let_env]
    \\ fs [EXTENSION] \\ metis_tac [])
  \\ fs []
  \\ rpt conj_tac
  >~ [‘LIST_REL (LIST_REL _) _ (MAP SND (FILTER _ (ZIP (_ ++ _,_))))’]
  >-
   (qpat_x_assum ‘LIST_REL (LIST_REL _) _ _’ mp_tac
    \\ match_mp_tac LIST_REL_LIST_REL_lemma
    \\ conj_tac >-
     (rpt gen_tac \\ match_mp_tac LIST_REL_mono
      \\ rw [] \\ irule_at Any v_rel_ext \\ fs [])
    \\ AP_TERM_TAC
    \\ ‘LENGTH p = LENGTH ss’ by (imp_res_tac LIST_REL_LENGTH)
    \\ irule FILTER_ZIP_EQ \\ simp []
    \\ fs [EVERY_MEM,MEM_FILTER,MEM_MAP,FORALL_PROD]
    \\ CCONTR_TAC \\ gvs []
    \\ Cases_on ‘p_2’ \\ gvs [dest_Delay_def]
    \\ drule MEM_IMP_ALOOKUP \\ fs []
    \\ CCONTR_TAC \\ fs []
    \\ gvs [AllCaseEqs(),dest_anyThunk_def])
  \\ irule EVERY2_APPEND_suff
  \\ conj_tac
  >-
   (qpat_x_assum ‘LIST_REL (thunk_rel p) p ss’ mp_tac
    \\ match_mp_tac LIST_REL_mono \\ rw []
    \\ irule_at Any thunk_rel_ext \\ fs [])
  \\ qmatch_goalsub_abbrev_tac ‘thunk_rel p1’
  \\ drule_all Letrec_split_compile_rel
  \\ simp [listTheory.EVERY2_MAP]
  \\ match_mp_tac LIST_REL_mono
  \\ simp [FORALL_PROD,MEM_FILTER]
  \\ rw []
  \\ pop_assum mp_tac
  \\ drule_at (Pos last) alistTheory.ALOOKUP_ALL_DISTINCT_MEM
  \\ fs [] \\ rw [] \\ gvs [dest_Delay_def]
  \\ rename [‘compile_rel e1 e2’]
  \\ simp [dest_anyThunk_def]
  \\ simp [thunk_rel_def]
  \\ reverse (Cases_on ‘Letrec_imm (MAP FST sfns) e2’) \\ gvs []
  >- fs [Letrec_store_def]
  \\ Cases_on ‘∃x1 x2. e2 = Lam x1 x2’
  >-
   (gvs [Letrec_store_def]
    \\ qpat_x_assum ‘compile_rel e1 _’ mp_tac
    \\ simp [Once compile_rel_cases,comp_Letrec_not]
    \\ strip_tac \\ gvs []
    \\ simp [Once SWAP_EXISTS_THM]
    \\ qexists_tac ‘1’ \\ fs [step]
    \\ irule v_rel_Closure \\ fs [])
  \\ ‘∃v. e2 = Var v’ by (Cases_on ‘e2’ \\ fs [Letrec_imm_def])
  \\ gvs [Letrec_imm_def,Letrec_store_def]
  \\ qpat_x_assum ‘compile_rel e1 _’ mp_tac
  \\ simp [Once compile_rel_cases,comp_Letrec_not]
  \\ strip_tac \\ gvs []
  \\ simp [Once SWAP_EXISTS_THM]
  \\ qexists_tac ‘1’ \\ fs [step]
  \\ CASE_TAC
  >-
   (qpat_x_assum ‘MAP FST tfns = MAP FST sfns’ (assume_tac o GSYM) \\ gvs []
    \\ gvs [ALOOKUP_NONE,rec_env_def,MEM_MAP,FORALL_PROD]
    \\ PairCases_on ‘y’ \\ fs [])
  \\ fs [env_rel_def]
  \\ first_x_assum drule
  \\ strip_tac \\ fs []
QED

Theorem step_Bool:
  step ss k (Exp env (Bool b)) = (Val (Bool_v b),ss,k)
Proof
  Cases_on ‘b’ \\ fs [step]
QED

Theorem step_n_make_let_env:
  ∀delays ss m n env x sk.
    step_n m (Exp (make_let_env delays (LENGTH ss) env) x,
              SOME (ss ++ MAP (λ(v,b,y). [Bool_v b; Bool_v b]) delays),sk) = (sr1,ss1,sk1) ∧
    n = m + 7 * LENGTH delays ⇒
    step_n n (Exp env (Lets (MAP some_ref_bool delays) x),SOME ss,sk) = (sr1,ss1,sk1)
Proof
  Induct \\ fs [make_let_env_def,Lets_def]
  \\ rw [] \\ fs [ADD1,LEFT_ADD_DISTRIB]
  \\ rewrite_tac [ADD_ASSOC,GSYM (EVAL “1+1+1+1+1+1+1:num”)]
  \\ ntac 7 (once_rewrite_tac [step_n_add])
  \\ PairCases_on ‘h’
  \\ fs [some_ref_bool_def,Lets_def,step,step_Bool]
  \\ last_x_assum irule
  \\ fs [SNOC_APPEND,ADD1]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs []
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
  \\ Cases_on ‘is_halt (tr,ts,tk)’
  >- (‘is_halt (step_n n (tr,ts,tk)) ∧ is_halt (step_n 0 (tr,ts,tk))’ by fs []
      \\ dxrule is_halt_imp_eq
      \\ disch_then dxrule
      \\ fs [] \\ strip_tac \\ gvs []
      \\ qexists_tac ‘0’ \\ qexists_tac ‘[]’ \\ fs []
      \\ Cases_on ‘sr’ \\ gvs [step_res_rel_cases]
      \\ Cases_on ‘tk’ \\ gvs [cont_rel_nil])
  \\ qpat_x_assum ‘step_res_rel p tr sr’ mp_tac
  \\ simp [Once step_res_rel_cases]
  \\ strip_tac \\ gvs [is_halt_def]
  >-
   (Cases_on ‘tk’ \\ gvs [is_halt_def]
    \\ Cases_on ‘sk’ \\ gvs [is_halt_def,cont_rel_nil_cons]
    \\ rename [‘cont_rel p (tk'::tk) (sk'::sk)’]
    \\ qpat_x_assum ‘cont_rel _ _ _’ mp_tac
    \\ simp [Once cont_rel_cases]
    \\ strip_tac \\ gvs []
    >~ [‘ForceK1’] >-
     (Cases_on ‘n’ \\ fs [ADD1,step_n_add,step]
      \\ rename [‘v_rel p v1 v2’]
      \\ Cases_on ‘dest_anyThunk v1’ \\ gvs []
      \\ PairCases_on ‘x’ \\ gvs []
      \\ rename [‘_ = SOME (yy,_)’] \\ Cases_on ‘yy’ \\ gvs []
      \\ ntac 4 (irule_at Any step_n_unwind \\ fs [step_n_add,step])
      >-
       (drule_all dest_anyThunk_INL
        \\ strip_tac \\ gvs []
        \\ ntac 15 (irule_at Any step_n_unwind \\ fs [step_n_add,step,get_atoms_def])
        \\ last_x_assum $ drule_at $ Pos $ el 2 \\ fs []
        \\ simp [Once step_res_rel_cases,PULL_EXISTS]
        \\ disch_then drule_all \\ strip_tac \\ gvs []
        \\ rpt $ first_assum $ irule_at Any)
      \\ PairCases_on ‘y’ \\ fs []
      \\ drule_all dest_anyThunk_INR \\ reverse strip_tac \\ gvs []
      >-
       (ntac 15 (irule_at Any step_n_unwind \\ fs [step_n_add,step,get_atoms_def])
        \\ gvs [GSYM rec_env_def]
        \\ drule step_n_set_cont
        \\ disch_then (qspec_then ‘ForceK2 ts::tk’ assume_tac)
        \\ drule_all step_n_fast_forward
        \\ strip_tac
        \\ pop_assum mp_tac
        \\ Cases_on ‘m3’ \\ fs [] \\ strip_tac \\ gvs []
        \\ gvs [step_n_add,step,ADD1]
        \\ last_x_assum $ drule_at $ Pos $ el 2 \\ fs []
        \\ simp [Once step_res_rel_cases,PULL_EXISTS]
        \\ disch_then drule_all \\ strip_tac \\ gvs []
        \\ rpt $ first_assum $ irule_at Any)
      \\ gvs [GSYM rec_env_def]
      \\ drule_all step_n_NONE_split
      \\ strip_tac
      \\ ntac 2 $ pop_assum mp_tac
      \\ last_assum $ drule_at $ Pos $ el 2
      \\ fs [cont_rel_nil]
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ disch_then $ qspec_then ‘THE $ pick_opt zs ts’ mp_tac
      \\ fs [SOME_THE_pick_opt]
      \\ disch_then drule_all \\ strip_tac
      \\ rpt strip_tac
      \\ ntac 20 (irule_at Any step_n_unwind \\ fs [step_n_add,step,get_atoms_def])
      \\ qmatch_goalsub_abbrev_tac ‘step_n _ (_,_,kk3)’
      \\ qpat_x_assum ‘step_res_rel (p ++ q) (Val v) _’ mp_tac
      \\ simp [Once step_res_rel_cases] \\ strip_tac \\ gvs []
      \\ drule_then (qspec_then ‘kk3’ strip_assume_tac) step_n_set_cont
      \\ qsuff_tac ‘∃m' ss1' sr1' sk1 q'.
          step_n m' (Exp senv' se,SOME ss,kk3) = (sr1',SOME ss1',sk1) ∧
          is_halt (sr1',SOME ss1',sk1) ∧ cont_rel (p ++ q') tk1 sk1 ∧
          state_rel (p ++ q') (pick_opt zs ts1) (SOME ss1') ∧
          step_res_rel (p ++ q') tr1 sr1'’ >- metis_tac []
      \\ Q.REFINE_EXISTS_TAC ‘ck+1+m’
      \\ rewrite_tac [step_n_add] \\ fs []
      \\ fs [step,Abbr‘kk3’]
      \\ ntac 8 (irule_at Any step_n_unwind \\ fs [step_n_add,step,get_atoms_def])
      \\ drule_at (Pos $ el 2) dest_anyThunk_INR_abs \\ fs []
      \\ disch_then $ drule_at $ Pos last
      \\ disch_then $ qspec_then ‘loc’ mp_tac
      \\ impl_keep_tac >- (irule v_rel_ext \\ fs [])
      \\ strip_tac \\ fs []
      \\ ntac 9 (irule_at Any step_n_unwind \\ fs [step_n_add,step,get_atoms_def])
      \\ fs [oEL_THM,EL_LUPDATE]
      \\ ntac 2 (irule_at Any step_n_unwind \\ fs [step_n_add,step,get_atoms_def])
      \\ qmatch_goalsub_abbrev_tac ‘SOME ss3’
      \\ gvs [LUPDATE_DEF,LUPDATE_DEF,LUPDATE_LUPDATE]
      \\ drule_at (Pos $ el 4) state_rel_LUPDATE_anyThunk
      \\ disch_then $ drule_at (Pos $ el 3)
      \\ disch_then drule_all \\ strip_tac \\ gvs []
      \\ Cases_on ‘m2’ \\ gvs []
      \\ gvs [ADD1,step_n_add,step]
      \\ qpat_x_assum ‘step_n n (Val v,ts,tk) = (tr1,ts1,tk1)’ assume_tac
      \\ last_x_assum $ drule_at $ Pos $ el 2 \\ simp []
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ rpt $ disch_then $ drule_at $ Pos last
      \\ disch_then $ qspec_then ‘sk’ mp_tac
      \\ impl_tac
      >- (irule_at Any cont_rel_ext \\ fs [])
      \\ strip_tac
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ rpt $ first_assum $ irule_at $ Pos hd)
    >~ [‘BoxK’] >-
     (Cases_on ‘n’ \\ fs [ADD1,step_n_add,step]
      \\ ntac 3 (irule_at Any step_n_unwind \\ fs [step_n_add,step])
      \\ first_x_assum $ drule_at $ Pos $ el 2 \\ fs []
      \\ drule_all state_rel_INL
      \\ disch_then $ qspec_then ‘[]’ assume_tac
      \\ disch_then $ drule_at Any
      \\ simp [Once step_res_rel_cases, PULL_EXISTS]
      \\ disch_then $ qspecl_then [‘sk’,‘Atom (Loc (LENGTH ss))’] mp_tac
      \\ impl_tac >-
       (irule_at Any v_rel_new_Thunk
        \\ irule_at Any cont_rel_ext
        \\ fs [state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
      \\ strip_tac
      \\ first_x_assum $ irule_at $ Pos hd \\ fs []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
    >~ [‘LetK tenv n te’] >-
     (Cases_on ‘n'’ \\ fs [ADD1,step_n_add,step]
      \\ irule_at Any step_n_unwind \\ fs [step_n_add,step]
      \\ Cases_on ‘n’ \\ gvs [step]
      \\ first_x_assum $ drule_at $ Pos $ el 2 \\ fs []
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ rpt (disch_then drule)
      \\ strip_tac
      \\ rpt (first_assum $ irule_at Any \\ gvs [])
      \\ drule_all imp_env_rel_cons
      \\ metis_tac [])
    >~ [‘IfK tenv te1 te2’] >-
     (Cases_on ‘n’ \\ fs [ADD1,step_n_add,step]
      \\ irule_at Any step_n_unwind \\ fs [step_n_add,step]
      \\ qpat_x_assum ‘v_rel p v1 v2’ mp_tac
      \\ Cases_on ‘v1 = True_v ∨ v1 = False_v’ \\ gvs [step]
      \\ simp [Once v_rel_cases] \\ rpt strip_tac \\ gvs []
      \\ first_x_assum $ drule_at $ Pos $ el 2 \\ fs []
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ rpt (disch_then drule) \\ strip_tac
      \\ rpt (first_assum $ irule_at Any \\ gvs []))
    >~ [‘RaiseK’] >-
     (Cases_on ‘n’ \\ fs [ADD1,step_n_add,step]
      \\ irule_at Any step_n_unwind \\ fs [step_n_add,step]
      \\ first_x_assum $ drule_at $ Pos $ el 2 \\ fs []
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ rpt (disch_then drule) \\ strip_tac
      \\ rpt (first_assum $ irule_at Any \\ gvs []))
    >~ [‘HandleK tenv _ te’] >-
     (Cases_on ‘n’ \\ fs [ADD1,step_n_add,step]
      \\ irule_at Any step_n_unwind \\ fs [step_n_add,step]
      \\ first_x_assum $ drule_at $ Pos $ el 2 \\ fs []
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ rpt (disch_then drule) \\ strip_tac
      \\ rpt (first_assum $ irule_at Any \\ gvs []))
    >~ [‘HandleAppK tenv te’] >-
     (Cases_on ‘n’ \\ fs [ADD1,step_n_add,step]
      \\ irule_at Any step_n_unwind \\ fs [step_n_add,step]
      \\ first_x_assum $ drule_at $ Pos $ el 2 \\ fs []
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ rpt (disch_then drule) \\ strip_tac
      \\ rpt (first_assum $ irule_at Any \\ gvs []))
    \\ rename [‘AppK tenv op tvs tes’]
    \\ Cases_on ‘n’ \\ fs [ADD1,step_n_add,step]
    \\ irule_at Any step_n_unwind \\ fs [step_n_add,step]
    \\ reverse (Cases_on ‘tes’) \\ gvs []
    >- (* more args to evaluate *)
     (fs [return_def,continue_def]
      \\ first_x_assum $ drule_at $ Pos $ el 2 \\ fs []
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ simp [Once cont_rel_cases,PULL_EXISTS]
      \\ rpt (disch_then drule) \\ strip_tac
      \\ rpt (first_assum $ irule_at Any \\ gvs []))
    \\ gvs [return_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ IF_CASES_TAC >- (gvs [error_def,is_halt_def])
    \\ gvs []
    \\ Cases_on ‘op = AppOp’ \\ gvs []
    >-
     (gvs [application_def]
      \\ Cases_on ‘dest_anyClosure v1’ \\ gvs [error_def]
      \\ PairCases_on ‘x’
      \\ drule_all dest_anyClosure_v_rel
      \\ strip_tac \\ gvs [LENGTH_EQ_NUM_compute]
      \\ gvs [continue_def]
      \\ last_x_assum $ drule_at_then (Pos $ el 2) mp_tac
      \\ simp [Once step_res_rel_cases,PULL_EXISTS]
      \\ rpt $ disch_then $ drule_at Any
      \\ rename [‘opt_bind z1 z2 x1’]
      \\ drule imp_env_rel_opt_bind \\ simp []
      \\ disch_then drule
      \\ disch_then $ qspec_then ‘z1’ assume_tac
      \\ disch_then drule
      \\ strip_tac
      \\ rpt (first_x_assum $ irule_at Any))
    \\ ‘∃s_. application op tenv (v2::tvs) (SOME ss) sk = s_’ by fs []
    \\ PairCases_on ‘s_’ \\ gvs []
    \\ ‘∃t_. application op tenv' (v1::tvs') ts tk = t_’ by fs []
    \\ PairCases_on ‘t_’ \\ gvs []
    \\ drule_then drule application_thm
    \\ disch_then drule \\ simp [ADD1] \\ rw [] \\ gvs [ADD1]
    \\ last_x_assum $ drule_at $ Pos $ el 2
    \\ rpt $ disch_then $ drule_at $ Pos $ last \\ fs []
    \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt (first_x_assum $ irule_at Any))
  >-
   (Cases_on ‘tk’ \\ gvs [is_halt_def]
    \\ Cases_on ‘sk’ \\ gvs [is_halt_def,cont_rel_nil_cons]
    \\ rename [‘cont_rel p (tk'::tk) (sk'::sk)’]
    \\ qpat_x_assum ‘cont_rel _ _ _’ mp_tac
    \\ simp [Once cont_rel_cases]
    \\ strip_tac \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘ck+1:num’
    \\ qpat_x_assum ‘step_n _ _ = _’ mp_tac
    \\ (Cases_on ‘n’ >- fs [])
    \\ rewrite_tac [step_n_add,ADD1]
    \\ fs [] \\ simp [step]
    \\ strip_tac
    \\ last_x_assum irule \\ simp []
    \\ pop_assum $ irule_at Any \\ fs []
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ rpt (first_assum $ irule_at $ Any \\ fs [])
    \\ once_rewrite_tac [cont_rel_cases] \\ fs []
    \\ fs [env_rel_def] \\ rw [] \\ fs [])
  \\ qpat_x_assum ‘compile_rel e1 e2’ mp_tac
  \\ simp [Once compile_rel_cases] \\ rw []
  \\ Q.REFINE_EXISTS_TAC ‘ck+1:num’
  \\ qpat_x_assum ‘step_n n _ = _’ mp_tac
  \\ (Cases_on ‘n’ >- fs [])
  \\ rewrite_tac [step_n_add,ADD1]
  \\ TRY
     ((rename [‘Exp _ $ Lam _ _’] ORELSE
       rename [‘Exp _ $ If _ _ _’] ORELSE
       rename [‘Raise’] ORELSE
       rename [‘Handle’] ORELSE
       rename [‘HandleApp’] ORELSE
       rename [‘Box’] ORELSE
       rename [‘Force’])
      \\ simp [step] \\ strip_tac
      \\ last_x_assum irule
      \\ pop_assum $ irule_at Any \\ fs []
      \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
      \\ rpt (first_assum $ irule_at $ Any \\ fs [])
      \\ once_rewrite_tac [cont_rel_cases] \\ fs []
      \\ once_rewrite_tac [v_rel_cases] \\ fs [dest_anyClosure_def])
  >~ [‘Var vname’] >-
   (fs [step,error_def]
    \\ Cases_on ‘ALOOKUP env1 vname’ \\ fs [is_halt_def]
    \\ fs [env_rel_def] \\ fs []
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ gvs []
    \\ last_x_assum irule
    \\ pop_assum $ irule_at Any \\ fs []
    \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
    \\ rpt (first_assum $ irule_at $ Any \\ fs []))
  >~ [‘Delay te’] >-
   (simp [step]
    \\ strip_tac
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1+1+1+1’
    \\ rewrite_tac [step_n_add,ADD1]
    \\ simp [step,return_def]
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ simp []
    \\ ‘step_res_rel (p ++ [SOME (INR (env1,te),[])])
          (Val (Thunk (INR (env1,te)))) (Val (Atom (Loc (LENGTH ss)))) ∧
        state_rel (p ++ [SOME (INR (env1,te),[])])
          (pick_opt zs ts) (SOME (SNOC [False_v; Closure NONE env2 se] ss))’ by
     (once_rewrite_tac [step_res_rel_cases] \\ fs []
      \\ irule_at Any v_rel_new_Thunk
      \\ irule_at Any state_rel_INR \\ fs [rec_env_def,state_rel_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
    \\ rpt (disch_then $ drule_at $ Pos last)
    \\ disch_then $ qspec_then ‘sk’ mp_tac
    \\ impl_tac >- (irule cont_rel_ext \\ fs [])
    \\ strip_tac \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt $ first_x_assum $ irule_at $ Pos last)
  >~ [‘Let’] >-
     (simp [step] \\ strip_tac
      \\ last_x_assum irule
      \\ pop_assum $ irule_at Any \\ fs []
      \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
      \\ rpt (first_assum $ irule_at $ Any \\ fs [])
      \\ once_rewrite_tac [cont_rel_cases] \\ fs []
      \\ once_rewrite_tac [v_rel_cases] \\ fs [dest_anyClosure_def])
  >~ [‘App op ys’] >-
   (fs [step,error_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ rename [‘LIST_REL compile_rel xs ys’]
    \\ reverse CASE_TAC \\ gvs []
    >-
     (Cases_on ‘REVERSE ys’ >- gvs []
      \\ gvs [SWAP_REVERSE_SYM]
      \\ strip_tac
      \\ last_x_assum irule
      \\ pop_assum $ irule_at Any \\ fs []
      \\ once_rewrite_tac [step_res_rel_cases] \\ fs []
      \\ once_rewrite_tac [cont_rel_cases] \\ fs [])
    \\ ‘∃s_. application op env2 [] (SOME ss) sk = s_’ by fs []
    \\ PairCases_on ‘s_’ \\ gvs []
    \\ ‘∃t_. application op env1 [] ts tk = t_’ by fs []
    \\ PairCases_on ‘t_’ \\ gvs []
    \\ drule_then drule application_thm
    \\ disch_then drule \\ simp [ADD1]
    \\ impl_tac >- (strip_tac \\ gvs [])
    \\ rw [] \\ gvs []
    \\ last_x_assum $ drule_at $ Pos $ el 2 \\ fs []
    \\ rpt $ disch_then drule
    \\ strip_tac \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt (last_x_assum $ irule_at Any))
  \\ rename [‘Letrec tfns te’]
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV (srw_ss()) [step,GSYM rec_env_def]))
  \\ strip_tac
  \\ last_x_assum $ dxrule_at $ Pos $ el 2
  \\ strip_tac
  \\ rewrite_tac [GSYM step_n_add,ADD1] \\ gvs []
  \\ simp [comp_Letrec_def] \\ pairarg_tac \\ gvs []
  \\ irule_at Any step_n_make_let_env
  \\ irule_at Any step_n_unwind
  \\ simp [] \\ fs [GSYM ADD1,ADD_CLAUSES]
  \\ simp [ADD1,step_n_add,step,GSYM rec_env_def]
  \\ imp_res_tac Letrec_split_EVERY
  \\ drule_all Letrec_split_ALL_DISTINCT \\ strip_tac
  \\ fs [rec_env_def]
  \\ drule Letrec_store_forward \\ asm_rewrite_tac []
  \\ disch_then $ irule_at Any
  \\ fs []
  \\ pop_assum $ irule_at Any
  \\ simp [GSYM PULL_EXISTS]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ conj_tac
  >-
   (simp [EVERY_MEM,FORALL_PROD,MAP_MAP_o,combinTheory.o_DEF]
    \\ drule_all Letrec_split_ALL_DISTINCT \\ strip_tac
    \\ simp [LAMBDA_PROD,FST_INTRO]
    \\ fs [ALOOKUP_NONE,MEM_make_let_env,MAP_MAP_o,combinTheory.o_DEF,IN_DISJOINT]
    \\ simp [LAMBDA_PROD,FST_INTRO]
    \\ qpat_x_assum ‘_ = set (MAP _ _)’ (assume_tac o GSYM)
    \\ simp [FST_INTRO]
    \\ fs [MEM_MAP,FORALL_PROD,EXISTS_PROD]
    \\ metis_tac [])
  \\ simp [PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac ‘Exp env5 _, SOME ss5, _’
  \\ qabbrev_tac ‘p5 = p ++
       MAP (λ(fn,_). dest_anyThunk (Recclosure tfns env1 fn))
          (FILTER (is_Delay o SND) tfns)’
  \\ first_x_assum $ qspecl_then [‘zs’,‘p5’,‘ss5’,‘Exp env5 se’,‘sk’] mp_tac
  \\ reverse impl_tac
  >-
   (strip_tac
    \\ first_assum $ irule_at $ Pos hd
    \\ full_simp_tac std_ss [Abbr‘p5’,GSYM APPEND_ASSOC]
    \\ first_assum $ irule_at $ Pos hd \\ fs [])
  \\ conj_tac
  >- fs [Abbr‘p5’,cont_rel_ext]
  \\ unabbrev_all_tac
  \\ fs [step_res_rel_cases,GSYM rec_env_def]
  \\ irule state_rel_Letrec \\ fs []
  \\ first_x_assum $ irule_at $ Pos last \\ fs []
  \\ drule_all Letrec_split_ALL_DISTINCT \\ fs []
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
    >~ [‘LetK tenv n te’] >-
     (Q.REFINE_EXISTS_TAC ‘ck1+1’
      \\ rewrite_tac [step_n_add,ADD1] \\ simp [step]
      \\ Cases_on ‘n’ \\ simp [step]
      \\ Cases_on ‘m’ \\ gvs [step,ADD1]
      \\ gvs [step_n_add,ADD1,step]
      \\ last_x_assum irule
      \\ gvs [step_res_rel_cases,PULL_EXISTS]
      \\ rpt (first_assum $ irule_at Any \\ gvs [])
      \\ irule_at Any imp_env_rel_cons \\ gs [])
    >~ [‘IfK tenv te1 te2’] >-
     (Q.REFINE_EXISTS_TAC ‘ck1+1’
      \\ rewrite_tac [step_n_add,ADD1]
      \\ qpat_x_assum ‘v_rel p v1 v2’ mp_tac
      \\ Cases_on ‘v1 = True_v ∨ v1 = False_v’ \\ gvs [step]
      \\ simp [Once v_rel_cases] \\ rpt strip_tac \\ gvs []
      \\ TRY (qexists_tac ‘0’ \\ fs [is_halt_def,error_def] \\ NO_TAC)
      \\ Cases_on ‘m’ \\ gvs [step,ADD1]
      \\ gvs [step_n_add,ADD1,step]
      \\ last_x_assum irule
      \\ gvs [step_res_rel_cases,PULL_EXISTS]
      \\ rpt (first_assum $ irule_at Any \\ gvs []))
    >~ [‘RaiseK’] >-
     (Q.REFINE_EXISTS_TAC ‘ck1+1’
      \\ rewrite_tac [step_n_add,ADD1] \\ gvs [step]
      \\ Cases_on ‘m’ \\ gvs [step_n_add,step,ADD1]
      \\ last_x_assum irule
      \\ gvs [step_res_rel_cases,PULL_EXISTS]
      \\ rpt (first_assum $ irule_at Any \\ gvs []))
    >~ [‘HandleK tenv n te’] >-
     (Q.REFINE_EXISTS_TAC ‘ck1+1’
      \\ rewrite_tac [step_n_add,ADD1] \\ gvs [step]
      \\ Cases_on ‘m’ \\ gvs [step,ADD1]
      \\ gvs [step_n_add,ADD1,step]
      \\ last_x_assum irule
      \\ gvs [step_res_rel_cases,PULL_EXISTS]
      \\ rpt (first_assum $ irule_at Any \\ gvs []))
    >~ [‘HandleAppK tenv te’] >-
     (Q.REFINE_EXISTS_TAC ‘ck1+1’
      \\ rewrite_tac [step_n_add,ADD1] \\ gvs [step]
      \\ Cases_on ‘m’ \\ gvs [step,ADD1]
      \\ gvs [step_n_add,ADD1,step]
      \\ last_x_assum irule
      \\ gvs [step_res_rel_cases,PULL_EXISTS]
      \\ rpt (first_assum $ irule_at Any \\ gvs []))
    \\ rename [‘AppK tenv op tvs tes’]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add,ADD1] \\ simp [step]
    \\ reverse (Cases_on ‘tes’) \\ fs []
    >- (* more args to evaluate *)
     (fs [return_def,continue_def]
      \\ first_x_assum irule \\ gvs []
      \\ last_x_assum mp_tac
      \\ Cases_on ‘m’ \\ fs [ADD1,step,step_n_add]
      \\ disch_then $ irule_at Any \\ fs []
      \\ last_x_assum $ irule_at Any
      \\ simp [Once step_res_rel_cases]
      \\ simp [Once cont_rel_cases])
    \\ simp [return_def]
    \\ Cases_on ‘m’ \\ fs [ADD1,step,step_n_add]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ IF_CASES_TAC >- (qexists_tac ‘0’ \\ gvs [error_def,is_halt_def])
    \\ gvs []
    \\ Cases_on ‘op = AppOp’ \\ gvs []
    >-
     (gvs [application_def]
      \\ Cases_on ‘dest_anyClosure v1’ \\ fs []
      >- (qexists_tac ‘0’ \\ gvs [error_def,is_halt_def])
      \\ PairCases_on ‘x’
      \\ drule_all dest_anyClosure_v_rel
      \\ strip_tac \\ gvs []
      \\ Cases_on ‘svs’ \\ fs [] \\ Cases_on ‘t’ \\ gvs []
      \\ gvs [continue_def]
      \\ last_x_assum $ drule_at_then (Pos $ el 2) irule
      \\ gvs [] \\ rpt (first_x_assum $ irule_at Any)
      \\ simp [Once step_res_rel_cases]
      \\ irule_at Any imp_env_rel_opt_bind \\ simp [])
    \\ ‘∃s_. application op senv (v2::svs) (SOME ss) sk = s_’ by fs []
    \\ PairCases_on ‘s_’ \\ gvs []
    \\ ‘∃t_. application op tenv (v1::tvs) ts tk = t_’ by fs []
    \\ PairCases_on ‘t_’ \\ gvs []
    \\ drule_then drule application_thm
    \\ disch_then drule \\ simp [ADD1] \\ rw []
    >- (qexists_tac ‘0’ \\ gvs [is_halt_def])
    \\ last_x_assum irule
    \\ rpt (last_x_assum $ irule_at Any \\ fs []))
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
    \\ irule_at Any state_rel_INR \\ fs [rec_env_def]
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
    \\ ‘∃s_. application op env2 [] (SOME ss) sk = s_’ by fs []
    \\ PairCases_on ‘s_’ \\ gvs []
    \\ ‘∃t_. application op env1 [] ts tk = t_’ by fs []
    \\ PairCases_on ‘t_’ \\ gvs []
    \\ drule_then drule application_thm
    \\ disch_then drule \\ simp [ADD1]
    \\ impl_tac >- (strip_tac \\ gvs [])
    \\ rw []
    >- (qexists_tac ‘0’ \\ gvs [is_halt_def])
    \\ last_x_assum irule
    \\ rpt (last_x_assum $ irule_at Any \\ fs []))
  \\ rename [‘Letrec tfns te’]
  \\ rewrite_tac [GSYM step_n_add,ADD1] \\ gvs []
  \\ simp [comp_Letrec_def] \\ pairarg_tac \\ gvs []
  \\ strip_tac
  \\ simp [step_n_add,step,GSYM rec_env_def]
  \\ drule_all step_n_Lets_some_ref_bool \\ strip_tac
  \\ pop_assum mp_tac
  \\ Cases_on ‘m’
  >- (gvs [] \\ rw [] \\ gvs [is_halt_def])
  \\ simp [step_n_add,step,GSYM rec_env_def,ADD1]
  \\ gvs [ADD1]
  \\ imp_res_tac Letrec_split_EVERY
  \\ drule_all Letrec_split_ALL_DISTINCT \\ strip_tac
  \\ fs [rec_env_def] \\ strip_tac
  \\ drule_at (Pos last) Letrec_store_thm
  \\ simp []
  \\ rpt (disch_then drule)
  \\ impl_tac
  >-
   (simp [EVERY_LAM]
    \\ fs [ALOOKUP_NONE,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,MEM_make_let_env]
    \\ qpat_x_assum ‘_ = set (MAP _ _)’ (assume_tac o GSYM)
    \\ simp [FST_INTRO]
    \\ gvs [IN_DISJOINT,MEM_MAP,FORALL_PROD,EXTENSION,EVERY_MEM]
    \\ gvs [FORALL_PROD,EXISTS_PROD]
    \\ metis_tac [])
  \\ strip_tac
  \\ ‘k < n + 1’ by fs []
  \\ last_x_assum drule
  \\ disch_then drule
  \\ disch_then irule \\ simp []
  \\ fs [GSYM rec_env_def]
  \\ qexists_tac ‘p ++
       MAP (λ(fn,_). dest_anyThunk (Recclosure tfns env1 fn))
          (FILTER (is_Delay o SND) tfns)’
  \\ irule_at Any cont_rel_ext
  \\ qexists_tac ‘zs’ \\ fs []
  \\ simp [step_res_rel_cases]
  \\ irule state_rel_Letrec \\ fs []
  \\ first_x_assum $ irule_at $ Pos last \\ fs []
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
  \\ once_rewrite_tac [itreeTheory.itree_unfold_err]
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
  \\ qexists_tac ‘[]’ \\ fs [state_rel_def]
QED

val _ = export_theory ();
