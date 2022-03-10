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

Overload "force" = “λx.
  Let (SOME "v") x $
  Let (SOME "v1") (App UnsafeSub [Var "v"; IntLit 0]) $
  Let (SOME "v2") (App UnsafeSub [Var "v"; IntLit 1]) $
    If (Var "v1") (Var "v2") $
      Let (SOME "a") (app (Var "v2") Unit) $
      Let NONE (App UnsafeUpdate [Var "v"; IntLit 0; True]) $
      Let NONE (App UnsafeUpdate [Var "v"; IntLit 1; Var "a"]) $
        Var "a"”

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
  (LIST_REL compile_rel xs ys ⇒
  compile_rel (App op xs) (App op ys)) ∧

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
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
  (∀p tvs svs.
     LIST_REL (v_rel p) tvs svs ⇒
     v_rel p (Constructor s tvs) (Constructor s svs)) ∧

[~Closure:]
  (∀p tenv senv te se x.
     env_rel p tenv senv ∧
     compile_rel te se ⇒
     v_rel p (Closure x tenv te) (Closure x senv se)) ∧

[~Recclosure:]
  (∀p tenv senv tfns sfns n.
     env_rel p tenv senv ∧
     LIST_REL ((=) ### compile_rel) tfns sfns ⇒
     v_rel p (Recclosure tfns tenv n) (Recclosure sfns senv n)) ∧

[~Thunk:]
  (∀p n r.
     oEL n p = SOME (SOME r) ⇒
     v_rel p (Thunk r) (Atom (Loc n))) ∧

[env_rel:]
  (∀p tenv senv.
     (∀n tv.
       ALOOKUP tenv n = SOME tv ⇒
       ∃sv. ALOOKUP senv n = SOME sv ∧ v_rel p tv sv) ⇒
     env_rel p tenv senv)

End

Theorem env_rel_def = “env_rel p tenv senv”
  |> SIMP_CONV (srw_ss()) [Once v_rel_cases];

Inductive step_res_rel:
  (v_rel p v1 v2 ⇒
   step_res_rel p (Val v1) (Val v2)) ∧
  (v_rel p v1 v2 ⇒
   step_res_rel p (Exn v1) (Exn v2)) ∧
  (compile_rel e1 e2 ∧ env_rel p env1 env2 ⇒
   step_res_rel p (Exp env1 e1) (Exp env2 e2)) ∧
  (step_res_rel p (Action a b) (Action a b))
End

Inductive cont_rel:
  ∀xs. xs = [] ⇒ cont_rel p xs []
End

Definition state_rel_def:
  state_rel (p:(v + env # exp) option list) (ts:state option) (ss:state option) = T
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

Theorem step_forward:
  ∀n p tr ts tk tr1 ts1 tk1 ss sr sk.
    step_n n (tr,ts,tk) = (tr1,ts1,tk1) ∧ is_halt (tr1,ts1,tk1) ∧
    cont_rel p tk sk ∧
    state_rel p ts (SOME ss) ∧
    step_res_rel p tr sr ∧ tr1 ≠ Error ⇒
    ∃m q sr1 ss1 sk1.
      step_n m (sr,SOME ss,sk) = (sr1,SOME ss1,sk1) ∧
      is_halt (sr1,SOME ss1,sk1) ∧
      cont_rel q tk1 sk1 ∧
      state_rel q ts1 (SOME ss1) ∧
      step_res_rel q tr1 sr1
Proof
  cheat
QED

Theorem step_backward:
  ∀m p sr ss sk sr1 ss1 sk1 tr ts tk.
    step_n m (sr,SOME ss,sk) = (sr1,ss1,sk1) ∧
    is_halt (sr1,ss1,sk1) ∧
    cont_rel p tk sk ∧
    state_rel p ts (SOME ss) ∧
    step_res_rel p tr sr ⇒
    ∃n q tr1 ts1 tk1.
      step_n n (tr,ts,tk) = (tr1,ts1,tk1) ∧
      is_halt (tr1,ts1,tk1)
Proof
  cheat
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
