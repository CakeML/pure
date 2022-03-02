(*
  Correctness for compilation from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     envLangTheory thunkLang_primitivesTheory envLang_cexpTheory
     stateLangTheory env_semanticsTheory;

val _ = new_theory "env_to_stateProof";

val _ = set_grammar_ancestry ["stateLang", "envLang", "env_semantics"];

Overload "app" = ``λe1 e2. App AppOp [e1;e2]``;
Overload "cons0" = ``λs. App (Cons s) []``;

Definition Lets_def:
  Lets [] e = e ∧
  Lets ((x,a)::rest) e = stateLang$Let x a (Lets rest e)
End

(****************************************)

Inductive compile_rel:

[~Var:]
  compile_rel (envLang$Var v) (stateLang$Var v) ∧

[~Ret:]
  (compile_rel te se ∧ u ∉ freevars se ⇒
  compile_rel (Prim (Cons "Ret") [Delay te]) (Lam u se)) ∧

[~Bind:]
  (compile_rel te1 se1 ∧ compile_rel te2 se2 ∧
   u ∉ freevars se1 ∪ freevars se2 ∧ x ∉ freevars se2 ∧ u ≠ x ⇒
  compile_rel
    (Prim (Cons "Bind") [Delay te1; Delay te2])
    (Lam u $ App AppOp
      [Lam x (app (app se2 (Var x)) (Var u)); app se1 (Var u)])) ∧
(*
  e.g.
    Ret (Delay a)   -->   Lam "u". a'
    Lam "x". Ret (Delay "x")   --> Lam "x". Lam "u". "x"
  so consider `return a >>= (λx. return x)`:
      Bind (Delay $ Ret (Delay a)) (Delay $ Lam "x". Ret (Delay "x")):
  --> Lam "u". (Lam "x". (Lam "x". Lam "u". "x") "x" "u") ((Lam "u". a') "u")
*)

[~Raise:]
  (compile_rel te se ∧
   u ∉ freevars se ⇒
  compile_rel (Prim (Cons "Raise") [Delay te]) (Lam u $ Raise se)) ∧

[~Handle:]
  (compile_rel te1 se1 ∧ compile_rel te2 se2 ∧
   u ∉ freevars se1 ∪ freevars se2 ∧ x ∉ freevars se2 ∧ u ≠ x ⇒
  compile_rel
    (Prim (Cons "Handle") [Delay te1; Delay te2])
    (Lam u $ Handle (app se1 (Var u)) x (app (app se2 (Var x)) (Var u)))) ∧

[~Alloc:]
  (LIST_REL compile_rel tes ses ∧
   EVERY (λse. u ∉ freevars se) ses ⇒
  compile_rel (Prim (Cons "Alloc") (MAP Delay tes)) (Lam u $ App Alloc ses)) ∧

[~Length:]
  (LIST_REL compile_rel tes ses ∧
   EVERY (λse. u ∉ freevars se) ses ⇒
  compile_rel (Prim (Cons "Length") (MAP Delay tes)) (Lam u $ App Length ses)) ∧

[~Deref:]
  (LIST_REL compile_rel tes ses ∧
   EVERY (λse. u ∉ freevars se) ses ⇒
  compile_rel (Prim (Cons "Deref") (MAP Delay tes)) (Lam u $ App Sub ses)) ∧

[~Update:]
  (LIST_REL compile_rel tes ses ∧
   EVERY (λse. u ∉ freevars se) ses ⇒
  compile_rel (Prim (Cons "Update") (MAP Delay tes)) (Lam u $ App Update ses)) ∧

[~Act:]
  (compile_rel te se ∧
   u ∉ freevars se ⇒
  compile_rel (Prim (Cons "Act") [Delay te]) (Lam u $ app se (Var u))) ∧

[~Cons:]
  (LIST_REL compile_rel tes ses ∧
   s ∉ monad_cns ⇒
  compile_rel (Prim (Cons s) tes) (App (Cons s) ses)) ∧

[~Message:]
  (compile_rel te se ∧ u ≠ x ⇒
  compile_rel
    (Prim (AtomOp (Message s)) [te])
    (Let (SOME x) se $ Lam u $ App (FFI s) [Var x])) ∧

[~AtomOp:]
  (LIST_REL compile_rel tes ses ∧
   (∀s. aop ≠ Message s) ⇒
  compile_rel (Prim (AtomOp aop) tes) (App (AtomOp aop) ses)) ∧

[~App:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (App te1 te2) (App AppOp [se1;se2])) ∧

[~Lam:]
  (compile_rel te se ⇒
   compile_rel (Lam x te) (Lam x se)) ∧

(*
[~Letrec:]
  (ALL_DISTINCT (MAP FST tfns) ∧
   letrec_funs_rel (freevars (Letrec fns te) ∪ set (MAP FST fns)) tfns sfns sets ∧
   compile_rel te se
  ⇒ compile_rel
      (Letrec fns te)
      (Lets
        (MAP (λ(fn,_). (SOME fn, ref (inl (Lam u (Raise $ cons0 TODO))))) fns) $
        stateLang$Letrec sfns $ Sets sets se)) ∧
*)

[~Let:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (Let x_opt te1 te2) (Let x_opt se1 se2)) ∧

[~If:]
  (compile_rel te se ∧
   compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (If te te1 te2) (If se se1 se2)) ∧

[~Delay:]
  (compile_rel te se ∧
   u ∉ freevars se ⇒
  compile_rel (Delay te) (App Ref [inl $ Lam u se])) ∧

[~Box:]
  (compile_rel te se ⇒
  compile_rel (Box te) (App Ref [inr se]))

(*
[~Force:]
  (compile_rel te se ⇒
  compile_rel (Force te) (App AppOp [force; se])) ∧

  letrec_funs_rel fvs [] [] [] ∧

  (letrec_funs_rel fvs tfns sfns sets ∧ compile_rel te se ∧
   f_fn ∉ fvs ∧ u ∉ freevars se ⇒
  letrec_funs_rel fvs
    ((f, Delay te)::tfns) ((f_fn, u, se)::sfns) ((Var f, inl (Var f_fn))::sets)) ∧

  (letrec_funs_rel fvs tfns sfns sets ∧ compile_rel te se ⇒
   letrec_funs_rel fvs
    ((f, Lam x te)::tfns) ((f, x, se)::sfns) ((Var f, inl (Var f))::sets)) ∧

  (letrec_funs_rel fvs tfns sfns sets ∧ compile_rel te se ⇒
  letrec_funs_rel fvs ((f, Box te)::tfns) sfns ((Var f, inr se)::sets))
*)

End

(* TODO HOL gives "index too large" error if below comment is
   within Inductive ... End and does not name all rules *)

  (*
    In general, we have:
      envLang$Letrec [(x, y); ...] e
    -->
      Let x (Ref (INL (fn u => Raise Bind))) ... (* declare all references *)
      Letrec [...] (* use the bindings *)
        (x := INL (fn u => y); ...) (* update the references *)

  As `y` can only be `Box`, `Delay`, or `Lam`:
      envLang$Letrec [(x, Lam a b); ...] e
    -->
      Let x (Ref _) ... (Letrec [(x, a, b'); ...] (x := INL x; ...; e'))

      envLang$Letrec [(x, Delay d); ...] e
    -->
      Let x (Ref _) ... (Letrec [(fresh1, fresh2, d'); ...] (x := INL fresh1; ...; e'))

      envLang$Letrec [(x, Box b); ...] e
    -->
      Let x (Ref _) ... (Letrec [...] (x := INR b'; ...; e'))
  *)


(* TODO *)
Inductive v_rel:

[~Constructor:]
  (∀tvs svs.
     LIST_REL v_rel tvs svs ⇒
     v_rel (envLang$Constructor s tvs) (stateLang$Constructor s svs)) ∧

[~Closure:]
  (∀tenv senv te se.
     env_rel tenv senv ∧
     compile_rel te se ⇒
     v_rel (Closure x tenv te) (Closure x senv se)) ∧

(*
[~Recclosure:]
  (∀tenv senv tfns sfns n.
     env_rel tenv senv ∧
     LIST_REL ((=) ### compile_rel) tfns sfns ⇒
     v_rel (envLang$Recclosure tfns tenv n) (stateLang$Recclosure sfns senv n)) ∧
*)

[~ThunkL:]
  (∀tv sv.
     v_rel tv sv ⇒
     v_rel (Thunk $ INL tv) (Thunk $ IL sv)) ∧

[~ThunkR:]
  (∀tenv senv te se.
     env_rel tenv senv ∧
     compile_rel te se ⇒
     v_rel (Thunk $ INR (tenv, te)) (Thunk $ INR (senv, se))) ∧

[~Atom:]
  (∀a.
     v_rel (Atom a) (Atom a)) ∧

[env_rel:]
  (∀tenv senv.
     (∀n tv.
       ALOOKUP (REVERSE tenv) n = SOME tv ⇒
       ∃sv. ALOOKUP senv n = SOME sv ∧ v_rel tv sv) ⇒
     env_rel tenv senv)

End

Theorem env_rel_def = v_rel_cases |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL;

Theorem step_n_0[simp]:
  step_n 0 x = x
Proof
  PairCases_on ‘x’ \\ fs [step_n_def]
QED

Theorem step_n_1[simp]:
  step_n 1 x = step (FST (SND x)) (SND (SND x)) (FST x)
Proof
  PairCases_on ‘x’ \\ fs [step_n_def]
QED

Theorem step_n_unfold:
  (∃n. k = n + 1 ∧ step_n n (step st c sr) = res) ⇒
  step_n k (sr,st,c) = res
Proof
  Cases_on ‘k’ >- fs []
  \\ rewrite_tac [step_n_def,FUNPOW]
  \\ fs [ADD1]
  \\ Cases_on ‘step st c sr’ \\ Cases_on ‘r’
  \\ fs [step_n_def]
QED

Theorem step_n_add:
  step_n (m+n) x = step_n m (step_n n x)
Proof
  PairCases_on ‘x’ \\ fs [step_n_def,FUNPOW_ADD]
  \\ AP_THM_TAC \\ fs [FUN_EQ_THM,FORALL_PROD,step_n_def]
QED

Theorem eval_to_thm:
  ∀n tenv te tres se senv st k.
    eval_to n tenv te = tres ∧ compile_rel te se ∧
    env_rel tenv senv ∧ tres ≠ INL Type_error ⇒
    ∃ck sres.
      step_n ck (Exp senv se, st, k) = sres ∧
      case tres of
      | INR tv => ∃sv. sres = (Val sv,st,k) ∧ v_rel tv sv
      | INL err => n ≤ ck ∧ ~is_halt sres
Proof
  ho_match_mp_tac eval_to_ind \\ rpt conj_tac \\ rpt gen_tac
  \\ strip_tac
  >~ [‘Var v’]
  >- (fs [eval_to_def,AllCaseEqs()] \\ rw []
    \\ gvs [Once compile_rel_cases]
    \\ qexists_tac ‘1’ \\ fs []
    \\ fs [step_def]
    \\ fs [env_rel_def] \\ first_x_assum drule \\ rw []
    \\ gvs [value_def])
  >~ [‘App tf tx’]
  >- (
    simp [Once compile_rel_cases] \\ rw []
    \\ fs [eval_to_def,AllCaseEqs()] \\ rw []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ asm_rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ Cases_on ‘eval_to n tenv tx’ \\ fs []
    >- (first_x_assum drule_all
      \\ disch_then (qspecl_then [‘st’,‘AppK senv AppOp [] [se1]::k’] mp_tac)
      \\ strip_tac \\ qexists_tac ‘ck’ \\ fs [])
    \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘AppK senv AppOp [] [se1]::k’] mp_tac)
    \\ strip_tac
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’
    \\ asm_rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ asm_rewrite_tac [step_n_add] \\ fs [step_def,push_def,return_def,continue_def]
    \\ Cases_on ‘eval_to n tenv tf’ \\ fs []
    >- (first_x_assum drule_all
      \\ disch_then (qspecl_then [‘st’,‘AppK senv AppOp [sv] []::k’] mp_tac)
      \\ rw [] \\ qexists_tac ‘ck'’ \\ fs [])
    \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘AppK senv AppOp [sv] []::k’] mp_tac)
    \\ rw []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’
    \\ asm_rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ asm_rewrite_tac [step_n_add] \\ fs [step_def,push_def,return_def,continue_def]
    \\ Cases_on ‘dest_anyClosure y'’ \\ fs []
    >- (fs [dest_anyClosure_def]
        \\ Cases_on ‘y'’ \\ gvs [dest_Closure_def,AllCaseEqs()])
    \\ rename [‘_ = INR yy’] \\ PairCases_on ‘yy’ \\ fs []
    \\ fs [application_def]
    \\ Cases_on ‘n=0’ \\ gvs []
    >-
     (qexists_tac ‘0’ \\ fs []
      \\ fs [dest_anyClosure_def]
      \\ Cases_on ‘y'’ \\ gvs [dest_Closure_def,AllCaseEqs()]
      \\ qpat_x_assum ‘v_rel _ _’ mp_tac
      \\ simp [Once v_rel_cases]
      \\ rw [] \\ fs [continue_def,is_halt_def])
    \\ fs [dest_anyClosure_def]
    \\ Cases_on ‘y'’ \\ gvs [dest_Closure_def,AllCaseEqs()]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    \\ first_x_assum drule
    \\ disch_then $ drule_at Any \\ fs []
    \\ ‘env_rel (l ++ [(s,y)]) ((s,sv)::senv')’ by
         (fs [env_rel_def,REVERSE_APPEND] \\ rw [] \\ fs [])
    \\ disch_then $ drule_at Any \\ fs []
    \\ fs [continue_def]
    \\ disch_then (qspecl_then [‘st’,‘k’] mp_tac)
    \\ strip_tac \\ fs []
    \\ qexists_tac ‘ck''’ \\ fs []
    \\ CASE_TAC \\ fs [])
  \\ cheat
QED


(******************** Notes ********************)

(*

  thunks are ((unit -> 'a) + 'a) ref

  envLang                       stateLang

  Prim (Cons "Ret") [x]       --> (fn u => App "force" (compile x ()))
  Prim (Cons "Bind") [x; y]   --> (fn u => Let v (compile x ()) (compile y () v))
  Prim (Cons "Handle") [x; y] --> (fn u => Handle (compile x ()) v (compile y () v))
  Prim (Msg ffi) [x]          --> (fn u => App (FFI ffi) [compile x])
  Prim (Cons "Act" [msg])     --> (fn u => compile msg ())

  Box x                       --> (Ref (Cons "INR" [(compile x)]))
  Delay x                     --> (Ref (Cons "INL" [fn u => (compile x) ()]))
  Force x                     --> force (compile x)

fun force t =
  case !t of
  | INL f => let val v = f () in (t := INR v; v) end
  | INR v => v


  env$Letrec [(x, y + 1); ...] rest

-->

  (* declare all references *)
  Let x (Ref (INL (fn u => Raise Bind)))
  (* use the bindings *)
  Letrec [...]
  (* update the references *)
    (x := INL (fn u => y + 1); compiler rest))



  step (Exp (LitInt i)) s c = (Val (Lit i), s, c)
  step (Exp (Raise x)) s c = (Exp x, s, RaiseC c)

  step (Val v) s (RaiseC (LetC ... c)) = (Val v, s, RaiseC c)

  eval exp s c = Act ffi msg s' c'



  env$semantics (Bind (Bind (Ret ...) (Bind ... (Act ...))))
~
  state$eval (fn _ => ...) ()

  eval : exp -> v

  itree_of : exp -> itree

  cakeml_semantics : exp -> io_oracle -> io_trace

*)

(****************************************)

CoInductive compiles_to:
  compiles_to Div Div ∧
  (∀x. compiles_to (Ret x) (Ret x)) ∧
  (∀t. compiles_to (Ret pure_semantics$Error) t) ∧
  (∀a f g.
     (∀x. f x ≠ g x ⇒ compiles_to (f x) (g x)) ⇒
     compiles_to (Vis a f) (Vis a g))
End

val _ = set_fixity "--->" (Infixl 480);
Overload "--->" = “compiles_to”;

Theorem safe_itree_compiles_to_IMP_eq:
  safe_itree x ∧ x ---> y ⇒
  x = y
Proof
  once_rewrite_tac [io_treeTheory.io_bisimulation] \\ rw []
  \\ qexists_tac ‘λx y. x = y ∨ safe_itree x ∧ x ---> y’ \\ fs []
  \\ rpt (pop_assum kall_tac) \\ rw []
  \\ gvs [Once compiles_to_cases]
  \\ fs [Once pure_semanticsTheory.safe_itree_cases]
  \\ metis_tac []
QED

Inductive cont_rel:
  (∀tk. tk = env_semantics$Done ⇒
    cont_rel tk [])
End

(*
Definition exp_or_v_rel_def:
  (exp_or_v_rel t (Exp senv se) ⇔
     ∃tenv te ss. t = eval tenv te ∧ env_rel ss tenv senv ∧ compile_rel e1 e2) ∧
  (exp_or_v_rel t (Val sv) ⇔
     ∃tv ss. t = INL sv ∧ v_rel ss tv sv)
End
*)

Theorem next_action_thm:
  compile_rel e1 e2 ∧
  LIST_REL (LIST_REL v_rel) ts ss ∧
  cont_rel tk sk ∧
  env_rel tenv senv ∧
  next_action (eval tenv e1) tk ts = tres ∧ tres ≠ Err ∧
  step_until_halt (Exp senv e2,ss,sk) = sres ⇒
  (tres = Div ⇒ sres = Div) ∧
  (tres = Ret ⇒ sres = Ret) ∧
  (∀a tk ts.
     tres = Act a tk ts ⇒
     ∃sk ss.
       sres = Act a sk ss ∧
       cont_rel tk sk ∧
       LIST_REL (LIST_REL v_rel) ts ss)
Proof
  cheat
QED

Theorem semantics_thm:
  compile_rel e1 e2 ∧ LIST_REL (LIST_REL v_rel) ts ss ∧
  cont_rel tk sk ∧ env_rel tenv senv ⇒
  env_semantics$semantics e1 tenv tk ts --->
  semantics e2 senv ss sk
Proof
  qsuff_tac ‘
    ∀t1 t2.
      (∃e1 e2 ts ss tenv senv tk sk.
        compile_rel e1 e2 ∧ LIST_REL (LIST_REL v_rel) ts ss ∧
        cont_rel tk sk ∧ env_rel tenv senv ∧
        t1 = env_semantics$semantics e1 tenv tk ts ∧
        t2 = semantics e2 senv ss sk) ⇒
      t1 ---> t2’
  >- fs [PULL_EXISTS]
  \\ ho_match_mp_tac compiles_to_coind
  \\ rpt gen_tac \\ strip_tac
  \\ ntac 2 (pop_assum $ mp_tac o GSYM)
  \\ simp [env_semanticsTheory.semantics_def]
  \\ simp [stateLangTheory.semantics_def]
  \\ simp [Once env_semanticsTheory.interp_def]
  \\ Cases_on ‘next_action (eval tenv e1) tk ts = Err’ >- fs []
  \\ simp [sinterp_def]
  \\ simp [Once io_treeTheory.io_unfold_err]
  \\ rename [‘io_unfold_err fs’]
  \\ ‘∃r1 r2. next_action (eval tenv e1) tk ts = r1 ∧
              step_until_halt (Exp senv e2,ss,sk) = r2’ by fs []
  \\ fs []
  \\ drule_all next_action_thm
  \\ Cases_on ‘r1’ \\ gvs []
  \\ strip_tac \\ fs []
  \\ rw [] \\ fs []
  \\ Cases \\ fs []
  \\ reverse IF_CASES_TAC >- fs []
  \\ fs [] \\ fs [value_def]
  \\ rw []
  \\ ‘interp (INR (Constructor "Ret" [Thunk (INR ([],Lit (Str y)))])) c l =
      interp (eval [] (Prim (Cons "Ret") [Delay (Lit (Str y))])) c l’ by
   (fs [eval_def,eval_to_def,result_map_def]
    \\ DEEP_INTRO_TAC some_intro \\ fs [])
  \\ pop_assum $ irule_at Any
  \\ rpt (first_assum $ irule_at Any)
  \\ simp [env_rel_def]
  \\ qexists_tac ‘[]’
  \\ qexists_tac ‘Lam "" (Lit (Str y))’
  \\ cheat
QED

Theorem compile_rel_itree_of:
  compile_rel e1 e2 ⇒
  env_semantics$itree_of e1 ---> stateLang$itree_of e2
Proof
  fs [env_semanticsTheory.itree_of_def,
      stateLangTheory.itree_of_def] \\ rw []
  \\ irule semantics_thm
  \\ simp [cont_rel_cases]
  \\ fs [env_rel_def]
QED

val _ = export_theory ();
