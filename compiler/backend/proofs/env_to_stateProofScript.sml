(*
  Correctness for compilation from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     envLangTheory thunkLang_primitivesTheory envLang_cexpTheory
     stateLangTheory env_semanticsTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_to_stateProof";

val _ = set_grammar_ancestry ["stateLang", "envLang", "env_semantics"];

Overload "app" = ``λe1 e2. App AppOp [e1;e2]``;
Overload "ret" = “λx. app (Let (SOME "v") x $
                             Let (SOME "v") (Delay (Var "v")) $
                               Lam NONE (Var "v")) Unit”

(****************************************)

Inductive compile_rel:

[~Var:]
  compile_rel (envLang$Var v) (stateLang$Var v) ∧

[~Ret:]
  (compile_rel te se ⇒
  compile_rel (Prim (Cons "Ret") [te])
              (Let (SOME "v") se $ Lam NONE (Var "v"))) ∧

[~Raise:]
  (compile_rel te se ⇒
  compile_rel (Prim (Cons "Raise") [te])
              (Let (SOME "v") se $ Lam NONE (Raise (Var "v")))) ∧

[~Bind:]
  (compile_rel te1 se1 ∧ compile_rel te2 se2 ⇒
  compile_rel
    (Prim (Cons "Bind") [Delay te1; Delay te2])
    (Lam NONE $ app (app se2 (app se1 Unit)) Unit)) ∧

[~Handle:]
  (compile_rel te1 se1 ∧ compile_rel te2 se2 ⇒
  compile_rel
    (Prim (Cons "Handle") [Delay te1; Delay te2])
    (Lam NONE $ app (HandleApp se2
      (Let (SOME "v") (app se1 Unit) (Lam NONE (Var "v")))) Unit)) ∧

[~Alloc:]
  (compile_rel tl sl ∧ compile_rel tx sx ⇒
  compile_rel (Prim (Cons "Alloc") [Delay tl; Delay tx])
              (Lam NONE $ ret (App Alloc [sl; Delay sx]))) ∧

[~Length:]
  (compile_rel tl sl ⇒
  compile_rel (Prim (Cons "Length") [Delay tl])
              (Lam NONE $ ret (App Length [sl]))) ∧

[~Deref:]
  (compile_rel tl sl ∧ compile_rel ti si ⇒
  compile_rel (Prim (Cons "Deref") [Delay tl; Delay ti])
              (Lam NONE $ ret (Handle (App Sub [si; sl]) "v"
                                      (Raise (Delay (Var "v")))))) ∧

[~Update:]
  (compile_rel tl sl ∧ compile_rel ti si ∧ compile_rel tx sx ⇒
  compile_rel (Prim (Cons "Update") [Delay tl; Delay ti; Delay tx])
              (Lam NONE $ ret (Handle (App Update [si; sl; Delay sx]) "v"
                                      (Raise (Delay (Var "v")))))) ∧

[~Message:]
  (compile_rel te se ⇒
  compile_rel
    (Prim (AtomOp (Message s)) [te])
    (Let (SOME x) se $ Lam NONE $ App (FFI s) [Var x])) ∧

[~Act:]
  (compile_rel te se ⇒
  compile_rel (Prim (Cons "Act") [Delay te]) (Lam NONE (ret (app se Unit)))) ∧

[~Proj:]
  (compile_rel te se ∧ s ∉ monad_cns ⇒
  compile_rel (Prim (Proj s n) [te]) (App (Proj s n) [se])) ∧

[~IsEq:]
  (compile_rel te se ∧ s ∉ monad_cns ⇒
  compile_rel (Prim (IsEq s n q) [te]) (App (IsEq s n) [se])) ∧

[~AtomOp:]
  (LIST_REL compile_rel tes ses ∧
   (∀s. aop ≠ Message s) ∧ (∀s1 s2. aop ≠ Lit (Msg s1 s2)) ⇒
  compile_rel (Prim (AtomOp aop) tes) (App (AtomOp aop) ses)) ∧

[~Cons:]
  (LIST_REL compile_rel tes ses ∧
   s ∉ monad_cns ⇒
  compile_rel (Prim (Cons s) tes) (App (Cons s) ses)) ∧

[~App:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (App te1 te2) (App AppOp [se1;se2])) ∧

[~Lam:]
  (∀x te se.
    compile_rel te se ⇒
    compile_rel (Lam x te) (Lam (SOME x) se)) ∧

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
    compile_rel (Box te) (Box se)) ∧

[~Delay:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Delay te) (Delay se)) ∧

[~Force:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Force te) (Force se))

End

Inductive v_rel:

[~Constructor:]
  (∀tvs svs.
     LIST_REL v_rel tvs svs ∧ ~(s IN monad_cns) ⇒
     v_rel (envLang$Constructor s tvs) (stateLang$Constructor s svs)) ∧

[~Closure:]
  (∀tenv senv te se.
     env_rel tenv senv ∧
     compile_rel te se ⇒
     v_rel (Closure x tenv te) (Closure (SOME x) senv se)) ∧

[~Recclosure:]
  (∀tenv senv tfns sfns n.
     env_rel tenv senv ∧
     LIST_REL ((=) ### compile_rel) tfns sfns ⇒
     v_rel (envLang$Recclosure tfns tenv n) (stateLang$Recclosure sfns senv n)) ∧

[~ThunkL:]
  (∀tv sv.
     v_rel tv sv ⇒
     v_rel (Thunk $ INL tv) (Thunk $ INL sv)) ∧

[~ThunkR:]
  (∀tenv senv te se.
     env_rel tenv senv ∧
     compile_rel te se ⇒
     v_rel (Thunk $ INR (tenv, te)) (Thunk $ INR (senv, se))) ∧

[~Atom:]
  (∀a.
     (∀msg x. ~(a = Msg msg x)) ⇒
     v_rel (Atom a) (Atom a)) ∧

[~Msg:]
  (∀msg s x senv.
     v_rel (Atom (Msg msg s))
           (Closure NONE ((x,Atom (Str s))::senv) (App (FFI msg) [Var x]))) ∧

[~Act:]
  (∀te se tenv senv.
     compile_rel te se ∧ env_rel tenv senv ⇒
     v_rel (Constructor "Act" [Thunk (INR (tenv,te))])
           (Closure NONE senv (ret (app se Unit)))) ∧

[~Ret:]
  (∀tv sv senv.
     v_rel tv sv ⇒
     v_rel (Constructor "Ret" [tv])
           (Closure NONE (("v",sv)::senv) (Var "v"))) ∧

[~Bind:]
  (∀te1 se1 te2 se2 tenv senv.
     compile_rel te1 se1 ∧ compile_rel te2 se2 ∧ env_rel tenv senv ⇒
     v_rel
       (Constructor "Bind" [Thunk (INR (tenv,te1)); Thunk (INR (tenv,te2))])
       (Closure NONE senv (app (app se2 (app se1 Unit)) Unit))) ∧

[~Handle:]
  (∀te1 se1 te2 se2 tenv senv.
     compile_rel te1 se1 ∧ compile_rel te2 se2 ∧ env_rel tenv senv ⇒
     v_rel
       (Constructor "Handle" [Thunk (INR (tenv,te1)); Thunk (INR (tenv,te2))])
       (Closure NONE senv
         (app (HandleApp se2 (Let (SOME "v") (app se1 Unit) (Lam NONE (Var "v")))) Unit))) ∧

[~Raise:]
  (∀tv sv senv.
     v_rel tv sv ⇒
     v_rel (Constructor "Raise" [tv])
           (Closure NONE (("v",sv)::senv) (Raise (Var "v")))) ∧

[~Length:]
  (∀tl sl tenv senv.
     compile_rel tl sl ∧ env_rel tenv senv ⇒
     v_rel (Constructor "Length" [Thunk (INR (tenv,tl))])
          (Closure NONE senv (ret (App Length [sl])))) ∧

[~Alloc:]
  (∀tl sl tenv senv.
     compile_rel tl sl ∧ compile_rel tx sx ∧ env_rel tenv senv ⇒
     v_rel
       (Constructor "Alloc" [Thunk (INR (tenv,tl)); Thunk (INR (tenv,tx))])
       (Closure NONE senv (ret (App Alloc [sl; Delay sx])))) ∧

[~Deref:]
  (∀tl sl ti si tenv senv.
     compile_rel tl sl ∧ compile_rel ti si ∧ env_rel tenv senv ⇒
     v_rel
       (Constructor "Deref" [Thunk (INR (tenv,tl)); Thunk (INR (tenv,ti))])
       (Closure NONE senv (ret (Handle (App Sub [si; sl]) "v"
                                       (Raise (Delay (Var "v"))))))) ∧

[~Update:]
  (∀tl sl ti si tx sx tenv senv.
     compile_rel tl sl ∧ compile_rel ti si ∧ compile_rel tx sx ∧ env_rel tenv senv ⇒
     v_rel
       (Constructor "Update"
         [Thunk (INR (tenv,tl)); Thunk (INR (tenv,ti)); Thunk (INR (tenv,tx))])
       (Closure NONE senv (ret (Handle (App Update [si; sl; Delay sx]) "v"
                                       (Raise (Delay (Var "v"))))))) ∧

[env_rel:]
  (∀tenv senv.
     (∀n tv.
       ALOOKUP tenv n = SOME tv ⇒
       ∃sv. ALOOKUP senv n = SOME sv ∧ v_rel tv sv) ⇒
     env_rel tenv senv)

End

Theorem env_rel_def = v_rel_cases |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL;

Theorem ALOOKUP_LIST_REL:
  ∀tfns sfns s tx.
    ALOOKUP tfns s = SOME tx ∧
    LIST_REL ($= ### compile_rel) tfns sfns ⇒
    ∃sx. ALOOKUP sfns s = SOME sx ∧ compile_rel tx sx
Proof
  Induct \\ Cases_on ‘sfns’ \\ fs [FORALL_PROD]
  \\ PairCases_on ‘h’ \\ fs [] \\ rw []
  \\ qpat_x_assum ‘compile_rel _ _’ mp_tac
  \\ simp [Once compile_rel_cases]
QED

Theorem ALOOKUP_LIST_REL_Lam:
  ∀tfns sfns s n tx.
    ALOOKUP tfns s = SOME (Lam n tx) ∧
    LIST_REL ($= ### compile_rel) tfns sfns ⇒
    ∃sx. ALOOKUP sfns s = SOME (Lam (SOME n) sx) ∧ compile_rel tx sx
Proof
  rw []
  \\ drule_all ALOOKUP_LIST_REL
  \\ rw [] \\ fs []
  \\ gvs [Once compile_rel_cases]
QED

Theorem env_rel_cons:
  v_rel tv sv ∧ env_rel tenv senv ⇒
  env_rel ((n,tv)::tenv) ((n,sv)::senv)
Proof
  rw [env_rel_def] \\ rw [] \\ fs []
QED

Theorem env_rel_rec:
  ∀xs ys.
    env_rel tenv' senv' ∧ LIST_REL ($= ### compile_rel) xs ys ∧
    env_rel tenv senv ∧ LIST_REL ($= ### compile_rel) tfns sfns ⇒
    env_rel (MAP (λ(fn,_). (fn,Recclosure tfns tenv fn)) xs ++ tenv')
            (MAP (λ(fn,_). (fn,Recclosure sfns senv fn)) ys ++ senv')
Proof
  Induct \\ Cases_on ‘ys’ \\ fs []
  \\ PairCases_on ‘h’ \\ Cases \\ fs [] \\ rw []
  \\ irule env_rel_cons \\ fs []
  \\ simp [Once v_rel_cases]
QED

Theorem v_rel_dest_anyThunk:
  v_rel th1 th2 ∧
  envLang$dest_anyThunk th1 = INR (xx0,xx1) ⇒
  ∃yy0 yy1.
    stateLang$dest_anyThunk th2 = SOME (yy0,yy1) ∧
    LIST_REL ($= ### compile_rel) xx1 yy1 ∧
    (∀xv. xx0 = INL xv ⇒ ∃yv. yy0 = INL yv ∧ v_rel xv yv) ∧
    (∀xenv x. xx0 = INR (xenv,x) ⇒
        ∃yenv y. yy0 = INR (yenv,y) ∧ compile_rel x y ∧
                 env_rel xenv yenv)
Proof
  reverse (Cases_on ‘th1’)
  \\ fs [envLangTheory.dest_anyThunk_def,envLangTheory.dest_Thunk_def]
  >- (simp [Once v_rel_cases] \\ rw []
      \\ fs [stateLangTheory.dest_anyThunk_def])
  \\ fs [AllCaseEqs()]
  \\ simp [Once v_rel_cases] \\ rw []
  \\ fs [stateLangTheory.dest_anyThunk_def]
  \\ drule_all ALOOKUP_LIST_REL
  \\ simp [Once compile_rel_cases] \\ rw [] \\ fs []
QED

Theorem v_rel_bool:
  (v_rel (Constructor "True" []) sv  ⇔ sv = Constructor "True" []) ∧
  (v_rel (Constructor "False" []) sv ⇔ sv = Constructor "False" [])
Proof
  once_rewrite_tac [v_rel_cases] \\ fs [] \\ EVAL_TAC
QED

Theorem v_rel_dest_anyClosure:
  v_rel tv sv ∧ dest_anyClosure tv = INR (a,tenv,te) ⇒
  ∃senv se.
    dest_anyClosure sv = SOME (SOME a,senv,se) ∧
    compile_rel te se ∧ env_rel tenv senv
Proof
  Cases_on ‘tv’ \\ fs [envLangTheory.dest_anyClosure_def,AllCaseEqs()]
  \\ simp [Once v_rel_cases] \\ rw [] \\ gvs []
  \\ fs [stateLangTheory.dest_anyClosure_def]
  \\ drule_all ALOOKUP_LIST_REL_Lam \\ rw [] \\ gvs []
  \\ irule env_rel_rec \\ fs []
QED

val step =
  LIST_CONJ [step_def,push_def,return_def,value_def,opt_bind_def,continue_def,
             application_def,dest_anyClosure_def,dest_Closure_def];

Theorem eval_to_list_div:
  ∀xs t n k aux sv.
    env_rel tenv senv ∧ LIST_REL compile_rel xs t ∧
    ¬MEM (INL Type_error) (MAP (eval_to n tenv) (REVERSE xs)) ∧
    (∀te se senv' st' k'.
       compile_rel te se ∧ env_rel tenv senv' ∧ MEM te xs ∧
       eval_to n tenv te ≠ INL Type_error ⇒
       ∃ck.
         case eval_to n tenv te of
           INL err => n ≤ ck ∧ ¬is_halt (step_n ck (Exp senv' se,st',k'))
         | INR tv =>
           ∃sv.
             step_n ck (Exp senv' se,st',k') = (Val sv,st',k') ∧
             v_rel tv sv) ⇒
    MEM (INL Diverge) (MAP (eval_to n tenv) xs) ⇒
    ∃ck1.
      n ≤ ck1 + 1 ∧
      ¬is_halt (step_n ck1 (Val sv,st,AppK senv op aux t::k))
Proof
  Induct >- fs [] \\ rw []
  \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
  \\ gvs [SF DNF_ss]
  \\ qpat_x_assum ‘∀x. _’ mp_tac
  \\ first_x_assum drule \\ fs []
  \\ disch_then drule
  \\ disch_then $ qspecl_then [‘st’,‘AppK senv op (sv::aux) ys::k’] strip_assume_tac
  \\ rw []
  >- (first_x_assum $ irule_at Any \\ fs [])
  \\ Cases_on ‘eval_to n tenv h’ \\ fs []
  >- (first_x_assum $ irule_at Any \\ fs [])
  \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
  \\ last_x_assum drule_all
  \\ disch_then $ qspecl_then [‘k’,‘sv::aux’,‘sv'’] strip_assume_tac
  \\ first_x_assum $ irule_at Any \\ fs []
QED

Theorem eval_to_list_val:
  ∀xs t k aux sv vs ts y.
    env_rel tenv senv ∧ LIST_REL compile_rel xs t ∧
    ¬MEM (INL Type_error) (MAP (eval_to n tenv) (REVERSE xs)) ∧
    ¬MEM (INL Diverge) (MAP (eval_to n tenv) (REVERSE xs)) ∧
    (∀te se senv' st' k'.
       compile_rel te se ∧ env_rel tenv senv' ∧ MEM te xs ∧
       eval_to n tenv te ≠ INL Type_error ⇒
       ∃ck.
         case eval_to n tenv te of
           INL err => n ≤ ck ∧ ¬is_halt (step_n ck (Exp senv' se,st',k'))
         | INR tv =>
           ∃sv.
             step_n ck (Exp senv' se,st',k') = (Val sv,st',k') ∧
             v_rel tv sv) ⇒
    LIST_REL v_rel ts vs ∧ v_rel y sv ⇒
    ∃ck1 svs.
      step_n ck1 (Val sv,st,AppK senv (Cons s) vs t::k) =
        (Val (Constructor s svs),st,k) ∧
      LIST_REL v_rel
         (REVERSE (MAP OUTR (MAP (eval_to n tenv) xs)) ++ [y] ++ ts) svs
Proof
  Induct \\ fs [] \\ rw[]
  >-
   (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ qexists_tac ‘0’ \\ fs [])
  \\ gvs [SF DNF_ss]
  \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
  \\ qpat_x_assum ‘∀x. _’ mp_tac
  \\ first_x_assum drule \\ fs []
  \\ disch_then drule
  \\ disch_then $ qspecl_then [‘st’,‘AppK senv (Cons s) (sv::vs) ys::k’] strip_assume_tac
  \\ rw []
  \\ Cases_on ‘eval_to n tenv h’ \\ gvs []
  >- (Cases_on ‘x’ \\ fs [])
  \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ last_x_assum irule
  \\ fs []
QED

Theorem step_n_AtomOp:
  ∀t ys a' vs.
    LIST_REL (λes a. ∀k. ∃ck. step_n ck (Exp senv es,st,k) = (Val (Atom a),st,k)) t ys ⇒
    ∃ck1. step_n ck1 (Val (Atom a'),st,AppK senv (AtomOp a) vs t::k) =
            application (AtomOp a) [] (MAP Atom (REVERSE ys) ++ Atom a' :: vs) st k
Proof
  Induct \\ fs [] \\ rw []
  >- (qexists_tac ‘1’ \\ fs [step])
  \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
  \\ first_x_assum $ qspec_then ‘AppK senv (AtomOp a) (Atom a'::vs) t::k’ strip_assume_tac
  \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
  \\ last_x_assum drule
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ rename [‘Atom a1::Atom a2::vs’]
  \\ disch_then $ qspecl_then [‘a1’,‘Atom a2 :: vs’] strip_assume_tac
  \\ qexists_tac ‘ck1’ \\ fs []
QED

Theorem eval_op_not_Msg:
  eval_op a as = SOME x ∧ (∀msg. a ≠ Message msg) ⇒
  EVERY (λa. ∀a1 a2. a ≠ Msg a1 a2) as
Proof
  strip_tac
  \\ gvs [DefnBase.one_line_ify NONE eval_op_def,AllCaseEqs()]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘z’
  \\ qid_spec_tac ‘as’
  \\ Induct \\ fs []
  \\ Cases \\ fs [concat_def,implode_def]
  \\ rw [] \\ res_tac
QED

Theorem get_atoms_MAP_Atom:
  ∀as. stateLang$get_atoms (MAP Atom as) = SOME as
Proof
  Induct \\ fs [stateLangTheory.get_atoms_def]
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
  >~ [‘Var v’] >-
   (fs [eval_to_def,AllCaseEqs()] \\ rw []
    \\ gvs [Once compile_rel_cases]
    \\ qexists_tac ‘1’ \\ fs []
    \\ fs [step_def]
    \\ fs [env_rel_def] \\ first_x_assum drule \\ rw []
    \\ gvs [value_def])
  >~ [‘App tf tx’] >-
   (simp [Once compile_rel_cases] \\ rw []
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
        \\ Cases_on ‘y'’ \\ gvs [envLangTheory.dest_anyClosure_def,
             envLangTheory.dest_Closure_def,AllCaseEqs()])
    \\ rename [‘_ = INR yy’] \\ PairCases_on ‘yy’ \\ fs []
    \\ fs [application_def]
    \\ Cases_on ‘n=0’ \\ gvs []
    >-
     (qexists_tac ‘0’ \\ fs []
      \\ fs [envLangTheory.dest_anyClosure_def]
      \\ Cases_on ‘y'’ \\ gvs [envLangTheory.dest_Closure_def,AllCaseEqs()]
      \\ qpat_x_assum ‘v_rel _ _’ mp_tac
      \\ simp [Once v_rel_cases]
      \\ rw [] \\ fs [continue_def,is_halt_def,stateLangTheory.dest_anyClosure_def]
      \\ drule_all ALOOKUP_LIST_REL_Lam \\ rw [] \\ fs [is_halt_def])
    \\ fs [envLangTheory.dest_anyClosure_def]
    \\ Cases_on ‘y'’ \\ gvs [envLangTheory.dest_Closure_def,AllCaseEqs()]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    >-
     (first_x_assum drule
      \\ disch_then $ drule_at Any \\ fs []
      \\ ‘env_rel ((s,y)::l) ((s,sv)::senv')’ by
        (fs [env_rel_def,REVERSE_APPEND] \\ rw [] \\ fs [])
      \\ disch_then $ drule_at Any \\ fs []
      \\ fs [continue_def,stateLangTheory.dest_anyClosure_def,
             stateLangTheory.dest_Closure_def]
      \\ disch_then (qspecl_then [‘st’,‘k’] mp_tac)
      \\ strip_tac \\ fs []
      \\ qexists_tac ‘ck''’ \\ fs []
      \\ CASE_TAC \\ fs [opt_bind_def])
    \\ fs [stateLangTheory.dest_anyClosure_def,
           stateLangTheory.dest_Closure_def]
    \\ drule_all ALOOKUP_LIST_REL_Lam \\ rw [] \\ fs []
    \\ fs [opt_bind_def,continue_def]
    \\ qmatch_goalsub_abbrev_tac ‘Exp senv1’
    \\ first_x_assum $ drule_then $ drule_at Any
    \\ disch_then (qspecl_then [‘senv1’,‘st’,‘k’] mp_tac)
    \\ impl_tac
    >-
     (unabbrev_all_tac \\ fs []
      \\ irule env_rel_cons \\ fs []
      \\ irule env_rel_rec \\ fs [])
    \\ strip_tac
    \\ qexists_tac ‘ck''’ \\ CASE_TAC \\ fs [])
  >~ [‘Lam nm tx’] >-
   (fs [Once compile_rel_cases] \\ gvs []
    \\ fs [eval_to_def]
    \\ qexists_tac ‘1’ \\ fs [step_def,value_def]
    \\ simp [Once v_rel_cases])
  >~ [‘Letrec tfns tx’] >-
   (simp [Once compile_rel_cases] \\ gvs []
    \\ rpt strip_tac \\ gvs []
    \\ fs [eval_to_def] \\ rw [] \\ fs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add]
    \\ fs [step_def,continue_def]
    \\ qmatch_goalsub_abbrev_tac ‘Exp senv1’
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [‘senv1’,‘st’,‘k’] mp_tac)
    \\ impl_tac
    >-
     (unabbrev_all_tac
      \\ irule env_rel_rec \\ fs []
      \\ last_x_assum mp_tac
      \\ last_x_assum mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ qid_spec_tac ‘tfns’
      \\ qid_spec_tac ‘sfns’
      \\ Induct \\ Cases_on ‘tfns’ \\ fs [FORALL_PROD]
      \\ PairCases_on ‘h’ \\ fs [])
    \\ strip_tac
    \\ qexists_tac ‘ck’ \\ fs [])
  >~ [‘Delay x’] >-
   (fs [eval_to_def,AllCaseEqs()] \\ rw []
    \\ gvs [Once compile_rel_cases]
    \\ qexists_tac ‘1’ \\ fs []
    \\ fs [step_def,value_def]
    \\ simp [Once v_rel_cases])
  >~ [‘Box x’] >-
   (simp [Once compile_rel_cases] \\ rw []
    \\ fs [eval_to_def]
    \\ Cases_on ‘eval_to n tenv x = INL Type_error’ >- fs [] \\ fs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ rename [‘compile_rel x y’] \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘BoxK::k’] mp_tac)
    \\ strip_tac
    \\ Cases_on ‘eval_to n tenv x’ \\ fs []
    >- (first_x_assum $ irule_at (Pos last) \\ fs [])
    \\ gvs []
    \\ qexists_tac ‘1+ck’
    \\ rewrite_tac [step_n_add]
    \\ fs [step_def,push_def,return_def,value_def]
    \\ simp [Once v_rel_cases])
  >~ [‘Force x’] >-
   (simp [Once compile_rel_cases] \\ rw []
    \\ fs [eval_to_def]
    \\ IF_CASES_TAC \\ gvs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ Cases_on ‘eval_to n tenv x = INL Type_error’ >- fs [] \\ fs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ rename [‘compile_rel x y’] \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘ForceK1::k’] mp_tac)
    \\ strip_tac
    \\ Cases_on ‘eval_to n tenv x’ \\ fs []
    >- (qexists_tac ‘ck’ \\ fs [is_halt_def])
    \\ rename [‘dest_anyThunk th1’]
    \\ rename [‘v_rel th1 th2’]
    \\ Cases_on ‘dest_anyThunk th1’ \\ fs []
    \\ imp_res_tac dest_anyThunk_INL \\ fs []
    \\ rename [‘INR xx’] \\ PairCases_on ‘xx’ \\ fs []
    \\ drule_all v_rel_dest_anyThunk
    \\ strip_tac
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ Cases_on ‘xx0’ \\ fs []
    >- (qexists_tac ‘1’ \\ fs [step_def,return_def,value_def])
    \\ rename [‘INR (INR aa,xx1)’] \\ PairCases_on ‘aa’ \\ fs []
    \\ gvs []
    \\ rename [‘compile_rel a1 a2’]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def,return_def,continue_def]
    \\ qmatch_goalsub_abbrev_tac ‘Exp env3’
    \\ last_x_assum $ drule_at $ Pos last
    \\ disch_then $ drule_then $ qspecl_then [‘env3’,‘NONE’,‘ForceK2 st::k’] mp_tac
    \\ unabbrev_all_tac
    \\ impl_tac >- (irule env_rel_rec \\ fs [])
    \\ strip_tac
    \\ CASE_TAC \\ fs []
    >- (first_x_assum $ irule_at $ Pos last \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ qexists_tac ‘1’ \\ fs [step_def,return_def,value_def])
  >~ [‘Let NONE x1 x2’] >-
   (simp [Once compile_rel_cases] \\ rw []
    \\ fs [eval_to_def]
    \\ IF_CASES_TAC \\ gvs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ Cases_on ‘eval_to (n-1) tenv x1 = INL Type_error’ >- fs [] \\ fs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ qpat_x_assum ‘compile_rel x1 se1’ assume_tac
    \\ last_x_assum assume_tac
    \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘LetK senv NONE se2::k’] mp_tac)
    \\ strip_tac
    \\ Cases_on ‘eval_to (n-1) tenv x1’ \\ fs []
    >- (qexists_tac ‘ck’ \\ fs [is_halt_def])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def,return_def,continue_def]
    \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘k’] mp_tac)
    \\ strip_tac
    \\ qexists_tac ‘ck'’ \\ fs []
    \\ CASE_TAC \\ fs [])
  >~ [‘Let (SOME ss) x1 x2’] >-
   (simp [Once compile_rel_cases] \\ rw []
    \\ fs [eval_to_def]
    \\ IF_CASES_TAC \\ gvs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ Cases_on ‘eval_to (n-1) tenv x1 = INL Type_error’ >- fs [] \\ fs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ qpat_x_assum ‘compile_rel x1 se1’ assume_tac
    \\ last_x_assum assume_tac
    \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘LetK senv (SOME ss) se2::k’] mp_tac)
    \\ strip_tac
    \\ Cases_on ‘eval_to (n-1) tenv x1’ \\ fs []
    >- (qexists_tac ‘ck’ \\ fs [is_halt_def])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def,return_def,continue_def]
    \\ ‘env_rel ((ss,y)::tenv) ((ss,sv)::senv)’ by (irule env_rel_cons \\ fs [])
    \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘k’] mp_tac)
    \\ strip_tac
    \\ qexists_tac ‘ck'’ \\ fs []
    \\ CASE_TAC \\ fs [])
  >~ [‘If x1 x2 x3’] >-
   (simp [Once compile_rel_cases] \\ rw []
    \\ fs [eval_to_def]
    \\ IF_CASES_TAC \\ gvs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ Cases_on ‘eval_to (n-1) tenv x1 = INL Type_error’ >- fs [] \\ fs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ qpat_x_assum ‘compile_rel x1 _’ assume_tac
    \\ last_x_assum assume_tac
    \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘IfK senv se1 se2::k’] mp_tac)
    \\ strip_tac
    \\ Cases_on ‘eval_to (n-1) tenv x1’ \\ fs []
    >- (qexists_tac ‘ck’ \\ fs [is_halt_def])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ gvs [AllCaseEqs(),v_rel_bool]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def,return_def,continue_def]
    \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,‘k’] mp_tac)
    \\ strip_tac
    \\ qexists_tac ‘ck'’ \\ fs []
    \\ CASE_TAC \\ fs [])
  \\ rename [‘Prim op xs’]
  \\ Cases_on ‘op’ \\ gvs []
  \\ TRY (fs [eval_to_def] \\ NO_TAC)
  >~ [‘Cons s’] >-
   (Cases_on ‘s = "Ret"’ \\ gvs [] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ fs [eval_to_def,result_map_def]
      \\ IF_CASES_TAC \\ gvs []
      \\ first_x_assum drule_all
      \\ disch_then $ qspecl_then [‘st’,‘LetK senv (SOME "v") (Lam NONE (Var "v"))::k’]
            strip_assume_tac
      \\ IF_CASES_TAC \\ gvs []
      >- (qexists_tac ‘ck’ \\ fs [])
      \\ ‘∃tv. eval_to n tenv te = INR tv’ by
        (Cases_on ‘eval_to n tenv te’ \\ fs [] \\ Cases_on ‘x’ \\ fs [])
      \\ gvs []
      \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ qexists_tac ‘0’ \\ fs []
      \\ simp [Once v_rel_cases])
    \\ Cases_on ‘s = "Raise"’ \\ gvs [] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ fs [eval_to_def,result_map_def]
      \\ IF_CASES_TAC \\ gvs []
      \\ first_x_assum drule_all
      \\ disch_then $ qspecl_then [‘st’,‘LetK senv (SOME "v") (Lam NONE (Raise (Var "v")))::k’]
            strip_assume_tac
      \\ IF_CASES_TAC \\ gvs []
      >- (qexists_tac ‘ck’ \\ fs [])
      \\ ‘∃tv. eval_to n tenv te = INR tv’ by
        (Cases_on ‘eval_to n tenv te’ \\ fs [] \\ Cases_on ‘x’ \\ fs [])
      \\ gvs []
      \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ qexists_tac ‘0’ \\ fs []
      \\ simp [Once v_rel_cases])
    \\ Cases_on ‘s = "Act"’ \\ gvs [] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
      \\ fs [eval_to_def,result_map_def] \\ qexists_tac ‘1’ \\ fs [step]
      \\ simp [Once v_rel_cases])
    \\ Cases_on ‘s = "Bind"’ \\ gvs [] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
      \\ fs [eval_to_def,result_map_def] \\ qexists_tac ‘1’
      \\ fs [step_def,push_def,return_def,continue_def,value_def]
      \\ simp [Once v_rel_cases])
    \\ Cases_on ‘s = "Handle"’ \\ gvs [] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
      \\ fs [eval_to_def,result_map_def] \\ qexists_tac ‘1’
      \\ fs [step_def,push_def,return_def,continue_def,value_def]
      \\ simp [Once v_rel_cases])
    \\ Cases_on ‘s = "Length"’ \\ gvs [] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
      \\ fs [eval_to_def,result_map_def] \\ qexists_tac ‘1’ \\ fs [step]
      \\ simp [Once v_rel_cases])
    \\ Cases_on ‘s = "Alloc"’ \\ gvs [] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
      \\ fs [eval_to_def,result_map_def] \\ qexists_tac ‘1’ \\ fs [step]
      \\ simp [Once v_rel_cases])
    \\ Cases_on ‘s = "Deref"’ \\ gvs [] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
      \\ fs [eval_to_def,result_map_def] \\ qexists_tac ‘1’ \\ fs [step]
      \\ simp [Once v_rel_cases])
    \\ Cases_on ‘s = "Update"’ \\ gvs [] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
      \\ fs [eval_to_def,result_map_def] \\ qexists_tac ‘1’ \\ fs [step]
      \\ simp [Once v_rel_cases])
    \\ simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [eval_to_def] \\ fs [SF ETA_ss]
    \\ fs [result_map_def]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ gvs [PULL_FORALL]
    \\ Cases_on ‘REVERSE ses’ \\ fs []
    >-
     (qexists_tac ‘0’ \\ fs [] \\ simp [Once v_rel_cases]
      \\ fs [monad_cns_def])
    \\ gvs [SWAP_REVERSE_SYM]
    \\ drule listTheory.EVERY2_REVERSE
    \\ strip_tac
    \\ full_simp_tac std_ss [REVERSE_APPEND]
    \\ fs []
    \\ ‘∀n. MEM n (REVERSE xs) = MEM n (x::xs')’ by metis_tac []
    \\ full_simp_tac std_ss [MEM_REVERSE]
    \\ fs [AND_IMP_INTRO]
    \\ first_assum $ drule_at Any
    \\ simp_tac std_ss []
    \\ disch_then $ drule_then $ qspecl_then [‘st’,‘AppK senv (Cons s) [] t::k’] mp_tac
    \\ impl_keep_tac
    >- (every_case_tac \\ gvs [] \\ gvs [MEM_MAP] \\ metis_tac [])
    \\ strip_tac
    \\ Cases_on ‘eval_to n tenv x’ \\ gvs []
    >-
     (rename [‘eval_to _ _ _ = INL yy’] \\ Cases_on ‘yy’ \\ gvs []
      \\ ‘MEM (INL Diverge) (MAP (eval_to n tenv) xs)’ by (fs [MEM_MAP] \\ metis_tac [])
      \\ fs [] \\ first_x_assum $ irule_at Any \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ gvs [SWAP_REVERSE_SYM,SF DNF_ss]
    \\ last_x_assum kall_tac
    \\ rewrite_tac [MEM_REVERSE,MAP_REVERSE]
    \\ IF_CASES_TAC \\ fs []
    >-
     (drule eval_to_list_div
      \\ rpt (disch_then $ drule_at Any)
      \\ gvs [GSYM PULL_FORALL] \\ rw []
      \\ irule_at Any (DECIDE “n ≤ k:num ⇒ n ≤ m + k”)
      \\ metis_tac [])
    \\ full_simp_tac bool_ss [MEM_REVERSE,MAP_REVERSE] \\ gvs []
    \\ simp [Once v_rel_cases,PULL_EXISTS]
    \\ fs [monad_cns_def]
    \\ drule_then drule eval_to_list_val
    \\ full_simp_tac bool_ss [MEM_REVERSE,MAP_REVERSE] \\ gvs []
    \\ rpt (disch_then drule)
    \\ disch_then $ drule_at $ Pos last
    \\ ‘LIST_REL v_rel [] []’ by fs []
    \\ disch_then $ drule_at $ Pos last
    \\ fs [GSYM PULL_FORALL])
  >~ [‘Proj s i’] >-
   (simp [Once compile_rel_cases,PULL_EXISTS] \\ rw []
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [eval_to_def] \\ fs []
    \\ Cases_on ‘n’ \\ fs [ADD1]
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ Cases_on ‘eval_to n' tenv te’ \\ fs [] \\ rw []
    >-
     (Cases_on ‘x’ \\ gvs []
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ Cases_on ‘y’ \\ fs [dest_Constructor_def]
    \\ pop_assum mp_tac
    \\ IF_CASES_TAC \\ fs [] \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ last_x_assum drule_all
    \\ disch_then $ qspecl_then [‘st’,‘AppK senv (Proj s i) [] []::k’] strip_assume_tac
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ pop_assum mp_tac
    \\ simp [Once v_rel_cases]
    \\ fs [monad_cns_def]
    \\ strip_tac \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ qexists_tac ‘0’ \\ fs []
    \\ gvs [listTheory.LIST_REL_EL_EQN])
  >~ [‘IsEq s i a’] >-
   (simp [Once compile_rel_cases,PULL_EXISTS] \\ rw []
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [eval_to_def] \\ fs []
    \\ Cases_on ‘n’ \\ fs [ADD1]
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ Cases_on ‘eval_to n' tenv te’ \\ fs [] \\ rw []
    >-
     (Cases_on ‘x’ \\ gvs []
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ Cases_on ‘y’ \\ fs [dest_Constructor_def]
    \\ pop_assum mp_tac
    \\ IF_CASES_TAC \\ fs [] \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ last_x_assum drule_all
    \\ disch_then $ qspecl_then [‘st’,‘AppK senv (IsEq s i) [] []::k’] strip_assume_tac
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ pop_assum mp_tac
    \\ simp [Once v_rel_cases]
    \\ fs [monad_cns_def]
    \\ strip_tac \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ qexists_tac ‘0’ \\ fs []
    \\ IF_CASES_TAC \\ gvs []
    \\ simp [Once v_rel_cases, monad_cns_def])
  \\ rename [‘AtomOp a’]
  \\ Cases_on ‘∃msg. a = Message msg’
  >-
   (simp [Once compile_rel_cases] \\ gvs [GSYM PULL_FORALL]
    \\ rpt strip_tac \\ gvs []
    \\ gvs [eval_to_def]
    \\ Cases_on ‘n=0’ \\ gvs [result_map_def]
    >- (qexists_tac ‘0’ \\ fs [result_map_def,is_halt_def])
    \\ Cases_on ‘eval_to (n − 1) tenv te’ \\ fs []
    >-
     (Cases_on ‘x'’ \\ fs []
      \\ first_x_assum drule_all \\ rw []
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ gvs []
    \\ Cases_on ‘y’ \\ gvs []
    \\ Cases_on ‘l’ \\ gvs [eval_op_def]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ first_x_assum drule_all
    \\ disch_then (qspecl_then [‘st’,
           ‘LetK senv (SOME x) (Lam NONE (App (FFI msg) [Var x]))::k’] strip_assume_tac)
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ qexists_tac ‘0’ \\ fs []
    \\ pop_assum mp_tac
    \\ simp [Once v_rel_cases] \\ rw []
    \\ simp [Once v_rel_cases] \\ rw [])
  \\ simp [Once compile_rel_cases]
  \\ fs [PULL_EXISTS] \\ rw []
  \\ Cases_on ‘eval_to n tenv (Prim (AtomOp a) xs)’ \\ gvs []
  >-
   (Cases_on ‘x’ \\ gvs [] \\ pop_assum mp_tac
    \\ Cases_on ‘n’ \\ fs []
    >- (fs [eval_to_def,result_map_def]
        \\ rw [] \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ simp [Once eval_to_def,ADD1]
    \\ fs [result_map_def]
    \\ every_case_tac \\ fs [] \\ fs [AllCaseEqs()]
    \\ fs [MEM_MAP,AllCaseEqs()]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Cases_on ‘REVERSE ses’
    >- (fs [] \\ gvs [])
    \\ fs []
    \\ gvs [SWAP_REVERSE_SYM]
    \\ drule listTheory.EVERY2_REVERSE
    \\ rewrite_tac [REVERSE_APPEND] \\ fs []
    \\ gvs [SWAP_REVERSE_SYM]
    \\ strip_tac
    \\ Cases_on ‘x = x'’ \\ fs [] \\ gvs []
    >- (last_x_assum $ qspec_then ‘x’ mp_tac \\ fs [ADD1])
    \\ rename [‘compile_rel h1 h2’]
    \\ first_assum $ qspec_then ‘h1’ mp_tac
    \\ rewrite_tac [] \\ strip_tac
    \\ last_assum $ qspec_then ‘h1’ mp_tac \\ rewrite_tac []
    \\ disch_then drule
    \\ disch_then drule
    \\ asm_rewrite_tac []
    \\ disch_then $ qspecl_then [‘st’,‘AppK senv (AtomOp a) [] t::k’] strip_assume_tac
    \\ Cases_on ‘eval_to n' tenv h1’ \\ gvs [ADD1]
    >- (metis_tac [])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ drule_then drule eval_to_list_div
    \\ Cases_on ‘ck’ \\ fs []
    \\ strip_tac
    \\ irule_at Any (DECIDE “n ≤ m+1 ⇒ n ≤ m + SUC k:num”)
    \\ pop_assum irule
    \\ gvs [SF DNF_ss]
    \\ fs [MEM_MAP,MEM_REVERSE]
    \\ metis_tac [])
  \\ pop_assum mp_tac
  \\ Cases_on ‘xs = []’ \\ gvs []
  >-
   (simp [Once eval_to_def,result_map_def]
    \\ CASE_TAC \\ strip_tac
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ fs [stateLangTheory.get_atoms_def]
    \\ every_case_tac \\ gvs []
    \\ qexists_tac ‘0’ \\ fs []
    \\ simp [Once v_rel_cases, monad_cns_def]
    \\ Cases_on ‘a’ \\ gvs [eval_op_def])
  \\ Cases_on ‘n’ \\ fs []
  >-
   (fs [eval_to_def,result_map_def] \\ Cases_on ‘xs’ \\ fs []
    \\ gvs [MEM_MAP])
  \\ fs [eval_to_def,result_map_def]
  \\ IF_CASES_TAC \\ fs []
  \\ fs [MEM_MAP,AllCaseEqs()]
  \\ IF_CASES_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ qmatch_asmsub_abbrev_tac ‘eval_op _ as’
  \\ ‘LIST_REL (λx a. eval_to n' tenv x = INR (Atom a)) xs as’ by
    (unabbrev_all_tac
     \\ qpat_x_assum ‘∀x. _’ mp_tac
     \\ qpat_x_assum ‘∀x. _’ mp_tac
     \\ qid_spec_tac ‘xs’ \\ Induct
     \\ fs []
     \\ simp []
     \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
     \\ first_x_assum $ irule_at Any
     \\ conj_tac >- (metis_tac [])
     \\ conj_tac >- (metis_tac [])
     \\ first_x_assum $ qspec_then ‘h’ mp_tac
     \\ first_x_assum $ qspec_then ‘h’ mp_tac
     \\ Cases_on ‘eval_to n' tenv h’ \\ fs []
     >- (Cases_on ‘x'’ \\ fs [])
     \\ Cases_on ‘y’ \\ fs [])
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ rw []
  \\ drule_all eval_op_not_Msg
  \\ strip_tac
  \\ ‘LIST_REL (λes a.
        ∀k. ∃ck. step_n ck (Exp senv es,st,k) = (Val (Atom a),st,k)) ses as’ by
   (pop_assum mp_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ last_x_assum mp_tac
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ qid_spec_tac ‘ses’
    \\ qid_spec_tac ‘as’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
    \\ gvs [PULL_EXISTS]
    \\ first_x_assum $ qspec_then ‘h’ mp_tac
    \\ rewrite_tac []
    \\ rpt (disch_then drule) \\ fs []
    \\ disch_then $ qspecl_then [‘st’,‘k’] strip_assume_tac \\ fs []
    \\ qexists_tac ‘ck’ \\ fs []
    \\ pop_assum mp_tac
    \\ Cases_on ‘a’
    \\ simp [Once v_rel_cases])
  \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
  \\ Cases_on ‘REVERSE ses’ \\ fs []
  \\ gvs [SWAP_REVERSE_SYM]
  \\ full_simp_tac std_ss [GSYM SNOC_APPEND,LIST_REL_SNOC]
  \\ rpt var_eq_tac
  \\ full_simp_tac std_ss [GSYM SNOC_APPEND,LIST_REL_SNOC,SNOC_11]
  \\ gvs []
  \\ first_x_assum $ qspec_then ‘AppK senv (AtomOp a) [] t::k’ strip_assume_tac
  \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
  \\ fs [SNOC_APPEND]
  \\ drule listTheory.EVERY2_REVERSE
  \\ rewrite_tac [REVERSE_REVERSE]
  \\ strip_tac
  \\ drule_all step_n_AtomOp
  \\ disch_then $ qspecl_then [‘k’,‘a’,‘a'’,‘[]’] strip_assume_tac
  \\ qexists_tac ‘ck1’
  \\ fs []
  \\ simp [application_def]
  \\ rewrite_tac [GSYM SNOC_APPEND,GSYM MAP_SNOC,get_atoms_MAP_Atom]
  \\ simp [SNOC_APPEND]
  \\ fs [value_def]
  \\ every_case_tac \\ gvs []
  \\ simp [Once v_rel_cases,monad_cns_def]
  \\ gvs [DefnBase.one_line_ify NONE eval_op_def,AllCaseEqs()]
QED

Theorem eval_thm:
  ∀tenv senv te se st k.
    compile_rel te se ∧ env_rel tenv senv ⇒
    eval tenv te = INL Type_error ∨
    (eval tenv te = INL Diverge ∧
     ∀n. ∃ck x1 x2 x3.
           n ≤ ck ∧ ~is_halt (x1,x2,x3) ∧
           step_n ck (Exp senv se, st, k) = (x1,x2,x3)) ∨
    ∃ck tv sv.
      eval tenv te = INR tv ∧
      step_n ck (Exp senv se, st, k) = (Val sv,st,k) ∧ v_rel tv sv
Proof
  rw [] \\ Cases_on ‘eval tenv te’ \\ gvs []
  >-
   (Cases_on ‘x’ \\ fs [] \\ rw []
    \\ gvs [eval_eq_Diverge]
    \\ pop_assum $ qspec_then ‘n’ assume_tac
    \\ drule eval_to_thm \\ fs []
    \\ rw [] \\ pop_assum drule_all
    \\ disch_then $ qspecl_then [‘st’,‘k’] strip_assume_tac
    \\ ‘∃tt. step_n ck (Exp senv se,st,k) = tt’ by fs [] \\ PairCases_on ‘tt’ \\ fs []
    \\ qexists_tac ‘ck’ \\ fs [])
  \\ drule eval_neq_Diverge \\ gvs []
  \\ strip_tac \\ fs []
  \\ drule eval_to_thm \\ fs []
QED

(****************************************)

Inductive cont_rel:
  (cont_rel Done [])
  ∧
  (∀tk sk senv tenv te se.
    cont_rel tk sk ∧ env_rel tenv senv ∧ compile_rel te se ⇒
    cont_rel (BC (Thunk (INR (tenv,te))) tk)
      (AppK senv AppOp [] [se] ::
       AppK senv AppOp [Constructor "" []] [] :: sk))
  ∧
  (∀tk sk senv tenv te se.
    cont_rel tk sk ∧ env_rel tenv senv ∧ compile_rel te se ⇒
    cont_rel (HC (Thunk (INR (tenv,te))) tk)
      (LetK senv (SOME "v") (Lam NONE (Var "v")) ::
       HandleAppK senv se ::
       AppK senv AppOp [Constructor "" []] [] :: sk))
End

Theorem eval_Delay:
  eval env (Delay e) = INR (Thunk (INR (env,e)))
Proof
  fs [eval_def,eval_to_def]
  \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
QED

Theorem next_thm:
  ∀k tv sv tk sk senv tres ts ss.
    v_rel tv sv ∧
    LIST_REL (LIST_REL v_rel) ts ss ∧
    cont_rel tk sk ∧
    next k (INR tv) tk ts = tres ∧ tres ≠ Err ⇒
    ∃n sres ss0 ss1 sk1.
      step_n n (Val sv,SOME ss,AppK senv AppOp [Constructor "" []] []::sk) =
          (sres,ss0,sk1) ∧
      (tres = Div ⇒ k ≤ n ∧ ~is_halt (sres,ss0,sk1)) ∧
      (tres = Ret ⇒ ss0 = SOME ss1 ∧
                    is_halt (sres,ss0,sk1) ∧ ∀ch c. sres ≠ Action ch c ∧ sres ≠ Error) ∧
      (∀a b tk ts1.
         tres = Act (a,b) tk ts1 ⇒
         ∃sk nenv1 nenv2.
           ss0 = SOME ss1 ∧
           sres = Action a b ∧
           cont_rel tk sk ∧ sk1 = LetK nenv1 (SOME "v")
               (Let (SOME "v") (Delay (Var "v")) (Lam NONE (Var "v")))::
               AppK nenv2 AppOp [Constructor "" []] []::sk ∧
           LIST_REL (LIST_REL v_rel) ts1 ss1)
Proof
  gen_tac \\ completeInduct_on ‘k’
  \\ gvs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ reverse (Cases_on ‘∃s vs. tv = Constructor s vs’)
  >- (Cases_on ‘tv’ \\ fs [Once next_def])
  \\ gvs []
  \\ pop_assum mp_tac
  \\ qpat_x_assum ‘v_rel _ _’ mp_tac
  \\ Cases_on ‘s = "Ret"’ >-
   (reverse (Cases_on ‘LENGTH vs = 1’) >- fs [Once next_def]
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ once_rewrite_tac [next_def] \\ gvs []
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘tk’ \\ fs []
    >-
     (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ qexists_tac ‘0’ \\ fs [GSYM PULL_FORALL]
      \\ fs [Once cont_rel_cases,is_halt_def])
    >-
     (IF_CASES_TAC \\ gvs []
      >- (qexists_tac ‘0’ \\ fs [is_halt_def])
      \\ strip_tac
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ qpat_x_assum ‘cont_rel _ _’ mp_tac
      \\ simp [Once cont_rel_cases]
      \\ strip_tac \\ gvs []
      \\ fs [force_apply_closure_def]
      \\ rename [‘env_rel tenv1 senv1’]
      \\ rename [‘compile_rel te1 se1’]
      \\ rename [‘cont_rel tk1 sk1’]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ qmatch_goalsub_abbrev_tac ‘(Exp senv1 se1,SOME ss,kk)’
      \\ drule_all eval_thm
      \\ disch_then (qspecl_then [‘SOME ss’,‘kk’] strip_assume_tac)
      \\ gvs []
      >-
       (pop_assum (qspec_then ‘k’ strip_assume_tac)
        \\ pop_assum $ irule_at Any \\ fs [])
      \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ simp [Abbr‘kk’]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add]
      \\ fs [step_def,return_def]
      \\ gvs [apply_closure_def,AllCaseEqs(),PULL_EXISTS,PULL_FORALL]
      \\ rename [‘dest_anyClosure tv1’]
      \\ Cases_on ‘dest_anyClosure tv1’ \\ fs []
      \\ PairCases_on ‘y’ \\ gvs []
      \\ gvs [application_def]
      \\ drule_all v_rel_dest_anyClosure
      \\ strip_tac \\ gvs [opt_bind_def,continue_def]
      \\ qmatch_asmsub_abbrev_tac ‘next _ (eval tenv2 _)’
      \\ qmatch_goalsub_abbrev_tac ‘step_n _  (Exp senv2 _,_)’
      \\ ‘env_rel tenv2 senv2’ by
         (unabbrev_all_tac \\ irule env_rel_cons
          \\ fs [] \\ simp [Once v_rel_cases])
      \\ drule_all eval_thm
      \\ disch_then (qspecl_then [‘SOME ss’,
           ‘AppK senv1 AppOp [Constructor "" []] []::sk1’] strip_assume_tac) \\ gvs []
      >- (gvs [EVAL “next k (INL Type_error) tk1 ts”])
      \\ gvs [GSYM PULL_FORALL]
      >-
       (once_rewrite_tac [next_def] \\ fs []
        \\ first_x_assum $ qspec_then ‘k’ strip_assume_tac
        \\ qexists_tac ‘ck'’ \\ fs [])
      \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ last_x_assum $ drule_at $ Pos last \\ fs []
      \\ disch_then drule_all
      \\ disch_then $ qspec_then ‘senv1’ strip_assume_tac
      \\ qexists_tac ‘n’ \\ fs []
      \\ Cases_on ‘next (k − 1) (INR tv') tk1 ts’ \\ fs [] \\ gvs []
      \\ Cases_on ‘e’ \\ gvs [])
    >-
     (IF_CASES_TAC \\ gvs []
      >- (qexists_tac ‘0’ \\ fs [is_halt_def])
      \\ strip_tac
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ qpat_x_assum ‘cont_rel _ _’ mp_tac \\ simp [Once cont_rel_cases]
      \\ rpt strip_tac \\ gvs []
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ last_x_assum $ drule_at $ Pos last \\ fs []
      \\ ntac 2 (disch_then $ drule_at $ Pos last)
      \\ qmatch_goalsub_abbrev_tac ‘Val vvv’
      \\ disch_then $ qspecl_then [‘vvv’,‘senv’] mp_tac
      \\ (impl_tac >- (unabbrev_all_tac \\ simp [Once v_rel_cases]))
      \\ strip_tac \\ gvs [GSYM PULL_FORALL]
      \\ qexists_tac ‘n’ \\ fs []
      \\ Cases_on ‘next (k − 1) (INR (Constructor "Ret" [tv])) c ts’
      \\ gvs [] \\ PairCases_on ‘e’ \\ fs []))
  \\ Cases_on ‘s = "Raise"’ >-
   (reverse (Cases_on ‘LENGTH vs = 1’) >- fs [Once next_def]
    \\ once_rewrite_tac [next_def] \\ fs []
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘tk’ \\ gvs []
    >-
     (fs [Once cont_rel_cases] \\ gvs []
      \\ ntac 5 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
      \\ qexists_tac ‘0’ \\ fs [GSYM PULL_FORALL,is_halt_def])
    >-
     (IF_CASES_TAC \\ gvs []
      >- (qexists_tac ‘0’ \\ fs [is_halt_def])
      \\ rpt strip_tac
      \\ qpat_x_assum ‘cont_rel (BC v c) sk’ mp_tac
      \\ simp [Once cont_rel_cases] \\ strip_tac \\ gvs []
      \\ last_x_assum $ drule_at $ Pos last \\ fs []
      \\ rpt (disch_then $ drule_at $ Pos last)
      \\ simp [Once v_rel_cases,monad_cns_def]
      \\ simp [PULL_EXISTS]
      \\ rpt (disch_then $ drule_at $ Pos last)
      \\ disch_then $ qspecl_then [‘senv’,‘senv'’] strip_assume_tac
      \\ gvs [GSYM PULL_FORALL]
      \\ qpat_x_assum ‘step_n n _ = _’ mp_tac
      \\ Cases_on ‘n’ \\ fs []
      >-
       (strip_tac \\ gvs [is_halt_def]
        \\ Cases_on ‘next (k − 1) (INR (Constructor "Raise" [tv])) c ts’
        \\ fs [] >- (qexists_tac ‘0’ \\ fs [])
        \\ qexists_tac ‘1’ \\ fs [step,is_halt_def])
      \\ rewrite_tac [ADD1,step_n_add] \\ fs [step]
      \\ Cases_on ‘n'’ \\ fs []
      >-
       (strip_tac \\ gvs [is_halt_def]
        \\ Cases_on ‘next (k − 1) (INR (Constructor "Raise" [tv])) c ts’
        \\ fs [] >- (qexists_tac ‘0’ \\ fs [])
        \\ qexists_tac ‘1+1’
        \\ fs [step_n_add] \\ fs [step,is_halt_def])
      \\ rewrite_tac [ADD1,step_n_add] \\ fs [step]
      \\ Cases_on ‘n’ \\ fs []
      >-
       (strip_tac \\ gvs [is_halt_def]
        \\ Cases_on ‘next (k − 1) (INR (Constructor "Raise" [tv])) c ts’
        \\ fs [] >- (qexists_tac ‘0’ \\ fs [])
        \\ qexists_tac ‘1+1+1’
        \\ fs [step_n_add] \\ fs [step,is_halt_def])
      \\ rewrite_tac [ADD1,step_n_add] \\ fs [step]
      \\ Cases_on ‘n'’ \\ fs []
      >-
       (strip_tac \\ gvs [is_halt_def]
        \\ Cases_on ‘next (k − 1) (INR (Constructor "Raise" [tv])) c ts’
        \\ fs [] >- (qexists_tac ‘0’ \\ fs [])
        \\ qexists_tac ‘1+1+1+1’
        \\ fs [step_n_add] \\ fs [step,is_halt_def])
      \\ rewrite_tac [ADD1,step_n_add] \\ fs [step]
      \\ strip_tac
      \\ ntac 6 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
      \\ gvs [ADD1]
      \\ pop_assum $ irule_at Any
      \\ Cases_on ‘next (k − 1) (INR (Constructor "Raise" [tv])) c ts’
      \\ fs [] \\ PairCases_on ‘e’ \\ fs [is_halt_def])
    >-
     (IF_CASES_TAC \\ gvs []
      >- (qexists_tac ‘0’ \\ fs [is_halt_def])
      \\ strip_tac
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ fs [force_apply_closure_def]
      \\ qpat_x_assum ‘cont_rel _ _’ mp_tac
      \\ simp [Once cont_rel_cases]
      \\ strip_tac \\ gvs []
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ rename [‘env_rel tenv1 senv1’]
      \\ rename [‘compile_rel te1 se1’]
      \\ rename [‘cont_rel tk1 sk1’]
      \\ drule_all eval_thm
      \\ qmatch_goalsub_abbrev_tac ‘(Exp senv1 se1,SOME ss,kk)’
      \\ disch_then (qspecl_then [‘SOME ss’,‘kk’] strip_assume_tac)
      \\ gvs []
      >-
       (pop_assum (qspec_then ‘k’ strip_assume_tac)
        \\ pop_assum $ irule_at Any \\ fs [])
      \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ simp [Abbr‘kk’]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add]
      \\ fs [step_def,return_def]
      \\ gvs [apply_closure_def,AllCaseEqs(),PULL_EXISTS,PULL_FORALL]
      \\ rename [‘dest_anyClosure tv1’]
      \\ Cases_on ‘dest_anyClosure tv1’ \\ fs []
      \\ PairCases_on ‘y’ \\ gvs []
      \\ gvs [application_def]
      \\ drule_all v_rel_dest_anyClosure
      \\ strip_tac \\ gvs [opt_bind_def,continue_def]
      \\ qmatch_asmsub_abbrev_tac ‘next _ (eval tenv2 _)’
      \\ qmatch_goalsub_abbrev_tac ‘step_n _  (Exp senv2 _,_)’
      \\ ‘env_rel tenv2 senv2’ by
         (unabbrev_all_tac \\ irule env_rel_cons
          \\ fs [] \\ simp [Once v_rel_cases])
      \\ drule_all eval_thm
      \\ disch_then (qspecl_then [‘SOME ss’,
           ‘AppK senv1 AppOp [Constructor "" []] []::sk1’] strip_assume_tac) \\ gvs []
      >- (gvs [EVAL “next k (INL Type_error) tk1 ts”])
      \\ gvs [GSYM PULL_FORALL]
      >-
       (once_rewrite_tac [next_def] \\ fs []
        \\ first_x_assum $ qspec_then ‘k’ strip_assume_tac
        \\ qexists_tac ‘ck'’ \\ fs [])
      \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ last_x_assum $ drule_at $ Pos last \\ fs []
      \\ disch_then drule_all
      \\ disch_then $ qspec_then ‘senv1’ strip_assume_tac
      \\ qexists_tac ‘n’ \\ fs []
      \\ Cases_on ‘next (k − 1) (INR tv') tk1 ts’ \\ fs [] \\ gvs []
      \\ Cases_on ‘e’ \\ gvs []))
  \\ Cases_on ‘s = "Bind"’ >-
   (reverse (Cases_on ‘LENGTH vs = 2’) >- fs [Once next_def]
    \\ once_rewrite_tac [next_def] \\ fs []
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ strip_tac
    \\ ntac 8 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ rename [‘step_n _ (Exp senv se1,SOME ss,_)’]
    \\ Cases_on ‘eval tenv te1’
    >-
     (Cases_on ‘x’ >- fs [Once next_def]
      \\ ntac 2 (pop_assum mp_tac) \\ once_rewrite_tac [next_def] \\ simp []
      \\ fs [eval_eq_Diverge]
      \\ disch_then (qspec_then ‘k’ assume_tac)
      \\ drule eval_to_thm
      \\ disch_then drule
      \\ disch_then drule \\ fs []
      \\ rename [‘(Exp senv se1,SOME ss,kk)’]
      \\ disch_then (qspecl_then [‘SOME ss’,‘kk’] strip_assume_tac)
      \\ ‘∃l. step_n ck (Exp senv se1,SOME ss,kk) = l’ by fs [] \\ PairCases_on ‘l’ \\ fs []
      \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ drule eval_neq_Diverge \\ fs [] \\ strip_tac
    \\ rename [‘eval_to ck’]
    \\ drule eval_to_thm
    \\ disch_then drule
    \\ disch_then drule \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘step_n _ (_,SOME _,k1)’
    \\ disch_then (qspecl_then [‘SOME ss’,‘k1’] strip_assume_tac)
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ last_x_assum $ drule_at $ Pos last \\ simp []
    \\ rpt (disch_then drule)
    \\ disch_then (qspecl_then [‘AppK senv AppOp [] [se2]::
             AppK senv AppOp [Constructor "" []] []::sk’,‘senv’] mp_tac)
    \\ impl_tac >- (simp [Once cont_rel_cases] \\ fs [])
    \\ fs [] \\ strip_tac
    \\ gvs [GSYM PULL_FORALL]
    \\ first_x_assum $ irule_at $ Pos hd
    \\ Cases_on ‘next (k − 1) (INR y) (BC (Thunk (INR (tenv,te2))) tk) ts’ \\ fs []
    \\ PairCases_on ‘e’ \\ fs [])
  \\ Cases_on ‘s = "Handle"’ >-
   (reverse (Cases_on ‘LENGTH vs = 2’) >- fs [Once next_def]
    \\ once_rewrite_tac [next_def] \\ fs []
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ strip_tac
    \\ ntac 9 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ rename [‘step_n _ (Exp senv se1,SOME ss,_)’]
    \\ qpat_x_assum ‘compile_rel te1 se1’ assume_tac
    \\ drule_all eval_thm
    \\ disch_then (qspecl_then [‘SOME ss’,
         ‘AppK senv AppOp [Constructor "" []] []::
           LetK senv (SOME "v") (Lam NONE (Var "v"))::HandleAppK senv se2::
               AppK senv AppOp [Constructor "" []] []::sk’] strip_assume_tac)
    \\ gvs [] >- (fs [Once next_def] \\ gvs [])
    >-
     (gvs [EVAL “next n (INL Diverge) k s”]
      \\ pop_assum (qspec_then ‘k’ strip_assume_tac)
      \\ first_x_assum $ irule_at Any \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ qabbrev_tac ‘tk3 = HC (Thunk (INR (tenv,te2))) tk’
    \\ qabbrev_tac ‘sk3 = LetK senv (SOME "v") (Lam NONE (Var "v"))::
                          HandleAppK senv se2::
                          AppK senv AppOp [Constructor "" []] []::sk’
    \\ ‘cont_rel tk3 sk3’ by (unabbrev_all_tac \\ simp [Once cont_rel_cases])
    \\ last_x_assum $ drule_at $ Pos last \\ fs []
    \\ disch_then drule_all
    \\ disch_then $ qspec_then ‘senv’ strip_assume_tac
    \\ gvs [GSYM PULL_FORALL]
    \\ Cases_on ‘next (k − 1) (INR tv) tk3 ts’ \\ gvs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ PairCases_on ‘e’ \\ gvs [])
  \\ Cases_on ‘s = "Act"’ >-
   (reverse (Cases_on ‘LENGTH vs = 1’) >- fs [Once next_def]
    \\ once_rewrite_tac [next_def] \\ fs []
    \\ simp [Once v_rel_cases,monad_cns_def] \\ rw []
    \\ ntac 8 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ gvs [with_atoms_def,force_list_def]
    \\ rename [‘env_rel tenv senv’]
    \\ drule_all_then (qspecl_then [‘SOME ss’,‘
         AppK senv AppOp [Constructor "" []] []::
               LetK senv (SOME "v")
                 (Let (SOME "v") (Delay (Var "v")) (Lam NONE (Var "v")))::
               AppK senv AppOp [Constructor "" []] []::sk’]
         strip_assume_tac) eval_thm \\ gvs []
    >-
     (pop_assum $ qspec_then ‘k’ strip_assume_tac \\ gvs []
      \\ qexists_tac ‘ck’ \\ fs [])
    \\ gvs [AllCaseEqs()]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Cases_on ‘tv’ \\ fs [get_atoms_def]
    \\ Cases_on ‘l’ \\ gvs [GSYM PULL_FORALL,PULL_EXISTS]
    \\ pop_assum mp_tac
    \\ simp [Once v_rel_cases]
    \\ strip_tac \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ qexists_tac ‘0’ \\ fs [])
  \\ Cases_on ‘s = "Alloc"’ >-
   (reverse (Cases_on ‘LENGTH vs = 2’) >- fs [Once next_def]
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ strip_tac \\ gvs [with_atoms_def,force_list_def] \\ strip_tac
    \\ ntac 8 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ rename [‘env_rel tenv senv’]
    \\ pop_assum mp_tac
    \\ qpat_x_assum ‘compile_rel tl sl’ assume_tac
    \\ once_rewrite_tac [next_def]
    \\ fs [with_atoms_def,force_list_def]
    \\ drule_all eval_thm
    \\ disch_then $ qspecl_then [‘SOME ss’,
         ‘AppK senv Alloc [Thunk (INR (senv,sx))] []::
               LetK senv (SOME "v")
                 (Let (SOME "v") (Delay (Var "v")) (Lam NONE (Var "v")))::
               AppK senv AppOp [Constructor "" []] []::sk’] strip_assume_tac
    \\ gvs []
    >-
     (first_x_assum $ qspec_then ‘k’ strip_assume_tac \\ fs []
      \\ first_x_assum $ irule_at Any \\ fs [])
    \\ Cases_on ‘tv’ \\ fs [get_atoms_def]
    \\ Cases_on ‘l’ \\ fs [get_atoms_def]
    \\ pop_assum mp_tac \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ strip_tac
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ qmatch_goalsub_abbrev_tac ‘Val vvv’
    \\ first_x_assum $ drule_at $ Pos last
    \\ fs [LIST_REL_SPLIT1,PULL_EXISTS]
    \\ rpt (disch_then $ drule_at Any)
    \\ qabbrev_tac ‘l = if i < 0 then 0 else Num i’
    \\ disch_then (qspecl_then [‘vvv’,‘senv’,‘REPLICATE l (Thunk (INR (senv,sx)))’] mp_tac)
    \\ impl_tac >-
     (fs [LIST_REL_REPLICATE_same,Abbr‘vvv’]
      \\ once_rewrite_tac [v_rel_cases] \\ fs []
      \\ simp [Once v_rel_cases]
      \\ simp [Once compile_rel_cases,env_rel_def]
      \\ simp [Once v_rel_cases]
      \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
    \\ strip_tac \\ gvs [GSYM PULL_FORALL]
    \\ qexists_tac ‘n’ \\ fs [SNOC_APPEND]
    \\ rename [‘next _ nnn _ mmm’]
    \\ Cases_on ‘next (k − 1) nnn tk mmm’ \\ gvs [is_halt_def]
    \\ PairCases_on ‘e’ \\ fs [])
  \\ Cases_on ‘s = "Length"’ >-
   (reverse (Cases_on ‘LENGTH vs = 1’) >- fs [Once next_def]
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ strip_tac \\ gvs [with_atoms_def,force_list_def] \\ strip_tac
    \\ ntac 6 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ rename [‘env_rel tenv senv’]
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [next_def] \\ fs []
    \\ fs [with_atoms_def,force_list_def]
    \\ drule_all eval_thm
    \\ disch_then $ qspecl_then [‘SOME ss’,
         ‘AppK senv Length [] []::
               LetK senv (SOME "v")
                 (Let (SOME "v") (Delay (Var "v")) (Lam NONE (Var "v")))::
               AppK senv AppOp [Constructor "" []] []::sk’] strip_assume_tac
    \\ gvs []
    >-
     (first_x_assum $ qspec_then ‘k’ strip_assume_tac \\ fs []
      \\ first_x_assum $ irule_at Any \\ fs [])
    \\ Cases_on ‘tv’ \\ fs [get_atoms_def]
    \\ Cases_on ‘l’ \\ fs [get_atoms_def]
    \\ IF_CASES_TAC >- fs [] \\ fs [GSYM NOT_LESS]
    \\ IF_CASES_TAC \\ fs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ strip_tac
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ qpat_x_assum ‘v_rel _ sv’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [listTheory.oEL_THM]
    \\ ntac 5 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ qmatch_goalsub_abbrev_tac ‘Val vvv’
    \\ first_x_assum $ drule_at $ Pos last
    \\ fs [LIST_REL_SPLIT1,PULL_EXISTS]
    \\ rpt (disch_then $ drule_at Any)
    \\ disch_then (qspecl_then [‘vvv’,‘senv’] mp_tac)
    \\ impl_tac >-
     (fs [LIST_REL_REPLICATE_same,Abbr‘vvv’]
      \\ once_rewrite_tac [v_rel_cases] \\ fs []
      \\ once_rewrite_tac [v_rel_cases] \\ fs []
      \\ simp [Once compile_rel_cases,env_rel_def]
      \\ once_rewrite_tac [v_rel_cases] \\ fs []
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ gvs [listTheory.LIST_REL_EL_EQN])
    \\ strip_tac \\ gvs [GSYM PULL_FORALL]
    \\ qexists_tac ‘n'’ \\ fs [SNOC_APPEND]
    \\ rename [‘next _ nnn _ mmm’]
    \\ Cases_on ‘next (k − 1) nnn tk mmm’ \\ gvs [is_halt_def]
    \\ PairCases_on ‘e’ \\ fs [])
  \\ Cases_on ‘s = "Deref"’ >-
   (reverse (Cases_on ‘LENGTH vs = 2’) >- fs [Once next_def]
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ strip_tac \\ gvs [with_atoms_def,force_list_def] \\ strip_tac
    \\ ntac 7 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ rename [‘env_rel tenv senv’]
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [next_def] \\ fs []
    \\ fs [with_atoms_def,force_list_def]
    \\ strip_tac
    \\ qpat_x_assum ‘compile_rel tl sl’ assume_tac
    \\ drule_all eval_thm
    \\ disch_then $ qspecl_then [‘SOME ss’,
                                 ‘AppK senv Sub [] [si]::
               HandleK senv "v" (Raise (Delay (Var "v")))::
               LetK senv (SOME "v")
                 (Let (SOME "v") (Delay (Var "v")) (Lam NONE (Var "v")))::
               AppK senv AppOp [Constructor "" []] []::sk’] strip_assume_tac
    \\ gvs []
    >-
     (first_x_assum $ qspec_then ‘k’ strip_assume_tac \\ fs []
      \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ qpat_x_assum ‘compile_rel ti si’ assume_tac
    \\ drule_all eval_thm
    \\ disch_then $ qspecl_then [‘SOME ss’,
                                 ‘AppK senv Sub [sv] []::
               HandleK senv "v" (Raise (Delay (Var "v")))::
               LetK senv (SOME "v")
                 (Let (SOME "v") (Delay (Var "v")) (Lam NONE (Var "v")))::
               AppK senv AppOp [Constructor "" []] []::sk’] strip_assume_tac
    \\ gvs []
    >-
     (first_x_assum $ qspec_then ‘k’ strip_assume_tac \\ fs []
      \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ rename [‘get_atoms [tv1; tv2]’]
    \\ Cases_on ‘get_atoms [tv1; tv2]’ \\ fs []
    \\ ‘∃a1 a2. get_atoms [tv1; tv2] = SOME [a1; a2] ∧
                tv1 = Atom a1 ∧ tv2 = Atom a2’ by
     (Cases_on ‘tv1’ \\ fs [env_semanticsTheory.get_atoms_def]
      \\ Cases_on ‘tv2’ \\ fs [env_semanticsTheory.get_atoms_def])
    \\ gvs []
    \\ Cases_on ‘a1’ \\ gvs []
    \\ Cases_on ‘a2’ \\ gvs []
    \\ IF_CASES_TAC >- fs []
    \\ IF_CASES_TAC \\ fs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ rpt (qpat_x_assum ‘v_rel _ _’ mp_tac \\ simp [Once v_rel_cases])
    \\ rpt strip_tac \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ gvs [GSYM NOT_LESS]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ gvs [oEL_THM]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ ‘LENGTH (EL n ss) = LENGTH (EL n ts)’ by gvs [listTheory.LIST_REL_EL_EQN]
    \\ gvs []
    \\ qpat_x_assum ‘_ ≠ Err’ mp_tac
    \\ IF_CASES_TAC \\ strip_tac
    >- (* within bounds case *)
     (gvs []
      \\ qabbrev_tac ‘tel = (EL (Num i) (EL n ts))’
      \\ qabbrev_tac ‘sel = (EL (Num i) (EL n ss))’
      \\ ‘v_rel tel sel’ by
       (unabbrev_all_tac
        \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
        \\ simp [Once listTheory.LIST_REL_EL_EQN]
        \\ disch_then drule
        \\ simp [Once listTheory.LIST_REL_EL_EQN]
        \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs [])
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
      \\ qmatch_goalsub_abbrev_tac ‘Val vvv’
      \\ first_x_assum $ drule_at $ Pos last
      \\ fs [LIST_REL_SPLIT1,PULL_EXISTS]
      \\ rpt (disch_then $ drule_at Any)
      \\ disch_then (qspecl_then [‘vvv’,‘senv’] mp_tac)
      \\ impl_tac >-
       (fs [LIST_REL_REPLICATE_same,Abbr‘vvv’]
        \\ once_rewrite_tac [v_rel_cases] \\ fs []
        \\ once_rewrite_tac [v_rel_cases] \\ fs []
        \\ simp [Once compile_rel_cases,env_rel_def]
        \\ once_rewrite_tac [v_rel_cases] \\ fs []
        \\ imp_res_tac LIST_REL_LENGTH \\ fs []
        \\ gvs [listTheory.LIST_REL_EL_EQN])
      \\ strip_tac \\ gvs [GSYM PULL_FORALL]
      \\ qexists_tac ‘n'’ \\ fs [SNOC_APPEND]
      \\ rename [‘next _ nnn _ mmm’]
      \\ Cases_on ‘next (k − 1) nnn tk mmm’ \\ gvs [is_halt_def]
      \\ PairCases_on ‘e’ \\ fs [])
    (* out of bounds case *)
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac \\ gvs [] \\ strip_tac
    \\ first_x_assum $ drule_at $ Pos last \\ fs []
    \\ rpt (disch_then $ drule_at $ Pos last)
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ gvs [PULL_EXISTS]
    \\ simp [Once v_rel_cases,monad_cns_def,PULL_EXISTS]
    \\ qabbrev_tac ‘aa = next (k − 1) (INR (RaiseVal (Constructor "Subscript" []))) tk ts’
    \\ simp [Once compile_rel_cases,GSYM PULL_FORALL]
    \\ rpt (disch_then (qspec_then ‘[("v",Constructor "Subscript" [])] ++ senv’ mp_tac))
    \\ impl_tac
    >- (fs [env_rel_def] \\ simp [Once v_rel_cases] \\ fs [monad_cns_def])
    \\ strip_tac \\ gvs [NOT_LESS]
    \\ rename [‘step_n nn’] \\ Cases_on ‘nn’ >-
     (gvs [is_halt_def]
      \\ Cases_on ‘aa’ \\ fs [] \\ TRY (Cases_on ‘e’ \\ fs []) \\ gvs []
      \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs [ADD1,step_n_add,step]
    \\ rename [‘step_n nn’] \\ Cases_on ‘nn’ >-
     (gvs [is_halt_def]
      \\ Cases_on ‘aa’ \\ fs [] \\ TRY (Cases_on ‘e’ \\ fs []) \\ gvs []
      \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs [ADD1,step_n_add,step]
    \\ rename [‘step_n nn’] \\ Cases_on ‘nn’ >-
     (gvs [is_halt_def]
      \\ Cases_on ‘aa’ \\ fs [] \\ TRY (Cases_on ‘e’ \\ fs []) \\ gvs []
      \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs [ADD1,step_n_add,step]
    \\ rename [‘step_n nn’] \\ Cases_on ‘nn’ >-
     (gvs [is_halt_def]
      \\ Cases_on ‘aa’ \\ fs [] \\ TRY (Cases_on ‘e’ \\ fs []) \\ gvs []
      \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs [ADD1,step_n_add,step]
    \\ ntac 9 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ first_x_assum $ irule_at $ Pos hd
    \\ Cases_on ‘aa’ \\ gvs []
    \\ PairCases_on ‘e’ \\ gvs [])
  \\ Cases_on ‘s = "Update"’ >-
   (reverse (Cases_on ‘LENGTH vs = 3’) >- fs [Once next_def]
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ strip_tac \\ gvs [with_atoms_def,force_list_def] \\ strip_tac
    \\ ntac 9 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ rename [‘env_rel tenv senv’]
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [next_def] \\ fs []
    \\ fs [with_atoms_def,force_list_def]
    \\ strip_tac
    \\ qabbrev_tac ‘k5 = HandleK senv "v" (Raise (Delay (Var "v")))::
               LetK senv (SOME "v")
                 (Let (SOME "v") (Delay (Var "v")) (Lam NONE (Var "v")))::
               AppK senv AppOp [Constructor "" []] []::sk’
    \\ qpat_x_assum ‘compile_rel tl sl’ assume_tac
    \\ drule_all eval_thm
    \\ disch_then $ qspecl_then [‘SOME ss’,
         ‘AppK senv Update [Thunk (INR (senv,sx))] [si]::k5’] strip_assume_tac
    \\ gvs []
    >-
     (first_x_assum $ qspec_then ‘k’ strip_assume_tac \\ fs []
      \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ qpat_x_assum ‘compile_rel ti si’ assume_tac
    \\ drule_all eval_thm
    \\ disch_then $ qspecl_then [‘SOME ss’,
        ‘AppK senv Update [sv; Thunk (INR (senv,sx))] []::k5’] strip_assume_tac
    \\ gvs []
    >-
     (first_x_assum $ qspec_then ‘k’ strip_assume_tac \\ fs []
      \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ rename [‘get_atoms [tv1; tv2]’]
    \\ Cases_on ‘get_atoms [tv1; tv2]’ \\ fs []
    \\ ‘∃a1 a2. get_atoms [tv1; tv2] = SOME [a1; a2] ∧
                tv1 = Atom a1 ∧ tv2 = Atom a2’ by
     (Cases_on ‘tv1’ \\ fs [env_semanticsTheory.get_atoms_def]
      \\ Cases_on ‘tv2’ \\ fs [env_semanticsTheory.get_atoms_def])
    \\ gvs []
    \\ Cases_on ‘a1’ \\ gvs []
    \\ Cases_on ‘a2’ \\ gvs []
    \\ IF_CASES_TAC >- fs []
    \\ IF_CASES_TAC \\ fs []
    >- (qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ rpt (qpat_x_assum ‘v_rel (Atom _) _’ mp_tac \\ simp [Once v_rel_cases])
    \\ rpt strip_tac \\ gvs []
    \\ gvs [GSYM NOT_LESS]
    \\ Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step]
    \\ gvs [oEL_THM]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
    \\ ‘LENGTH (EL n ss) = LENGTH (EL n ts)’ by gvs [listTheory.LIST_REL_EL_EQN]
    \\ gvs []
    \\ qpat_x_assum ‘_ ≠ Err’ mp_tac
    \\ IF_CASES_TAC \\ strip_tac
    >- (* within bounds case *)
     (gvs [Abbr‘k5’]
      \\ ntac 6 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
      \\ qmatch_goalsub_abbrev_tac ‘(Val vvv, SOME sss, _)’
      \\ first_x_assum $ drule_at $ Pos last
      \\ fs [LIST_REL_SPLIT1,PULL_EXISTS]
      \\ rpt (disch_then $ drule_at Any)
      \\ disch_then (qspecl_then [‘vvv’,‘senv’,‘sss’] mp_tac)
      \\ impl_tac >-
       (fs [LIST_REL_REPLICATE_same,Abbr‘vvv’]
        \\ once_rewrite_tac [v_rel_cases] \\ fs []
        \\ once_rewrite_tac [v_rel_cases] \\ fs []
        \\ simp [Once compile_rel_cases,env_rel_def]
        \\ once_rewrite_tac [v_rel_cases] \\ fs []
        \\ fs [monad_cns_def,Abbr‘sss’]
        \\ rpt (irule_at Any EVERY2_LUPDATE_same)
        \\ fs []
        \\ once_rewrite_tac [v_rel_cases] \\ fs []
        \\ gvs [listTheory.LIST_REL_EL_EQN])
      \\ strip_tac \\ gvs [GSYM PULL_FORALL]
      \\ qexists_tac ‘n'’ \\ fs [SNOC_APPEND]
      \\ rename [‘next _ nnn _ mmm’]
      \\ Cases_on ‘next (k − 1) nnn tk mmm’ \\ gvs [is_halt_def]
      \\ PairCases_on ‘e’ \\ fs [])
    (* out of bounds case *)
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac \\ gvs [] \\ strip_tac
    \\ first_x_assum $ drule_at $ Pos last \\ fs []
    \\ rpt (disch_then $ drule_at $ Pos last)
    \\ simp [Once v_rel_cases,monad_cns_def]
    \\ gvs [PULL_EXISTS]
    \\ simp [Once v_rel_cases,monad_cns_def,PULL_EXISTS]
    \\ qabbrev_tac ‘aa = next (k − 1) (INR (RaiseVal (Constructor "Subscript" []))) tk ts’
    \\ simp [Once compile_rel_cases,GSYM PULL_FORALL]
    \\ rpt (disch_then (qspec_then ‘[("v",Constructor "Subscript" [])] ++ senv’ mp_tac))
    \\ impl_tac
    >- (fs [env_rel_def] \\ simp [Once v_rel_cases] \\ fs [monad_cns_def])
    \\ strip_tac \\ gvs [NOT_LESS,Abbr‘k5’]
    \\ rename [‘step_n nn’] \\ Cases_on ‘nn’ >-
     (gvs [is_halt_def]
      \\ Cases_on ‘aa’ \\ fs [] \\ TRY (Cases_on ‘e’ \\ fs []) \\ gvs []
      \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs [ADD1,step_n_add,step]
    \\ rename [‘step_n nn’] \\ Cases_on ‘nn’ >-
     (gvs [is_halt_def]
      \\ Cases_on ‘aa’ \\ fs [] \\ TRY (Cases_on ‘e’ \\ fs []) \\ gvs []
      \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs [ADD1,step_n_add,step]
    \\ rename [‘step_n nn’] \\ Cases_on ‘nn’ >-
     (gvs [is_halt_def]
      \\ Cases_on ‘aa’ \\ fs [] \\ TRY (Cases_on ‘e’ \\ fs []) \\ gvs []
      \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs [ADD1,step_n_add,step]
    \\ rename [‘step_n nn’] \\ Cases_on ‘nn’ >-
     (gvs [is_halt_def]
      \\ Cases_on ‘aa’ \\ fs [] \\ TRY (Cases_on ‘e’ \\ fs []) \\ gvs []
      \\ qexists_tac ‘0’ \\ fs [is_halt_def])
    \\ fs [ADD1,step_n_add,step]
    \\ ntac 9 (Q.REFINE_EXISTS_TAC ‘ck1+1’ \\ rewrite_tac [step_n_add] \\ fs [step])
    \\ first_x_assum $ irule_at $ Pos hd
    \\ Cases_on ‘aa’ \\ gvs []
    \\ PairCases_on ‘e’ \\ gvs [])
  \\ once_rewrite_tac [next_def] \\ fs []
QED

Theorem next_eval_thm:
  ∀k e1 e2 tk sk senv tenv tres ts ss.
    compile_rel e1 e2 ∧
    LIST_REL (LIST_REL v_rel) ts ss ∧
    cont_rel tk sk ∧
    env_rel tenv senv ∧
    next k (eval tenv e1) tk ts = tres ∧ tres ≠ Err ⇒
    ∃n sres ss0 ss1 sk1.
      step_n n (Exp senv e2,SOME ss,AppK senv AppOp [Constructor "" []] []::sk) =
          (sres,ss0,sk1) ∧
      (tres = Div ⇒ k ≤ n ∧ ~is_halt (sres,ss0,sk1)) ∧
      (tres = Ret ⇒ ss0 = SOME ss1 ∧
                    is_halt (sres,ss0,sk1) ∧ ∀ch c. sres ≠ Action ch c ∧ sres ≠ Error) ∧
      (∀a b tk ts1.
         tres = Act (a,b) tk ts1 ⇒
         ∃sk nenv1 nenv2.
           ss0 = SOME ss1 ∧
           sres = Action a b ∧
           cont_rel tk sk ∧ sk1 = LetK nenv1 (SOME "v")
               (Let (SOME "v") (Delay (Var "v")) (Lam NONE (Var "v")))::
               AppK nenv2 AppOp [Constructor "" []] []::sk ∧
           LIST_REL (LIST_REL v_rel) ts1 ss1)
Proof
  rw [] \\ pop_assum mp_tac
  \\ Cases_on ‘eval tenv e1 = INL Type_error’ \\ fs []
  >- simp [Once next_def]
  \\ Cases_on ‘eval tenv e1 = INL Diverge’ \\ fs []
  >-
   (ntac 5 (simp [Once next_def])
    \\ fs [eval_eq_Diverge]
    \\ first_x_assum $ qspec_then ‘k’ assume_tac
    \\ drule eval_to_thm \\ fs []
    \\ disch_then drule_all
    \\ rename [‘SOME _,kk’]
    \\ disch_then (qspecl_then [‘SOME ss’,‘kk’] mp_tac) \\ rw []
    \\ ‘∃a. step_n ck (Exp senv e2,SOME ss,kk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  \\ reverse (Cases_on ‘∃s vs. eval tenv e1 = INR (Constructor s vs)’)
  >-
   (Cases_on ‘eval tenv e1’ \\ fs []
    >- (Cases_on ‘x’ \\ fs [])
    \\ Cases_on ‘y’ \\ once_rewrite_tac [next_def] \\ fs [])
  \\ gvs []
  \\ drule eval_neq_Diverge \\ fs []
  \\ strip_tac
  \\ rename [‘eval_to ck’]
  \\ drule eval_to_thm \\ fs []
  \\ disch_then drule_all
  \\ disch_then (qspecl_then [‘SOME ss’,‘AppK senv AppOp [Constructor "" []] []::sk’] mp_tac)
  \\ rpt strip_tac
  \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’
  \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
  \\ ‘∃res. next k (INR (Constructor s vs)) tk ts = res’ by fs []
  \\ fs []
  \\ drule_all next_thm
  \\ disch_then (qspec_then ‘senv’ strip_assume_tac)
  \\ first_x_assum $ irule_at Any
  \\ Cases_on ‘res’ \\ fs []
  \\ PairCases_on ‘e’ \\ fs []
QED

Theorem next_action_thm:
  compile_rel e1 e2 ∧
  LIST_REL (LIST_REL v_rel) ts ss ∧
  cont_rel tk sk ∧
  env_rel tenv senv ∧
  next_action (eval tenv e1) tk ts = tres ∧ tres ≠ Err ∧
  step_until_halt (Exp senv e2,SOME ss,AppK senv AppOp [Constructor "" []] []::sk) = sres ⇒
  (tres = Div ⇒ sres = Div) ∧
  (tres = Ret ⇒ sres = Ret) ∧
  (∀a tk ts.
     tres = Act a tk ts ⇒
     ∃sk ss nenv1 nenv2.
       sres = Act a (LetK nenv1 (SOME "v")
               (Let (SOME "v") (Delay (Var "v")) (Lam NONE (Var "v")))::
               AppK nenv2 AppOp [Constructor "" []] []::sk) (SOME ss) ∧
       cont_rel tk sk ∧
       LIST_REL (LIST_REL v_rel) ts ss)
Proof
  fs [next_action_def]
  \\ CASE_TAC
  >-
   (pop_assum mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
    \\ fs [step_until_halt_def,AllCaseEqs()]
    \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
    \\ ‘∃s. next x (eval tenv e1) tk ts = s’ by fs []
    \\ ‘s = Div’ by metis_tac []
    \\ ‘s ≠ Err ∧ x ≤ x’ by gvs []
    \\ drule_all next_eval_thm \\ fs []
    \\ strip_tac \\ gvs []
    \\ ‘x = n ∨ x < n’ by fs [] \\ gvs []
    \\ strip_tac
    \\ drule_all step_n_mono
    \\ strip_tac \\ gvs [])
  \\ pop_assum mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ rpt (disch_then strip_assume_tac)
  \\ ‘tres ≠ Div’ by fs [] \\ fs []
  \\ qpat_x_assum ‘_ = _’ mp_tac
  \\ fs [step_until_halt_def]
  \\ CASE_TAC
  \\ pop_assum mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ fs []
  \\ rpt (disch_then strip_assume_tac)
  >-
   (CCONTR_TAC
    \\ drule_all next_eval_thm
    \\ fs []
    >- metis_tac  []
    \\ PairCases_on ‘a’ \\ fs []
    \\ gvs [] \\ rw []
    \\ first_x_assum (qspec_then ‘n’ mp_tac)
    \\ gvs [is_halt_def])
  \\ ‘∃t. (step_n x'
             (Exp senv e2,SOME ss,AppK senv AppOp [Constructor "" []] []::sk)) = t’ by fs []
  \\ PairCases_on ‘t’ \\ fs []
  \\ drule_all next_eval_thm \\ fs []
  \\ strip_tac
  \\ ‘(sres',ss0,sk1) = (t0,t1,t2)’ by
   (qpat_x_assum ‘is_halt (t0,t1,t2)’ mp_tac
    \\ ‘is_halt (sres',ss0,sk1)’ by
      (Cases_on ‘tres’ \\ fs [] \\ Cases_on ‘e’ \\ fs [is_halt_def])
    \\ pop_assum mp_tac
    \\ rpt (qpat_x_assum ‘_ = _’ (rewrite_tac o single o SYM))
    \\ rename [‘step_n _ abc’]
    \\ rename [‘step_n n1 _ = step_n n2 _’]
    \\ ‘n1 < n2 ∨ n1 = n2 ∨ n2 < n1’ by fs [] \\ gvs []
    \\ rw []
    \\ drule_all step_n_mono
    \\ strip_tac \\ gvs [])
  \\ rw []
  >-
   (res_tac \\ fs []
    \\ Cases_on ‘sres'’ \\ fs [])
  \\ PairCases_on ‘a’ \\ fs []
QED

Theorem semantics_app_Unit:
  semantics (app e2 Unit) senv ss sk =
  semantics e2 senv ss (AppK senv AppOp [Constructor "" []] []::sk)
Proof
  fs [stateLangTheory.semantics_def,sinterp_def]
  \\ once_rewrite_tac [io_treeTheory.io_unfold_err] \\ fs []
  \\ qsuff_tac
    ‘step_until_halt (Exp senv (app e2 Unit),ss,sk) =
     step_until_halt (Exp senv e2,ss,AppK senv AppOp [Constructor "" []] []::sk)’
  >- fs []
  \\ irule EQ_TRANS
  \\ irule_at Any step_unitl_halt_unwind
  \\ fs [step_def,push_def]
  \\ irule EQ_TRANS
  \\ irule_at Any step_unitl_halt_unwind
  \\ fs [step_def,push_def,application_def,value_def]
  \\ irule EQ_TRANS
  \\ irule_at Any step_unitl_halt_unwind
  \\ fs [step_def,push_def,application_def,value_def,return_def,continue_def]
QED

Theorem semantics_thm:
  compile_rel e1 e2 ∧ LIST_REL (LIST_REL v_rel) ts ss ∧
  cont_rel tk sk ∧ env_rel tenv senv ⇒
  env_semantics$semantics e1 tenv tk ts --->
  semantics (app e2 Unit) senv (SOME ss) sk
Proof
  fs [semantics_app_Unit]
  \\ qsuff_tac ‘
    ∀t1 t2.
      (∃e1 e2 ts ss tenv senv tk sk.
        compile_rel e1 e2 ∧ LIST_REL (LIST_REL v_rel) ts ss ∧
        cont_rel tk sk ∧ env_rel tenv senv ∧
        t1 = env_semantics$semantics e1 tenv tk ts ∧
        t2 = semantics e2 senv (SOME ss) (AppK senv AppOp [Constructor "" []] []::sk)) ⇒
      t1 ---> t2’
  >- fs [PULL_EXISTS]
  \\ ho_match_mp_tac pure_semanticsTheory.compiles_to_coind
  \\ rpt gen_tac \\ strip_tac
  \\ ntac 2 (pop_assum $ mp_tac o GSYM)
  \\ simp [env_semanticsTheory.semantics_def]
  \\ simp [stateLangTheory.semantics_def]
  \\ simp [Once env_semanticsTheory.interp_def]
  \\ Cases_on ‘next_action (eval tenv e1) tk ts = Err’ >- fs []
  \\ simp [sinterp_def]
  \\ simp [Once io_treeTheory.io_unfold_err]
  \\ qmatch_goalsub_abbrev_tac ‘io_unfold_err fs’
  \\ ‘∃r1 r2. next_action (eval tenv e1) tk ts = r1 ∧
              step_until_halt (Exp senv e2,SOME ss,
                AppK senv AppOp [Constructor "" []] []::sk) = r2’ by fs []
  \\ fs []
  \\ drule_all next_action_thm
  \\ Cases_on ‘r1’ \\ gvs []
  \\ strip_tac \\ fs []
  \\ rw [] \\ fs []
  \\ Cases \\ fs []
  \\ reverse IF_CASES_TAC >- fs []
  \\ fs [] \\ fs [value_def]
  \\ rw []
  \\ ‘interp (INR (Constructor "Ret" [Thunk (INR ([("v",Atom (Str y))],Var "v"))])) c l =
      interp (eval [("v",Atom (Str y))] (Prim (Cons "Ret") [Delay (Var "v")])) c l’ by
   (fs [eval_def,eval_to_def,result_map_def]
    \\ DEEP_INTRO_TAC some_intro \\ fs [])
  \\ pop_assum $ irule_at Any
  \\ ‘compile_rel (Prim (Cons "Ret") [Delay (Var "v")])
        (Let (SOME "v") (Delay (Var "v")) $ Lam NONE (Var "v"))’ by
            (rpt (simp [Once compile_rel_cases]))
  \\ pop_assum $ irule_at Any
  \\ rpt (first_assum $ irule_at $ Pos hd)
  \\ qexists_tac ‘[("v",Atom (Str y))] ++ nenv1’
  \\ conj_tac
  >- fs [env_rel_def,Once v_rel_cases]
  \\ once_rewrite_tac [io_treeTheory.io_unfold_err]
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ unabbrev_all_tac \\ fs []
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ ntac 7 (irule EQ_TRANS
             \\ irule_at Any step_unitl_halt_unwind \\ fs [step])
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ ntac 10 (irule EQ_TRANS
              \\ irule_at Any step_unitl_halt_unwind \\ fs [step])
QED

Theorem compile_rel_itree_of:
  compile_rel e1 e2 ⇒
  env_semantics$itree_of e1 ---> stateLang$itree_of (app e2 Unit)
Proof
  fs [env_semanticsTheory.itree_of_def,
      stateLangTheory.itree_of_def] \\ rw []
  \\ irule semantics_thm
  \\ simp [Once cont_rel_cases]
  \\ fs [env_rel_def]
QED

val _ = export_theory ();
