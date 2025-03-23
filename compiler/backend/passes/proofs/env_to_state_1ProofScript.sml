(*
  Correctness for compilation from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory intLib
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     envLangTheory thunkLang_primitivesTheory env_cexpTheory
     stateLangTheory env_semanticsTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_to_state_1Proof";

val _ = set_grammar_ancestry ["stateLang", "envLang", "env_semantics", "pure_config"];

Overload "app" = ``λe1 e2. App AppOp [e1;e2]``;
Overload "slet" = ``λv e1 e2. stateLang$Let (SOME v) e1 e2``
Overload "suspend" = ``Lam NONE``
Overload "trigger" = ``λe. app e Unit``;
Overload "suspended" = ``Closure NONE``

(****************************************)

Inductive compile_rel:

[~Var:]
  compile_rel (envLang$Var v) (stateLang$Var v)

[~Ret:]
  (compile_rel te se ⇒
  compile_rel (Monad Ret [te]) (suspend se))

[~Raise:]
  (compile_rel te se ⇒
  compile_rel (Monad Raise [te]) (suspend (Raise se)))

[~Bind:]
  (compile_rel te1 se1 ∧ compile_rel te2 se2 ⇒
  compile_rel
    (Monad Bind [te1; te2])
    (suspend $ trigger $ app se2 (trigger se1)))

[~Handle:]
  (compile_rel te1 se1 ∧ compile_rel te2 se2 ⇒
  compile_rel
    (Monad Handle [te1; te2])
    (suspend $ trigger $
      HandleApp se2 $ slet "v" (trigger se1) (suspend $ Var "v")))

[~Alloc:]
  (compile_rel tl sl ∧ compile_rel tx sx ⇒
  compile_rel (Monad Alloc [tl; tx])
              (suspend $ App Alloc [sl; sx]))

[~Length:]
  (compile_rel tl sl ⇒
  compile_rel (Monad Length [tl])
              (suspend $ App Length [sl]))

[~Deref:]
  (compile_rel tl sl ∧ compile_rel ti si ⇒
  compile_rel (Monad Deref [tl; ti])
              (suspend $ App Sub [sl; si]))

[~Update:]
  (compile_rel tl sl ∧ compile_rel ti si ∧ compile_rel tx sx ⇒
  compile_rel (Monad Update [tl; ti; tx])
              (suspend $ App Update [sl; si; sx]))

[~Message:]
  (compile_rel te se ⇒
   compile_rel
    (Prim (AtomOp (Message s)) [te])
    (slet x se $ suspend (App (FFI s) [Var x])))

[~Act:]
  (compile_rel te se ⇒
  compile_rel (Monad Act [te])
              (suspend $ trigger se))

[~Proj:]
  (compile_rel te se ⇒
  compile_rel (Prim (Proj s n) [te]) (App (Proj s n) [se]))

[~IsEq:]
  (compile_rel te se ⇒
  compile_rel (Prim (IsEq s n q) [te]) (App (IsEq s n) [se]))

[~AtomOp:]
  (LIST_REL compile_rel tes ses ∧
   (∀s. aop ≠ Message s) ∧ (∀s1 s2. aop ≠ Lit (Msg s1 s2)) ⇒
  compile_rel (Prim (AtomOp aop) tes) (App (AtomOp aop) ses))

[~Cons:]
  (LIST_REL compile_rel tes ses ⇒
  compile_rel (Prim (Cons s) tes) (App (Cons s) ses))

[~App:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (App te1 te2) (app se1 se2))

[~Lam:]
  (∀x te se.
    compile_rel te se ⇒
    compile_rel (Lam x te) (Lam (SOME x) se))

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
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

[~Box:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Box te) (Box se))

[~Delay:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Delay te) (Delay se))

[~Force:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Force te) (Force se))

End

Inductive v_rel:

[~Constructor:]
  (∀tvs svs.
     LIST_REL v_rel tvs svs ⇒
     v_rel (envLang$Constructor s tvs) (stateLang$Constructor s svs))

[~Closure:]
  (∀tenv senv te se.
     env_rel tenv senv ∧
     compile_rel te se ⇒
     v_rel (Closure x tenv te) (Closure (SOME x) senv se))

[~Recclosure:]
  (∀tenv senv tfns sfns n.
     env_rel tenv senv ∧
     LIST_REL ((=) ### compile_rel) tfns sfns ⇒
     v_rel (envLang$Recclosure tfns tenv n) (stateLang$Recclosure sfns senv n))

[~ThunkL:]
  (∀tv sv.
     v_rel tv sv ⇒
     v_rel (Thunk $ INL tv) (Thunk $ INL sv))

[~ThunkR:]
  (∀tenv senv te se.
     env_rel tenv senv ∧
     compile_rel te se ⇒
     v_rel (Thunk $ INR (tenv, te)) (Thunk $ INR (senv, se)))

[~Atom:]
  (∀a.
     (∀msg x. ~(a = Msg msg x)) ⇒
     v_rel (Atom a) (Atom a))

[~Msg:]
  (∀msg s x senv.
     v_rel (Atom (Msg msg s))
           (suspended ((x,Atom $ Str s)::senv) $ (App (FFI msg) [Var x])))

[~Act:]
  (∀te se tenv senv.
     compile_rel te se ∧ env_rel tenv senv ⇒
     v_rel (Monadic tenv Act [te])
           (suspended senv $ trigger se))

[~Ret:]
  (∀te se tenv senv.
     compile_rel te se ∧ env_rel tenv senv ⇒
     v_rel (Monadic tenv Ret [te]) (suspended senv se))

[~Bind:]
  (∀te1 se1 te2 se2 tenv senv.
     compile_rel te1 se1 ∧ compile_rel te2 se2 ∧ env_rel tenv senv ⇒
     v_rel
       (Monadic tenv Bind [te1; te2])
       (suspended senv $ trigger $ app se2 (trigger se1)))

[~Handle:]
  (∀te1 se1 te2 se2 tenv senv.
     compile_rel te1 se1 ∧ compile_rel te2 se2 ∧ env_rel tenv senv ⇒
     v_rel
       (Monadic tenv Handle [te1; te2])
       (suspended senv $ trigger $
          HandleApp se2 (slet "v" (trigger se1) (suspend $ Var "v"))))

[~Raise:]
  (∀te se tenv senv.
     compile_rel te se ∧ env_rel tenv senv ⇒
     v_rel (Monadic tenv Raise [te]) (suspended senv $ Raise se))

[~Length:]
  (∀tl sl tenv senv.
     compile_rel tl sl ∧ env_rel tenv senv ⇒
     v_rel (Monadic tenv Length [tl])
           (suspended senv $ App Length [sl]))

[~Alloc:]
  (∀tl sl tenv senv.
     compile_rel tl sl ∧ compile_rel tx sx ∧ env_rel tenv senv ⇒
     v_rel
       (Monadic tenv Alloc [tl; tx])
       (suspended senv $ App Alloc [sl; sx]))

[~Deref:]
  (∀tl sl ti si tenv senv.
     compile_rel tl sl ∧ compile_rel ti si ∧ env_rel tenv senv ⇒
     v_rel
       (Monadic tenv Deref [tl; ti])
       (suspended senv $ (App Sub [sl; si])))

[~Update:]
  (∀tl sl ti si tx sx tenv senv.
     compile_rel tl sl ∧ compile_rel ti si ∧ compile_rel tx sx ∧ env_rel tenv senv ⇒
     v_rel
       (Monadic tenv Update [tl; ti; tx])
       (suspended senv $ App Update [sl; si; sx]))

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
  once_rewrite_tac [v_rel_cases] \\ fs [] \\ EVAL_TAC \\ simp[]
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
            application (AtomOp a) (MAP Atom (REVERSE ys) ++ Atom a' :: vs) st k
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

Overload AppArgK = ``λsenv se. AppK senv AppOp [] [se]``
Overload AppUnitK = ``λsenv. AppK senv AppOp [Constructor "" []] []``

Theorem LIST_REL_split:
  ∀l l'.
    LIST_REL ($= ### compile_rel) l l' ⇒
    MAP FST l = MAP FST l' ∧
    LIST_REL compile_rel (MAP SND l) (MAP SND l')
Proof
  Induct \\ rw [] \\ gvs [RPROD_DEF]
  \\ rpt $ (pairarg_tac \\ gvs [])
QED

Theorem LIST_REL_ALOOKUP:
  ∀l l'.
    MAP FST l = MAP FST l' ∧
    LIST_REL compile_rel (MAP SND l) (MAP SND l') ⇒
    (ALOOKUP l s = NONE ⇒ ALOOKUP l' s = NONE) ∧
    (∀e. ALOOKUP l s = SOME e ⇒
         ∃e'. ALOOKUP l' s = SOME e' ∧ compile_rel e e')
Proof
  rw []
  >- gvs [ALOOKUP_NONE]
  \\ drule_all ALOOKUP_SOME_EL_2 \\ rw []
  \\ gvs [SF SFY_ss, LIST_REL_EL_EQN, EL_MAP]
  \\ first_x_assum drule \\ rw []
QED

Theorem v_rel_anyThunk:
  ∀v w.
    v_rel v w ⇒
    (envLang$is_anyThunk v ⇔ (∃dt. stateLang$dest_anyThunk w = SOME dt))
Proof
 `(∀v w.
      v_rel v w ⇒
      (envLang$is_anyThunk v ⇔ (∃dt. stateLang$dest_anyThunk w = SOME dt))) ∧
   (∀tenv senv. env_rel tenv senv ⇒ T)`
   suffices_by gvs []
  \\ ho_match_mp_tac v_rel_strongind \\ rw [] \\ gvs []
  \\ rw [envLangTheory.is_anyThunk_def, envLangTheory.dest_anyThunk_def,
         stateLangTheory.dest_anyThunk_def]
  \\ dxrule LIST_REL_split \\ rpt strip_tac
  \\ rpt CASE_TAC
  \\ drule_all_then (qspec_then ‘n’ mp_tac) LIST_REL_ALOOKUP
  \\ rpt strip_tac
  \\ rgs [Once compile_rel_cases]
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
    \\ simp [Once v_rel_cases]
    \\ CASE_TAC \\ rw [error_def]
    \\ drule v_rel_anyThunk \\ rw [])
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
    \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ rw [] \\ gvs []
    >- (
      `eval_to (n − 1)
         (MAP (λ(fn,_). (fn,Recclosure xx1 aa0 fn)) xx1 ++ aa0) a1
         ≠ INL Type_error` by gvs []
      \\ last_x_assum $ drule_at $ Pos last
      \\ disch_then $ drule_then $ qspecl_then [‘env3’,‘NONE’,‘ForceK2 st::k’] mp_tac
      \\ unabbrev_all_tac
      \\ impl_tac >- (irule env_rel_rec \\ fs [])
      \\ strip_tac
      \\ BasicProvers.FULL_CASE_TAC \\ gvs []
      \\ first_x_assum $ irule_at $ Pos last \\ fs [])
    \\ `eval_to (n − 1)
         (MAP (λ(fn,_). (fn,Recclosure xx1 aa0 fn)) xx1 ++ aa0) a1
         ≠ INL Type_error` by gvs []
    \\ last_x_assum $ drule_at $ Pos last
    \\ disch_then $ drule_then $ qspecl_then [‘env3’,‘NONE’,‘ForceK2 st::k’] mp_tac
    \\ unabbrev_all_tac
    \\ impl_tac >- (irule env_rel_rec \\ fs [])
    \\ strip_tac
    \\ BasicProvers.FULL_CASE_TAC \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’
    \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
    \\ qexists_tac ‘1’ \\ fs [step_def,return_def,value_def]
    \\ CASE_TAC \\ rw [error_def]
    \\ drule v_rel_anyThunk \\ rw [])
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
  >~ [`Prim op xs`]
  >- (Cases_on ‘op’ \\ gvs []
    \\ TRY (fs [eval_to_def] \\ NO_TAC)
    >~ [‘Cons s’] >-
     (simp [Once compile_rel_cases] \\ fs [monad_cns_def] \\ rw []
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
    \\ gvs [DefnBase.one_line_ify NONE eval_op_def,AllCaseEqs()]) >>
  gvs[eval_to_def] >> fs[Once compile_rel_cases] >>
  simp[Once v_rel_cases, PULL_EXISTS] >>
  rpt $ goal_assum $ drule_at Any >>
  qexists `1` >> gvs[step]
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
    cont_rel (BC (tenv, te) tk)
             (AppArgK senv se :: AppUnitK senv :: sk))
  ∧
  (∀tk sk senv tenv te se.
    cont_rel tk sk ∧ env_rel tenv senv ∧ compile_rel te se ⇒
    cont_rel (HC (tenv, te) tk)
       ((LetK senv (SOME "v") $ suspend $ Var "v") ::
        HandleAppK senv se :: AppUnitK senv :: sk))
End

Definition store_rel_def:
  store_rel ts (Array vs) = LIST_REL v_rel ts vs ∧
  store_rel _ _ = F
End

Definition state_rel_def:
  state_rel ts ss = LIST_REL store_rel ts ss
End

Inductive next_rel:
  (v_rel tv sv ∧
   state_rel ts ss ∧
   cont_rel tk sk
    ⇒ next_rel (tv, ts, tk)
               (Val sv, SOME ss, AppUnitK senv :: sk)) ∧

  (eval tenv te = INR tv ∧
   v_rel tv sv ∧
   state_rel ts ss ∧
   cont_rel tk sk
    ⇒ next_rel (Monadic tenv Ret [te], ts, tk)
               (Val sv, SOME ss, sk)) ∧

  (eval tenv te = INR tv ∧
   v_rel tv sv ∧
   state_rel ts ss ∧
   cont_rel tk sk
    ⇒ next_rel (Monadic tenv Raise [te], ts, tk)
               (Exn sv, SOME ss, sk))
End

Inductive next_res_rel:
  (is_halt (sres, SOME ss, sk) ∧ sres ≠ Error ∧ (∀ch c. sres ≠ Action ch c)
    ⇒ next_res_rel env_semantics$Ret (sres, SOME ss, sk)) ∧

  (¬is_halt (sres,ssopt,sk)
    ⇒ next_res_rel Div (sres,ssopt,sk)) ∧

  (cont_rel tk sk ∧ state_rel ts ss
    ⇒ next_res_rel (Act (ea,eb) tk ts)
                   (Action ea eb, SOME ss, sk))
End

Inductive next_action_rel:
  next_action_rel Div Div ∧
  next_action_rel Ret Ret ∧
  (next_res_rel (Act (a,b) tk ts) (Action a b, ss, sk)
    ⇒ next_action_rel (Act (a,b) tk ts) (Act (a,b) sk ss))
End

Theorem next_k_thm:
  ∀k tv sev tk sk tres ts ss.
  next_rel (tv, ts, tk) (sev, SOME ss, sk) ∧
  next k (INR tv) tk ts = tres ∧ tres ≠ Err
  ⇒ ∃n. k ≤ n ∧
        next_res_rel
          (next k (INR tv) tk ts)
          (step_n n (sev, SOME ss, sk))
Proof
  completeInduct_on `k` >> rw[] >>
  reverse $ Cases_on `∃tenv mop tes. tv = Monadic tenv mop tes` >> gvs[]
  >- (Cases_on `tv` >> fs[Once next_def]) >>
  qpat_x_assum `next_rel _ _` mp_tac >> reverse $ rw[next_rel_cases] >> gvs[]
  >- ( (* Exn *)
    qpat_x_assum `next _ _ _ _ ≠ _` mp_tac >>
    once_rewrite_tac[next_def] >> rw[with_value_def] >>
    TOP_CASE_TAC >> gvs[] >> fs[Once cont_rel_cases]
    >- (simp[next_res_rel_cases] >> qexists `k` >> simp[step_n_Exn_NIL])
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
      ntac 2 (qrefine `n + 1` >> simp[step_n_add, step]) >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >> disch_then $ qspec_then `Exn sv` mp_tac >>
      simp[next_rel_cases] >> rpt $ disch_then drule >> rw[] >>
      goal_assum $ drule_at Any >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
      ntac 2 (qrefine `n + 1` >> simp[step_n_add, step]) >>
      gvs[apply_closure_def, with_value_def] >>
      dxrule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
      disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
      >- (
        simp[next_res_rel_cases, PULL_EXISTS] >>
        pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
        goal_assum $ drule_at Any >> simp[]
        ) >>
      unabbrev_all_tac >> qrefine `n + ck` >> simp[step_n_add] >>
      rename1 `dest_anyClosure tv1` >> Cases_on `dest_anyClosure tv1` >> gvs[] >>
      rename1 `INR y` >> PairCases_on `y` >> gvs[] >>
      drule_all v_rel_dest_anyClosure >> strip_tac >> gvs[] >>
      qrefine `n + 1` >> simp[step_n_add, step_def] >>
      simp[return_def, application_def, opt_bind_def, continue_def] >>
      qmatch_goalsub_abbrev_tac `next _ (eval tenv2 _)` >>
      qmatch_goalsub_abbrev_tac `step_n _ (Exp senv2 _, _)` >>
      `env_rel tenv2 senv2` by (unabbrev_all_tac >> irule env_rel_cons >> gvs[]) >>
      drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
      disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
      >- fs[Once next_def]
      >- (
        simp[Once next_def] >> simp[next_res_rel_cases, PULL_EXISTS] >>
        pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
        goal_assum $ drule_at Any >> simp[]
        ) >>
      qrefine `n + ck'` >> simp[step_n_add] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      disch_then $ qspecl_then [`Val sv''`,`sk`,`ss`] mp_tac >> impl_tac >> rw[]
      >- (unabbrev_all_tac >> simp[next_rel_cases]) >>
      goal_assum $ drule_at Any >> simp[]
      )
    )
  >- ( (* Val *)
    qpat_x_assum `next _ _ _ _ ≠ _` mp_tac >>
    once_rewrite_tac[next_def] >> rw[with_value_def] >>
    TOP_CASE_TAC >> gvs[] >> fs[Once cont_rel_cases]
    >- (simp[next_res_rel_cases] >> qexists `k` >> simp[step_n_Val])
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
      qrefine `n + 1` >> simp[step_n_add, step] >>
      gvs[apply_closure_def, with_value_def] >>
      dxrule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
      disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
      >- (
        simp[next_res_rel_cases, PULL_EXISTS] >>
        pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
        goal_assum $ drule_at Any >> simp[]
        ) >>
      unabbrev_all_tac >> qrefine `n + ck` >> simp[step_n_add] >>
      rename1 `dest_anyClosure tv1` >> Cases_on `dest_anyClosure tv1` >> gvs[] >>
      rename1 `INR y` >> PairCases_on `y` >> gvs[] >>
      drule_all v_rel_dest_anyClosure >> strip_tac >> gvs[] >>
      qrefine `n + 1` >> simp[step_n_add, step_def] >>
      simp[return_def, application_def, opt_bind_def, continue_def] >>
      qmatch_goalsub_abbrev_tac `next _ (eval tenv2 _)` >>
      qmatch_goalsub_abbrev_tac `step_n _ (Exp senv2 _, _)` >>
      `env_rel tenv2 senv2` by (unabbrev_all_tac >> irule env_rel_cons >> gvs[]) >>
      drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
      disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
      >- fs[Once next_def]
      >- (
        simp[Once next_def] >> simp[next_res_rel_cases, PULL_EXISTS] >>
        pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
        goal_assum $ drule_at Any >> simp[]
        ) >>
      qrefine `n + ck'` >> simp[step_n_add] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      disch_then $ qspecl_then [`Val sv''`, `sk`,`ss`] mp_tac >> impl_tac >> rw[]
      >- (unabbrev_all_tac >> simp[next_rel_cases]) >>
      goal_assum $ drule_at Any >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
      ntac 5 (qrefine `n + 1` >> simp[step_n_add, step]) >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      disch_then $ qspecl_then [`Val sv`,`sk'`,`ss`] mp_tac >>
      rw[next_rel_cases] >> goal_assum $ drule_at Any >> simp[]
      )
    ) >>
  qpat_x_assum `next _ _ _ _ ≠ _` mp_tac >>
  once_rewrite_tac[next_def] >> simp[with_value_def] >>
  fs[Once v_rel_cases]
  >~ [`Ret`]
  >- (
    strip_tac >> gvs[] >>
    qrefine `n + 1` >> simp[step_n_add, step] >>
    drule_all eval_thm >>
    disch_then $ qspecl_then [`SOME ss`,`sk'`] assume_tac >> gvs[]
    >- (
      simp[next_res_rel_cases, PULL_EXISTS] >>
      pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck` >> simp[step_n_add] >>
    Cases_on `tk` >> fs[Once cont_rel_cases] >> gvs[]
    >- (simp[next_res_rel_cases, PULL_EXISTS] >> qexists `k` >> simp[step_n_Val])
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
      qrefine `n + 1` >> simp[step_n_add, step] >>
      gvs[apply_closure_def, with_value_def] >>
      dxrule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk1` >>
      disch_then $ qspecl_then [`SOME ss`,`sk1`] assume_tac >> gvs[]
      >- (
        simp[next_res_rel_cases, PULL_EXISTS] >>
        pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
        goal_assum $ drule_at Any >> simp[]
        ) >>
      unabbrev_all_tac >> qrefine `n + ck'` >> simp[step_n_add] >>
      rename1 `dest_anyClosure tv1` >> Cases_on `dest_anyClosure tv1` >> gvs[] >>
      rename1 `INR y` >> PairCases_on `y` >> gvs[] >>
      drule_all v_rel_dest_anyClosure >> strip_tac >> gvs[] >>
      qrefine `n + 1` >> simp[step_n_add, step_def] >>
      simp[return_def, application_def, opt_bind_def, continue_def] >>
      qmatch_goalsub_abbrev_tac `next _ (eval tenv2 _)` >>
      qmatch_goalsub_abbrev_tac `step_n _ (Exp senv2 _, _)` >>
      `env_rel tenv2 senv2` by (unabbrev_all_tac >> irule env_rel_cons >> gvs[]) >>
      drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk2` >>
      disch_then $ qspecl_then [`SOME ss`,`sk2`] assume_tac >> gvs[]
      >- fs[Once next_def]
      >- (
        simp[Once next_def] >> simp[next_res_rel_cases, PULL_EXISTS] >>
        pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
        goal_assum $ drule_at Any >> simp[]
        ) >>
      qrefine `n + ck''` >> simp[step_n_add] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      disch_then $ qspecl_then [`Val sv''`,`sk2`,`ss`] mp_tac >> impl_tac >> rw[]
      >- (unabbrev_all_tac >> simp[next_rel_cases]) >>
      goal_assum $ drule_at Any >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
      ntac 5 (qrefine `n + 1` >> simp[step_n_add, step]) >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      disch_then $ qspecl_then [`Val sv`,`sk`,`ss`] mp_tac >> rw[next_rel_cases] >>
      goal_assum $ drule_at Any >> simp[]
      )
    )
  >~ [`Raise`]
  >- (
    strip_tac >> gvs[] >>
    ntac 2 (qrefine `n + 1` >> simp[step_n_add, step]) >>
    drule_all eval_thm >>
    disch_then $ qspecl_then [`SOME ss`,`RaiseK::sk'`] assume_tac >> gvs[]
    >- (
      simp[next_res_rel_cases, PULL_EXISTS] >>
      pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck` >> simp[step_n_add] >>
    Cases_on `tk` >> fs[Once cont_rel_cases] >> gvs[]
    >- (
      simp[next_res_rel_cases, PULL_EXISTS] >>
      qrefine `n + 1` >> simp[step_n_add, step] >>
      qexists `k` >> simp[step_n_Exn_NIL]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
      ntac 3 (qrefine `n + 1` >> simp[step_n_add, step]) >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      disch_then $ qspec_then `Exn sv` mp_tac >> simp[next_rel_cases] >>
      disch_then drule_all >> rw[] >> goal_assum $ drule_at Any >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
      ntac 3 (qrefine `n + 1` >> simp[step_n_add, step]) >>
      gvs[apply_closure_def, with_value_def] >>
      dxrule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk1` >>
      disch_then $ qspecl_then [`SOME ss`,`sk1`] assume_tac >> gvs[]
      >- (
        simp[next_res_rel_cases, PULL_EXISTS] >>
        pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
        goal_assum $ drule_at Any >> simp[]
        ) >>
      unabbrev_all_tac >> qrefine `n + ck'` >> simp[step_n_add] >>
      rename1 `dest_anyClosure tv1` >> Cases_on `dest_anyClosure tv1` >> gvs[] >>
      rename1 `INR y` >> PairCases_on `y` >> gvs[] >>
      drule_all v_rel_dest_anyClosure >> strip_tac >> gvs[] >>
      qrefine `n + 1` >> simp[step_n_add, step_def] >>
      simp[return_def, application_def, opt_bind_def, continue_def] >>
      qmatch_goalsub_abbrev_tac `next _ (eval tenv2 _)` >>
      qmatch_goalsub_abbrev_tac `step_n _ (Exp senv2 _, _)` >>
      `env_rel tenv2 senv2` by (unabbrev_all_tac >> irule env_rel_cons >> gvs[]) >>
      drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk2` >>
      disch_then $ qspecl_then [`SOME ss`,`sk2`] assume_tac >> gvs[]
      >- fs[Once next_def]
      >- (
        simp[Once next_def] >> simp[next_res_rel_cases, PULL_EXISTS] >>
        pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
        goal_assum $ drule_at Any >> simp[]
        ) >>
      qrefine `n + ck''` >> simp[step_n_add] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      disch_then $ qspecl_then [`Val sv''`,`sk2`,`ss`] mp_tac >> impl_tac >> rw[]
      >- (unabbrev_all_tac >> simp[next_rel_cases]) >>
      goal_assum $ drule_at Any >> simp[]
      )
    )
  >~ [`Bind`]
  >- (
    IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
    strip_tac >> gvs[] >>
    ntac 8 (qrefine `n + 1` >> simp[step_n_add, step]) >>
    rev_drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- fs[Once next_def]
    >- (
      simp[Once next_def] >> simp[next_res_rel_cases, PULL_EXISTS] >>
      pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck` >> simp[step_n_add] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    disch_then $ drule_at Any >>
    disch_then $ qspecl_then [`Val sv`,`sk`,`ss`] mp_tac >> reverse impl_tac >> rw[]
    >- (goal_assum $ drule_at Any >> simp[]) >>
    unabbrev_all_tac >> simp[next_rel_cases] >> simp[Once cont_rel_cases]
    )
  >~ [`Handle`]
  >- (
    IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
    strip_tac >> gvs[] >>
    ntac 9 (qrefine `n + 1` >> simp[step_n_add, step]) >>
    rev_drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- fs[Once next_def]
    >- (
      simp[Once next_def] >> simp[next_res_rel_cases, PULL_EXISTS] >>
      pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck` >> simp[step_n_add] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    disch_then $ drule_at Any >>
    disch_then $ qspecl_then [`Val sv`,`sk`,`ss`] mp_tac >> reverse impl_tac >> rw[]
    >- (goal_assum $ drule_at Any >> simp[]) >>
    unabbrev_all_tac >> simp[next_rel_cases] >> simp[Once cont_rel_cases]
    )
  >~ [`Act`]
  >- (
    strip_tac >> gvs[with_atoms_def, result_map_def] >>
    ntac 4 (qrefine `n + 1` >> simp[step_n_add, step]) >>
    rev_drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- (
      simp[next_res_rel_cases, PULL_EXISTS] >>
      pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck` >> simp[step_n_add] >>
    Cases_on `tv` >> gvs[get_atoms_def] >> TOP_CASE_TAC >> gvs[] >>
    fs[Once v_rel_cases] >> unabbrev_all_tac >> gvs[] >>
    simp[next_res_rel_cases, PULL_EXISTS] >>
    ntac 4 (qrefine `n + 1` >> simp[step_n_add, step]) >>
    qexists `k` >> simp[step_n_Action]
    )
  >~ [`Alloc`]
  >- (
    strip_tac >> gvs[result_map_def] >>
    ntac 2 (qrefine `n + 1` >> simp[step_n_add, step]) >>
    drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- (
      IF_CASES_TAC >> gvs[] >>
      simp[next_res_rel_cases, PULL_EXISTS] >>
      first_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck` >> simp[step_n_add] >> unabbrev_all_tac >>
    qrefine `n + 1` >> simp[step_n_add, step] >>
    rev_drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- (
      simp[next_res_rel_cases, PULL_EXISTS] >>
      pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck'` >> simp[step_n_add] >> unabbrev_all_tac >>
    Cases_on `tv'` >> gvs[get_atoms_def] >> TOP_CASE_TAC >> gvs[] >>
    IF_CASES_TAC >> gvs[] >- (qexists `0` >> simp[next_res_rel_cases]) >>
    qpat_x_assum `v_rel (Atom _) _` mp_tac >> simp[Once v_rel_cases] >>
    strip_tac >> gvs[] >>
    qrefine `n + 1` >> simp[step_n_add, step] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    disch_then $ drule_at Any >>
    qmatch_goalsub_abbrev_tac `Val v` >>
    qmatch_goalsub_abbrev_tac `SNOC new _` >>
    disch_then $ qspecl_then [`Val v`,`sk'`,`SNOC new ss`] mp_tac >>
    reverse impl_tac >> simp[]
    >- (strip_tac >> goal_assum $ drule_at Any >> simp[]) >>
    unabbrev_all_tac >> simp[next_rel_cases] >> disj2_tac >>
    simp[eval_def] >> simp[Once eval_to_def, result_map_def, eval_op_def] >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    simp[Once eval_to_def, result_map_def, eval_op_def] >>
    simp[Once v_rel_cases] >> imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    gvs[state_rel_def,store_rel_def,LIST_REL_EL_EQN, EL_REPLICATE]
    )
  >~ [`Length`]
  >- (
    strip_tac >> gvs[with_atoms_def, result_map_def] >>
    ntac 2 (qrefine `n + 1` >> simp[step_n_add, step]) >>
    drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- (
      simp[next_res_rel_cases, PULL_EXISTS] >>
      pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck` >> simp[step_n_add] >> unabbrev_all_tac >>
    Cases_on `tv` >> gvs[get_atoms_def] >> TOP_CASE_TAC >> gvs[] >>
    IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[NOT_LESS_EQUAL]
    >- (qexists `0` >> simp[next_res_rel_cases]) >>
    qpat_x_assum `v_rel (Atom _) _` mp_tac >> simp[Once v_rel_cases] >>
    strip_tac >> gvs[] >>
    qrefine `m + 1` >> simp[step_n_add, step] >>
    gvs[state_rel_def] >>
    imp_res_tac LIST_REL_LENGTH >> simp[oEL_THM] >>
    gvs[LIST_REL_EL_EQN] >>
    first_assum $ qspec_then `n` assume_tac >>
    Cases_on `EL n ss` >> gvs[store_rel_def] >>
    last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
    disch_then $ drule_at Any >>
    qmatch_goalsub_abbrev_tac `Val v` >>
    disch_then $ qspecl_then [`Val v`,`sk'`,`ss`] mp_tac >>
    reverse impl_tac >> simp[]
    >- (strip_tac >> goal_assum $ drule_at Any >> simp[]) >>
    simp[next_rel_cases] >> disj2_tac >>
    simp[eval_def] >> simp[Once eval_to_def, result_map_def, eval_op_def] >>
    DEEP_INTRO_TAC some_intro >>simp[Once eval_to_def, result_map_def, eval_op_def] >>
    unabbrev_all_tac >> simp[Once v_rel_cases] >> gvs[state_rel_def,LIST_REL_EL_EQN]
    )
  >~ [`Deref`]
  >- (
    strip_tac >> gvs[with_atoms_def, result_map_def] >>
    ntac 2 (qrefine `n + 1` >> simp[step_n_add, step]) >>
    drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- (
      IF_CASES_TAC >> gvs[] >>
      simp[next_res_rel_cases, PULL_EXISTS] >>
      first_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck` >> simp[step_n_add] >> unabbrev_all_tac >>
    qrefine `n + 1` >> simp[step_n_add, step] >>
    rev_drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- (
      simp[next_res_rel_cases, PULL_EXISTS] >>
      pop_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck'` >> simp[step_n_add] >> unabbrev_all_tac >>
    Cases_on `tv'` >> gvs[get_atoms_def] >> Cases_on `tv` >> gvs[get_atoms_def] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
    >- (qexists `0` >> simp[next_res_rel_cases]) >>
    rpt $ qpat_x_assum `v_rel (Atom _) _` mp_tac >>
    ntac 2 $ simp[Once v_rel_cases] >> rpt strip_tac >> gvs[] >>
    qrefine `m + 1` >> simp[step_n_add, step] >>
    gvs [state_rel_def] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[oEL_THM] >>
    gvs [LIST_REL_EL_EQN] >>
    first_assum $ qspec_then `n` assume_tac >>
    Cases_on `EL n ss` >> gvs [store_rel_def] >>
    `LENGTH (EL n ts) = LENGTH l` by gvs[LIST_REL_EL_EQN] >> gvs[] >>
    IF_CASES_TAC >> gvs[DISJ_EQ_IMP]
    >- (
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      qmatch_goalsub_abbrev_tac `Val v` >>
      disch_then $ qspecl_then [`Val v`,`sk'`,`ss`] mp_tac >>
      reverse impl_tac >> simp[]
      >- (strip_tac >> goal_assum $ drule_at Any >> simp[]) >>
      unabbrev_all_tac >> simp[next_rel_cases] >> disj2_tac >>
      simp[eval_def] >> simp[Once eval_to_def, result_map_def, eval_op_def] >>
      DEEP_INTRO_TAC some_intro >> simp[] >>
      simp[Once eval_to_def, result_map_def, eval_op_def] >>
      `Num i < &LENGTH l` by ARITH_TAC >>
      gvs[state_rel_def,LIST_REL_EL_EQN,NOT_LESS_EQUAL]
      )
    >- (
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      qmatch_goalsub_abbrev_tac `Exn e` >>
      disch_then $ qspecl_then [`Exn e`,`sk'`,`ss`] mp_tac >>
      reverse impl_tac >> simp[]
      >- (strip_tac >> goal_assum $ drule_at Any >> simp[]) >>
      unabbrev_all_tac >> simp[next_rel_cases] >>
      simp[eval_def] >> simp[Once eval_to_def, result_map_def, eval_op_def] >>
      DEEP_INTRO_TAC some_intro >> simp[] >>
      simp[Once eval_to_def, result_map_def, eval_op_def] >>
      simp[Once v_rel_cases, monad_cns_def] >>
      gvs[state_rel_def,LIST_REL_EL_EQN]
      )
    )
  >~ [`Update`]
  >- (
    strip_tac >> gvs[with_atoms_def, result_map_def] >>
    ntac 2 (qrefine `n + 1` >> simp[step_n_add, step]) >>
    drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- (
      IF_CASES_TAC >> gvs[] >>
      simp[next_res_rel_cases, PULL_EXISTS] >>
      first_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck` >> simp[step_n_add] >> unabbrev_all_tac >>
    qrefine `n + 1` >> simp[step_n_add, step] >>
    qspecl_then [`tenv`,`senv'`,`ti`] mp_tac eval_thm >>
    disch_then drule_all >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- (
      IF_CASES_TAC >> gvs[] >>
      simp[next_res_rel_cases, PULL_EXISTS] >>
      first_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck'` >> simp[step_n_add] >> unabbrev_all_tac >>
    qrefine `n + 1` >> simp[step_n_add, step] >>
    rev_drule_all eval_thm >> qmatch_goalsub_abbrev_tac `_,_,sk` >>
    disch_then $ qspecl_then [`SOME ss`,`sk`] assume_tac >> gvs[]
    >- (
      simp[next_res_rel_cases, PULL_EXISTS] >>
      first_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
      goal_assum $ drule_at Any >> simp[]
      ) >>
    qrefine `n + ck''` >> simp[step_n_add] >> unabbrev_all_tac >>
    Cases_on `tv''` >> Cases_on `tv'` >> gvs[get_atoms_def] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    IF_CASES_TAC >> gvs[NOT_LESS_EQUAL] >> IF_CASES_TAC >> gvs[]
    >- (qexists `0` >> simp[next_res_rel_cases]) >>
    rpt $ qpat_x_assum `v_rel (Atom _) _` mp_tac >>
    ntac 2 $ simp[Once v_rel_cases] >> rpt strip_tac >> gvs[] >>
    qrefine `m + 1` >> simp[step_n_add, step] >>
    gvs[state_rel_def] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[oEL_THM] >>
    gvs[LIST_REL_EL_EQN] >>
    first_assum $ qspec_then `n` assume_tac >>
    Cases_on `EL n ss` >> gvs[store_rel_def] >>
    `LENGTH (EL n ts) = LENGTH l` by gvs[LIST_REL_EL_EQN] >> gvs[] >>
    IF_CASES_TAC >> gvs[DISJ_EQ_IMP]
    >- (
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      qmatch_goalsub_abbrev_tac `Val v` >>
      gvs[miscTheory.LLOOKUP_THM] >>
      qmatch_goalsub_abbrev_tac `Val v,SOME ss',_` >>
      disch_then $ qspecl_then [`Val v`,`sk'`,`ss'`] mp_tac >>
      reverse impl_tac >> rw[]
      >- (goal_assum $ drule_at Any >> simp[]) >>
      unabbrev_all_tac >> simp[next_rel_cases] >> disj2_tac >>
      simp[eval_def] >> simp[Once eval_to_def, result_map_def, eval_op_def] >>
      DEEP_INTRO_TAC some_intro >> simp[] >>
      simp[Once eval_to_def, result_map_def, eval_op_def] >>
      simp[Once v_rel_cases, monad_cns_def] >>
      gvs[state_rel_def, store_rel_def, LIST_REL_EL_EQN, EL_LUPDATE, COND_RAND]
      )
    >- (
      gvs[miscTheory.LLOOKUP_THM] >>
      last_x_assum $ qspec_then `k - 1` mp_tac >> simp[] >>
      disch_then $ drule_at Any >>
      qmatch_goalsub_abbrev_tac `Exn e` >>
      disch_then $ qspecl_then [`Exn e`,`sk'`,`ss`] mp_tac >>
      reverse impl_tac >> rw[]
      >- (goal_assum $ drule_at Any >> simp[]) >>
      unabbrev_all_tac >> simp[next_rel_cases] >>
      simp[eval_def] >> simp[Once eval_to_def, result_map_def, eval_op_def] >>
      DEEP_INTRO_TAC some_intro >> simp[] >>
      simp[Once eval_to_def, result_map_def, eval_op_def] >>
      simp[Once v_rel_cases, monad_cns_def] >>
      gvs[state_rel_def,store_rel_def,LIST_REL_EL_EQN]
      )
    )
QED

Theorem next_k_eval_thm:
  compile_rel te se ∧
  state_rel ts ss ∧
  cont_rel tk sk ∧
  env_rel tenv senv ∧
  next k (eval tenv te) tk ts = tres ∧ tres ≠ Err
  ⇒ ∃n. k ≤ n ∧
        next_res_rel tres (step_n n (Exp senv se, SOME ss, AppUnitK senv'::sk))
Proof
  rw [] \\ pop_assum mp_tac
  \\ Cases_on ‘eval tenv te = INL Type_error’ \\ fs []
  >- simp [Once next_def]
  \\ Cases_on ‘eval tenv te = INL Diverge’ \\ fs []
  >-
   (ntac 2 (simp [Once next_def])
    \\ fs [eval_eq_Diverge]
    \\ first_x_assum $ qspec_then ‘k’ assume_tac
    \\ drule eval_to_thm \\ fs []
    \\ disch_then drule_all
    \\ rename [‘SOME _,kk’]
    \\ disch_then (qspecl_then [‘SOME ss’,‘kk’] mp_tac) \\ rw []
    \\ simp[next_res_rel_cases, PULL_EXISTS]
    \\ ‘∃a. step_n ck (Exp senv se,SOME ss,kk) = a’ by fs []
    \\ PairCases_on ‘a’ \\ fs []
    \\ rpt $ goal_assum drule)
  \\ strip_tac
  \\ reverse (Cases_on ‘∃tenv' mop tes. eval tenv te = INR (Monadic tenv' mop tes)’)
  >- (
    irule FALSITY >> pop_assum mp_tac >> simp[] >>
    pop_assum mp_tac >> simp[Once next_def] >>
    rpt (TOP_CASE_TAC >> gvs[])
    )
  \\ gvs []
  \\ drule eval_neq_Diverge \\ fs []
  \\ strip_tac
  \\ rename [‘eval_to ck’]
  \\ drule eval_to_thm \\ fs []
  \\ disch_then drule_all
  \\ disch_then (qspecl_then [‘SOME ss’,‘AppUnitK senv'::sk’] mp_tac)
  \\ rpt strip_tac
  \\ Q.REFINE_EXISTS_TAC ‘ck1+ck'’
  \\ rewrite_tac [step_n_add] \\ fs [step_def,push_def]
  \\ ‘∃res. next k (INR (Monadic tenv' mop tes)) tk ts = res’ by fs []
  \\ fs []
  \\ drule_at Any next_k_thm
  \\ disch_then (qspecl_then [`Val sv`,`AppUnitK senv'::sk`,`ss`] mp_tac)
  \\ simp[next_rel_cases] \\ strip_tac
  \\ first_x_assum $ irule_at Any
  \\ simp[]
QED

Theorem next_action_thm:
  compile_rel te se ∧
  state_rel ts ss ∧
  cont_rel tk sk ∧
  env_rel tenv senv ∧
  next_action (eval tenv te) tk ts = tres ∧ tres ≠ Err
  ⇒ next_action_rel tres
      (step_until_halt (Exp senv se, SOME ss, AppUnitK senv'::sk))
Proof
  fs [next_action_def]
  \\ CASE_TAC
  >-
   (pop_assum mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
    \\ fs [step_until_halt_def,AllCaseEqs(),next_action_rel_cases]
    \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
    \\ ‘∃s. next x (eval tenv te) tk ts = s’ by fs []
    \\ ‘s = Div’ by metis_tac []
    \\ ‘s ≠ Err ∧ x ≤ x’ by gvs []
    \\ drule_all next_k_eval_thm \\ fs []
    \\ disch_then $ qspec_then `senv'` assume_tac \\ gvs[next_res_rel_cases]
    \\ ‘x = n ∨ x < n’ by fs [] \\ gvs []
    \\ strip_tac
    \\ drule_all step_n_mono
    \\ strip_tac \\ gvs []
    )
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
   (CCONTR_TAC \\ fs[next_action_rel_cases]
    \\ drule_all next_k_eval_thm
    \\ disch_then $ qspec_then `senv'` assume_tac \\ gvs[next_res_rel_cases]
    \\ fs []
    >- metis_tac  []
    \\ first_x_assum (qspec_then ‘n’ mp_tac)
    \\ gvs [is_halt_def])
  \\ ‘∃t. (step_n x' (Exp senv se,SOME ss,AppUnitK senv'::sk)) = t’ by fs []
  \\ PairCases_on ‘t’ \\ fs []
  \\ drule_all next_k_eval_thm \\ fs []
  \\ disch_then $ qspec_then `senv'` assume_tac \\ fs[]
  \\ qmatch_asmsub_abbrev_tac `step_n _ foo`
  \\ `is_halt (step_n n foo)` by (Cases_on `tres` \\ fs[next_res_rel_cases])
  \\ `step_n n foo = step_n x' foo` by (
        `n = x' ∨ n < x' ∨ x' < n` by fs[] >> fs[] >> rename1 `a < b` >>
        qspecl_then [`a`,`foo`] mp_tac step_n_mono >> simp[] >>
        disch_then drule >> rw[])
  \\ unabbrev_all_tac \\ rw []
  \\ gvs[next_res_rel_cases, next_action_rel_cases]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem semantics_app_Unit:
  semantics (app e2 Unit) senv ss sk =
  semantics e2 senv ss (AppUnitK senv::sk)
Proof
  fs [stateLangTheory.semantics_def,sinterp_def]
  \\ once_rewrite_tac [itreeTheory.itree_unfold_err] \\ fs []
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
  compile_rel e1 e2 ∧ state_rel ts ss ∧
  cont_rel tk sk ∧ env_rel tenv senv ⇒
  env_semantics$semantics e1 tenv tk ts --->
  semantics (app e2 Unit) senv (SOME ss) sk
Proof
  fs [semantics_app_Unit]
  \\ qsuff_tac ‘
    ∀t1 t2.
      (∃e1 e2 ts ss tenv senv tk sk.
        compile_rel e1 e2 ∧ state_rel ts ss ∧
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
  \\ simp [Once itreeTheory.itree_unfold_err]
  \\ qmatch_goalsub_abbrev_tac ‘itree_unfold_err fs’
  \\ ‘∃r1 r2. next_action (eval tenv e1) tk ts = r1 ∧
              step_until_halt (Exp senv e2,SOME ss,
                AppK senv AppOp [Constructor "" []] []::sk) = r2’ by fs []
  \\ fs []
  \\ drule_all next_action_thm
  \\ disch_then $ qspec_then `senv` mp_tac
  \\ Cases_on ‘r1’ \\ gvs[next_action_rel_cases, next_res_rel_cases]
  \\ strip_tac \\ fs []
  \\ rw [] \\ gvs []
  \\ Cases \\ fs []
  \\ reverse IF_CASES_TAC >- fs []
  \\ fs [] \\ fs [value_def]
  \\ rw []
  \\ `interp (INR (RetVal (Atom (Str y)))) c l =
      interp (eval [("v",Atom (Str y))] (Monad Ret [Var "v"])) c l` by
   (fs [eval_def,eval_to_def,result_map_def]
    \\ DEEP_INTRO_TAC some_intro \\ fs [])
  \\ pop_assum $ irule_at Any
  \\ ‘compile_rel (Monad Ret [Var "v"]) (suspend (Var "v"))’ by
        ntac 2 (simp[Once compile_rel_cases])
  \\ pop_assum $ irule_at Any
  \\ rpt (first_assum $ irule_at $ Pos hd)
  \\ qexists_tac ‘[("v",Atom (Str y))] ++ nenv1’
  \\ conj_tac
  >- fs [env_rel_def,Once v_rel_cases]
  \\ once_rewrite_tac [itreeTheory.itree_unfold_err]
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ unabbrev_all_tac \\ fs []
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ ntac 3 (irule EQ_TRANS
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
  \\ fs [env_rel_def,state_rel_def]
QED

val _ = export_theory ();
