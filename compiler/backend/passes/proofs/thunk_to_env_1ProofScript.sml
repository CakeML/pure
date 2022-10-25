(*
  Proof of correctness for the thunk_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pred_setTheory rich_listTheory thunkLang_primitivesTheory envLangTheory
     finite_mapTheory thunkLangTheory env_semanticsTheory thunk_semanticsTheory;
open thunk_to_envTheory;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_to_env_1Proof";

val _ = set_grammar_ancestry ["pred_set", "rich_list", "envLang", "thunkLang",
                              "thunk_to_env", "thunkLangProps", "env_semantics" ]

val _ = numLib.prefer_num ();

Inductive exp_rel:
[exp_rel_Value:]
  (∀env n v w.
     ALOOKUP env n = SOME w ∧
     v_rel v w ⇒
       exp_rel env (Value v) (Var n)) ∧
[exp_rel_Lit_Var:] (* Used in proof of interp_eq below *)
  (∀env n s.
     ALOOKUP env n = SOME (Atom s) ⇒
       exp_rel env (Lit s) (Var n)) ∧
[exp_rel_Unit_Var:] (* Used in proof of interp_eq below *)
  (∀env n s.
     ALOOKUP env n = SOME (Constructor s []) ⇒
       exp_rel env (Cons s []) (Var n)) ∧
[exp_rel_Var:]
  (∀env n.
     ALOOKUP env n = NONE ⇒
       exp_rel env (Var n) (Var n)) ∧
[exp_rel_App:]
  (∀env x1 x2 y1 y2.
     exp_rel env x1 x2 ∧
     exp_rel env y1 y2 ⇒
       exp_rel env (App x1 y1) (App x2 y2)) ∧
[exp_rel_Lam:]
  (∀env x y s.
     exp_rel (FILTER (λ(n,x). n ≠ s) env) x y ⇒
       exp_rel env (Lam s x) (Lam s y)) ∧
[exp_rel_Let_NONE:]
  (∀env x1 x2 y1 y2.
     exp_rel env x1 x2 ∧
     exp_rel env y1 y2 ⇒
       exp_rel env (Let NONE x1 y1) (Let NONE x2 y2)) ∧
[exp_rel_Let_SOME:]
  (∀env x1 x2 y1 y2 s.
     exp_rel env x1 x2 ∧
     exp_rel (FILTER (λ(n,x). n ≠ s) env) y1 y2 ⇒
       exp_rel env (Let (SOME s) x1 y1) (Let (SOME s) x2 y2)) ∧
[exp_rel_If:]
  (∀env x1 x2 y1 y2 z1 z2.
     LIST_REL (exp_rel env) [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel env (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_Prim:]
  (∀env op xs ys.
     LIST_REL (exp_rel env) xs ys ⇒
       exp_rel env (Prim op xs) (Prim op ys)) ∧
[exp_rel_Letrec:]
  (∀env f g x y.
     LIST_REL (λ(fn,b) (gn,c). fn = gn ∧
                 exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c)
              (REVERSE f) g ∧
     exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) x y ⇒
       exp_rel env (Letrec f x) (Letrec g y)) ∧
[exp_rel_Delay:]
  (∀env x y.
     exp_rel env x y ⇒
       exp_rel env (Delay x) (Delay y)) ∧
[exp_rel_Box:]
  (∀env x y.
     exp_rel env x y ⇒
       exp_rel env (Box x) (Box y)) ∧
[exp_rel_Force:]
  (∀env x y.
     exp_rel env x y ⇒
       exp_rel env (Force x) (Force y)) ∧
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Closure:]
  (∀env s x y.
     exp_rel env (Lam s x) (Lam s y) ⇒
       v_rel (Closure s x) (Closure s env y)) ∧
[v_rel_Recclosure:]
  (∀env f g n.
     LIST_REL (λ(fn,b) (gn,c). fn = gn ∧
                 exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c)
              (REVERSE f) g ⇒
       v_rel (Recclosure f n) (Recclosure g env n)) ∧
[v_rel_Thunk_v:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INL v)) (Thunk (INL w))) ∧
[v_rel_Thunk_exp:]
  (∀env x y.
     exp_rel env x y ⇒
       v_rel (Thunk (INR x)) (Thunk (INR (env, y)))) ∧
[v_rel_Atom:]
  (∀l.
     v_rel (Atom l) (Atom l))
End

Theorem v_rel_cases = CONJUNCT2 exp_rel_cases;

Theorem exp_rel_def =
  [ “exp_rel env (Value v) y”,
    “exp_rel env (Var v) y”,
    “exp_rel env (Prim op xs) y”,
    “exp_rel env (App x y) z”,
    “exp_rel env (Lam s x) y”,
    “exp_rel env (Let NONE x y) z”,
    “exp_rel env (Let (SOME s) x y) z”,
    “exp_rel env (If x y z) w”,
    “exp_rel env (Letrec f x) y”,
    “exp_rel env (Delay x) y”,
    “exp_rel env (Box x) y”,
    “exp_rel env (Force x) y” ]
  |> map (SIMP_CONV (srw_ss ()) [Once exp_rel_cases])
  |> LIST_CONJ;

Theorem v_rel_def =
  [ “v_rel (Closure s x) z”,
    “v_rel z (Closure s env x)”,
    “v_rel (Recclosure s x) z”,
    “v_rel z (Recclosure s funs x)”,
    “v_rel (Constructor s x) z”,
    “v_rel z (Constructor s x)”,
    “v_rel (Atom s) z”,
    “v_rel z (Atom s)”,
    “v_rel (Thunk (INL s)) z”,
    “v_rel z (Thunk (INL s))”,
    “v_rel (Thunk (INR s)) z”,
    “v_rel z (Thunk (INR (env, s)))” ]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ;

Definition env_rel_def:
  env_rel binds env =
    LIST_REL (λ(f,v) (g,w). f = g ∧ v_rel v w) (REVERSE binds) env
End

Theorem env_rel_OPTREL[local]:
  env_rel binds env ⇒
    ∀k. OPTREL v_rel (ALOOKUP (REVERSE binds) k) (ALOOKUP env k)
Proof
  rw [env_rel_def]
  \\ ‘env = REVERSE (REVERSE env)’
    by gs []
  \\ pop_assum SUBST_ALL_TAC
  \\ irule LIST_REL_OPTREL \\ gs []
QED

Theorem env_rel_MAP_FST[local]:
  env_rel binds env ⇒
    MAP FST (REVERSE binds) = MAP FST env
Proof
  rw [env_rel_def]
  \\ irule LIST_EQ
  \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_REVERSE, ELIM_UNCURRY]
QED

Theorem exp_rel_subst:
  exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST binds)) env) x y ∧
  env_rel binds extra ⇒
    exp_rel (extra ++ env) (subst binds x) y
Proof
  ‘(∀env' x y.
     exp_rel env' x y ⇒
       ∀env binds extra.
         env' = FILTER (λ(n,x). ¬MEM n (MAP FST binds)) env ∧
         env_rel binds extra ⇒
           exp_rel (extra ++ env) (subst binds x) y) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
  >~ [‘Value v’] >- (
    dxrule_then assume_tac env_rel_OPTREL
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ gvs [ALOOKUP_FILTER, OPTREL_def, ALOOKUP_NONE, MAP_REVERSE]
    \\ simp [subst_def, exp_rel_def, ALOOKUP_APPEND]
    \\ imp_res_tac ALOOKUP_SOME \\ gs [MAP_REVERSE]
    \\ CASE_TAC \\ gs [ALOOKUP_SOME])
  >~ [‘Lit _’] >-
   (dxrule_then assume_tac env_rel_OPTREL
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ gvs [ALOOKUP_FILTER, OPTREL_def, ALOOKUP_NONE, MAP_REVERSE]
    \\ simp [subst_def, exp_rel_def, ALOOKUP_APPEND]
    \\ imp_res_tac ALOOKUP_SOME \\ gs [MAP_REVERSE]
    \\ CASE_TAC \\ gs [ALOOKUP_SOME])
  >~ [‘Cons _ []’] >-
   (dxrule_then assume_tac env_rel_OPTREL
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ gvs [ALOOKUP_FILTER, OPTREL_def, ALOOKUP_NONE, MAP_REVERSE]
    \\ simp [subst_def, exp_rel_def, ALOOKUP_APPEND]
    \\ imp_res_tac ALOOKUP_SOME \\ gs [MAP_REVERSE]
    \\ CASE_TAC \\ gs [ALOOKUP_SOME])
  >~ [‘Var n’] >- (
    dxrule_then assume_tac env_rel_OPTREL
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ simp [subst_def]
    \\ gvs [ALOOKUP_FILTER, OPTREL_def]
    \\ (irule exp_rel_Var ORELSE irule exp_rel_Value)
    \\ gs [ALOOKUP_APPEND, ALOOKUP_NONE, MAP_REVERSE])
  >~ [‘App f x’] >- (
    simp [subst_def, exp_rel_def])
  >~ [‘Lam s x’] >- (
    simp [subst_def, exp_rel_def, FILTER_APPEND_DISTRIB]
    \\ first_x_assum irule
    \\ gs [FILTER_FILTER, LAMBDA_PROD, MAP_FST_FILTER, env_rel_def,
           GSYM FILTER_REVERSE]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule_at Any LIST_REL_FILTER
    \\ irule_at Any env_rel_MAP_FST \\ gs [env_rel_def, Abbr ‘P’]
    \\ gvs [LIST_REL_EL_EQN]
    \\ irule_at Any LIST_EQ
    \\ gvs [EL_MAP, ELIM_UNCURRY, MEM_FILTER]
    \\ rw [DISJ_EQ_IMP, SF CONJ_ss, AC CONJ_COMM CONJ_ASSOC])
  >~ [‘Seq x y’] >- (
    simp [subst_def, exp_rel_def])
  >~ [‘Let (SOME n) x y’] >- (
    simp [subst_def, exp_rel_def, FILTER_APPEND_DISTRIB]
    \\ first_x_assum irule
    \\ gvs [FILTER_FILTER, LAMBDA_PROD, GSYM FST_THM, MAP_FST_FILTER,
            MEM_FILTER]
    \\ qabbrev_tac ‘P = λx. x ≠ n’ \\ gs []
    \\ rw [DISJ_EQ_IMP, SF CONJ_ss, AC CONJ_COMM CONJ_ASSOC]
    \\ gs [env_rel_def, GSYM FILTER_REVERSE]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN]
    \\ irule LIST_EQ
    \\ gvs [EL_MAP, ELIM_UNCURRY])
  >~ [‘If x1 y1 z1’] >- (
    simp [subst_def, exp_rel_def])
  >~ [‘Prim op xs’] >- (
    simp [subst_def, exp_rel_def, EVERY2_MAP, SF ETA_ss]
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘Letrec f x’] >- (
    gs [subst_def, exp_rel_def, EVERY2_MAP, FILTER_FILTER, LAMBDA_PROD,
        MAP_MAP_o, combinTheory.o_DEF, GSYM FST_THM, FILTER_APPEND_DISTRIB]
    \\ first_x_assum (irule_at Any)
    \\ qabbrev_tac ‘P = λn. ¬MEM n (MAP FST f)’ \\ gs []
    \\ gs [MAP_FST_FILTER, MEM_FILTER, FILTER_FILTER, DISJ_EQ_IMP, LAMBDA_PROD]
    \\ gs [SF CONJ_ss, AC CONJ_COMM CONJ_ASSOC, env_rel_def,
           GSYM FILTER_REVERSE]
    \\ irule_at Any LIST_REL_FILTER
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [LAMBDA_PROD, FORALL_PROD]
    \\ irule_at Any env_rel_MAP_FST \\ gvs [env_rel_def]
    \\ simp [GSYM MAP_REVERSE, LIST_REL_MAP1, combinTheory.o_DEF, LAMBDA_PROD]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ rw [FORALL_PROD] \\ gvs [ELIM_UNCURRY]
    \\ first_x_assum (irule_at Any)
    \\ simp [MAP_FST_FILTER, LAMBDA_PROD, MEM_FILTER, DISJ_EQ_IMP, SF CONJ_ss,
             FILTER_FILTER, AC CONJ_COMM CONJ_ASSOC, GSYM FILTER_REVERSE]
    \\ irule LIST_REL_FILTER
    \\ irule_at Any env_rel_MAP_FST
    \\ gvs [ELIM_UNCURRY, env_rel_def, LIST_REL_EL_EQN])
  >~ [‘Delay x’] >- (
    rw [subst_def, exp_rel_def])
  >~ [‘Box x’] >- (
    rw [subst_def, exp_rel_def])
  >~ [‘Force x’] >- (
    rw [subst_def, exp_rel_def])
QED

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;

Theorem PAIR_REL_def[local,simp] = quotient_pairTheory.PAIR_REL;

Theorem eval_to_exp_rel:
  ∀k x env y.
    exp_rel env x y ⇒
      ($= +++ v_rel) (eval_to k x) (eval_to k env y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  >~ [‘Value v’] >- (
    gs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def])
  >~ [‘Var n’] >- (
    gs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def])
  >~ [‘App f x’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def]
    \\ rename1 ‘exp_rel env f g’
    \\ rename1 ‘exp_rel env x y’
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k env y’ \\ gs []
    \\ Cases_on ‘eval_to k f’ \\ Cases_on ‘eval_to k env g’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyClosure_def, v_rel_def,
                                            envLangTheory.dest_anyClosure_def]
    >- (
      IF_CASES_TAC \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ ‘[s,v] = [] ++ [s,v]’ by gs []
      \\ pop_assum SUBST1_TAC
      \\ first_x_assum (irule_at Any) \\ gs []
      \\ ‘(s,w)::l = [s,w] ++ l’ by gs []
      \\ pop_assum SUBST1_TAC
      \\ irule exp_rel_subst
      \\ gs [exp_rel_def, env_rel_def])
    \\ qmatch_asmsub_abbrev_tac ‘LIST_REL (λ(a,x) (b,y). a = b ∧ R x y) xs ys’
    \\ ‘OPTREL R (ALOOKUP xs s) (ALOOKUP ys s)’
      by (‘xs = REVERSE (REVERSE xs)’ by gs [] \\ pop_assum SUBST1_TAC
          \\ ‘ys = REVERSE (REVERSE ys)’ by gs [] \\ pop_assum SUBST1_TAC
          \\ irule LIST_REL_OPTREL
          \\ gvs [LIST_REL_EL_EQN])
    \\ gs [OPTREL_def, Abbr ‘ys’, Abbr ‘R’]
    \\ qpat_x_assum ‘exp_rel _ x0 y0’ mp_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (irule_at Any)
    \\ qmatch_goalsub_abbrev_tac ‘exp_rel (A::(B ++ C))’
    \\ ‘A::(B ++ C) = A::B ++ C’ by gs []
    \\ pop_assum SUBST1_TAC
    \\ irule exp_rel_subst
    \\ unabbrev_all_tac
    \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
           FILTER_FILTER, AC CONJ_COMM CONJ_ASSOC]
    \\ gs [env_rel_def, LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, EL_REVERSE,
           v_rel_def])
  >~ [‘Lam s x’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def, v_rel_def])
  >~ [‘Seq x1 y1’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def, v_rel_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’
    \\ Cases_on ‘eval_to (k - 1) env x2’ \\ gs [])
  >~ [‘Let (SOME n) x1 y1’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def, v_rel_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’
    \\ Cases_on ‘eval_to (k - 1) env x2’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ first_x_assum irule
    \\ ‘(n,w)::env = [n,w] ++ env’ by gs []
    \\ pop_assum SUBST_ALL_TAC
    \\ irule exp_rel_subst
    \\ gs [env_rel_def])
  >~ [‘If x1 y1 z1’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def, v_rel_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’
    \\ Cases_on ‘eval_to (k - 1) env x2’ \\ gs []
    \\ IF_CASES_TAC \\ gs [v_rel_def]
    \\ IF_CASES_TAC \\ gs [v_rel_def]
    \\ IF_CASES_TAC \\ gs [v_rel_def]
    \\ IF_CASES_TAC \\ gs [v_rel_def])
  >~ [‘Letrec f x’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def, v_rel_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def]
    \\ irule exp_rel_subst
    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ gvs [env_rel_def, LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, EL_REVERSE,
            v_rel_def])
  >~ [‘Delay x’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def, v_rel_def])
  >~ [‘Box x’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def, v_rel_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ rename1 ‘exp_rel _ x y’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k env y’ \\ gs [v_rel_def])
  >~ [‘Force x’] >- (
    gvs [exp_rel_def]
    \\ rename1 ‘exp_rel _ x y’
    \\ simp [Once eval_to_def, envLangTheory.eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_all_then assume_tac)
    \\ gs [PULL_EXISTS]
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k env y’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ reverse (Cases_on ‘dest_Tick v’) \\ gs []
    >- (
      Cases_on ‘v’ \\ gs []
      \\ rgs [Once v_rel_cases])
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def, v_rel_def,
                                           envLangTheory.dest_anyThunk_def]
    >- (
      qmatch_asmsub_abbrev_tac
        ‘LIST_REL (λ(a,x) (b,y). a = b ∧ R x y) xs ys’
      \\ ‘OPTREL R (ALOOKUP xs s) (ALOOKUP ys s)’
        by (‘xs = REVERSE (REVERSE xs)’ by gs [] \\ pop_assum SUBST1_TAC
            \\ ‘ys = REVERSE (REVERSE ys)’ by gs [] \\ pop_assum SUBST1_TAC
            \\ irule LIST_REL_OPTREL \\ gs [])
      \\ gvs [OPTREL_def, Abbr ‘R’]
      \\ pop_assum mp_tac
      \\ rw [Once exp_rel_cases] \\ gs []
      \\ first_x_assum irule
      \\ gs [subst_funs_def]
      \\ irule exp_rel_subst
      \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
      \\ gvs [env_rel_def, LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, EL_REVERSE,
              Abbr ‘xs’, v_rel_def])
    \\ CASE_TAC \\ gvs [v_rel_def]
    \\ first_x_assum irule
    \\ simp [subst_funs_def])
  >~ [‘MkTick x’] >- (
    rgs [Once exp_rel_cases])
  >~ [‘Prim op xs’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def]
    >- (fs [result_map_def] \\ simp [Once v_rel_cases])
    >- (fs [result_map_def] \\ simp [Once v_rel_cases])
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, SF ETA_ss]
      \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ ‘($= +++ (LIST_REL v_rel)) (result_map f xs) (result_map g ys)’
        suffices_by (
          rw []
          \\ Cases_on ‘result_map f xs’ \\ Cases_on ‘result_map g ys’ \\ gs []
          \\ simp [v_rel_def])
      \\ gs [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ unabbrev_all_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to k env (EL n ys)’ \\ gvs [SF SFY_ss])
      \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      >- (
        last_assum (drule_all_then assume_tac)
        \\ last_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to k env (EL n ys)’ \\ gvs [SF SFY_ss]
        \\ IF_CASES_TAC \\ gs []
        \\ rename1 ‘m < LENGTH ys’
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
      \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ gvs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”, EVERY2_MAP, LIST_REL_EL_EQN]
      \\ rw []
      \\ first_x_assum (drule_all_then assume_tac)
      \\ first_x_assum (drule_all_then assume_tac)
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ Cases_on ‘eval_to k (EL n xs)’
      \\ Cases_on ‘eval_to k env (EL n ys)’ \\ gs []
      \\ rename1 ‘INL err’ \\ Cases_on ‘err’ \\ gs [])
    >- ((* IsEq *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel env x y’
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) env y’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [v_rel_def]
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [v_rel_def])
    >- ((* Proj *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel env x y’
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) env y’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [v_rel_def]
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [v_rel_def])
    >- ((* AtomOp *)
      gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
      \\ Cases_on ‘k = 0’ \\ gs []
      >- (
        simp [result_map_def, MEM_MAP, GSYM NOT_NULL_MEM, NULL_EQ]
        \\ rw [] \\ gvs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [v_rel_def])
      \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ ‘result_map f xs = result_map g ys’
        suffices_by (
          rw []
          \\ Cases_on ‘result_map g ys’ \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
      \\ gs [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ unabbrev_all_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ rw [] \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ rpt (first_x_assum (qspec_then ‘n’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
        \\ Cases_on ‘eval_to (k - 1) env (EL n ys)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      >- (
        rw [] \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        >- (
          rename1 ‘m < LENGTH ys’
          \\ last_x_assum (drule_all_then assume_tac)
          \\ last_x_assum (drule_all_then assume_tac)
          \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
          \\ Cases_on ‘eval_to (k - 1) (EL m xs)’
          \\ Cases_on ‘eval_to (k - 1) env (EL m ys)’ \\ gs []
          \\ rename1 ‘v_rel v w’
          \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
        \\ last_x_assum (drule_all_then assume_tac)
        \\ last_x_assum (drule_all_then assume_tac)
        \\ rpt (first_x_assum (qspec_then ‘n’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
        \\ Cases_on ‘eval_to (k - 1) env (EL n ys)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      \\ rw [] \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      >- (
        first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
        \\ Cases_on ‘eval_to (k - 1) env (EL n ys)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      >- (
        first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
        \\ Cases_on ‘eval_to (k - 1) env (EL n ys)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      \\ irule LIST_EQ
      \\ gs [MAP_MAP_o, combinTheory.o_DEF, EL_MAP]
      \\ qx_gen_tac ‘m’ \\ rw []
      \\ first_x_assum (drule_all_then assume_tac)
      \\ first_x_assum (drule_all_then assume_tac)
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ Cases_on ‘eval_to (k - 1) (EL m xs)’
      \\ Cases_on ‘eval_to (k - 1) env (EL m ys)’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def]))
QED

Theorem eval_exp_rel:
  exp_rel env x y ⇒
    ($= +++ v_rel) (eval x) (eval env y)
Proof
  rw [thunkLangTheory.eval_def, envLangTheory.eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ rw [] \\ gs []
  >- (
    drule_all_then (qspec_then ‘i + j’ assume_tac) eval_to_exp_rel
    \\ drule_then (qspec_then ‘i + j’ assume_tac) eval_to_mono
    \\ drule_then (qspec_then ‘i + j’ assume_tac) envLangTheory.eval_to_mono
    \\ gs [])
  >- (
    drule_all_then (qspec_then ‘i’ assume_tac) eval_to_exp_rel
    \\ first_x_assum (qspec_then ‘i’ assume_tac) \\ gs [])
  \\ drule_all_then (qspec_then ‘k’ assume_tac) eval_to_exp_rel
  \\ first_x_assum (qspec_then ‘k’ assume_tac) \\ gs []
QED

(************************)

Definition cont_rel_def[simp]:
  cont_rel thunk_semantics$Done env_semantics$Done = T ∧
  cont_rel (BC v c) (BC w d) = (v_rel v w ∧ cont_rel c d) ∧
  cont_rel (HC v c) (HC w d) = (v_rel v w ∧ cont_rel c d) ∧
  cont_rel _ _ = F
End

Definition next_rel_def[simp]:
  next_rel (Act a c s) (env_semantics$Act b d t) =
    (a = b ∧ cont_rel c d ∧ LIST_REL (LIST_REL v_rel) s t) ∧
  next_rel Ret Ret = T ∧
  next_rel Div Div = T ∧
  next_rel Err Err = T ∧
  next_rel (_: (string # string) thunk_semantics$next_res) _ = F
End

Triviality LIST_REL_ALOOKUP_lemma:
  ∀f g s.
    LIST_REL (λ(fn,b) (gn,c). fn = gn ∧ exp_rel xs b c) f g ⇒
    ALOOKUP f s = NONE ∧ ALOOKUP g s = NONE ∨
    ∃b c.
      ALOOKUP f s = SOME b ∧
      ALOOKUP g s = SOME c ∧ exp_rel xs b c
Proof
  Induct \\ fs [PULL_EXISTS,FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ IF_CASES_TAC \\ fs []
QED

Theorem LIST_REL_MAP_MAP:
  ∀xs ys f g.
    LIST_REL P (MAP f xs) (MAP g ys) ⇔
    LIST_REL (λx y. P (f x) (g y)) xs ys
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on ‘ys’ \\ gvs []
QED

Theorem force_thm:
  ∀v w. v_rel v w ⇒ ($= +++ v_rel) (force v) (force w)
Proof
  fs [force_def,env_semanticsTheory.force_def]
  \\ reverse Cases \\ simp [Once v_rel_cases]
  \\ fs [PULL_EXISTS]
  \\ fs [dest_anyThunk_def,envLangTheory.dest_anyThunk_def]
  \\ rw [] \\ gvs []
  >~ [‘subst_funs []’]
  >- (fs [subst_funs_def] \\ imp_res_tac eval_exp_rel \\ fs [])
  \\ drule LIST_REL_ALOOKUP_lemma
  \\ disch_then $ qspec_then ‘s’ strip_assume_tac
  \\ fs []
  \\ pop_assum mp_tac
  \\ simp [Once exp_rel_cases]
  \\ strip_tac \\ gvs []
  \\ fs [subst_funs_def]
  \\ irule eval_exp_rel
  \\ irule exp_rel_subst
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD]
  \\ fs [MEM_MAP,FORALL_PROD]
  \\ fs [env_rel_def]
  \\ fs [GSYM MAP_REVERSE]
  \\ simp [LIST_REL_MAP_MAP,LAMBDA_PROD]
  \\ fs [LIST_REL_EL_EQN]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs []
  \\ rw [LAMBDA_PROD]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs []
  \\ first_assum drule
  \\ asm_rewrite_tac []
  \\ fs [] \\ rw []
  \\ simp [Once v_rel_cases]
  \\ fs [LIST_REL_EL_EQN,MEM_MAP,FORALL_PROD]
QED

Theorem apply_closure_thm:
  ∀v1 w1 v2 w2 f g.
    v_rel v1 w1 ∧
    v_rel v2 w2 ∧
    (∀x y. ($= +++ v_rel) x y ⇒ next_rel (f x) (g y)) ⇒
    next_rel (apply_closure v1 v2 f)
             (apply_closure w1 w2 g)
Proof
  fs [apply_closure_def,env_semanticsTheory.apply_closure_def]
  \\ fs [dest_anyClosure_def,envLangTheory.dest_anyClosure_def]
  \\ simp [Once v_rel_cases] \\ rw [] \\ gvs []
  >-
   (first_x_assum irule
    \\ irule eval_exp_rel
    \\ once_rewrite_tac [GSYM (EVAL “[x:'a] ++ xs”)]
    \\ irule exp_rel_subst \\ fs []
    \\ fs [env_rel_def]
    \\ last_x_assum mp_tac
    \\ simp [Once exp_rel_cases])
  \\ drule LIST_REL_ALOOKUP_lemma
  \\ disch_then $ qspec_then ‘n’ strip_assume_tac
  \\ fs []
  \\ pop_assum mp_tac
  \\ simp [Once exp_rel_cases]
  \\ strip_tac \\ gvs []
  \\ first_assum irule
  \\ irule eval_exp_rel
  \\ rewrite_tac [APPEND |> CONJUNCT2 |> GSYM]
  \\ irule exp_rel_subst
  \\ simp [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FILTER_FILTER]
  \\ fs [MEM_MAP,FORALL_PROD,FILTER_FILTER]
  \\ reverse conj_tac
  >-
   (pop_assum mp_tac
    \\ match_mp_tac (METIS_PROVE [] “x = y ⇒ (x ⇒ y)”)
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ fs [FUN_EQ_THM,FORALL_PROD]
    \\ rw [] \\ eq_tac \\ rw [])
  \\ fs [env_rel_def]
  \\ fs [GSYM MAP_REVERSE]
  \\ simp [LIST_REL_MAP_MAP,LAMBDA_PROD]
  \\ fs [LIST_REL_EL_EQN]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs []
  \\ rw [LAMBDA_PROD]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs []
  \\ first_assum drule
  \\ asm_rewrite_tac []
  \\ simp_tac std_ss []
  \\ fs [] \\ rw []
  \\ simp [Once v_rel_cases]
  \\ fs [LIST_REL_EL_EQN,MEM_MAP,FORALL_PROD]
QED

Triviality v_rel_RetVal[simp]:
  v_rel (Constructor "Ret" [Thunk (INR (Lit a))]) (RetVal (Atom a))
Proof
  simp [Once v_rel_cases]
  \\ simp [Once v_rel_cases]
  \\ simp [Once exp_rel_cases]
QED

Triviality force_similar:
  ($= +++ v_rel) (force x) (force y) ⇒
  (force y = INL Type_error ⇔ force x = INL Type_error) ∧
  (force y = INL Diverge ⇔ force x = INL Diverge)
Proof
  Cases_on ‘force y’ \\ Cases_on ‘force x’ \\ gvs []
QED

Theorem LIST_REL_LUPDATE:
  ∀xs ys x y n.
    LIST_REL R xs ys ∧ R x y ⇒
    LIST_REL R (LUPDATE x n xs) (LUPDATE y n ys)
Proof
  Induct \\ fs [PULL_EXISTS,LUPDATE_def] \\ rw []
  \\ Cases_on ‘n’ \\ fs [LUPDATE_def]
QED

Theorem next_thm:
  ∀k v c s w d t.
    ($= +++ v_rel) v w ∧
    cont_rel c d ∧
    LIST_REL (LIST_REL v_rel) s t ⇒
      next_rel (next k v c s) (next k w d t)
Proof
  ho_match_mp_tac next_ind \\ rw []
  \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs []
  >- (
    simp [next_def,env_semanticsTheory.next_def]
    \\ CASE_TAC \\ gs [])
  \\ rename1 ‘v_rel v w’
  \\ Cases_on ‘(∃s x. v = Closure s x) ∨
               (∃f n. v = Recclosure f n) ∨
               (∃x. v = Thunk x) ∨
               (∃x. v = Atom x)’
  >- (
    gvs [] \\ fs [Once v_rel_cases]
    \\ res_tac \\ rgs []
    >~ [‘Atom x’] >- (
      Cases_on ‘w’ \\ res_tac \\ gs []
      \\ simp [next_def,env_semanticsTheory.next_def])
    \\ simp [next_def,env_semanticsTheory.next_def])
  \\ Cases_on ‘∃x. v = DoTick x’
  >- (gvs [] \\ fs [Once v_rel_cases])
  \\  fs []
  \\ ‘∃nm vs. v = Constructor nm vs’
    by (Cases_on ‘v’ \\ gs [])
  \\ gvs [v_rel_def]
  \\ simp [Once next_def]
  \\ simp [Once env_semanticsTheory.next_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ Cases_on ‘nm = "Ret"’ \\ gvs [] >-
   (IF_CASES_TAC \\ gs [] \\ gvs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1n ⇔ x = 0”]
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs [])
    \\ reverse (Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs [])
    >- (first_x_assum irule \\ gs []
        \\ simp [Once v_rel_cases])
    \\ simp [force_apply_closure_def,
             env_semanticsTheory.force_apply_closure_def]
    \\ rename1 ‘v_rel v w’
    \\ ‘($= +++ v_rel) (force v) (force w)’ by (irule force_thm \\ fs [])
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (CASE_TAC \\ gs [])
    \\ irule apply_closure_thm \\ fs [])
  \\ Cases_on ‘nm = "Raise"’ \\ gvs [] >-
   (IF_CASES_TAC \\ gs [] \\ gvs []
    \\ gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1n ⇔ x = 0”]
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs [])
    \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs []
    >- (first_x_assum irule \\ gs []
        \\ simp [Once v_rel_cases])
    \\ simp [force_apply_closure_def,
             env_semanticsTheory.force_apply_closure_def]
    \\ rename1 ‘v_rel v w’
    \\ ‘($= +++ v_rel) (force v) (force w)’ by (irule force_thm \\ fs [])
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (CASE_TAC \\ gs [])
    \\ irule apply_closure_thm \\ fs [])
  \\ Cases_on ‘nm = "Bind"’ \\ gvs [] >-
   (IF_CASES_TAC \\ gs [] \\ gvs []
    \\ rgs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”]
    \\ rw [] \\ rgs [SF DNF_ss]
    \\ rename1 ‘v_rel v w’
    \\ ‘($= +++ v_rel) (force v) (force w)’ by (irule force_thm \\ fs [])
    \\ simp [Once next_def])
  \\ Cases_on ‘nm = "Handle"’ \\ gvs [] >-
   (IF_CASES_TAC \\ gs []
    \\ gs [] \\ res_tac \\ gvs []
    \\ rgs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”]
    \\ rw [] \\ rgs [SF DNF_ss]
    \\ rename1 ‘v_rel v w’
    \\ ‘($= +++ v_rel) (force v) (force w)’ by (irule force_thm \\ fs [])
    \\ simp [Once next_def])
  \\ Cases_on ‘nm = "Act"’ \\ gvs [] >-
   (IF_CASES_TAC \\ gs []
    \\ gs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1n ⇔ x = 0”]
    \\ simp [with_atoms_def, result_map_def, env_semanticsTheory.with_atoms_def] \\ gvs[]
    \\ rename1 ‘v_rel v w’
    \\ ‘($= +++ v_rel) (force v) (force w)’ by (irule force_thm \\ fs [])
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (Cases_on `x'` \\ gs [])
    \\ gvs []
    \\ rename1 ‘v_rel a b’
    \\ qpat_x_assum ‘v_rel a b’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [get_atoms_def,env_semanticsTheory.get_atoms_def]
    \\ CASE_TAC \\ gs []
    \\ gs [LIST_REL_EL_EQN])
  \\ Cases_on ‘nm = "Alloc"’ \\ gvs [] >-
   (IF_CASES_TAC \\ gs []
    \\ rgs [LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”, SF DNF_ss]
    \\ simp [with_atoms_def, result_map_def, env_semanticsTheory.with_atoms_def] \\ gvs[]
    \\ rename1 ‘v_rel v w’
    \\ ‘($= +++ v_rel) (force v) (force w)’ by (irule force_thm \\ fs [])
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (Cases_on `x'` \\ gs [])
    \\ qpat_x_assum ‘v_rel a b’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [get_atoms_def,env_semanticsTheory.get_atoms_def]
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ simp [PULL_EXISTS]
    \\ qexists_tac ‘[Int i]’ \\ simp [LIST_REL_REPLICATE_same]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ Cases_on ‘nm = "Length"’ \\ gvs [] >-
   (IF_CASES_TAC \\ gs []
    \\ gs [] \\ res_tac \\ gvs []
    \\ gs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute, DECIDE “∀x. x < 1n ⇔ x = 0”]
    \\ simp [with_atoms_def, result_map_def, env_semanticsTheory.with_atoms_def] \\ gvs[]
    \\ rename1 ‘v_rel v w’
    \\ ‘($= +++ v_rel) (force v) (force w)’ by (irule force_thm \\ fs [])
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (Cases_on `x'` \\ gs [])
    \\ gvs []
    \\ rename1 ‘v_rel a b’
    \\ qpat_x_assum ‘v_rel a b’ mp_tac
    \\ simp [Once v_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [get_atoms_def,env_semanticsTheory.get_atoms_def]
    \\ rpt (CASE_TAC \\ gs [])
    \\ first_x_assum irule \\ gs []
    \\ qexists_tac ‘[Loc n]’ \\ fs [])
  \\ Cases_on ‘nm = "Deref"’ \\ gvs [] >-
   (IF_CASES_TAC \\ gs []
    \\ rgs [LENGTH_EQ_NUM_compute,
            DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”, SF DNF_ss]
    \\ simp [with_atoms_def, result_map_def, env_semanticsTheory.with_atoms_def] \\ gvs[]
    \\ rename [‘force h1 = INL Type_error ∨ force h2 = INL Type_error’]
    \\ rename1 ‘v_rel h1' h1’
    \\ rename1 ‘v_rel h2' h2’
    \\ ‘($= +++ v_rel) (force h1') (force h1)’ by (irule force_thm \\ fs [])
    \\ drule force_similar \\ strip_tac
    \\ ‘($= +++ v_rel) (force h2') (force h2)’ by (irule force_thm \\ fs [])
    \\ drule force_similar \\ strip_tac
    \\ fs []
    \\ IF_CASES_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    \\ Cases_on ‘force h1'’ \\ fs []
    >- (Cases_on ‘x’ \\ gvs [])
    \\ Cases_on ‘force h2'’ \\ fs []
    >- (Cases_on ‘x’ \\ gvs [])
    \\ Cases_on ‘force h1’ >- gvs []
    \\ Cases_on ‘force h2’ >- gvs []
    \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ qpat_x_assum ‘v_rel _ _’ mp_tac
    \\ simp [Once v_rel_cases]
    \\ rpt strip_tac \\ gvs []
    \\ fs [thunk_semanticsTheory.get_atoms_def,
           env_semanticsTheory.get_atoms_def]
    \\ Cases_on ‘l’ \\ gvs []
    \\ Cases_on ‘l'’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs [] \\ fs []
    \\ IF_CASES_TAC >- gvs []
    \\ IF_CASES_TAC >- gvs []
    \\ IF_CASES_TAC
    >-
     (fs [] \\ gvs [LIST_REL_EL_EQN]
      \\ first_x_assum irule
      \\ fs [PULL_EXISTS]
      \\ qexists_tac ‘[Loc n; Int i]’ \\ fs []
      \\ gvs [GSYM arithmeticTheory.NOT_LESS]
      \\ simp [Once v_rel_cases]
      \\ ‘Num i < LENGTH (EL n t)’ by (Cases_on ‘i’ \\ fs [])
      \\ metis_tac [])
    \\ ‘LENGTH (EL n t) = LENGTH (EL n s)’ by gvs [LIST_REL_EL_EQN]
    \\ simp [] \\ gvs []
    \\ first_x_assum $ qspec_then ‘[Loc n; Int i]’ mp_tac
    \\ first_x_assum $ qspec_then ‘[Loc n; Int i]’ mp_tac
    \\ first_x_assum $ qspec_then ‘[Loc n; Int i]’ mp_tac
    \\ fs [] \\ rw []
    >-
     (first_x_assum irule \\ simp [PULL_EXISTS]
      \\ simp [Once v_rel_cases]
      \\ simp [Once v_rel_cases]
      \\ simp [Once exp_rel_cases])
    >-
     (first_x_assum irule \\ simp [PULL_EXISTS]
      \\ simp [Once v_rel_cases]
      \\ simp [Once v_rel_cases]
      \\ simp [Once exp_rel_cases]))
  \\ Cases_on ‘nm = "Update"’ \\ gvs []
  \\ IF_CASES_TAC \\ gs []
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ rename [‘next_rel (with_atoms [h1; h2] _) (with_atoms [h1'; h2'] _)’]
  \\ ‘($= +++ v_rel) (force h1) (force h1')’ by (irule force_thm \\ fs [])
  \\ drule force_similar \\ strip_tac
  \\ ‘($= +++ v_rel) (force h2) (force h2')’ by (irule force_thm \\ fs [])
  \\ drule force_similar \\ strip_tac
  \\ simp [with_atoms_def, result_map_def, env_semanticsTheory.with_atoms_def]
  \\ IF_CASES_TAC >- fs []
  \\ IF_CASES_TAC >- fs []
  \\ fs []
  \\ Cases_on ‘force h1’ \\ fs []
  \\ Cases_on ‘force h1'’ \\ gvs []
  >- (Cases_on ‘x’ \\ gvs [])
  \\ Cases_on ‘force h2’ \\ fs []
  \\ Cases_on ‘force h2'’ \\ gvs []
  >- (Cases_on ‘x’ \\ gvs [])
  \\ qpat_x_assum ‘v_rel _ _’ mp_tac
  \\ qpat_x_assum ‘v_rel _ _’ mp_tac
  \\ simp_tac std_ss [Once v_rel_cases] \\ strip_tac
  \\ gvs [get_atoms_def,env_semanticsTheory.get_atoms_def]
  \\ simp_tac std_ss [Once v_rel_cases] \\ strip_tac
  \\ gvs [get_atoms_def,env_semanticsTheory.get_atoms_def]
  \\ Cases_on ‘l’ \\ fs []
  \\ Cases_on ‘l'’ \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ ‘LENGTH (EL n t) = LENGTH (EL n s)’ by gvs [LIST_REL_EL_EQN]
  \\ simp []
  \\ IF_CASES_TAC
  >-
   (gvs []
    \\ first_x_assum irule
    \\ fs [PULL_EXISTS]
    \\ qexists_tac ‘[Loc n; Int i]’ \\ fs []
    \\ simp [Once v_rel_cases]
    \\ simp [Once v_rel_cases]
    \\ irule_at Any LIST_REL_LUPDATE \\ fs []
    \\ irule_at Any LIST_REL_LUPDATE \\ fs []
    \\ conj_tac >- gvs [LIST_REL_EL_EQN]
    \\ simp [Once exp_rel_cases])
  \\ simp []
  \\ first_x_assum irule \\ simp [PULL_EXISTS]
  \\ qexists_tac ‘[Loc n; Int i]’ \\ fs []
  \\ simp [Once v_rel_cases]
  \\ simp [Once v_rel_cases]
  \\ simp [Once exp_rel_cases]
QED

Theorem next_action_thm:
  ($= +++ v_rel) v w ∧
  cont_rel c d ∧
  LIST_REL (LIST_REL v_rel) s t ⇒
  next_rel (next_action v c s) (next_action w d t)
Proof
  strip_tac
  \\ rw [next_action_def,env_semanticsTheory.next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ rw []
  >-
   (drule_all next_thm
    \\ dxrule env_semanticsTheory.next_less_eq
    \\ dxrule thunk_semanticsTheory.next_less_eq
    \\ disch_then $ qspec_then ‘i+j’ assume_tac
    \\ disch_then $ qspec_then ‘i+j’ assume_tac
    \\ fs [])
  >-
   (last_x_assum (qspec_then ‘i’ assume_tac)
    \\ drule_all_then assume_tac next_thm
    \\ last_x_assum (qspec_then ‘i’ assume_tac)
    \\ gvs [])
  >-
   (last_x_assum (qspec_then ‘k’ assume_tac)
    \\ drule_all_then assume_tac next_thm
    \\ last_x_assum (qspec_then ‘k’ assume_tac)
    \\ gvs [])
QED

Theorem interp_eq:
  ($= +++ v_rel) v w ∧
  cont_rel c d ∧
  LIST_REL (LIST_REL v_rel) s t ⇒
  interp v c s = interp w d t
Proof
  strip_tac
  \\ rw [Once itreeTheory.itree_bisimulation]
  \\ qexists_tac `λt1 t2.
    (t1 = t2 ∨
     ∃v c s w d t.
       interp v c s = t1 ∧
       interp w d t = t2 ∧
       ($= +++ v_rel) v w ∧
       cont_rel c d ∧
       LIST_REL (LIST_REL v_rel) s t)`
  \\ rw []
  >~ [‘interp v c s = interp w d t’] >-
   (disj2_tac >> rpt $ irule_at Any EQ_REFL >> simp[])
  \\ drule_all next_action_thm \\ strip_tac
  \\ qpat_assum ‘interp _ _ _ = _’ mp_tac
  >~ [‘Ret’] >-
   (gvs []
    \\ qpat_x_assum ‘thunk_semantics$interp _ _ _ = _’ mp_tac
    \\ once_rewrite_tac [thunk_semanticsTheory.interp_def]
    \\ once_rewrite_tac [env_semanticsTheory.interp_def]
    \\ simp [AllCaseEqs()]
    \\ rw [] \\ gvs []
    \\ Cases_on `next_action w' d' t''` \\ gvs[])
  >~ [‘Div’] >-
   (gvs []
    \\ qpat_x_assum ‘thunk_semantics$interp _ _ _ = _’ mp_tac
    \\ once_rewrite_tac [thunk_semanticsTheory.interp_def]
    \\ once_rewrite_tac [env_semanticsTheory.interp_def]
    \\ simp [AllCaseEqs()]
    \\ rw [] \\ gvs []
    \\ Cases_on `next_action w' d' t''` \\ gvs[])
  \\ gvs []
  \\ qpat_x_assum ‘thunk_semantics$interp _ _ _ = _’ mp_tac
  \\ simp [Once thunk_semanticsTheory.interp_def]
  \\ simp [AllCaseEqs()]
  \\ rw [] \\ gvs []
  \\ Cases_on `next_action w' d' t''` \\ gvs[]
  \\ simp [Once env_semanticsTheory.interp_def]
  \\ rw []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ disj2_tac
  \\ rpt (irule_at Any EQ_REFL)
  \\ rpt $ first_assum $ irule_at Any
  \\ fs []
QED

Theorem exp_rel_semantics:
  exp_rel [] x y ∧
  closed x ⇒
  thunk_semantics$semantics x Done [] =
  env_semantics$semantics y [] Done []
Proof
  strip_tac
  \\ rw [thunk_semanticsTheory.semantics_def,env_semanticsTheory.semantics_def]
  \\ irule interp_eq
  \\ fs [state_rel_def]
  \\ irule eval_exp_rel \\ fs []
QED

val _ = export_theory ();
