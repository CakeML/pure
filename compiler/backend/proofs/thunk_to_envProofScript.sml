(*
  Proof of correctness for the thunk_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pred_setTheory rich_listTheory thunkLang_primitivesTheory envLangTheory
     finite_mapTheory thunkLangTheory;
open thunk_to_envTheory;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_to_envProof";

val _ = set_grammar_ancestry ["pred_set", "rich_list", "envLang", "thunkLang",
                              "thunk_to_env", "thunkLangProps" ]

val _ = numLib.prefer_num ();

Inductive exp_rel:
[exp_rel_Value:]
  (∀env n v w.
     ALOOKUP env n = SOME w ∧
     v_rel v w ⇒
       exp_rel env (Value v) (Var n)) ∧
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
              f (REVERSE g) ∧
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
              f (REVERSE g) ⇒
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
  exp_rel env x y ∧
  env_rel binds extra ∧
  (∀k. MEM k (MAP FST extra) ⇒ ¬MEM k (MAP FST env)) ⇒
    exp_rel (extra ++ env) (subst binds x) y
Proof
  ‘(∀env x y.
     exp_rel env x y ⇒
       ∀binds extra.
         env_rel binds extra ∧
         (∀k. MEM k (MAP FST extra) ⇒ ¬MEM k (MAP FST env)) ⇒
           exp_rel (extra ++ env) (subst binds x) y) ∧
   (∀v w. v_rel v w ⇒ T)’
   suffices_by rw []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
  >~ [‘Value v’] >- (
    dxrule_then assume_tac env_rel_OPTREL
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ simp [subst_def, exp_rel_def, ALOOKUP_APPEND]
    \\ CASE_TAC \\ gs []
    \\ gvs [OPTREL_def, ALOOKUP_SOME, SF SFY_ss])
  >~ [‘Var n’] >- (
    dxrule_then assume_tac env_rel_OPTREL
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ simp [subst_def]
    \\ CASE_TAC \\ gs [exp_rel_def, OPTREL_def, ALOOKUP_NONE, ALOOKUP_APPEND])
  >~ [‘App f x’] >- (
    simp [subst_def, exp_rel_def])
  >~ [‘Lam s x’] >- (
    simp [subst_def, exp_rel_def, FILTER_APPEND_DISTRIB]
    \\ first_x_assum irule
    \\ gs [MEM_MAP, MAP_FILTER, MEM_FILTER, PULL_EXISTS, FORALL_PROD, SF SFY_ss]
    \\ gs [env_rel_def, GSYM FILTER_REVERSE]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER
    \\ irule_at Any env_rel_MAP_FST \\ gs [env_rel_def, Abbr ‘P’]
    \\ gvs [ELIM_UNCURRY, LIST_REL_EL_EQN] )
  >~ [‘Seq x y’] >- (
    simp [subst_def, exp_rel_def])
  >~ [‘Let (SOME n) x y’] >- (
    simp [subst_def, exp_rel_def, FILTER_APPEND_DISTRIB]
    \\ first_x_assum irule
    \\ gs [MEM_MAP, MAP_FILTER, MEM_FILTER, PULL_EXISTS, FORALL_PROD, SF SFY_ss]
    \\ gs [env_rel_def, GSYM FILTER_REVERSE]
    \\ qabbrev_tac ‘P = λx. x ≠ n’ \\ gs []
    \\ irule LIST_REL_FILTER
    \\ irule_at Any env_rel_MAP_FST \\ gs [env_rel_def, Abbr ‘P’]
    \\ gvs [ELIM_UNCURRY, LIST_REL_EL_EQN])
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
    \\ gs [MAP_FST_FILTER, MEM_FILTER]
    \\ gs [env_rel_def, GSYM FILTER_REVERSE]
    \\ irule_at Any LIST_REL_FILTER
    \\ irule_at Any env_rel_MAP_FST
    \\ gs [env_rel_def]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule_at Any LIST_REL_mono
    \\ last_x_assum (irule_at Any)
    \\ simp [FORALL_PROD] \\ rw []
    \\ first_x_assum irule
    \\ gs [MAP_FST_FILTER, GSYM FILTER_REVERSE, MEM_FILTER]
    \\ irule LIST_REL_FILTER
    \\ irule_at Any env_rel_MAP_FST \\ gvs [env_rel_def, LIST_REL_EL_EQN])
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
      \\ gs [exp_rel_def, env_rel_def]
      \\ cheat (* TODO See remark below *))
    \\ qmatch_asmsub_abbrev_tac ‘LIST_REL (λ(a,x) (b,y). a = b ∧ R x y) xs ys’
    \\ ‘OPTREL R (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
      by (irule LIST_REL_OPTREL
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
    \\ cheat (* TODO See remark below *))
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
    (* TODO: It's OK to just filter anything we bind from env;
             doesn't matter if its in there. The exp_rel_subst
             theorem statement looks wrong. *)
    \\ cheat)
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
    (* TODO: Same remark as above about exp_rel_subst. *)
    \\ cheat)
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
        ‘LIST_REL (λ(a,x) (b,y). a = b ∧ R x y) xs (REVERSE ys)’
      \\ ‘OPTREL R (ALOOKUP (REVERSE xs) s) (ALOOKUP ys s)’
        by (‘ys = REVERSE (REVERSE ys)’
              by gs []
            \\ pop_assum SUBST1_TAC
            \\ irule LIST_REL_OPTREL \\ gs [])
      \\ gvs [OPTREL_def, Abbr ‘R’]
      \\ pop_assum mp_tac
      \\ rw [Once exp_rel_cases] \\ gs []
      \\ first_x_assum irule
      \\ gs [subst_funs_def]
      \\ irule exp_rel_subst
      \\ cheat (* exp_rel_subst *))
    \\ CASE_TAC \\ gvs [v_rel_def]
    \\ first_x_assum irule
    \\ simp [subst_funs_def])
  >~ [‘MkTick x’] >- (
    rgs [Once exp_rel_cases])
  >~ [‘Prim op xs’] >- (
    gvs [exp_rel_def, eval_to_def, envLangTheory.eval_to_def]
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

val _ = export_theory ();

