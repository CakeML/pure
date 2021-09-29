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

val _ = numLib.prefer_num ();

(*
Inductive exp_inv:
  (∀v.
     v_inv v ⇒
       exp_inv (Value v)) ∧
  (∀n.
     exp_inv (Var n)) ∧
  (∀f x.
     exp_inv f ∧
     exp_inv x ⇒
       exp_inv (App f x)) ∧
  (∀s x.
     exp_inv x ⇒
       exp_inv (Lam s x)) ∧
  (∀s x y.
     exp_inv x ∧
     exp_inv y ⇒
       exp_inv (Let s x y)) ∧
  (∀x y z.
     exp_inv x ∧
     exp_inv y ∧
     exp_inv z ⇒
       exp_inv (If x y z)) ∧
  (∀op xs.
     EVERY exp_inv xs ⇒
       exp_inv (Prim op xs)) ∧
  (∀f x.
     EVERY exp_inv (MAP SND f) ∧
     exp_inv x ⇒
       exp_inv (Letrec f x)) ∧
  (∀x.
     exp_inv x ⇒
       exp_inv (Delay x)) ∧
  (∀x.
     exp_inv x ⇒
       exp_inv (Box x)) ∧
  (∀x.
     exp_inv x ⇒
       exp_inv (Force x)) ∧
  (∀s vs.
     EVERY v_inv vs ⇒
       v_inv (Constructor s vs)) ∧
  (∀s x.
     exp_inv x ⇒
       v_inv (Closure s x)) ∧
  (∀f n.
     EVERY exp_inv (MAP SND f) ⇒
       v_inv (Recclosure f n)) ∧
  (∀x.
     v_inv (Atom x)) ∧
  (∀v.
     v_inv v ⇒
       v_inv (Thunk (INL v))) ∧
  (∀x.
     exp_inv x ⇒
       v_inv (Thunk (INR x)))
End

Theorem exp_inv_def[simp]:
  (∀v.
     exp_inv (Var v) = T) ∧
  (∀v.
     exp_inv (Value v) =
       v_inv v) ∧
  (∀f x.
     exp_inv (App f x) =
       (exp_inv f ∧ exp_inv x)) ∧
  (∀s x.
     exp_inv (Lam s x) =
       exp_inv x) ∧
  (∀s x y.
     exp_inv (Let s x y) =
       (exp_inv x ∧ exp_inv y)) ∧
  (∀x y z.
     exp_inv (If x y z) =
       (exp_inv x ∧
        exp_inv y ∧
        exp_inv z)) ∧
  (∀op xs.
     exp_inv (Prim op xs) =
       EVERY exp_inv xs) ∧
  (∀f x.
     exp_inv (Letrec f x) =
       (EVERY exp_inv (MAP SND f) ∧
        exp_inv x)) ∧
  (∀x.
     exp_inv (Delay x) =
       exp_inv x) ∧
  (∀x.
     exp_inv (Box x) =
       exp_inv x) ∧
  (∀x.
     exp_inv (Force x) =
       exp_inv x) ∧
  (∀x.
     ¬exp_inv (MkTick x))
Proof
  rw [] \\ rw [Once exp_inv_cases]
QED

Theorem v_inv_def[simp]:
  (∀s vs.
     v_inv (Constructor s vs) =
       EVERY v_inv vs) ∧
  (∀s x.
     v_inv (Closure s x) =
       exp_inv x) ∧
  (∀f n.
     v_inv (Recclosure f n) =
       EVERY exp_inv (MAP SND f)) ∧
  (∀x.
     v_inv (Atom x)) ∧
  (∀v.
     ¬v_inv (DoTick v)) ∧
  (∀v.
     v_inv (Thunk (INL v)) =
       v_inv v) ∧
  (∀x.
     v_inv (Thunk (INR x)) =
       exp_inv x)
Proof
  rw [] \\ rw [Once exp_inv_cases]
QED
 *)

Inductive exp_rel:
[exp_rel_Value:]
  (∀env n v w.
     ALOOKUP (REVERSE env) n = SOME w ∧
     v_rel v w ⇒
       exp_rel env (Value v) (Var n)) ∧
[exp_rel_Var:]
  (∀env n.
     ALOOKUP (REVERSE env) n = NONE ⇒
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
                 exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c) f g ∧
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
                 exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c) f g ⇒
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

(*
Theorem ALOOKUP_LIST_REL[local]:
  ∀xs ys x.
    MAP FST xs = MAP FST ys ∧
    LIST_REL P xs ys ⇒
      (ALOOKUP xs x = NONE ⇔ ALOOKUP ys x = NONE) ∧
      (∀vx.
         ALOOKUP xs x = SOME vx ⇒
           ∃vy.
             ALOOKUP ys x = SOME vy ∧
             P (x, vx) (x, vy))
Proof
  Induct \\ simp [PULL_EXISTS, FORALL_PROD]
  \\ rw [] \\ fs []
QED
 *)

Theorem dest_Closure_v_rel:
  v_rel v w ⇒
    (∀err. dest_Closure v = INL err ⇒ dest_Closure w = INL err) ∧
    (∀s x.
       dest_Closure v = INR (s, x) ⇒
         ∃env y.
           dest_Closure w = INR (s, env, y) ∧
           exp_rel (FILTER (λ(n, x). n ≠ s) env) x y)
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [envLangTheory.dest_Closure_def, thunkLangTheory.dest_Closure_def,
           v_rel_def, exp_rel_def]
QED

Theorem dest_Thunk_v_rel:
  v_rel v w ⇒
    (∀err. dest_Thunk v = INL err ⇒ dest_Thunk w = INL err) ∧
    (∀nf x. dest_Thunk v = INR x ⇒
       ∃y.
         dest_Thunk w = INR y ∧
           ((∃v1 v2.
               x = INL v1 ∧
               y = INL v2 ∧
               v_rel v1 v2) ∨
            (∃env x1 x2.
               x = INR x1 ∧
               y = INR (env, x2) ∧
               exp_rel env x1 x2)))
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [envLangTheory.dest_Thunk_def, thunkLangTheory.dest_Thunk_def,
           v_rel_def]
  \\ Cases_on ‘s’ \\ simp [v_rel_def]
  \\ Cases_on ‘y’ \\ simp [v_rel_def]
QED

Theorem dest_Recclosure_v_rel:
  v_rel v w ⇒
    (∀err. dest_Recclosure v = INL err ⇒ dest_Recclosure w = INL err) ∧
    (∀f n.
       dest_Recclosure v = INR (f, n) ⇒
         ∃g env.
           dest_Recclosure w = INR (g, env, n) ∧
           LIST_REL (λ(fn,b) (gn,c). fn = gn ∧
             exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c) f g)
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [envLangTheory.dest_Recclosure_def,
           thunkLangTheory.dest_Recclosure_def,
           v_rel_def, exp_rel_def]
QED

Theorem dest_Constructor_v_rel:
  v_rel v w ⇒
    (∀err. dest_Constructor v = INL err ⇒ dest_Constructor w = INL err) ∧
    (∀s vs.
       dest_Constructor v = INR (s, vs) ⇒
         ∃ws.
           dest_Constructor w = INR (s, ws) ∧
           LIST_REL v_rel vs ws)
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [envLangTheory.dest_Constructor_def,
           thunkLangTheory.dest_Constructor_def,
           v_rel_def, exp_rel_def]
QED

Definition env_rel_def:
  env_rel binds env ⇔
    MAP FST binds = MAP FST env ∧
    ∀k v.
      ALOOKUP (REVERSE binds) k = SOME v ⇒
        ∃w. ALOOKUP (REVERSE env) k = SOME w ∧
            v_rel v w
End

Theorem exp_rel_ALOOKUP_EQ:
  ∀env1 x y env2.
    exp_rel env1 x y ∧
    ALOOKUP (REVERSE env1) = ALOOKUP (REVERSE env2) ⇒
      exp_rel env2 x y
Proof
  qsuff_tac ‘
    (∀env1 x y.
       exp_rel env1 x y ⇒
       ∀env2.
         ALOOKUP (REVERSE env1) = ALOOKUP (REVERSE env2) ⇒
         exp_rel env2 x y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- (
    rw []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any) \\ fs [])
  \\ ho_match_mp_tac exp_rel_strongind
  \\ simp [exp_rel_def, MEM_MAP, v_rel_def]
  \\ rw [] \\ fs [ALOOKUP_FILTER, GSYM FILTER_REVERSE, FUN_EQ_THM]
  \\ gvs [LIST_REL_EL_EQN]
  \\ rw [] \\ fs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ first_x_assum drule \\ rw []
  \\ first_x_assum irule \\ rw []
  \\ fs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
  \\ rw [] \\ gs [ALOOKUP_NONE]
QED

(*
Theorem MAP_FILTER_FST[local]:
  MAP FST (FILTER (λx. P (FST x)) xs) = FILTER (λx. P x) (MAP FST xs)
Proof
  Induct_on ‘xs’ \\ rw []
QED
 *)

Theorem exp_rel_subst:
  ∀env x y binds extra.
    exp_rel env x y ∧
    env_rel binds extra ∧
    (∀k. MEM k (MAP FST extra) ⇒ ¬MEM k (MAP FST env)) ⇒
      exp_rel (env ++ extra) (subst binds x) y
Proof
  qsuff_tac ‘
    (∀env x y.
       exp_rel env x y ⇒
         ∀binds extra.
           env_rel binds extra ∧
           (∀k. MEM k (MAP FST extra) ⇒ ¬MEM k (MAP FST env)) ⇒
             exp_rel (env ++ extra) (subst binds x) y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- (
    rw [])
  \\ ho_match_mp_tac exp_rel_strongind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ simp [subst_def, exp_rel_def]
  >- ((* Value *)
    rw [ALOOKUP_APPEND, REVERSE_APPEND]
    \\ CASE_TAC \\ fs []
    \\ dxrule_then assume_tac ALOOKUP_SOME
    \\ dxrule_then assume_tac ALOOKUP_SOME
    \\ gs [MAP_REVERSE])
  >- ((* Var *)
    rw [env_rel_def]
    \\ CASE_TAC
    \\ gs [exp_rel_def, ALOOKUP_APPEND, CaseEq "option", ALOOKUP_NONE,
           MAP_REVERSE, REVERSE_APPEND]
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ first_assum (irule_at Any) \\ fs [])
  >- ((* Lam *)
    rw [FILTER_APPEND_DISTRIB]
    \\ first_x_assum irule
    \\ fs [MEM_MAP, MEM_FILTER, MAP_FILTER, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
    \\ fs [env_rel_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, MAP_FST_FILTER])
  >- ((* Let *)
    rw [FILTER_APPEND_DISTRIB]
    \\ first_x_assum irule
    \\ fs [MEM_MAP, MEM_FILTER, MAP_FILTER, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
    \\ fs [env_rel_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, MAP_FST_FILTER])
  >- ((* If *)
    rw []
    \\ fs [LIST_REL_EL_EQN, EL_MAP])
  >- ((* Letrec *)
    simp [FILTER_FILTER, MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY]
    \\ strip_tac \\ rpt gen_tac \\ strip_tac
    \\ simp [SF ETA_ss, FILTER_APPEND_DISTRIB]
    \\ first_x_assum (irule_at Any) \\ fs []
    \\ rpt conj_tac
    >- (
      fs [env_rel_def, LAMBDA_PROD, ALOOKUP_FILTER, GSYM FILTER_REVERSE,
          MAP_FST_FILTER])
    >- (
      fs [LAMBDA_PROD, MAP_FST_FILTER, MEM_FILTER])
    \\ fs [LIST_REL_EL_EQN, EL_MAP]
    \\ rw [] \\ gvs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ simp [FILTER_APPEND_DISTRIB] \\ gvs []
    \\ first_x_assum irule
    \\ simp [LAMBDA_PROD, MAP_FST_FILTER, MEM_FILTER]
    \\ fs [env_rel_def, LAMBDA_PROD, ALOOKUP_FILTER, GSYM FILTER_REVERSE,
           MAP_FST_FILTER])
QED

Theorem exp_rel_subst_app1[local]:
  exp_rel (FILTER (λ(n,x). n ≠ s) env) b c ∧
  v_rel v w ⇒
    exp_rel (env ++ [(s,w)]) (subst1 s v b) c
Proof
  strip_tac
  \\ irule_at Any exp_rel_ALOOKUP_EQ
  \\ irule_at Any exp_rel_subst
  \\ first_assum (irule_at Any) \\ simp []
  \\ simp [env_rel_def, PULL_EXISTS, EXISTS_PROD]
  \\ first_assum (irule_at Any)
  \\ simp [ALOOKUP_FILTER, GSYM FILTER_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND,
           FUN_EQ_THM, MEM_MAP, MEM_FILTER, FORALL_PROD]
QED

Theorem exp_rel_subst_app2[local]:
   exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST ys) ∧ n ≠ s) env) b c ∧
   LIST_REL
     (λ(fn,b) (gn,c).
        fn = gn ∧
        exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST ys)) env) b c) xs ys ∧
   v_rel v w ⇒
     exp_rel
       (env ++ MAP (λ(f,x). (f,Recclosure ys env f)) ys ++ [(s,w)])
       (subst (MAP (λ(g,x). (g,Recclosure xs g)) xs ++ [(s,v)]) b) c
Proof
  strip_tac
  \\ ‘MAP FST xs = MAP FST ys’
    by (qpat_x_assum ‘LIST_REL _ xs _’ mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ rename1 ‘exp_rel foo’
        \\ qid_spec_tac ‘ys’
        \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [ELIM_UNCURRY])
  \\ irule exp_rel_ALOOKUP_EQ
  \\ irule_at Any exp_rel_subst
  \\ first_assum (irule_at Any) \\ simp []
  \\ once_rewrite_tac [GSYM APPEND_ASSOC]
  \\ qmatch_goalsub_abbrev_tac ‘REVERSE (env ++ extra1)’
  \\ qexists_tac ‘extra1’ \\ fs [Abbr ‘extra1’]
  \\ rpt conj_tac \\ simp []
  >- (
    fs [env_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
        GSYM MAP_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND, ALOOKUP_MAP_2]
    \\ rpt gen_tac
    \\ IF_CASES_TAC \\ strip_tac \\ gvs []
    \\ drule_then (qspec_then ‘REVERSE ys’ mp_tac) ALOOKUP_SOME_EL_2
    \\ rw [MAP_REVERSE]
    \\ gvs [EL_REVERSE, LIST_REL_EL_EQN, v_rel_def])
  >- (
    simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ dsimp [MAP_FST_FILTER, MEM_FILTER])
  \\ simp [FUN_EQ_THM, ALOOKUP_APPEND, REVERSE_APPEND, GSYM MAP_REVERSE,
           GSYM FILTER_REVERSE, ALOOKUP_FILTER]
  \\ strip_tac
  \\ IF_CASES_TAC \\ gvs []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ gs [ALOOKUP_NONE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
         MAP_REVERSE]
QED

(*
Theorem exp_inv_subst:
  ∀ws x.
    EVERY v_inv (MAP SND ws) ∧
    exp_inv x ⇒
      exp_inv (subst ws x)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  >- ((* Var *)
    simp [subst_def]
    \\ CASE_TAC \\ fs []
    \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
    \\ gs [EVERY_EL, EL_MAP]
    \\ first_x_assum (drule_then assume_tac) \\ gs [])
  >- ((* Value *)
    gvs [subst_def, EVERY_MAP, EVERY_MEM])
  >- ((* If *)
    gvs [subst_def])
  >- ((* App *)
    gvs [subst_def])
  >- ((* Lam *)
    gvs [subst_def]
    \\ first_x_assum irule
    \\ gs [EVERY_MAP, EVERY_FILTER, EVERY_MEM, ELIM_UNCURRY, SF SFY_ss])
  >- ((* Let NONE *)
    gvs [subst_def])
  >- ((* Let SOME *)
    gvs [subst_def]
    \\ first_x_assum irule
    \\ gs [EVERY_MAP, EVERY_FILTER, EVERY_MEM, ELIM_UNCURRY, SF SFY_ss])
  >- ((* Letrec *)
    gs [subst_def]
    \\ gvs [EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
            EVERY_FILTER, GSYM FST_THM]
    \\ gvs [EVERY_MEM, FORALL_PROD, subst_def, SF SFY_ss])
  >- ((* Delay *)
    gvs [subst_def])
  >- ((* Box *)
    gvs [subst_def])
  >- ((* Force *)
    gvs [subst_def])
  >- ((* Value *)
    gvs [subst_def])
QED
       *)

Theorem eval_to_exp_rel:
  ∀k x res env y.
    eval_to k x = res ∧
    exp_rel env x y ⇒
      case res of
        INL err => eval_to k env y = INL err
      | INR v => ∃w. eval_to k env y = INR w ∧ v_rel v w
Proof
  ho_match_mp_tac eval_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Value *)
    rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def])
  >- ((* Var *)
    rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def ])
  >- ((* App *)
    rw [exp_rel_def]
    \\ rename1 ‘exp_rel env x1 x2’
    \\ rename1 ‘exp_rel env y1 y2’
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x1’ \\ fs []
    \\ Cases_on ‘eval_to k y1’ \\ fs []
    \\ simp [envLangTheory.dest_anyClosure_def,
             thunkLangTheory.dest_anyClosure_def]
    \\ rename1 ‘eval_to k x1 = INR v1’
    \\ qpat_x_assum ‘v_rel v1 _’ assume_tac
    \\ drule_all_then strip_assume_tac dest_Closure_v_rel
    \\ drule_all_then strip_assume_tac dest_Recclosure_v_rel
    \\ Cases_on ‘dest_Recclosure v1’ \\ fs []
    >- (
      Cases_on ‘dest_Closure v1’ \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum (qspec_then ‘[]’ assume_tac) \\ fs []
      \\ first_x_assum irule
      \\ irule_at Any exp_rel_subst_app1 \\ fs [])
    \\ reverse (Cases_on ‘dest_Closure v1’) \\ fs []
    >- (
      Cases_on ‘v1’
      \\ fs [dest_Closure_def, dest_Recclosure_def])
    \\ pairarg_tac \\ gvs []
    \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
    \\ gs [OPTREL_def]
    \\ qpat_x_assum ‘exp_rel _ x0 _’ mp_tac
    \\ simp [Once exp_rel_cases]
    \\ strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_subst_app2 \\ fs []
    \\ gvs [FILTER_FILTER, combinTheory.o_DEF, LAMBDA_PROD, MAP_REVERSE,
            AC CONJ_COMM CONJ_ASSOC]
    \\ ‘MAP FST f = MAP FST g’
      by (irule LIST_EQ \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP])
    \\ gs [])
  >- ((* Lam *)
    rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def,
             v_rel_def, exp_rel_def])
  >- ((* Let NONE *)
    rename1 ‘Let NONE x1 y1’
    \\ rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def,
             v_rel_def, exp_rel_def]
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs [])
  >- ((* Let SOME *)
    rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def,
             v_rel_def, exp_rel_def]
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ gvs []
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_subst_app1 \\ fs [])
  >- ((* If *)
    rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ rpt (first_x_assum (drule_then assume_tac)) \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >- (
      rw []
      \\ gvs [v_rel_def])
    \\ IF_CASES_TAC \\ fs []
    >- (
      rw []
      \\ gvs [v_rel_def])
    \\ Cases_on ‘y’ \\ rw [] \\ gvs [v_rel_def])
  >- ((* Letrec *)
    rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ fs [subst_funs_def]
    \\ irule_at Any exp_rel_ALOOKUP_EQ
    \\ irule_at Any exp_rel_subst
    \\ first_assum (irule_at Any) \\ simp []
    \\ qmatch_goalsub_abbrev_tac ‘MAP Q g’
    \\ qexists_tac ‘MAP Q g’ \\ simp [Abbr ‘Q’]
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘MAP FST xs = MAP FST ys’
      by (irule LIST_EQ \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP])
    \\ rpt conj_tac
    >- (
      fs [env_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
          MAP_REVERSE]
      \\ rw [GSYM MAP_REVERSE, ALOOKUP_MAP_2]
      \\ drule_then (qspec_then ‘REVERSE ys’ mp_tac) ALOOKUP_SOME_EL_2
      \\ simp [MAP_REVERSE]
      \\ rw [] \\ gvs [LIST_REL_EL_EQN, EL_REVERSE, v_rel_def])
    >- (
      fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
      \\ simp [MAP_FST_FILTER, MEM_FILTER])
    \\ rw [FUN_EQ_THM, REVERSE_APPEND, GSYM FILTER_REVERSE, GSYM MAP_REVERSE,
           ALOOKUP_APPEND, ALOOKUP_MAP_2, ALOOKUP_FILTER]
    \\ CASE_TAC \\ fs []
    \\ CASE_TAC \\ fs []
    \\ gs [ALOOKUP_NONE, MAP_REVERSE])
  >- ((* Delay *)
    rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def,
             v_rel_def])
  >- ((* Box *)
    rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ simp [v_rel_def])
  >- ((* Force *)
    rw [exp_rel_def]
    \\ simp [Once envLangTheory.eval_to_def, Once thunkLangTheory.eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ first_x_assum (drule_all_then strip_assume_tac) \\ gvs []
    \\ reverse (Cases_on ‘dest_Tick y’) \\ gs []
    >- (
      Cases_on ‘y’ \\ gs [Once v_rel_cases])
    \\ drule_all_then strip_assume_tac dest_Thunk_v_rel
    \\ drule_all_then strip_assume_tac dest_Recclosure_v_rel
    \\ simp [envLangTheory.dest_anyThunk_def, thunkLangTheory.dest_anyThunk_def]
    \\ reverse (Cases_on ‘dest_Thunk y’) \\ gvs []
    >- (
      Cases_on ‘y’ \\ gvs []
      \\ simp [Once envLangTheory.eval_to_def, envLangTheory.dest_anyThunk_def])
    >- (
      Cases_on ‘y’ \\ gvs []
      \\ simp [Once envLangTheory.eval_to_def, envLangTheory.dest_anyThunk_def]
      \\ first_x_assum irule
      \\ simp [subst_funs_def])
    \\ Cases_on ‘dest_Recclosure y’ \\ gvs []
    \\ Cases_on ‘y’ \\ gs []
    \\ pairarg_tac \\ gvs []
    \\ Cases_on ‘w’ \\ gvs [v_rel_def]
    \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
    \\ gs [OPTREL_def]
    \\ ‘MAP FST f = MAP FST g’
      by (irule LIST_EQ \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP])
    \\ qpat_x_assum ‘exp_rel _ x0 _’ mp_tac
    \\ simp [Once exp_rel_cases]
    \\ strip_tac \\ gvs []
    \\ simp [Once envLangTheory.eval_to_def, envLangTheory.dest_anyThunk_def]
    \\ first_x_assum irule \\ simp []
    \\ simp [subst_funs_def]
    \\ irule_at Any exp_rel_ALOOKUP_EQ
    \\ irule_at Any exp_rel_subst
    \\ qmatch_goalsub_abbrev_tac ‘REVERSE (env1 ++ extra1)’
    \\ qexists_tac ‘extra1’
    \\ first_assum (irule_at Any)
    \\ unabbrev_all_tac
    \\ fs [env_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_REVERSE,
           GSYM FST_THM]
    \\ simp [FUN_EQ_THM, GSYM MAP_REVERSE, ALOOKUP_MAP_2, GSYM FILTER_REVERSE,
             ALOOKUP_FILTER, REVERSE_APPEND, ALOOKUP_APPEND, GSYM ALOOKUP_NONE]
    \\ rw [] \\ rpt CASE_TAC \\ gs [ALOOKUP_NONE, PULL_EXISTS, v_rel_def,
                                    MAP_REVERSE]
    \\ rename1 ‘ALOOKUP (REVERSE f) k1’
    \\ drule_then (qspec_then ‘k1’ assume_tac) LIST_REL_OPTREL
    \\ gs [OPTREL_def])
  >- ((* MkTick *)
    rw [exp_rel_def]
    \\ gs [Once exp_rel_cases])
  >- ((* Prim *)
    rw [exp_rel_def]
    \\ simp [envLangTheory.eval_to_def, thunkLangTheory.eval_to_def]
    \\ Cases_on ‘op’ \\ fs []
    >- ((* Cons *)
      gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
      \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ Cases_on ‘result_map f xs’ \\ fs []
      >- (
        reverse (Cases_on ‘result_map g ys’) \\ fs []
        >- (
          gvs [result_map_def, CaseEq "bool", MEM_MAP]
          \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
          \\ unabbrev_all_tac
          \\ gs [MEM_EL, PULL_EXISTS]
          \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs [EVERY_EL])
        \\ gvs [result_map_def, CaseEq "bool", MEM_MAP]
        \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ unabbrev_all_tac \\ gs []
        \\ gvs [MEM_EL, PULL_EXISTS]
        >- (
          rpt (first_x_assum (drule_then assume_tac)) \\ gs [EVERY_EL]
          \\ pop_assum mp_tac \\ gs []
          \\ CASE_TAC \\ gs [])
        \\ rename1 ‘eval_to k (EL m xs)’
        \\ qpat_x_assum ‘m < LENGTH ys’ assume_tac
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs [EVERY_EL])
      \\ Cases_on ‘result_map g ys’ \\ gs []
      >- (
        gvs [result_map_def, CaseEq "bool", MEM_MAP, MEM_EL, PULL_EXISTS,
             EVERY_EL]
        \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ unabbrev_all_tac \\ gs []
        \\ rpt (first_x_assum (drule_all_then assume_tac))
        \\ pop_assum mp_tac
        \\ CASE_TAC \\ gs []
        \\ strip_tac \\ gs [])
      \\ gvs [v_rel_def, LIST_REL_EL_EQN, result_map_def, CaseEq "bool",
              MEM_MAP, EVERY_EL, EL_MAP]
      \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ gs [MAP_MAP_o, combinTheory.o_DEF, EL_MAP] \\ rw []
      \\ gvs [MEM_EL, PULL_EXISTS]
      \\ rpt (first_x_assum (drule_all_then assume_tac))
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ unabbrev_all_tac \\ gs []
      \\ Cases_on ‘eval_to k (EL n xs)’ \\ Cases_on ‘eval_to k env (EL n ys)’
      \\ gvs []
      \\ rename1 ‘INL err’
      \\ Cases_on ‘err’ \\ gs [])
    >- ((* IsEq *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ IF_CASES_TAC \\ fs []
      \\ rename1 ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ drule_all_then strip_assume_tac dest_Constructor_v_rel
      \\ Cases_on ‘dest_Constructor y’ \\ fs []
      \\ pairarg_tac \\ gvs []
      \\ imp_res_tac LIST_REL_LENGTH
      \\ IF_CASES_TAC \\ fs []
      \\ simp [v_rel_def])
    >- ((* Proj *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ IF_CASES_TAC \\ fs []
      \\ rename1 ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ drule_all_then strip_assume_tac dest_Constructor_v_rel
      \\ Cases_on ‘dest_Constructor y’ \\ fs []
      \\ pairarg_tac \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs []
      \\ Cases_on ‘y’ \\ gvs [EVERY_EL])
    >- ((* AtomOp *)
      gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
      \\ Cases_on ‘k = 0’ \\ gs []
      >- (
        simp [result_map_def, MEM_MAP, GSYM NOT_NULL_MEM, NULL_EQ]
        \\ IF_CASES_TAC \\ gs []
        >- (
          IF_CASES_TAC \\ gs [])
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [v_rel_def])
      \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ qsuff_tac ‘result_map f xs = result_map g ys’
      >- (
        rw []
        \\ Cases_on ‘result_map g ys’ \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [v_rel_def])
      \\ gs [result_map_def, MEM_MAP, EVERY_EL]
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ gvs [MEM_EL, PULL_EXISTS]
        \\ first_x_assum (drule_then assume_tac)
        \\ unabbrev_all_tac \\ gs []
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ gvs [CaseEqs ["sum", "v"]]
        \\ rename1 ‘v_rel _ w’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      \\ IF_CASES_TAC \\ gs []
      >- (
        reverse IF_CASES_TAC \\ gs []
        >- (
          fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
          \\ gvs [MEM_EL, PULL_EXISTS]
          \\ first_x_assum (drule_then assume_tac)
          \\ unabbrev_all_tac \\ gs []
          \\ rpt (first_x_assum (drule_then assume_tac))
          \\ first_assum (irule_at Any) \\ gs []
          \\ pop_assum mp_tac
          \\ rpt CASE_TAC \\ gs [CaseEqs ["v"], v_rel_def])
        \\ unabbrev_all_tac \\ gs []
        \\ gvs [MEM_EL, PULL_EXISTS]
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ pop_assum mp_tac
        \\ rpt CASE_TAC \\ gs []
        >- (
          strip_tac \\ gs [CaseEqs ["sum", "envLang$v"]])
        \\ rw [DISJ_EQ_IMP]
        \\ strip_tac
        \\ last_x_assum (qspec_then ‘EL n xs’ assume_tac)
        \\ gs [CaseEqs ["sum", "envLang$v", "v"]]
        \\ Cases_on ‘y’ \\ gvs [v_rel_def])
      \\ IF_CASES_TAC \\ gs []
      >- (
        fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ unabbrev_all_tac
        \\ gvs [MEM_EL, PULL_EXISTS]
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ pop_assum mp_tac
        \\ rpt CASE_TAC \\ gs []
        >- (
          strip_tac \\ gs [CaseEqs ["sum", "envLang$v"]])
        \\ rw [DISJ_EQ_IMP]
        \\ strip_tac
        \\ gs [CaseEqs ["sum", "envLang$v", "v"]]
        \\ Cases_on ‘y’ \\ gvs [v_rel_def])
      \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ gs [EL_MAP, MEM_EL, PULL_EXISTS]
      \\ unabbrev_all_tac \\ gs [] \\ rw []
      >- (
        rpt (first_x_assum (drule_then assume_tac))
        \\ pop_assum mp_tac
        \\ CASE_TAC \\ gs [] \\ rw []
        \\ gs [CaseEqs ["envLang$v", "v"]]
        \\ rename1 ‘v_rel v1 v2’
        \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs [v_rel_def])
      \\ simp [MAP_MAP_o, combinTheory.o_DEF]
      \\ irule LIST_EQ
      \\ gvs [EL_MAP] \\ rw []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gs [v_rel_def]))
QED

Theorem eval_exp_rel:
  eval x = res ∧
  exp_rel env x y ⇒
    case res of
      INL err => eval env y = INL err
    | INR v => ∃w. eval env y = INR w ∧ v_rel v w
Proof
  rw [thunkLangTheory.eval_def, envLangTheory.eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ reverse strip_tac
  >- (
    strip_tac
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ qx_gen_tac ‘k’
    \\ ‘∃r. eval_to k x = r’ by fs []
    \\ drule_all eval_to_exp_rel \\ gs [])
  \\ qx_gen_tac ‘k’
  \\ strip_tac
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ reverse strip_tac
  >- (
    strip_tac
    \\ ‘∃r. eval_to k x = r’ by fs []
    \\ drule_all eval_to_exp_rel \\ gs [])
  \\ qx_gen_tac ‘j’
  \\ strip_tac
  \\ ‘∃r. eval_to k x = r’ by fs []
  \\ drule_all_then assume_tac eval_to_exp_rel
  \\ Cases_on ‘j ≤ k’ \\ gvs []
  >- (
    drule_all envLangTheory.eval_to_mono
    \\ disch_then (assume_tac o SYM)
    \\ gs [])
  \\ ‘k ≤ j’ by fs []
  \\ drule_all thunkLangTheory.eval_to_mono
  \\ disch_then (assume_tac o SYM) \\ gs []
  \\ irule_at Any eval_to_exp_rel
  \\ irule_at Any EQ_REFL \\ fs []
QED

(*
Theorem compile_exp_freevars:
  ∀x. freevars (compile_exp x) = freevars x
Proof
  ho_match_mp_tac compile_exp_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ simp [compile_exp_def, envLangTheory.freevars_def,
           thunkLangTheory.freevars_def]
  \\ rpt strip_tac
  >- (
    simp [MAP_MAP_o, combinTheory.o_DEF]
    \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ irule LIST_EQ
    \\ gvs [MEM_EL, PULL_EXISTS, EL_MAP, EVERY_EL])
  >- (
    rename1 ‘Let opt _ _’
    \\ Cases_on ‘opt’ \\ gs [envLangTheory.freevars_def,
                             thunkLangTheory.freevars_def])
  >- (
    rw [MEM_MAP, MAP_MAP_o, combinTheory.o_DEF, EXTENSION, EVERY_MEM]
    \\ fs [EXISTS_PROD, FORALL_PROD]
    \\ metis_tac [])
QED
 *)

(*
Theorem compile_exp_closed:
  ∀x. closed (compile_exp x) = closed x
Proof
  rw [envLangTheory.closed_def, thunkLangTheory.closed_def,
      compile_exp_freevars]
QED
 *)

(*
 * No values, but also no MkTicks.
 *)
(*
Definition no_Value_def:
  no_Value (Value v) = F ∧
  no_Value (Var n) = T ∧
  no_Value (Prim op xs) = EVERY no_Value xs ∧
  no_Value (App x y) = (no_Value x ∧ no_Value y) ∧
  no_Value (Lam s x) = no_Value x ∧
  no_Value (Let s x y) = (no_Value x ∧ no_Value y) ∧
  no_Value (Letrec f x) =
    (EVERY (λ(f,x). no_Value x) f ∧
     no_Value x) ∧
  no_Value (If x y z) = (no_Value x ∧ no_Value y ∧ no_Value z) ∧
  no_Value (Delay x) = no_Value x ∧
  no_Value (Box x) = no_Value x ∧
  no_Value (Force x) = no_Value x ∧
  no_Value (MkTick x) = F (* no_Value x *)
Termination
  WF_REL_TAC ‘measure exp_size’ \\ simp []
  \\ rw [] \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw [] \\ fs [thunkLangTheory.exp_size_def]
End
*)

(*
Theorem exp_inv_rce:
  ∀x. exp_inv (rce x)
Proof
  ho_match_mp_tac rce_ind
  \\ rw [rce_def]
  \\ gs [EVERY_MEM, MEM_MAP, FORALL_PROD, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
QED

Theorem no_Value_exp_inv:
  ∀x. no_Value x ⇒ exp_inv x
Proof
  ho_match_mp_tac exp_ind
  \\ rw [] \\ gs [no_Value_def]
  \\ gs [EVERY_MEM, MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD, SF SFY_ss]
QED

Theorem compile_exp_rce:
  ∀x. no_Value x ⇒ rce (compile_exp x) = x
Proof
  ho_match_mp_tac compile_exp_ind
  \\ simp [rce_def, no_Value_def, compile_exp_def] \\ rw []
  \\ fs [MAP_MAP_o, combinTheory.o_DEF, EVERY_MEM]
  \\ irule MAP_ID_ON \\ fs []
  \\ fs [ELIM_UNCURRY, FORALL_PROD, SF SFY_ss]
QED

Theorem exp_rel_rce:
  ∀x. exp_rel [] (rce x) x
Proof
  ho_match_mp_tac rce_ind
  \\ simp [rce_def, exp_rel_def]
  \\ rw []
  \\ fs [EVERY2_MAP, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP] \\ rw []
  >- (
    rename1 ‘Let opt _ _’
    \\ Cases_on ‘opt’ \\ fs [exp_rel_def])
  \\ fs [ELIM_UNCURRY]
  \\ first_x_assum irule
  \\ first_assum (irule_at Any) \\ fs []
  \\ irule_at Any PAIR
QED

Theorem eval_to_rce:
  eval_to k (rce x) = res ⇒
  case res of
    INL err => eval_to k [] x = INL err
  | INR v => ∃w. eval_to k [] x = INR w ∧ v_rel v w ∧ v_inv v
Proof
  strip_tac
  \\ irule_at Any eval_to_exp_rel
  \\ irule_at Any exp_rel_rce \\ fs []
  \\ irule exp_inv_rce
QED

Theorem eval_rce:
  eval (rce x) = res ⇒
  case res of
    INL err => eval [] x = INL err
  | INR v => ∃w. eval [] x = INR w ∧ v_rel v w ∧ v_inv v
Proof
  strip_tac
  \\ irule_at Any eval_exp_rel
  \\ irule_at Any exp_rel_rce \\ fs []
  \\ irule exp_inv_rce
QED

Theorem compile_exp_eval_to:
  eval_to k x = res ∧
  no_Value x ⇒
    case res of
      INL err => eval_to k [] (compile_exp x) = INL err
    | INR v => ∃w. eval_to k [] (compile_exp x) = INR w ∧ v_rel v w ∧ v_inv v
Proof
  strip_tac
  \\ irule eval_to_rce
  \\ simp [compile_exp_rce]
QED

Theorem compile_exp_eval:
  eval x = res ∧
  no_Value x ⇒
    case res of
      INL err => eval [] (compile_exp x) = INL err
    | INR v => ∃w. eval [] (compile_exp x) = INR w ∧ v_rel v w ∧ v_inv v
Proof
  strip_tac
  \\ irule eval_rce
  \\ simp [compile_exp_rce]
QED
 *)

val _ = export_theory ();

