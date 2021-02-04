(*
  Proof of correctness for the thunk_to_thunk compiler pass.
 *)
open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pred_setTheory rich_listTheory thunkLang_primitivesTheory thunkLangTheory
     finite_mapTheory thunkLang_substTheory;
open thunk_to_thunkTheory;

val _ = new_theory "thunk_to_thunkProof";

val _ = numLib.prefer_num ();

Inductive exp_rel:
[exp_rel_Value:]
  (∀env n v v'.
     ALOOKUP env n = SOME v' ∧
     v_rel v v' ⇒
       exp_rel env (Value v) (Var n)) ∧
[exp_rel_Var:]
  (∀env n n'.
     ALOOKUP env n = NONE ∧
     n = n' ⇒
       exp_rel env (Var n) (Var n')) ∧
[exp_rel_App:]
  (∀env x x' y y'.
     exp_rel env x x' ∧
     exp_rel env y y' ⇒
       exp_rel env (App x y) (App x' y')) ∧
[exp_rel_Lam:]
  (∀env x x' s s'.
     exp_rel (FILTER (λ(n, x). n ≠ s) env) x x' ∧
     s = s' ⇒
       exp_rel env (Lam s x) (Lam s' x')) ∧
[exp_rel_If:]
  (∀env x x' y y' z z'.
     exp_rel env x x' ∧
     exp_rel env y y' ∧
     exp_rel env z z' ⇒
       exp_rel env (If x y z) (If x' y' z')) ∧
[exp_rel_Prim:]
  (∀env op op' xs xs'.
     LIST_REL (exp_rel env) xs xs' ∧
     op = op' ⇒
       exp_rel env (Prim op xs) (Prim op' xs')) ∧
[exp_rel_Letrec:]
  (∀env f f' x x'.
     LIST_REL (λ(fn,xn,b) (gn,yn,c).
       fn = gn ∧ xn = yn ∧
       exp_rel (FILTER (λ(n, x). ¬MEM n (MAP FST f) ∧ n ≠ xn) env) b c) f f' ∧
     exp_rel (FILTER (λ(n, x). ¬MEM n (MAP FST f)) env) x x' ⇒
       exp_rel env (Letrec f x) (Letrec f' x')) ∧
[exp_rel_Delay:]
  (∀env f x x'.
     exp_rel env x x' ⇒
       exp_rel env (Delay f x) (Delay f x')) ∧
[exp_rel_Force:]
  (∀env x x'.
     exp_rel env x x' ⇒
       exp_rel env (Force x) (Force x')) ∧
[v_rel_Constructor:]
  (∀s s' vs vs'.
     LIST_REL v_rel vs vs' ∧
     s = s' ⇒
       v_rel (Constructor s vs) (Constructor s' vs')) ∧
[v_rel_Closure:]
  (∀env s s' x x'.
     exp_rel env (Lam s x) (Lam s' x') ⇒
       v_rel (Closure s x) (Closure s' env x')) ∧
[v_rel_Recclosure:]
  (∀env f f' n n'.
     LIST_REL (λ(fn,xn,b) (gn,yn,c).
       fn = gn ∧ xn = yn ∧
       exp_rel (FILTER (λ(n, x). ¬MEM n (MAP FST f) ∧ n ≠ xn) env) b c) f f' ∧
       n = n' ⇒
        v_rel (Recclosure f n) (Recclosure f' env n')) ∧
[v_rel_Thunk:]
  (∀v w nf.
     v_rel v w ⇒
       v_rel (Thunk nf v) (Thunk nf w)) ∧
[v_rel_Atom:]
  (∀l l'.
     l = l' ⇒
       v_rel (Atom l) (Atom l'))
End

Theorem exp_rel_def:
  (∀n x.
     exp_rel env (Var n) x =
       (ALOOKUP env n = NONE ∧
        x = Var n)) ∧
  (∀op xs.
     exp_rel env (Prim op xs) z =
     ∃ys.
       z = Prim op ys ∧
       LIST_REL (exp_rel env) xs ys) ∧
  (∀x y.
     exp_rel env (App x y) z =
     ∃x1 y1.
       z = App x1 y1 ∧
       exp_rel env x x1 ∧
       exp_rel env y y1) ∧
  (∀s x.
     exp_rel env (Lam s x) y =
     ∃z.
       y = Lam s z ∧
       exp_rel (FILTER (λ(n, x). n ≠ s) env) x z) ∧
  (∀x y z.
     exp_rel env (If x y z) w =
     ∃a b c.
       w = If a b c ∧
       exp_rel env x a ∧
       exp_rel env y b ∧
       exp_rel env z c) ∧
  (∀f x.
     exp_rel env (Letrec f x) y =
     ∃g z.
       y = Letrec g z ∧
       LIST_REL (λ(fn,xn,b) (gn,yn,c).
         fn = gn ∧ xn = yn ∧
         exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f) ∧ n ≠ xn) env) b c) f g ∧
       exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) x z) ∧
  (∀x f.
     exp_rel env (Delay f x) y =
     ∃z.
       y = Delay f z ∧
       exp_rel env x z) ∧
  (∀x.
     exp_rel env (Force x) y =
     ∃z.
       y = Force z ∧
       exp_rel env x z) ∧
  (∀x.
     exp_rel env (Value v) y =
     ∃n w.
       y = Var n ∧
       ALOOKUP env n = SOME w ∧
       v_rel v w)
Proof
  rpt conj_tac
  \\ rpt gen_tac
  \\ rw [Once exp_rel_cases, AC CONJ_ASSOC CONJ_SYM]
QED

Theorem v_rel_def:
  (∀s vs.
     v_rel (Constructor s vs) v ⇔
     ∃ws.
       v = Constructor s ws ∧
       LIST_REL v_rel vs ws) ∧
  (∀s x.
     v_rel (Closure s x) v ⇔
     ∃env y.
       v = Closure s env y ∧
       exp_rel env (Lam s x) (Lam s y)) ∧
  (∀f x.
     v_rel (Recclosure f x) v ⇔
     ∃f' env.
       v = Recclosure f' env x ∧
       LIST_REL (λ(fn,xn,b) (gn,yn,c).
         fn = gn ∧ xn = yn ∧
         exp_rel (FILTER (λ(n, x).
           ¬MEM n (MAP FST f) ∧ n ≠ xn) env) b c) f f') ∧
  (∀nf v.
     v_rel (Thunk nf v) w ⇔
     ∃u. w = Thunk nf u ∧
             v_rel v u) ∧
  (∀x.
     v_rel (Atom x) v ⇔ v = Atom x)
Proof
  rpt conj_tac
  \\ rpt gen_tac
  \\ rw [Once exp_rel_cases, exp_rel_def]
  \\ simp [SimpLHS, Once SWAP_EXISTS_THM]
QED

(* TODO Move to thunkLang_primitives *)
Theorem map_MAP:
  map f (MAP g xs) = map (f o g) xs
Proof
  Induct_on ‘xs’ \\ simp [map_def]
QED

(* TODO Move to thunkLang_primitives *)
Theorem map_INL:
  map f xs = INL err ⇔
    ∃n. n < LENGTH xs ∧
        f (EL n xs) = INL err ∧
        ∀m. m < n ⇒ ∀e. f (EL m xs) ≠ INL e
Proof
  eq_tac
  >- (
    qid_spec_tac ‘err’
    \\ Induct_on ‘xs’
    \\ simp [map_def, sum_bind_def]
    \\ rw [CaseEq "sum"]
    >- (
      qexists_tac ‘0’
      \\ simp [])
    >- (
      first_x_assum (drule_then strip_assume_tac)
      \\ qexists_tac ‘SUC n’ \\ simp []
      \\ Cases \\ fs []))
  >- (
    simp [PULL_EXISTS]
    \\ qid_spec_tac ‘err’
    \\ Induct_on ‘xs’
    \\ simp [map_def, sum_bind_def]
    \\ gen_tac
    \\ gen_tac
    \\ Cases \\ simp []
    \\ rename1 ‘n < LENGTH xs’
    \\ rw [CaseEq "sum", DISJ_EQ_IMP]
    \\ first_x_assum (drule_then (drule_then strip_assume_tac))
    \\ simp [GSYM PULL_EXISTS]
    \\ conj_tac
    >- (
      first_assum (qspec_then ‘0’ mp_tac)
      \\ impl_tac >- simp []
      \\ strip_tac \\ fs []
      \\ Cases_on ‘f h’ \\ fs [])
    \\ first_x_assum irule
    \\ rw []
    \\ ‘SUC m < SUC n’ by fs []
    \\ first_x_assum drule \\ simp [])
QED

(* TODO Move to thunkLang_primitives *)
Theorem map_INR:
  map f xs = INR ys ⇒
    ∀n. n < LENGTH xs ⇒
        ∃y. f (EL n xs) = INR y
Proof
  qid_spec_tac ‘ys’
  \\ Induct_on ‘xs’
  \\ simp [map_def, sum_bind_def]
  \\ rpt gen_tac
  \\ simp [CaseEq "sum"]
  \\ strip_tac
  \\ Cases \\ fs []
QED

(* TODO Move to thunkLang_primitives *)
Theorem map_LENGTH:
  ∀xs ys.
    map f xs = INR ys ⇒ LENGTH ys = LENGTH xs
Proof
  Induct
  \\ simp [map_def, sum_bind_def]
  \\ gen_tac
  \\ Cases \\ simp []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ rw [] \\ fs []
QED

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
  \\ simp [thunkLangTheory.dest_Closure_def,
           thunkLang_substTheory.dest_Closure_def,
           v_rel_def, exp_rel_def]
  \\ metis_tac []
QED

Theorem dest_Thunk_v_rel:
  v_rel v w ⇒
    (∀err. dest_Thunk v = INL err ⇒ dest_Thunk w = INL err) ∧
    (∀nf x. dest_Thunk v = INR (nf, x) ⇒
       ∃y.
         dest_Thunk w = INR (nf, y) ∧
         v_rel x y)
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [thunkLangTheory.dest_Thunk_def,
           thunkLang_substTheory.dest_Thunk_def,
           v_rel_def]
  \\ metis_tac []
QED

Theorem dest_Recclosure_v_rel:
  v_rel v w ⇒
    (∀err. dest_Recclosure v = INL err ⇒ dest_Recclosure w = INL err) ∧
    (∀f n.
       dest_Recclosure v = INR (f, n) ⇒
         ∃f' env.
           dest_Recclosure w = INR (f', env, n) ∧
           LIST_REL (λ(fn,xn,b) (gn,yn,c).
             fn = gn ∧ xn = yn ∧
             exp_rel (FILTER (λ(n,x).
               ¬MEM n (MAP FST f) ∧ n ≠ xn) env) b c) f f')
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [thunkLangTheory.dest_Recclosure_def,
           thunkLang_substTheory.dest_Recclosure_def,
           v_rel_def, exp_rel_def]
  \\ metis_tac []
QED

Theorem get_lits_v_rel:
  ∀vs ws.
    LIST_REL v_rel vs ws ⇒
      get_lits vs = get_lits ws
Proof
  Induct
  \\ simp [thunkLangTheory.get_lits_def, thunkLang_substTheory.get_lits_def]
  \\ gen_tac
  \\ Cases \\ fs []
  \\ strip_tac
  \\ simp [thunkLangTheory.get_lits_def, thunkLang_substTheory.get_lits_def,
           sum_bind_def]
  \\ rename1 ‘v_rel v w’
  \\ Cases_on ‘v’ \\ fs [v_rel_def]
  \\ res_tac \\ fs []
QED

(* TODO Urk *)
Theorem map_LIST_REL_mono:
  ∀xs ys vs ws.
    map f xs = INR vs ∧
    map g ys = INR ws ∧
    LIST_REL R xs ys ∧
    LIST_REL (λx y. R x y ⇒ Q (OUTR (f x)) (OUTR (g y))) xs ys ⇒
      LIST_REL Q vs ws
Proof
  Induct \\ simp [map_def]
  \\ gen_tac
  \\ Cases \\ simp [map_def, sum_bind_def]
  \\ rw [CaseEq "sum"] \\ fs []
  \\ first_x_assum (irule_at Any) \\ fs []
  \\ first_x_assum (irule_at Any) \\ fs []
  \\ first_x_assum drule \\ fs []
QED

Definition env_rel_def:
  env_rel binds env ⇔
    MAP FST binds = MAP FST env ∧
    ∀k v.
      ALOOKUP binds k = SOME v ⇒
        ∃w. ALOOKUP env k = SOME w ∧
            v_rel v w
End

Theorem exp_rel_ALOOKUP_EQ:
  ∀env1 x y env2.
    exp_rel env1 x y ∧
    ALOOKUP env1 = ALOOKUP env2 ⇒
      exp_rel env2 x y
Proof
  qsuff_tac ‘
    (∀env1 x y.
       exp_rel env1 x y ⇒
       ∀env2.
         ALOOKUP env1 = ALOOKUP env2 ⇒
         exp_rel env2 x y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- (
    metis_tac [])
  \\ ho_match_mp_tac exp_rel_strongind
  \\ simp [exp_rel_def, ALOOKUP_FILTER, MEM_MAP, v_rel_def]
  \\ rw [] \\ fs []
  \\ fs [FUN_EQ_THM, ALOOKUP_FILTER, LIST_REL_EL_EQN]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ ‘n < LENGTH f’ by fs []
  \\ first_x_assum drule \\ rw []
  \\ first_x_assum irule \\ rw []
  \\ fs [ALOOKUP_FILTER]
  \\ rw []
  \\ metis_tac []
QED

Theorem MAP_FILTER_FST[local]:
  MAP FST (FILTER (λx. P (FST x)) xs) = FILTER (λx. P x) (MAP FST xs)
Proof
  Induct_on ‘xs’ \\ rw []
QED

Theorem exp_rel_subst:
  ∀env x y binds extra.
    exp_rel env x y ∧
    env_rel binds extra ∧
    (∀k. MEM k (MAP FST extra) ⇒ ¬MEM k (MAP FST env)) ⇒
      exp_rel (extra ++ env) (subst binds x) y
Proof
  qsuff_tac ‘
    (∀env x y.
       exp_rel env x y ⇒
         ∀binds extra.
           env_rel binds extra ∧
           (∀k. MEM k (MAP FST extra) ⇒ ¬MEM k (MAP FST env)) ⇒
             exp_rel (extra ++ env) (subst binds x) y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- (
    metis_tac [])
  \\ ho_match_mp_tac exp_rel_strongind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ simp [subst_def, exp_rel_def]
  >- (
    rw []
    \\ fs [ALOOKUP_APPEND, MEM_MAP, FORALL_PROD, EXISTS_PROD, PULL_EXISTS]
    \\ CASE_TAC \\ fs []
    \\ imp_res_tac ALOOKUP_MEM \\ fs []
    \\ res_tac)
  >- (
    rw []
    \\ fs [env_rel_def]
    \\ CASE_TAC \\ fs [exp_rel_def, ALOOKUP_APPEND, CaseEq "option",
                       ALOOKUP_NONE]
    >- (
      metis_tac [])
    \\ res_tac
    \\ gvs [exp_rel_def, ALOOKUP_APPEND]
    \\ first_x_assum (irule_at Any) \\ fs [])
  >- (
    rw []
    \\ simp [FILTER_APPEND_DISTRIB]
    \\ first_x_assum irule
    \\ conj_tac
    >- (
      fs [MEM_MAP, MEM_FILTER, FORALL_PROD, EXISTS_PROD, PULL_EXISTS]
      \\ metis_tac [])
    \\ fs [env_rel_def, ALOOKUP_FILTER, MAP_FILTER_FST, ELIM_UNCURRY])
  >- (
    rw []
    \\ fs [LIST_REL_EL_EQN, EL_MAP])
  >- (
    simp [FILTER_FILTER, MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY]
    \\ strip_tac
    \\ rpt gen_tac
    \\ strip_tac
    \\ fsrw_tac [boolSimps.ETA_ss] []
    \\ simp [FILTER_APPEND_DISTRIB]
    \\ first_x_assum (irule_at Any) \\ fs []
    \\ rpt conj_tac
    >- (
      fs [env_rel_def, LAMBDA_PROD, ALOOKUP_FILTER]
      \\ fs [MAP_FILTER_FST, ELIM_UNCURRY])
    >- (
      fs [MAP_FILTER_FST, MEM_FILTER])
    \\ fs [LIST_REL_EL_EQN, EL_MAP]
    \\ rw [] \\ gvs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ simp [FILTER_APPEND_DISTRIB] \\ gvs []
    \\ first_x_assum irule
    \\ simp [MAP_FILTER_FST, MEM_FILTER]
    \\ fs [env_rel_def, LAMBDA_PROD, ALOOKUP_FILTER]
    \\ fs [ELIM_UNCURRY, MAP_FILTER_FST]
    \\ AP_THM_TAC
    \\ AP_TERM_TAC
    \\ rw [FUN_EQ_THM, AC CONJ_COMM CONJ_ASSOC])
QED

Theorem exp_rel_Lam[local]:
  exp_rel (FILTER (λ(n,x). n ≠ s) env) b y ∧
  v_rel v w ⇒
    exp_rel ((s,w)::env) (subst1 s v b) y
Proof
  strip_tac
  \\ once_rewrite_tac [CONS_APPEND]
  \\ irule_at Any exp_rel_ALOOKUP_EQ
  \\ irule_at Any exp_rel_subst
  \\ first_assum (irule_at Any) \\ simp []
  \\ qexists_tac ‘[(s,w)]’
  \\ simp [MEM_FILTER, MEM_MAP, FORALL_PROD, FUN_EQ_THM, ALOOKUP_FILTER,
           env_rel_def]
QED

(*
Theorem ALOOKUP_lemma[local]:
  ∀funs fn funs1.
    MAP FST funs = MAP FST funs1 ∧
    MAP (FST o SND) funs = MAP (FST o SND) funs1 ⇒
      OPTION_MAP FST (ALOOKUP funs fn) =
      OPTION_MAP FST (ALOOKUP funs1 fn)
Proof
  ho_match_mp_tac ALOOKUP_ind
  \\ strip_tac
  >- (
    strip_tac
    \\ Cases
    \\ simp [])
  \\ gen_tac
  \\ PairCases
  \\ Cases
  >- (
    simp [EXISTS_PROD, PULL_EXISTS]
    \\ rw [])
  \\ PairCases_on ‘h’
  \\ simp []
  \\ strip_tac
  \\ strip_tac
  \\ Cases \\ simp []
  \\ PairCases_on ‘h’ \\ simp []
  \\ rw [] \\ fs []
QED
*)

(*
Theorem ALOOKUP_least_lemma[local]:
  ∀xs x v.
    ALOOKUP xs x = SOME v ⇒
      ∃n.
        n < LENGTH xs ∧
        EL n xs = (x, v) ∧
        ∀m. m < n ⇒ FST (EL m xs) ≠ x
Proof
  ho_match_mp_tac ALOOKUP_ind \\ rw []
  >- (
    qexists_tac ‘0’ \\ simp [])
  \\ first_x_assum (drule_then strip_assume_tac)
  \\ Q.REFINE_EXISTS_TAC ‘SUC k’ \\ simp []
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ Cases \\ simp []
QED
*)

(*
Theorem dest_anyClosure_v_rel:
  v_rel v w ⇒
    (∀err. dest_anyClosure v = INL err ⇒ dest_anyClosure w = INL err) ∧
    (∀s x.
       dest_anyClosure v = INR (s, x) ⇒
         ∃env y.
           dest_anyClosure w = INR (s, env, y) ∧
           exp_rel (FILTER (λ(n,x). n ≠ s) env) x y)
Proof
  strip_tac
  \\ ‘∃r1. dest_Closure v = r1’  by fs []
  \\ ‘∃r2. dest_Recclosure v = r2’  by fs []
  \\ drule_then strip_assume_tac dest_Closure_v_rel
  \\ drule_then strip_assume_tac dest_Recclosure_v_rel
  \\ simp [thunkLangTheory.dest_anyClosure_def,
            thunkLang_substTheory.dest_anyClosure_def,
            sum_choice_def, sum_bind_def]
  \\ Cases_on ‘r2’ \\ fs []
  >- (
    Cases_on ‘r1’ \\ gvs []
    \\ rw [] \\ fs [])
  \\ reverse (Cases_on ‘r1’) \\ fs []
  >- (
    Cases_on ‘v’
    \\ fs [dest_Closure_def, dest_Recclosure_def])
  \\ pairarg_tac \\ gvs []
  \\ simp [lookup_var_def]
  \\ rename1 ‘INR (funs1, _, _)’
  \\ ‘LIST_REL (λ(fn,xn,b) (gn,yn,c). fn = gn ∧ xn = yn) funs funs1’
    by (qmatch_goalsub_abbrev_tac ‘LIST_REL Q’
        \\ qmatch_asmsub_abbrev_tac ‘LIST_REL P’
        \\ ‘∀x y. P x y ⇒ Q x y’ by rw [ELIM_UNCURRY, Abbr ‘P’, Abbr ‘Q’]
        \\ drule_then irule EVERY2_mono \\ fs [])
  \\ ‘MAP FST funs = MAP FST funs1 ∧
      MAP (FST o SND) funs = MAP (FST o SND) funs1’
    by (pop_assum mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ qid_spec_tac ‘funs1’
        \\ Induct_on ‘funs’ \\ Cases_on ‘funs1’ \\ simp []
        \\ rw [] \\ fs [ELIM_UNCURRY])
  \\ ‘ALOOKUP funs fn = NONE ⇒ ALOOKUP funs1 fn = NONE’ by rw [ALOOKUP_NONE]
  \\ Cases_on ‘ALOOKUP funs fn’ \\ gs []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  >- (
    fs [ALOOKUP_NONE]
    \\ ‘¬MEM fn (MAP FST funs)’ by fs []
    \\ drule_then assume_tac ALOOKUP_MEM
    \\ gs [MEM_MAP, FORALL_PROD])
  \\ Cases_on ‘v’ \\ gvs [dest_Recclosure_def, v_rel_def]
  \\ gvs [thunkLangTheory.dest_Recclosure_def]
  \\ pairarg_tac \\ gvs []
  \\ drule_all_then (qspec_then ‘fn’ assume_tac) ALOOKUP_lemma
  \\ gvs [OPTION_MAP_DEF]
  \\ rename1 ‘exp_rel (FILTER (λ(n,x). n ≠ m) (bind_funs funs1 env)) bod1 bod’
  (* TODO Lemma *)
  \\ ‘exp_rel (FILTER (λ(n, x). ¬MEM n (MAP FST funs1) ∧ n ≠ m) env) bod1 bod’
    by (fs [LIST_REL_EL_EQN]
        \\ imp_res_tac ALOOKUP_least_lemma
        \\ rename1 ‘EL k funs’
        \\ ‘∀j. j < LENGTH funs ⇒ FST (EL j funs) = FST (EL j funs1)’
          by (qpat_x_assum ‘MAP FST _ = MAP _ _’ mp_tac
              \\ rpt (pop_assum kall_tac)
              \\ qid_spec_tac ‘funs1’
              \\ Induct_on ‘funs’ \\ Cases_on ‘funs1’ \\ simp []
              \\ rw []
              \\ first_x_assum (drule_then assume_tac)
              \\ Cases_on ‘j’ \\ fs [])
        \\ ‘k = n’
          by (CCONTR_TAC
              \\ Cases_on ‘k < n’ \\ fs []
              >- (
                first_x_assum (drule_then assume_tac)
                \\ first_x_assum (drule_then assume_tac)
                \\ gvs [])
              \\ ‘n < k’ by fs []
              \\ ‘n < LENGTH funs’ by fs []
              \\ first_x_assum (drule_then assume_tac)
              \\ first_x_assum (drule_then assume_tac)
              \\ gvs [])
        \\ gvs []
        \\ fs [LIST_REL_EL_EQN]
        \\ last_x_assum (qspec_then ‘k’ assume_tac)
        \\ pairarg_tac \\ gvs [])
  \\ irule exp_rel_ALOOKUP_EQ
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ simp [FUN_EQ_THM, ALOOKUP_FILTER]
  \\ rw [MEM_MAP, PULL_FORALL, DISJ_EQ_IMP, bind_funs_def]
  \\ simp [ALOOKUP_APPEND, ALOOKUP_MAP_2, LAMBDA_PROD]
  \\ CASE_TAC \\ gvs []
  >- (
    imp_res_tac ALOOKUP_MEM
    \\ gs [FORALL_PROD, DISJ_EQ_IMP, MEM_MAP])
  >- (
    PairCases_on ‘y’
    \\ fs [ALOOKUP_FAILS])
  \\ cheat (* TODO: Wat? *)
  (*
     It could be that I used the wrong environment for the exp_rel and that
     this lookup went past the env additions
   *)
QED
*)

Theorem do_prim_v_rel:
  LIST_REL v_rel vs ws ⇒
    case do_prim op vs of
      INL err => do_prim op ws = INL err
    | INR v => ∃w. do_prim op ws = INR w ∧ v_rel v w
Proof
  strip_tac
  \\ ‘LENGTH vs = LENGTH ws’ by fs [LIST_REL_EL_EQN]
  \\ Cases_on ‘op’
  >- ((* If *)
    simp [thunkLangTheory.do_prim_def, thunkLang_substTheory.do_prim_def])
  >- ((* Cons *)
    simp [thunkLangTheory.do_prim_def, thunkLang_substTheory.do_prim_def,
          v_rel_def])
  >- ((* IsEq *)
    simp [thunkLangTheory.do_prim_def, thunkLang_substTheory.do_prim_def,
          v_rel_def]
    \\ IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘v’ \\ gvs [v_rel_def]
    \\ rw [] \\ fs [v_rel_def, LIST_REL_EL_EQN])
  >- ((* Proj *)
    simp [thunkLangTheory.do_prim_def, thunkLang_substTheory.do_prim_def,
          v_rel_def]
    \\ IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘v’ \\ gvs [v_rel_def]
    \\ rw [] \\ fs [LIST_REL_EL_EQN])
  >- ((* AtomOp *)
    simp [thunkLangTheory.do_prim_def, thunkLang_substTheory.do_prim_def,
          v_rel_def, sum_bind_def]
    \\ drule_then assume_tac get_lits_v_rel
    \\ Cases_on ‘get_lits ws’ \\ simp []
    \\ Cases_on ‘config.parAtomOp a y’ \\ simp [v_rel_def])
  >- ((* Lit *)
    simp [thunkLangTheory.do_prim_def, thunkLang_substTheory.do_prim_def]
    \\ CASE_TAC \\ fs [v_rel_def, LIST_REL_EL_EQN]
    \\ strip_tac \\ fs [])
QED

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
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def,
             lookup_var_def])
  >- ((* Var *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def,
             lookup_var_def])
  >- ((* Prim *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ simp [sum_bind_def, CaseEq "sum"]
    \\ CASE_TAC \\ fs []
    >- ((* map eval xs = INL err *)
      disj1_tac
      \\ gvs [map_MAP, map_INL, LIST_REL_EL_EQN]
      \\ first_assum (irule_at Any) \\ rw []
      >- (
        first_assum (drule_then assume_tac)
        \\ last_x_assum drule
        \\ simp [])
      \\ first_x_assum (drule_then mp_tac)
      \\ ‘m < LENGTH ys’ by fs []
      \\ first_x_assum (drule_then assume_tac) \\ rw []
      \\ first_x_assum drule
      \\ CASE_TAC \\ rw [] \\ fs [])
    \\ ‘∃z. map (λx. eval_to (k - 1) env x) ys = INR z’
      by (drule map_INR \\ rw []
          \\ Cases_on ‘map (λx. eval_to (k - 1) env x) ys’ \\ fs []
          \\ gvs [map_INL, LIST_REL_EL_EQN]
          \\ last_x_assum drule \\ strip_tac
          \\ last_x_assum drule \\ strip_tac \\ gs []
          \\ Cases_on ‘eval_to (k - 1) (EL n xs)’ \\ gvs []
          \\ first_x_assum drule \\ fs [])
    \\ qabbrev_tac ‘f = λx. eval_to (k - 1) x’
    \\ qabbrev_tac ‘g = λx. eval_to (k - 1) env x’
    \\ ‘LIST_REL (λx y.
          exp_rel env x y ⇒ v_rel (OUTR (f x)) (OUTR (g y))) xs ys’
      by (fs [LIST_REL_EL_EQN]
          \\ rw [] \\ gvs []
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum drule
          \\ CASE_TAC \\ fs []
          >- (
            drule_all_then strip_assume_tac map_INR
            \\ fs [])
          \\ rw [] \\ fs [])
    \\ drule_all_then assume_tac map_LIST_REL_mono
    \\ drule_then (qspec_then ‘op’ assume_tac) do_prim_v_rel
    \\ CASE_TAC \\ fs [])
  >- ((* App *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum (drule_then assume_tac)
    \\ first_x_assum (drule_then assume_tac)
    \\ simp [map_def, sum_bind_def]
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x'’ \\ fs []
    \\ ‘∃r1. dest_Closure y = r1’ by fs []
    \\ drule_then strip_assume_tac dest_Closure_v_rel
    \\ ‘∃r2. dest_Recclosure y = r2’ by fs []
    \\ drule_then strip_assume_tac dest_Recclosure_v_rel
    \\ simp [thunkLangTheory.dest_anyClosure_def,
             thunkLang_substTheory.dest_anyClosure_def,
             sum_choice_def, sum_bind_def]
    \\ Cases_on ‘r2’ \\ fs []
    >- (
      Cases_on ‘r1’ \\ gvs []
      \\ pairarg_tac \\ gvs [bind_def]
      \\ first_x_assum irule
      \\ irule exp_rel_Lam \\ fs [])
    \\ reverse (Cases_on ‘r1’) \\ fs []
    >- (
      Cases_on ‘y’
      \\ fs [dest_Closure_def, dest_Recclosure_def])
    \\ pairarg_tac \\ gvs [lookup_var_def]
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘MAP FST xs = MAP FST ys’
      by (‘LIST_REL (λ(fn, xn, b) (gn, yn, c). fn = gn) xs ys’
            by (fs [LIST_REL_EL_EQN] \\ rw []
                \\ rpt (pairarg_tac \\ gvs [])
                \\ first_x_assum drule
                \\ rpt (pairarg_tac \\ gvs []))
          \\ pop_assum mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘ys’
          \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ simp []
          \\ rw []
          \\ rpt (pairarg_tac \\ gvs []))
    \\ rename1 ‘INR (ys, env2, _)’
    \\ drule_all_then (qspec_then ‘fn’ strip_assume_tac) ALOOKUP_LIST_REL
    \\ Cases_on ‘ALOOKUP xs fn’ \\ gs []
    \\ CASE_TAC \\ fs []
    \\ simp [bind_def, subst_funs_def]
    \\ Cases_on ‘y’ \\ gvs [dest_Recclosure_def, v_rel_def]
    \\ pairarg_tac \\ gvs []
    \\ first_x_assum irule
    \\ irule exp_rel_ALOOKUP_EQ
    \\ irule_at Any exp_rel_subst
    \\ first_assum (irule_at Any) \\ simp []
    \\ rename1 ‘v_rel v1 v2’
    \\ qexists_tac ‘(q,v2)::MAP (λ(f, x). (f, Recclosure ys env2 f)) ys’
    \\ rpt conj_tac \\ simp []
    >- (
      simp [env_rel_def, MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY]
      \\ fsrw_tac [boolSimps.ETA_ss] []
      \\ simp [Once LAMBDA_PROD, ALOOKUP_MAP_2]
      \\ qx_gen_tac ‘xx’ \\ rw [] \\ fs []
      \\ simp [Once LAMBDA_PROD, ALOOKUP_MAP_2, PULL_EXISTS, v_rel_def]
      \\ drule_all_then (qspec_then ‘xx’ strip_assume_tac) ALOOKUP_LIST_REL
      \\ gs [])
    >- (
      simp [MEM_MAP, ELIM_UNCURRY, MEM_FILTER, PULL_EXISTS, PULL_FORALL]
      \\ metis_tac [])
    \\ simp [FUN_EQ_THM, bind_funs_def, ALOOKUP_APPEND]
    \\ qx_gen_tac ‘xx’ \\ rw [] \\ fs []
    \\ simp [ALOOKUP_MAP_2, ALOOKUP_FILTER, GSYM ALOOKUP_NONE]
    \\ CASE_TAC \\ fs []
    \\ CASE_TAC \\ fs [])
  >- ((* Lam *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def,
             v_rel_def, exp_rel_def])
  >- ((* If *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ simp [sum_bind_def]
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
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ simp [sum_bind_def, subst_funs_def, bind_def, flookup_fupdate_list,
             bind_funs_def]
    \\ first_x_assum irule
    \\ irule exp_rel_ALOOKUP_EQ
    \\ irule_at Any exp_rel_subst
    \\ first_assum (irule_at Any) \\ simp []
    \\ qmatch_goalsub_abbrev_tac ‘MAP Q g’
    \\ qexists_tac ‘MAP Q g’ \\ simp [Abbr ‘Q’]
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘MAP FST xs = MAP FST ys’
      by (‘LIST_REL (λ(fn, xn, b) (gn, yn, c). fn = gn) xs ys’
            by (fs [LIST_REL_EL_EQN] \\ rw []
                \\ rpt (pairarg_tac \\ gvs [])
                \\ first_x_assum drule
                \\ rpt (pairarg_tac \\ gvs []))
          \\ pop_assum mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘ys’
          \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ simp []
          \\ rw []
          \\ rpt (pairarg_tac \\ gvs []))
    \\ rpt conj_tac
    >- (
      simp [env_rel_def, MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY]
      \\ fsrw_tac [boolSimps.ETA_ss] []
      \\ simp [Once LAMBDA_PROD, ALOOKUP_MAP_2]
      \\ qx_gen_tac ‘xx’ \\ rw []
      \\ simp [Once LAMBDA_PROD, ALOOKUP_MAP_2, PULL_EXISTS, v_rel_def]
      \\ drule_all_then (qspec_then ‘xx’ strip_assume_tac) ALOOKUP_LIST_REL
      \\ first_x_assum (drule_then strip_assume_tac) \\ fs [])
    >- (
      fsrw_tac [boolSimps.ETA_ss] [MAP_FILTER_FST, ELIM_UNCURRY, MEM_FILTER,
                                   MAP_MAP_o, combinTheory.o_DEF])
    \\ rw [FUN_EQ_THM, ALOOKUP_APPEND, ALOOKUP_MAP_2, ALOOKUP_FILTER]
    \\ CASE_TAC \\ fs []
    \\ CASE_TAC \\ fs []
    \\ fs [ALOOKUP_NONE])
  >- ((* Delay *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ simp [sum_bind_def]
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ simp [v_rel_def])
  >- ((* Force *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ simp [sum_bind_def]
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
    \\ ‘∃r. dest_Thunk y = r’ by fs []
    \\ drule_then strip_assume_tac dest_Thunk_v_rel
    \\ Cases_on ‘dest_Thunk y’ \\ gvs []
    \\ first_assum (drule_then strip_assume_tac) \\ gvs []
    \\ pairarg_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ qpat_x_assum ‘INR _ = _’ (assume_tac o SYM)
    \\ rename1 ‘dest_Closure w1’
    \\ ‘∃r. dest_Closure w1 = r’ by fs []
    \\ drule_then strip_assume_tac dest_Closure_v_rel
    \\ CASE_TAC \\ gvs [bind_def]
    \\ pairarg_tac \\ gvs []
    \\ first_x_assum irule
    \\ irule exp_rel_Lam \\ fs []
    \\ simp [thunkLangTheory.unit_def, thunkLang_substTheory.unit_def,
             v_rel_def])
QED

Theorem compile_exp_freevars:
  ∀x. freevars (compile_exp x) = freevars x
Proof
  ho_match_mp_tac compile_exp_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ simp [compile_exp_def,
           thunkLangTheory.freevars_def,
           thunkLang_substTheory.freevars_def]
  \\ strip_tac
  >- (
    rw [EVERY_MEM, MEM_MAP, EXTENSION]
    \\ metis_tac [])
  >- (
    rw [EVERY_MEM, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF, EXTENSION]
    \\ fs [EXISTS_PROD, FORALL_PROD])
QED

Theorem compile_exp_closed:
  ∀x. closed (compile_exp x) ⇔ closed x
Proof
  rw [thunkLangTheory.closed_def, thunkLang_substTheory.closed_def,
      compile_exp_freevars]
QED

val _ = export_theory ();

