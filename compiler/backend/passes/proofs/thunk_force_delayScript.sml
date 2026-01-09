(*
  Simplify occurrences of `Force (Delay e)` to `e`

  This proof is retired and not maintained because it's not used as a part of
  the compiler definition.
*)

Theory thunk_force_delay
Ancestors
  string option sum pair list alist finite_map pred_set rich_list
  thunkLang thunkLang_primitives wellorder arithmetic pure_misc
  thunkLangProps thunk_semantics thunk_remove_unuseful_bindings
  combin bool
Libs
  term_tactic monadsyntax dep_rewrite

Inductive force_delay_rel:
[~Var:]
  (∀n. force_delay_rel (Var n) (Var n))
[~Prim:]
  (∀op xs ys.
     LIST_REL force_delay_rel xs ys ⇒
       force_delay_rel (Prim op xs) (Prim op ys))
[~Monad:]
  (∀mop xs ys.
     LIST_REL force_delay_rel xs ys ⇒
       force_delay_rel (Monad mop xs) (Monad mop ys))
[~App:]
  (∀f g x y.
     force_delay_rel f g ∧
     force_delay_rel x y ⇒
       force_delay_rel (App f x) (App g y))
[~Lam:]
  (∀s x y.
     force_delay_rel x y ⇒
       force_delay_rel (Lam s x) (Lam s y))
[~Letrec:]
  (∀f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL force_delay_rel (MAP SND f) (MAP SND g) ∧
     force_delay_rel x y ⇒
     force_delay_rel (Letrec f x) (Letrec g y))
[~Let:]
  (∀opt x1 y1 x2 y2.
     force_delay_rel x1 x2 ∧
     force_delay_rel y1 y2 ⇒
     force_delay_rel (Let opt x1 y1) (Let opt x2 y2))
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     force_delay_rel x1 x2 ∧
     force_delay_rel y1 y2 ∧
     force_delay_rel z1 z2 ⇒
       force_delay_rel (If x1 y1 z1) (If x2 y2 z2))
[~Delay:]
  (∀x y.
     force_delay_rel x y ⇒
       force_delay_rel (Delay x) (Delay y))
[~Force:]
  (∀x y.
     force_delay_rel x y ⇒
     force_delay_rel (Force x) (Force y))
[~simp:]
   (∀x y.
     force_delay_rel x y ⇒
     force_delay_rel (Force (Delay x)) y)
[~MkTick:]
  (∀x y. force_delay_rel x y ⇒ force_delay_rel (MkTick x) (MkTick y))
End

Theorem force_delay_rel_def =
  [“force_delay_rel (Var v) x”,
   “force_delay_rel (Value v) x”,
   “force_delay_rel (Prim op xs) x”,
   “force_delay_rel (Monad mop xs) x”,
   “force_delay_rel (App f x) y”,
   “force_delay_rel (Lam s x) y”,
   “force_delay_rel (Letrec f x) y”,
   “force_delay_rel (Let s x y) z”,
   “force_delay_rel (If x y z) w”,
   “force_delay_rel (Delay x) y”,
   “force_delay_rel (MkTick x) y”,
   “force_delay_rel (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once force_delay_rel_cases])
  |> LIST_CONJ;


Inductive exp_rel:
[~Var:]
  (∀n. exp_rel (Var n) (Var n))
[~Value:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Value v) (Value w))
[~Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys))
[~Monad:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad mop xs) (Monad mop ys))
[~App:]
  (∀f g x y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f x) (App g y))
[~Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y))
[~Letrec:]
  (∀f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
     exp_rel x y ⇒
     exp_rel (Letrec f x) (Letrec g y))
[~Let:]
  (∀opt x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
     exp_rel (Let opt x1 y1) (Let opt x2 y2))
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ∧
     exp_rel z1 z2 ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2))
[~Delay:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Delay x) (Delay y))
[~Force:]
  (∀x y.
     exp_rel x y ⇒
     exp_rel (Force x) (Force y))
[~simp:]
   (∀x y.
     exp_rel x y ⇒
     exp_rel (Force (Delay x)) (Tick y))
[~MkTick:]
  (∀x y. exp_rel x y ⇒ exp_rel (MkTick x) (MkTick y))
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws))
[v_rel_Monadic:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ⇒
       v_rel (Monadic mop xs) (Monadic mop ys))
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ⇒
       v_rel (Closure s x) (Closure s y))
[v_rel_Recclosure:]
  (∀f g n.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ⇒
     v_rel (Recclosure f n) (Recclosure g n))
[v_rel_Thunk:]
  (∀x y.
     exp_rel x y ⇒
     v_rel (Thunk x) (Thunk y))
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x))
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
     v_rel (DoTick v) (DoTick w))
End

Theorem exp_rel_def =
  [“exp_rel (Var v) x”,
   “exp_rel (Value v) x”,
   “exp_rel (Prim op xs) x”,
   “exp_rel (Monad mop xs) x”,
   “exp_rel (App f x) y”,
   “exp_rel (Lam s x) y”,
   “exp_rel (Letrec f x) y”,
   “exp_rel (Let s x y) z”,
   “exp_rel (If x y z) w”,
   “exp_rel (Delay x) y”,
   “exp_rel (MkTick x) y”,
   “exp_rel (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once exp_rel_cases])
  |> LIST_CONJ;

Theorem v_rel_def =
  [“v_rel (Constructor s vs) v”,
   “v_rel (Monadic mop xs) v”,
   “v_rel (Closure s x) v”,
   “v_rel (Recclosure f n) v”,
   “v_rel (Atom x) v”,
   “v_rel (Thunk x) v”,
   “v_rel (DoTick x) v”]
  |> map (SIMP_CONV (srw_ss()) [Once exp_rel_cases])
  |> LIST_CONJ

Theorem ok_bind_subst[simp]: (* TODO : move *)
  ∀x. ok_bind x ⇒ ok_bind (subst ws x)
Proof
  Cases \\ rw [ok_bind_def] \\ gs [subst_def, ok_bind_def]
QED

Theorem exp_rel_freevars:
    ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
  Induct_on ‘x’ using freevars_ind >>
  rw[Once exp_rel_cases] >>
  gvs[freevars_def]
  >>~ [‘BIGUNION’]
  >- (
    cong_tac (SOME 2) >>
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
    )
  >- (
    cong_tac (SOME 2) >>
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
    )
  >- (
    first_x_assum drule >> rw[] >>
    cong_tac (SOME 4) >>
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS] >>
    rw[] >> rpt (pairarg_tac >> gvs[]) >>
    gvs[EL_MAP] >> rpt $ last_x_assum drule >> rw[]
    )
  >~ [‘exp_rel (Delay _)’]
  >- gvs[Once exp_rel_cases, PULL_EXISTS, freevars_def]
  >> metis_tac[]
QED

Theorem exp_rel_subst:
  ∀vs x ws y.
    MAP FST vs = MAP FST ws ∧
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    exp_rel x y ⇒
      exp_rel (subst vs x) (subst ws y)
Proof
   ‘(∀x y.
     exp_rel x y ⇒
     ∀vs ws.
       MAP FST vs = MAP FST ws ∧
       LIST_REL v_rel (MAP SND vs) (MAP SND ws) ⇒
         exp_rel (subst vs x) (subst ws y)) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
  >~ [‘Var v’] >- (
    rw [subst_def]
    \\ rename1 ‘LIST_REL v_rel (MAP SND vs) (MAP SND ws)’
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_OPTREL
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
    \\ gs [OPTREL_def, exp_rel_Var, exp_rel_Value])
  >~ [‘Value v’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Value])
  >~ [‘Prim op xs’] >- (
    rw [subst_def]
    \\ irule exp_rel_Prim
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [‘Monad mop xs’] >- (
    rw [subst_def]
    \\ irule exp_rel_Monad
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [‘App f x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_App])
  >~ [‘Lam s x’] >- (
    rw [subst_def]
    \\ irule exp_rel_Lam
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘Letrec f x’] >- (
    rw [subst_def]
    \\ irule exp_rel_Letrec
    \\ gvs [EVERY_MAP, EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
            GSYM FST_THM]
    \\ first_x_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER]
    \\ rename1 ‘MAP FST f = MAP FST g’
    \\ qabbrev_tac ‘P = λn. ¬MEM n (MAP FST g)’ \\ gs []
    \\ irule_at Any LIST_REL_FILTER
    \\ ‘∀f x. ok_bind x ⇒ ok_bind (subst f x)’
      by (ho_match_mp_tac subst_ind
          \\ rw [subst_def])
    \\ gvs [EVERY_EL, ELIM_UNCURRY]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ first_assum irule
    \\ gvs [MAP_FST_FILTER, LAMBDA_PROD]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘Let s x y’] >- (
    Cases_on ‘s’ \\ rw [subst_def]
    \\ irule exp_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER]
    \\ rename1 ‘_ ≠ s’
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ gs [EVERY2_MAP]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘If x y z’] >- (
    rw [subst_def]
    \\ gs [exp_rel_If])
   >~[‘Force (Delay _)’] >- (
    rw [subst_def]
    \\ ‘FILTER (λ(n,v). T) ws = ws’ suffices_by gs [exp_rel_simp]
    \\ rpt $ pop_assum kall_tac
    \\ Induct_on ‘ws’ \\ simp [FORALL_PROD])
  >~ [‘Delay x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Delay])
  >~ [‘Force x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Force])
  >~[‘MkTick x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_MkTick])
QED

Theorem bind_not_error:
  monad_bind f g ≠ INL Type_error
  ⇒
  f ≠ INL Type_error
Proof
  CCONTR_TAC>>gs[]
QED

Theorem v_rel_anyThunk:
  (∀x y. exp_rel x y ⇒ T) ∧
  (∀v w. v_rel v w ⇒ (is_anyThunk v ⇔ is_anyThunk w))
Proof
  ho_match_mp_tac exp_rel_strongind
  \\ rw[] \\ gvs [SF ETA_ss]
  \\ rw [is_anyThunk_def, dest_anyThunk_def]
  \\ simp[AllCaseEqs(),PULL_EXISTS]
  \\
  `OPTREL exp_rel
    (ALOOKUP (REVERSE f) n)
    (ALOOKUP (REVERSE g) n)` by (
    irule LIST_REL_OPTREL >>
    fs[LIST_REL_MAP,MAP_EQ_EVERY2]>>
    gvs[LIST_REL_EL_EQN]>>rw[]>>
    rpt (pairarg_tac>>gvs[])>>
    metis_tac[FST,SND])>>
  eq_tac>>rw[]>>
  gvs[OPTREL_SOME,Once exp_rel_cases]
QED

Theorem LIST_REL_EVERY_EVERY:
  LIST_REL R xs ys ∧
  EVERY P xs ∧
  (∀x y. R x y ∧ P x ⇒ Q y) ⇒
  EVERY Q ys
Proof
  rw[EVERY_EL,LIST_REL_EL_EQN]>>
  metis_tac[]
QED

Theorem exp_rel_eval_to[local]:
  ∀x y.
    exp_rel x y ∧
    eval_to k x ≠ INL Type_error ⇒
      ($= +++ v_rel) (eval_to k x) (eval_to k y)
Proof
  completeInduct_on ‘k’
  \\ Induct using freevars_ind \\ rpt gen_tac

  >~ [‘Var n’] >- (
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])

  >~ [‘Prim op xs’] >-(
    rpt strip_tac
    \\ gs [Once exp_rel_def, eval_to_def, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
    \\ Cases_on ‘op’ \\ gs []
    >- ( (* op = Cons *)
      drule_then assume_tac bind_not_error>>
      qsuff_tac ‘
        ($= +++ LIST_REL v_rel)
          (result_map (eval_to k) xs)
          (result_map (eval_to k) ys)’
      >- (
        strip_tac \\ gs [SF ETA_ss]
        \\ Cases_on ‘result_map (eval_to k) ys’
        \\ Cases_on ‘result_map (eval_to k) xs’
        \\ gs[o_DEF,SF ETA_ss]
        \\ IF_CASES_TAC
        >- gs[v_rel_def]
        \\ `F` by (
          pop_assum mp_tac
          \\ fs[]
          \\ drule_at_then Any irule LIST_REL_EVERY_EVERY
          \\ first_x_assum (irule_at Any)
          \\ metis_tac[v_rel_anyThunk]))
      \\ gs [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss, bind_not_error]
      \\ IF_CASES_TAC \\ gs [bind_not_error] \\ IF_CASES_TAC
      >- ( (* LHS = INL Diverge *)
          first_x_assum mp_tac \\ strip_tac
          \\ `($= +++ v_rel) (eval_to k (EL n xs)) (eval_to k (EL n ys))` by fs[]
          \\ Cases_on ‘eval_to k (EL n ys)’
          >- ( (*eval_to k (EL n ys) = INL x*)
            Cases_on `x`
            >- ( (* x = Type_error *)
                CCONTR_TAC
                \\ qpat_x_assum `($= +++ v_rel) (eval_to k (EL n xs)) (INL _)` mp_tac
                \\ fs[])
            >- ( (* x = Diverge *)
                IF_CASES_TAC
                >- (
                  fs[]
                  \\ res_tac
                  \\ qpat_x_assum `eval_to k (EL n' xs) ≠ INL Type_error ⇒
                      ($= +++ v_rel) (eval_to k (EL n' xs)) (eval_to k (EL n' ys))` mp_tac
                  \\ `eval_to k (EL n' xs) ≠ INL Type_error` by (
                      qpat_x_assum `!n. _ ⇒ ¬(n < LENGTH ys)` (fn thm => qspec_then `n'` assume_tac thm)
                      \\ `n' < LENGTH ys ⇒ ¬(eval_to k (EL n' xs) = INL Type_error)`
                          by simp[Once $ MONO_NOT_EQ]
                      \\ fs[])
                  \\ strip_tac    
                  \\ `($= +++ v_rel) (eval_to k (EL n' xs)) (eval_to k (EL n' ys))` by fs[]
                  \\ qpat_x_assum `($= +++ v_rel) (eval_to k (EL n' xs)) (eval_to k (EL n' ys))` mp_tac
                  \\ qpat_x_assum `eval_to k (EL n' ys) = _` (fn thm => pure_rewrite_tac [thm])
                  \\ Cases_on `eval_to k (EL n' xs)` \\ fs[])
                >- (
                  IF_CASES_TAC \\ simp[]
                  \\ qpat_x_assum `n < LENGTH ys` mp_tac \\ fs[])))
          >- ((*eval_to k (EL n ys) = INR x*)
              IF_CASES_TAC \\ gs[]))
      >-((*LHS = INR _ *)
        IF_CASES_TAC \\ gs[o_DEF]
        >-(
          Cases_on `eval_to k (EL n xs)`
          >- (
            Cases_on `x`
            >- (
              qpat_x_assum `∀n. eval_to k (EL n xs) = INL Type_error ⇒ ¬(n < LENGTH ys)` mp_tac \\ fs[]
              \\ qexists `n` \\ fs[])
            >- (
              qpat_x_assum `∀n. eval_to k (EL n xs) = INL Diverge ⇒ ¬(n < LENGTH ys)` mp_tac \\ fs[]
              \\ qexists `n` \\ fs[]))
          >- (
            `eval_to k (EL n xs) ≠ INL Type_error` by fs[]
            \\ res_tac \\ metis_tac[SUM_REL_THM])
        )
      >-(
          IF_CASES_TAC \\ gs[]
          >-(
            `exp_rel (EL n xs) (EL n ys)` by res_tac
            \\ rpt $ first_x_assum $ qspec_then `n` assume_tac
            \\ gvs[]
            \\ res_tac
            \\ qpat_x_assum `eval_to k (EL n ys) = INL Diverge` assume_tac
            \\ fs[]
            \\ Cases_on `eval_to k (EL n xs)` \\ fs[]
          )
          >-(
            simp[MAP_MAP_o]
            \\ simp[LIST_REL_MAP]
            \\ simp[LIST_REL_EL_EQN]
            \\ rw[]
            \\ rpt $ first_x_assum $ qspec_then `n` assume_tac
            \\ gvs[]
            \\ res_tac
            \\ Cases_on `eval_to k (EL n xs)` \\ fs[]
            >-(Cases_on `x` \\ fs[])
            \\ Cases_on `eval_to k (EL n ys)` \\ fs[])
          )
        ))
    >-( (* IsEq *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs []
      \\ rw [v_rel_def])
    >-( (* Proj *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs [])
    >-( (* AtomOp *)
      Cases_on ‘k = 0’ \\ gs []
      >- ( (*k = 0*)
        rw [result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS]
        \\ Cases_on ‘ys = []’ \\ gs []
        >- (
          CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
        \\ ‘xs ≠ []’ by (strip_tac \\ gs [])
        \\ first_x_assum (qspec_then ‘0’ assume_tac) \\ gs [])
      (* k ≠ 0 *)
      \\ qmatch_goalsub_abbrev_tac ‘result_map f ys’
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
      \\ last_x_assum kall_tac \\ gvs [bind_not_error]
      \\ ‘result_map f xs = result_map f ys’
        suffices_by (
          strip_tac \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map f ys’ \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
      \\ unabbrev_all_tac
      \\ simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ Cases_on ‘k’ \\ gs [arithmeticTheory.ADD1]
      \\ rename1 ‘eval_to k’
      \\ ‘∀n. n < LENGTH ys ⇒
          ($= +++ v_rel) (eval_to k (EL n xs)) (eval_to k (EL n ys))’ by (
            rpt strip_tac
            \\ res_tac
            \\ first_x_assum irule \\ fs[]
            \\ drule bind_not_error
            \\ fs[result_map_def, AllCaseEqs(), MEM_MAP] 
            \\ fs[MEM_EL]
            \\ metis_tac[]
        ) 
      \\ IF_CASES_TAC \\ gs []
      >- (
        rename1 ‘m < LENGTH ys’
        \\ first_x_assum $ drule_all_then assume_tac
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ rw [] \\ gs []
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to k (EL m ys)’
        \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      \\ ‘∀n. n < LENGTH ys ⇒ eval_to k (EL n ys) = INL Diverge ∨
                              ∃x. eval_to k (EL n ys) = INR (Atom x)’
        by (rw [DISJ_EQ_IMP]
            \\ first_x_assum drule
            \\ first_x_assum $ qspec_then ‘n’ assume_tac
            \\ rw [CaseEqs ["sum", "v"]]
            \\ Cases_on ‘eval_to k (EL n xs)’
            \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
            >~ [‘INL err’] >- (
              Cases_on ‘err’ \\ gs [])
            \\ rename1 ‘v_rel x _’
            \\ Cases_on ‘x’ \\ gs [v_rel_def])
      \\ qpat_x_assum ‘∀n. _ ⇒ ¬( _ < _)’ kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        >- (
          first_x_assum $ drule_then assume_tac \\ gs [])
        \\ rename1 ‘n < LENGTH ys’
        \\ first_assum $ irule_at Any
        \\ last_x_assum $ drule_then assume_tac
        \\ last_x_assum $ drule_then assume_tac
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs []
        >- (
          Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
        \\ rename1 ‘INR y’ \\ Cases_on ‘y’ \\ gs [])
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum $ drule_then assume_tac \\ gs [])
      \\ strip_tac
      >- (gen_tac \\ strip_tac \\ strip_tac
          \\ rpt $ last_x_assum $ drule_then assume_tac \\ gs []
          \\ rename1 ‘n < _’
          \\ last_x_assum $ qspec_then ‘n’ mp_tac \\ simp []
          \\ CASE_TAC \\ gs [])
      \\ AP_TERM_TAC \\ irule LIST_EQ \\ gs [EL_MAP]
      \\ gen_tac \\ strip_tac \\ rename1 ‘n < _’
      \\ rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gs []
      \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs []
      \\ CASE_TAC \\ gs [v_rel_def]
      \\ Cases_on `y` \\ gs[v_rel_def]))

    >~ [‘Monad mop xs’] >- (
      rw [Once exp_rel_cases] \\ gs []
      \\ simp [eval_to_def, v_rel_def])

    >~ [‘If x x' x''’] >- (
      rename1 `(If x1 y1 z1)`
      \\ rw [exp_rel_def, eval_to_def] \\ gs [eval_to_def]
      \\ rename1 ‘exp_rel x1 x2’
      \\ rename1 ‘exp_rel y1 y2’ \\ rename1 ‘exp_rel z1 z2’
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ rpt $ first_assum $ dxrule_then assume_tac
      \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
      \\ Cases_on ‘eval_to (k - 1) x2’
      \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
      \\ rename1 ‘v_rel v1 w1’
      \\ IF_CASES_TAC \\ gvs [v_rel_def]
      \\ IF_CASES_TAC \\ gvs [v_rel_def]
      \\ IF_CASES_TAC \\ gs [])

    >~ [‘App x x'’] >- (
      rename [`App g y`]
      \\ gvs [Once exp_rel_def, eval_to_def, PULL_EXISTS] \\ rw []
      \\ rename1 ‘exp_rel y x’ \\ rename1 ‘exp_rel g f’
      \\ first_x_assum $ drule_then assume_tac \\ gs []
      \\ Cases_on ‘eval_to k x’ \\ gs []
      \\ Cases_on ‘eval_to k y’ \\ gs []
      \\ rename1 ‘v_rel w1 v1’
      \\ first_x_assum $ drule_then assume_tac \\ gs []
      \\ Cases_on ‘eval_to k f’
      \\ Cases_on ‘eval_to k g’ \\ gs []
      \\ rename1 ‘v_rel w2 v2’
      \\ Cases_on ‘dest_anyClosure v2’ \\ gs []
      >- (
        Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
        \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
        \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
        \\ gvs [OPTREL_def]
        \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
        \\ last_x_assum $ dxrule_then assume_tac
        \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
        \\ rw [Once exp_rel_cases] \\ gs [ok_bind_def])
      \\ pairarg_tac \\ gvs []
      \\ ‘∃body' binds'. dest_anyClosure w2 = INR (s,body',binds')’
        by (Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
            >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
                \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                  by (irule LIST_REL_OPTREL
                      \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
                \\ gvs [OPTREL_def]
                \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
                \\ last_x_assum $ dxrule_then assume_tac
                \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
                \\ rw [Once exp_rel_cases] \\ gvs [CaseEqs ["option", "exp"], ok_bind_def]))
      \\ IF_CASES_TAC \\ gs []
      \\ last_x_assum $ qspec_then ‘k - 1’ irule \\ gs []
      \\ irule exp_rel_subst
      \\ Cases_on ‘w2’
      \\ gvs [dest_anyClosure_def, v_rel_def, subst_APPEND]
      \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
      \\ gvs [OPTREL_def]
      \\ rename1 ‘exp_rel x' y'’ \\ Cases_on ‘x'’ \\ gvs [exp_rel_def]
      \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
      \\ gs [LIST_REL_EL_EQN, EL_MAP]
      \\ gen_tac \\ strip_tac
      \\ pairarg_tac \\ fs []
      \\ pairarg_tac \\ fs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
      \\ rename1 ‘n < _’
      \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by simp []
      \\ gs [EL_MAP])

    >~ [‘Lam s x’] >-(
      rw [Once exp_rel_cases]
      \\ gs [eval_to_def, v_rel_def])

    >~ [‘Let NONE x x'’] >-(
      rw [exp_rel_def] \\ gs []
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel x x2’ \\ rename1 ‘exp_rel y y2’
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
      \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
      \\ last_assum $ dxrule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ Cases_on ‘eval_to (k - 1) x2’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
      \\ fs[eval_to_def])

    >~ [‘Let (SOME s) x x'’] >- (
      rw [exp_rel_def] \\ gs []
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel x x2’ \\ rename1 ‘exp_rel y y2’
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
      \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
      \\ last_x_assum assume_tac
      \\ last_assum $ dxrule_then assume_tac
      \\ Cases_on ‘eval_to (k - 1) x2’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
      \\ fs[eval_to_def, exp_rel_subst])

    >~ [‘Letrec f x’] >- (
      rw [exp_rel_def] \\ gs []
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum irule
      \\ simp [subst_funs_def, closed_subst, MAP_MAP_o, combinTheory.o_DEF,
               LAMBDA_PROD, GSYM FST_THM]
      \\ strip_tac
      >- (
        CCONTR_TAC
        \\ fs[eval_to_def]
        \\ metis_tac[subst_def, subst_funs_def]
        )
      >- (
        irule exp_rel_subst
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
        \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
        \\ rename1 ‘MAP FST f = MAP FST g’
        \\ ‘∀i. i < LENGTH f ⇒ FST (EL i f) = FST (EL i g)’
          by (rw [] >>
              ‘i < LENGTH f’ by gs [] >>
              dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
              ‘i < LENGTH g’ by gs [] >>
              dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
              rw [])
        \\ gs [] \\ first_x_assum $ dxrule_then assume_tac \\ gvs []))

  >~ [‘Delay x’] >- (
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def, v_rel_def])

  >~ [‘Force x’] >- (
    rw [exp_rel_def] \\ gs []
    >~[‘Force (Delay _)’] >-(
        once_rewrite_tac [eval_to_def]
        \\ IF_CASES_TAC \\ simp []
        \\ simp [Once eval_to_def, dest_anyThunk_def]
        \\ simp [subst_funs_def, subst_empty]
        \\ first_assum $ drule_at $ Pos $ el 2
        \\ disch_then (qspec_then `k-1` mp_tac)
        \\ impl_tac
        >-(
          simp[]
          \\ CCONTR_TAC
          \\ qpat_x_assum` _ ≠ INL Type_error` mp_tac
          \\ fs[]
          \\ simp[Once eval_to_def]
          \\ simp [Once eval_to_def, dest_anyThunk_def]
          \\ simp [subst_funs_def, subst_empty])
        \\ strip_tac
        \\ rfs[]
        \\ Cases_on ‘eval_to (k - 1) x'’
        \\ rw[]
        \\ qpat_x_assum` _ ≠ INL Type_error` mp_tac
        \\ fs[]
        \\ simp [Once eval_to_def]
        \\ simp [Once eval_to_def, dest_anyThunk_def]
        \\ simp [subst_funs_def, subst_empty])

    >~[`Force _`] >-(
      rename1 ‘exp_rel x y’
      \\ once_rewrite_tac [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ last_x_assum $ drule
      \\ impl_tac >- (CCONTR_TAC \\ fs[Once $ eval_to_def])
      \\ strip_tac
      \\ Cases_on ‘eval_to k y’ \\ Cases_on ‘eval_to k x’ \\ gvs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘dest_Tick w’ \\ gs []
      >~[`dest_Tick w = NONE`] >-(
        ‘dest_Tick v = NONE’ by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [Once v_rel_def])
        \\ Cases_on ‘v’ \\ gvs [dest_anyThunk_def, v_rel_def]
        >~[‘Recclosure _ _’] >-(
            rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
            \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
               by (irule LIST_REL_OPTREL \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
            \\ gs [OPTREL_def]
            \\rename1 `exp_rel x0 y0`
            \\ ‘MEM (s, x0) xs’ by (rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [])
            \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
            \\ Cases_on ‘x0’ \\ gs [ok_bind_def, exp_rel_def]
            \\ qsuff_tac `($= +++ v_rel) (eval_to (k − 1) (subst_funs xs e)) (eval_to (k − 1) (subst_funs ys y'))`
            >~[`($= +++ v_rel) _ _ ⇒ ($= +++ v_rel) _ _`] >-(
              rpt strip_tac
              (* stuck on last case *)
              \\ Cases_on `eval_to (k-1) (subst_funs xs e)`
              \\ Cases_on `eval_to (k-1) (subst_funs ys y')`
              \\ gs[SUM_REL_THM]
              \\ drule (cj 2 v_rel_anyThunk)
              \\ rw[])
            >~[`($= +++ v_rel) _ _`] >-(
              last_x_assum $ irule
              \\ conj_tac
              >- (
                gs[Once eval_to_def,dest_anyThunk_def]
                \\ metis_tac[bind_not_error])
              >- (
                simp[subst_funs_def]
                \\ irule exp_rel_subst \\ simp[]
                \\ gs [FORALL_PROD]
                \\ gvs [MAP_MAP_o, o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
                \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
                \\ gs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
                \\ rw []
                >- (
                   rename [‘n < _’, ‘MAP FST xs = MAP FST ys’]
                   \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gs []
                   \\ gvs [EL_MAP])
                \\ last_x_assum $ drule_then irule)))
        >~[`Thunk _`] >-(
            simp[subst_funs_def]
            \\ last_x_assum $ qspec_then `k-1` assume_tac
            \\ `eval_to (k-1) x ≠ INL Type_error` by (
                CCONTR_TAC
                \\ qpat_x_assum `eval_to k (Force x) ≠ INL Type_error` mp_tac
                \\ simp[]
                \\ `eval_to k x = INL Type_error` by (
                  qspecl_then [`k-1`, `x`, `k`] assume_tac eval_to_mono \\ fs[])
                \\ fs[Once $ eval_to_def])
            \\ `eval_to (k-1) e ≠ INL Type_error ⇒
                ($= +++ v_rel) (eval_to (k − 1) e) (eval_to (k − 1) y')` by (
                `k-1 < k` by fs[]
                \\ res_tac)
            \\ Cases_on `eval_to (k-1) y'` \\ Cases_on `eval_to (k-1) e` \\ fs[]
            >- (
              first_x_assum irule
              \\ Cases_on `x''` \\ fs[]
              \\ qpat_x_assum `eval_to k (Force x) ≠ _` mp_tac \\ simp[Once eval_to_def]
              \\ fs[dest_anyThunk_def, subst_funs_def])
            >- (
              Cases_on `is_anyThunk y''` \\ fs[]
              \\ qpat_x_assum `eval_to k (Force x) ≠ _` mp_tac \\ simp[Once eval_to_def]
              \\ fs[dest_anyThunk_def, subst_funs_def])
            >- (
              Cases_on `is_anyThunk y''` \\ Cases_on `is_anyThunk y'''`\\ gs[]
              \\ `eval_to (k-1) e ≠ INL Type_error` by fs[] \\ res_tac
              >- (
                qpat_x_assum `¬ is_anyThunk y'''` mp_tac \\ fs[]
                \\ mp_tac v_rel_anyThunk \\ strip_tac
                \\ `is_anyThunk y''' ⇔ is_anyThunk y''` by (
                  first_x_assum irule \\ fs[])
                  \\ fs[])
              >- (
                qpat_x_assum `¬ is_anyThunk y''` mp_tac \\ fs[]
                \\ mp_tac v_rel_anyThunk \\ strip_tac
                \\ `is_anyThunk y''' ⇔ is_anyThunk y''` by (
                  first_x_assum irule \\ fs[])
                  \\ fs[]))))
      >~[`dest_Tick w = SOME _`] >-(
        Cases_on ‘v’ \\ gs [v_rel_def, dest_Tick_def]
        \\ `k-1 < k` by simp []
        \\ first_x_assum $ drule \\ strip_tac
        \\ first_assum $ drule
        \\ impl_tac
        >- (
            CCONTR_TAC
            \\ qpat_x_assum `_ = INR (DoTick v')` mp_tac \\ fs[Once $ eval_to_def]
            \\ `eval_to (k-1) x = eval_to k x` by simp[eval_to_mono] \\ fs[])
        >- (
          strip_tac
          \\ `exp_rel (Force (Value v')) (Force (Value x'))` by
              metis_tac[SUM_REL_THM, exp_rel_def]
          \\ `eval_to (k-1) (Force (Value v')) ≠ INL Type_error` by (
              CCONTR_TAC
              \\ qpat_x_assum `eval_to k (Force x) ≠ _` mp_tac \\ fs[Once eval_to_def]
              \\ Cases_on `k ≤ 1` \\ fs[]
              \\ simp[Once eval_to_def])
          \\ metis_tac[]))))

    >~ [‘Value v’] >- (
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])

    >~ [‘MkTick x’] >- (
      rw [exp_rel_def] \\ gs []
      \\ simp [eval_to_def]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum $ drule_then mp_tac
      \\ impl_tac >- (
        CCONTR_TAC>>
        qpat_x_assum`_ ≠ _` mp_tac>>
        simp[eval_to_def]>>
        fs[])
      \\ Cases_on ‘eval_to k y’ \\ Cases_on ‘eval_to k x’ \\ gs [v_rel_def])
QED

Theorem exp_rel_eval:
  exp_rel x y ∧ (eval x ≠ INL Type_error) ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ `eval_to u x ≠ INL Type_error` by fs[eval_not_error]
  \\ simp [eval_def]
  \\ dxrule_then assume_tac exp_rel_eval_to \\ simp []
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ rw [] \\ gs []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ first_x_assum (qspec_then ‘MAX k j’ assume_tac)
    \\ ‘eval_to (MAX k j) x = eval_to k x’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to (MAX k j) y = eval_to j y’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ qsuff_tac `eval_to (MAX k j) x ≠ INL Type_error` \\ fs[]
    \\ irule eval_not_error \\ fs[]
  )
  >- (
    rename1 ‘_ (eval_to k x) _’
    \\ first_x_assum (qspec_then ‘MAX k j’ assume_tac)
    \\ ‘eval_to (MAX k j) x = eval_to k x’
        by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ qsuff_tac `eval_to (MAX k j) x ≠ INL Type_error` \\ fs[]
    \\ irule eval_not_error \\ fs[]
  )
QED


Theorem exp_rel_apply_closure[local]:
  exp_rel x y ∧
  v_rel v2 w2 ∧
  eval x ≠ INL Type_error ∧
  (∀x y. ($= +++ v_rel) x y ⇒ next_rel v_rel exp_rel (f x) (g y)) ⇒
    next_rel v_rel exp_rel (apply_closure x v2 f) (apply_closure y w2 g)
Proof
  rw [apply_closure_def] >> simp[with_value_def] >>
  dxrule_then assume_tac exp_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gs[exp_rel_eval_to]
  >- (Cases_on `x''` >> fs[])
  >- (
    Cases_on `dest_anyClosure y'` >> Cases_on `dest_anyClosure y''` >> fs[next_rel_def]
    >-(
      CASE_TAC >> CASE_TAC >>
      `x' = Type_error` by (
        Cases_on `y'` >> fs[dest_anyClosure_def] >>
        Cases_on `ALOOKUP (REVERSE l) s` >> fs[] >> Cases_on `x''` >> fs[]) >>
      CCONTR_TAC >> qpat_x_assum `v_rel y' y''` mp_tac >> fs[v_rel_def] >>
      Cases_on `y'` >>  Cases_on `y''` >> fs[v_rel_def,dest_anyClosure_def] >> rpt strip_tac >>
      `ALOOKUP (REVERSE l) s = SOME _` by fs[]
      Cases_on `ALOOKUP (REVERSE l) s` >> fs[]
      >-(
        Cases_on `ALOOKUP (REVERSE l') s` >> fs[] >> Cases_on `x''` >> fs[]
        
      )
      >-(
        Cases_on `x''` >> fs[] >>
        `EXISTS ($¬ o ok_bind) (MAP SND l)` by (
          `∃n. n < LENGTH l ∧ EL n l = (s, Var s'')` by simp[ALOOKUP_SOME_REVERSE_EL] >>
          `MEM (Var s'') (MAP SND l)` by (
            qspecl_then [`n`, `l`] assume_tac EL_MEM >> res_tac >>
            `MEM (s, Var s'') l` by metis_tac[] >>
            `EL n (MAP SND l) = SND (EL n l)` by simp[EL_MAP] >>
            ` Var s'' = SND (EL n l)` by fs[] >> pop_assum (fn x => pure_rewrite_tac[x]) >>
            metis_tac[MEM_MAP])>>
          simp[EXISTS_MEM] >> qexists `(Var s'')` >> simp[ok_bind_def]
          ) >> 
        fs[])
      )
    ) 
    >-()
    >-()
  )

  (* Old proof
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[]
  >- (CASE_TAC >> gvs[]) >>
  rename1 `eval x = INR v1` >> rename1 `eval y = INR w1`
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [v_rel_def, dest_anyClosure_def]
  >- (
    first_x_assum irule
    \\ irule exp_rel_eval
    \\ irule exp_rel_subst \\ gs [])
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ ‘ok_bind x0’ by (rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
                          \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
      \\ rw [Once exp_rel_cases] \\ gs [ok_bind_def]
      \\ drule_then assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
      \\ gvs [EVERY_EL, EL_MAP]
      \\ first_x_assum irule
      \\ irule exp_rel_eval
      \\ irule exp_rel_subst
      \\ simp [EVERY2_MAP, LAMBDA_PROD, v_rel_def, MAP_MAP_o, combinTheory.o_DEF,
               GSYM FST_THM]
      \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EVERY_EL, EL_MAP, LIST_EQ_REWRITE])
  *)
QED

Theorem exp_rel_rel_ok[local]:
  rel_ok T v_rel exp_rel
Proof
  rw [rel_ok_def, v_rel_def, exp_rel_def]
  \\ rw [exp_rel_apply_closure]
QED

Theorem exp_rel_sim_ok[local]:
  sim_ok T v_rel exp_rel
Proof
  rw [sim_ok_def, exp_rel_eval, exp_rel_subst]
QED

Theorem exp_rel_semantics[local]:
  exp_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics \\ gs []
  \\ first_assum (irule_at Any)
  \\ qexists_tac ‘T’ \\ gs []
  \\ irule_at Any exp_rel_rel_ok
  \\ irule_at Any exp_rel_sim_ok
QED

Theorem force_delay_rel_comp:
  ∀ x z. force_delay_rel x z ⇒ ∃y. exp_rel x y ∧ clean_rel y z
Proof
  ho_match_mp_tac force_delay_rel_ind \\ rw []
  \\ gs [exp_rel_def, clean_rel_def, PULL_EXISTS]
  >- (
    first_x_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘xs’ \\ rw [PULL_EXISTS]
    \\ last_x_assum $ drule_then assume_tac \\ gs []
    \\ rpt $ last_x_assum $ irule_at Any)
  >- (
    first_x_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘xs’ \\ rw [PULL_EXISTS]
    \\ last_x_assum $ drule_then assume_tac \\ gs []
    \\ rpt $ last_x_assum $ irule_at Any)
  >- rpt $ last_x_assum $ irule_at Any
  >- rpt $ last_x_assum $ irule_at Any
  >- (
    first_x_assum $ irule_at Any \\ simp []
    \\ rename1 ‘MAP FST f = MAP FST g’
    \\ ‘∃h. MAP FST f = MAP FST h ∧ EVERY ok_bind (MAP SND h) ∧
            LIST_REL exp_rel (MAP SND f) (MAP SND h) ∧
            LIST_REL clean_rel (MAP SND h) (MAP SND g)’
      by (
        pop_assum kall_tac \\ last_x_assum kall_tac
        \\ rpt $ first_x_assum $ mp_tac
        \\ qabbrev_tac ‘g' = MAP SND g’ \\ pop_assum kall_tac
        \\ qid_spec_tac ‘g'’ \\ Induct_on ‘f’ \\ gs [PULL_EXISTS, FORALL_PROD, PULL_FORALL]
        \\ rw []
        \\ last_x_assum $ dxrule_all_then assume_tac \\ gs []
        \\ Q.REFINE_EXISTS_TAC ‘(_, _) :: _’ \\ simp []
        \\ rpt $ first_assum $ irule_at Any \\ simp []
        \\ rename1 ‘exp_rel x y’ \\ Cases_on ‘x’ \\ gs [exp_rel_def, ok_bind_def])
    \\ qexists_tac ‘h’ \\ simp []
    \\ rw []
    >- (metis_tac [])
    >- (disj1_tac \\ metis_tac []))
  >- metis_tac []
  >- metis_tac []
  >- metis_tac []
  >- (
    Q.REFINE_EXISTS_TAC ‘Force _’ \\ gs [clean_rel_def]
    \\ metis_tac [])
  >- (
    Q.REFINE_EXISTS_TAC ‘Tick _’ \\ gs [clean_rel_def]
    \\ first_x_assum $ irule_at Any \\ gs [])
  >- metis_tac []
QED

Theorem force_delay_semantics:
  force_delay_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ dxrule_then assume_tac force_delay_rel_comp \\ gs []
  \\ drule_then assume_tac exp_rel_freevars
  \\ dxrule_then assume_tac exp_rel_semantics
  \\ dxrule_then assume_tac clean_rel_semantics
  \\ gs [closed_def]
QED


