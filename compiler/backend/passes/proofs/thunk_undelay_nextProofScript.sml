Theory thunk_undelay_nextProof
Ancestors
  string option sum pair list alist finite_map pred_set rich_list
  pure_misc pure_config pure_semantics thunkLang_primitives thunkLang
  thunkLangProps thunk_semantics thunk_semantics_delayed
Libs
  term_tactic monadsyntax

val _ = numLib.prefer_num ();

Theorem SUM_REL_THM[local,simp] = sumTheory.SUM_REL_THM;
Theorem PAIR_REL_def[local,simp] = pairTheory.PAIR_REL;

Definition mop_simple_def[simp]:
  mop_simple pure_config$Bind = T ∧
  mop_simple Handle = T ∧
  mop_simple _ = F
End

Definition mop_ret_def[simp]:
  mop_ret pure_config$Ret = T ∧
  mop_ret Raise = T ∧
  mop_ret _ = F
End

Definition mop_delay_def[simp]:
  mop_delay Length = T ∧
  mop_delay Alloc = T ∧
  mop_delay Act = T ∧
  mop_delay _ = F
End

Inductive exp_rel:
[exp_rel_Monad:]
  (∀mop xs ys.
     mop_simple mop ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad mop xs) (Monad mop ys))
[exp_rel_Monad_Delay:]
  (∀mop xs ys.
     mop_ret mop ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad mop xs) (Monad mop ys))
[exp_rel_Monad_Ret_Delay:]
  (∀mop xs ys.
     mop_delay mop ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad mop xs)
               (Monad Bind [
                  Monad mop ys;
                  Lam "v" (Monad Ret [Delay $ Var "v"])]))
[exp_rel_Monad_Deref:]
  (∀xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad Deref xs)
               (Monad Handle [
                  Monad Deref ys;
                  Lam "v" $ Monad Raise [Delay $ Var "v"]]))
[exp_rel_Monad_Update:]
  (∀xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad Update xs)
               (Monad Bind [
                  Monad Handle [
                    Monad Update ys;
                    Lam "v" $ Monad Raise [Delay $ Var "v"]];
                  Lam "v" $ Monad Ret [Delay $ Var "v"]]))
[exp_rel_LitVal:]
  (∀l. exp_rel (Lit l) (Value (Atom l)))
[exp_rel_ConsVal:]
  (cn ∉ monad_cns ⇒ exp_rel (Cons cn []) (Value (Constructor cn [])))
[exp_rel_App:]
  (∀f g x y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f x) (App g y))
[exp_rel_Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y))
[exp_rel_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y))
[exp_rel_Let:]
  (∀bv x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let bv x1 y1) (Let bv x2 y2))
[exp_rel_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL exp_rel [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2))
[exp_rel_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys))
[exp_rel_Delay:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Delay x) (Delay y))
[exp_rel_Force:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Force x) (Force y))
[exp_rel_MkTick:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (MkTick x) (MkTick y))
[exp_rel_Var:]
  (∀v.
     exp_rel (Var v) (Var v))
[exp_rel_Value:]
  (∀v w.
     v_rel v w ⇒
     exp_rel (Value v) (Value w))
[v_rel_Monadic:]
  (∀mop xs ys.
     mop_simple mop ∧
     LIST_REL exp_rel xs ys ⇒
       v_rel (Monadic mop xs) (Monadic mop ys))
[v_rel_Monadic_Delay:]
  (∀mop xs ys.
     mop_ret mop ∧
     LIST_REL exp_rel xs ys ⇒
       v_rel (Monadic mop xs) (Monadic mop ys))
[v_rel_Monadic_Thunk:]
  (∀mop xs ys vs.
     mop_ret mop ∧
     xs = MAP Value vs ∧
     LIST_REL (λv y. is_anyThunk v ∧ exp_rel (Value v) y) vs ys ⇒
       v_rel (Monadic mop xs) (Monadic mop ys))
[v_rel_Monadic_Ret_Delay:]
  (∀mop xs ys.
     mop_delay mop ∧
     LIST_REL exp_rel xs ys ⇒
       v_rel (Monadic mop xs)
             (Monadic Bind [
                Monad mop ys;
                Lam "v" (Monad Ret [Delay $ Var "v"])]))
[v_rel_Monadic_Deref:]
  (∀xs ys.
     LIST_REL exp_rel xs ys ⇒
       v_rel (Monadic Deref xs)
             (Monadic Handle [
                Monad Deref ys;
                Lam "v" $ Monad Raise [Delay $ Var "v"]]))
[v_rel_Monadic_Update:]
  (∀xs ys.
     LIST_REL exp_rel xs ys ⇒
       v_rel (Monadic Update xs)
             (Monadic Bind [
                Monad Handle [
                  Monad Update ys;
                  Lam "v" $ Monad Raise [Delay $ Var "v"]];
                Lam "v" $ Monad Ret [Delay $ Var "v"]]))
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x))
[v_rel_Constructor:]
  (∀vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws))
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ⇒
       v_rel (Closure s x) (Closure s y))
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) (DoTick w))
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n))
[v_rel_Thunk:]
  (∀x y.
     exp_rel x y ⇒
       v_rel (Thunk x) (Thunk y))
End

Theorem v_rel_cases[local] = CONJUNCT2 exp_rel_cases;

(* Boilerplate *)
Theorem v_rel_def[simp] =
  [ “v_rel (Closure s x) z”,
    “v_rel z (Closure s x)”,
    “v_rel (Recclosure s x) z”,
    “v_rel z (Recclosure s x)”,
    “v_rel (Constructor s x) z”,
    “v_rel z (Constructor s x)”,
    “v_rel (Monadic mop xs) z”,
    “v_rel z (Monadic mop ys)”,
    “v_rel (Atom x) z”,
    “v_rel z (Atom x)”,
    “v_rel (Thunk x) z”,
    “v_rel z (Thunk x)” ]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem exp_rel_freevars:
  exp_rel x y ⇒ freevars x = freevars y
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ freevars x = freevars y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- rw []
  \\ ho_match_mp_tac exp_rel_strongind \\ simp [freevars_def] \\ rw []
  >~ [`Let`] >- (
    Cases_on `bv` \\ simp [freevars_def])
  \\ (
    rw [EXTENSION, EQ_IMP_THM] \\ gs []
    \\ fs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN,
           Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
    \\ rw [] \\ gs [EL_MAP, ELIM_UNCURRY, SF CONJ_ss, SF SFY_ss])
QED

Theorem exp_rel_subst:
  ∀vs x ws y.
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    exp_rel x y ⇒
      exp_rel (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >~ [`Monad`] >- (
    rw [Once exp_rel_cases] \\ gvs [subst_def]
    >~ [`mop_simple`] >- (
      rw [Once exp_rel_cases]
      \\ disj1_tac
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS])
    >~ [`mop_ret`] >- (
      rw [Once exp_rel_cases]
      \\ disj2_tac \\ disj1_tac \\ rw []
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS])
    >~ [`mop_delay`] >- (
      rw [Once exp_rel_cases]
      \\ disj2_tac \\ disj2_tac \\ disj1_tac \\ rw []
      >- (
        CASE_TAC \\ gvs []
        \\ drule ALOOKUP_SOME \\ rw [MEM_MAP, MEM_FILTER]
        \\ pairarg_tac \\ gvs [])
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS])
    >~ [`Deref`] >- (
      rw [Once exp_rel_cases]
      >- (
        CASE_TAC \\ rw []
        \\ drule ALOOKUP_SOME \\ rw [MEM_MAP, MEM_FILTER]
        \\ pairarg_tac \\ gvs [])
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS])
    >~ [`Update`] >- (
      rw [Once exp_rel_cases]
      >- (
        CASE_TAC \\ gvs []
        \\ drule ALOOKUP_SOME \\ rw [MEM_MAP, MEM_FILTER]
        \\ pairarg_tac \\ gvs [])
      >- (
        CASE_TAC \\ gvs []
        \\ drule ALOOKUP_SOME \\ rw [MEM_MAP, MEM_FILTER]
        \\ pairarg_tac \\ gvs [])
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS] \\ rw []))
  (* Boilerplate *)
  >~ [`Var`] >- (
    rw [Once exp_rel_cases, subst_def] \\ gs []
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) s) (ALOOKUP (REVERSE ws) s)’
      by (irule LIST_REL_OPTREL
          \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ]
          \\ pop_assum mp_tac
          \\ qid_spec_tac ‘ws’
          \\ qid_spec_tac ‘vs’
          \\ Induct \\ simp []
          \\ gen_tac \\ Cases \\ simp [])
    \\ gs [OPTREL_def]
    \\ rw [Once exp_rel_cases])
  >~ [`Prim`] >- (
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    >- (simp [Once exp_rel_cases])
    >- (simp [Once exp_rel_cases])
    \\ irule exp_rel_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw [])
  >~ [`If`] >- (
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_If \\ fs [])
  >~ [`App`] >- (
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_App \\ fs [])
  >~ [`Lam`] >- (
    rw [Once exp_rel_cases]
    \\ gvs [subst_def]
    \\ irule exp_rel_Lam
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
  >~ [`Let NONE`] >- (
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ fs [])
  >~ [`Let (SOME _)`] >- (
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
  >~ [`Letrec`] >- (
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_Letrec
    \\ gvs [EVERY2_MAP, LAMBDA_PROD]
    \\ first_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ `MAP FST f = MAP FST g`
      by (irule LIST_EQ
          \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST g)’ \\ fs []
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [MAP_FST_FILTER, SF ETA_ss]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD] \\ rw []
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER, SF ETA_ss, SF SFY_ss]
    \\ irule_at Any LIST_REL_FILTER \\ gs []
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD])
  >~ [`Delay`] >- (
    rw [Once exp_rel_cases]
    \\ simp [subst_def, exp_rel_Value, exp_rel_Delay, SF SFY_ss]
    \\ qmatch_asmsub_abbrev_tac ‘LIST_REL R _ _’
    \\ ‘OPTREL R (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_OPTREL
          \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ, Abbr ‘R’]
          \\ pop_assum mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘ws’ \\ Induct_on ‘vs’ \\ Cases_on ‘ws’ \\ simp [])
    \\ gvs [Abbr ‘R’, OPTREL_def, exp_rel_Var, exp_rel_Value])
  >~ [`Force`] >- (
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Force \\ fs [])
  >~ [`Value`] >- (
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ rw [Once exp_rel_cases])
  >~ [`MkTick`] >- (
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_MkTick
    \\ first_x_assum irule \\ gs [])
QED

Theorem LIST_REL_split:
  ∀l l'.
    LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y) l l' ⇒
      MAP FST l = MAP FST l' ∧
      LIST_REL exp_rel (MAP SND l) (MAP SND l')
Proof
  Induct \\ rw [] \\ gvs []
  \\ rpt $ (pairarg_tac \\ gvs [])
QED

Theorem LIST_REL_ALOOKUP_REVERSE:
  ∀l l' s.
    MAP FST l = MAP FST l' ∧
    LIST_REL exp_rel (MAP SND l) (MAP SND l') ⇒
      (ALOOKUP (REVERSE l) s = NONE ⇒
         ALOOKUP (REVERSE l') s = NONE) ∧
      (∀e. ALOOKUP (REVERSE l) s = SOME e ⇒
         ∃e'. ALOOKUP (REVERSE l') s = SOME e' ∧
              exp_rel e e')
Proof
  rw []
  >- gvs [ALOOKUP_NONE, MAP_REVERSE]
  \\ ‘MAP FST (REVERSE l) = MAP FST (REVERSE l')’ by gvs [MAP_EQ_EVERY2]
  \\ drule_all ALOOKUP_SOME_EL_2 \\ rw []
  \\ gvs [SF SFY_ss, LIST_REL_EL_EQN, EL_MAP, EL_REVERSE]
  \\ ‘PRE (LENGTH l' - n) < LENGTH l'’ by gvs []
  \\ first_x_assum drule \\ rw []
QED

Theorem v_rel_anyThunk:
  ∀v w. v_rel v w ⇒ (is_anyThunk v ⇔ is_anyThunk w)
Proof
  `(∀v w. exp_rel v w ⇒ T) ∧
   (∀v w. v_rel v w ⇒ (is_anyThunk v ⇔ is_anyThunk w))`
    suffices_by gvs []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw [] \\ gvs []
  \\ rw [is_anyThunk_def, dest_anyThunk_def]
  \\ dxrule LIST_REL_split \\ rpt strip_tac
  \\ rpt CASE_TAC
  \\ drule_all_then (qspec_then ‘n’ mp_tac) LIST_REL_ALOOKUP_REVERSE
  \\ rpt strip_tac
  \\ rgs [Once exp_rel_cases]
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ⇒
      ($= +++ v_rel)
        (eval_to k x)
        (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ simp []
  \\ rpt conj_tac \\ rpt gen_tac
  >~ [‘Value v’] >- (
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Var n’] >- (
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘App f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ rename1 ‘exp_rel x y’
    \\ gs [eval_to_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ Cases_on ‘eval_to k f’ \\ Cases_on ‘eval_to k g’ \\ gvs []
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyClosure_def]
    >~ [`Closure`] >- (
      IF_CASES_TAC \\ gs []
      \\ rename1 ‘(_ +++ _) (_ _ (subst1 s u1 e1)) (_ _ (subst1 s u2 e2))’
      \\ ‘[s,u1] = [] ++ [s,u1]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ ‘[s,u2] = [] ++ [s,u2]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ first_x_assum irule \\ gs []
      \\ irule exp_rel_subst \\ gs [])
    >~ [`Recclosure`] >- (
      rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                         (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ rgs [Once exp_rel_cases]
      \\ IF_CASES_TAC \\ gs []
      \\ first_x_assum irule
      \\ irule exp_rel_subst \\ gs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP,
                                    LAMBDA_PROD, GSYM FST_THM]
      \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
      \\ irule LIST_EQ \\ gvs [EL_MAP]))
  >~ [‘Lam s x’] >- (
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def])
  >~ [‘Let NONE x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
  >~ [‘Let (SOME n) x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ irule exp_rel_subst \\ gs [])
  >~ [‘If x1 y1 z1’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [])
  >~ [‘Letrec f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def]
    \\ irule exp_rel_subst \\ gs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP,
                                  LAMBDA_PROD, GSYM FST_THM]
    \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
    \\ irule LIST_EQ \\ gvs [EL_MAP])
  >~ [‘Delay x’] >- (
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def])
  >~ [‘Force x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ rename1 ‘exp_rel x y’
    \\ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘dest_Tick v’ \\ gs []
    >- (
      ‘dest_Tick w = NONE’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_cases])
      \\ gs []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
      >- (
        rename1 ‘LIST_REL _ xs ys’
        \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                           (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL \\ gs [])
        \\ gs [OPTREL_def]
        \\ rgs [Once exp_rel_cases]
        \\ Cases_on ‘eval_to (k - 1) (subst_funs xs x')’ \\ gvs []
        \\ Cases_on ‘eval_to (k - 1) (subst_funs ys y')’ \\ gvs []
        \\ rpt (IF_CASES_TAC \\ gvs [])
        \\ ‘($= +++ v_rel) (eval_to (k − 1) (subst_funs xs x'))
                           (eval_to (k − 1) (subst_funs ys y'))’
          suffices_by
            (gvs [] \\ strip_tac \\ drule v_rel_anyThunk \\ gvs [])
        \\ first_x_assum irule
        \\ simp [subst_funs_def]
        \\ irule exp_rel_subst \\ gs [MAP_MAP_o, combinTheory.o_DEF,
                                      EVERY2_MAP, LAMBDA_PROD, GSYM FST_THM]
        \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
        \\ irule LIST_EQ \\ gvs [EL_MAP])
      \\ Cases_on ‘eval_to (k - 1) (subst_funs [] e)’ \\ gvs []
      \\ Cases_on ‘eval_to (k - 1) (subst_funs [] e')’ \\ gvs []
      \\ rpt (IF_CASES_TAC \\ gvs [])
      \\ ‘($= +++ v_rel) (eval_to (k − 1) (subst_funs [] e))
                         (eval_to (k − 1) (subst_funs [] e'))’
        suffices_by
          (gvs [] \\ strip_tac \\ drule v_rel_anyThunk \\ gvs [])
      \\ first_x_assum irule
      \\ simp [subst_funs_def])
    \\ ‘∃y. dest_Tick w = SOME y’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_cases])
    \\ gs []
    \\ first_x_assum irule
    \\ rw [Once exp_rel_cases]
    \\ rw [Once exp_rel_cases]
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [Once v_rel_cases])
  >~ [‘MkTick x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rw [Once v_rel_cases])
  >~ [‘Prim op xs’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    >- simp [eval_to_def, result_map_def]
    >- simp [eval_to_def, result_map_def]
    \\ simp [eval_to_def]
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      `($= +++ v_rel)
          do
            vs <- result_map (λx. eval_to k x) xs;
            INR (Constructor s vs)
          od
          do
            vs <- result_map (λx. eval_to k x) ys;
            INR (Constructor s vs)
          od` suffices_by (
            simp [oneline sum_bind_def]
            \\ rpt (CASE_TAC \\ gvs [])
            \\ gvs [EVERY_EL, EXISTS_MEM, MEM_EL, LIST_REL_EL_EQN]
            \\ rw [] \\ gvs []
            \\ goal_assum drule \\ rw []
            \\ first_x_assum drule \\ rw []
            \\ CCONTR_TAC \\ gvs []
            \\ drule v_rel_anyThunk \\ rw [])
      \\ rgs [result_map_def, MEM_MAP, PULL_EXISTS, LIST_REL_EL_EQN, MEM_EL]
      \\ IF_CASES_TAC \\ gs []
      >- (
        gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gvs []
        \\ rw [] \\ gs [])
      \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        >- (
          rename1 ‘m < LENGTH ys’
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
        \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ rw [] \\ gs []
        \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
        \\ last_x_assum drule_all
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
      \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ rw [EVERY2_MAP, LIST_REL_EL_EQN]
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to k (EL n xs)’
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
      \\ rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
    >- ((* IsEq *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1n ⇔ n = 0”]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ ntac 3 (IF_CASES_TAC \\ gs []))
    >- ((* Proj *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1n ⇔ n = 0”]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* AtomOp *)
      qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ ‘MAP f xs = MAP g ys’
        suffices_by (
          rw []
          \\ simp [result_map_def]
          \\ IF_CASES_TAC \\ gs []
          \\ IF_CASES_TAC \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [])
      \\ unabbrev_all_tac
      \\ irule LIST_EQ
      \\ gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP]
      \\ rw []
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_all_then assume_tac)
      \\ rpt CASE_TAC \\ gs []))
  >~ [`Monad mop xs`] >- (
     rw [Once exp_rel_cases]
     \\ simp [eval_to_def]
     \\ metis_tac [])
QED

Theorem exp_rel_eval[local] =
  Q.INST [‘allow_error’|->‘T’] eval_to_eval_lift
  |>  SIMP_RULE (srw_ss ()) []
  |> Lib.C MATCH_MP exp_rel_eval_to;

Definition next_rel_def[simp]:
  next_rel Ret Ret = T ∧
  next_rel Div Div = T ∧
  next_rel Err Err = T ∧
  next_rel (Act a c s) (Act b d t) = (
    ∃d'.
      d = BC (Lam "v" $ Monad Ret [Delay $ Var "v"]) d' ∧
      a = b ∧ cont_rel_delayed exp_rel c d' ∧ state_rel_delayed v_rel s t) ∧
  next_rel _ _ = F
End

Definition is_anyClosure_def[simp]:
  is_anyClosure v = (∃x. dest_anyClosure v = INR x)
End

Theorem v_rel_dest_anyClosure:
  ∀v w s body binds.
    v_rel v w ∧
    dest_anyClosure v = INR (s,body,binds) ⇒
      ∃body' binds'. dest_anyClosure w = INR (s,body',binds') ∧
                     exp_rel body body' ∧
                     LIST_REL (λ(s,v) (s',v'). s = s' ∧ v_rel v v') binds binds'
Proof
  rw []
  \\ Cases_on `v` \\ gvs [dest_anyClosure_def, AllCaseEqs()]
  \\ dxrule LIST_REL_split \\ rw []
  \\ ‘MAP FST (REVERSE l) = MAP FST (REVERSE g)’ by gvs [MAP_EQ_EVERY2]
  \\ drule_all ALOOKUP_SOME_EL_2 \\ rw []
  \\ gvs [SF SFY_ss, LIST_REL_EL_EQN, EL_MAP, EL_REVERSE]
  \\ ‘PRE (LENGTH g - n) < LENGTH g’ by gvs []
  \\ `exp_rel (Lam s body) v'` by (first_x_assum drule \\ rw [])
  \\ rgs [Once exp_rel_cases] \\ rw []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [MAP_EQ_EVERY2, LIST_REL_EL_EQN]
  \\ rw []
  >- (last_x_assum drule \\ rw [])
  >- (last_x_assum drule \\ rw [])
  >- (
    rpt (pairarg_tac \\ gvs [])
    \\ rpt (first_x_assum drule  \\ rw []))
QED

Theorem v_rel_anyClosure:
  ∀v w. v_rel v w ⇒ (is_anyClosure v ⇔ is_anyClosure w)
Proof
  `(∀v w. exp_rel v w ⇒ T) ∧
   (∀v w. v_rel v w ⇒ (is_anyClosure v ⇔ is_anyClosure w))`
    suffices_by gvs []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw [] \\ gvs []
  \\ rw [dest_anyClosure_def]
  \\ dxrule LIST_REL_split \\ rpt strip_tac
  \\ rpt CASE_TAC
  \\ drule_all_then (qspec_then ‘n’ mp_tac) LIST_REL_ALOOKUP_REVERSE
  \\ rpt strip_tac
  \\ rgs [Once exp_rel_cases]
QED

Theorem exp_rel_subst_LIST_REL[local]:
  exp_rel q q' ∧
  LIST_REL (λ(s,v) (s',v'). s = s' ∧ v_rel v v') r r' ⇒
    ($= +++ v_rel) (eval (subst r q)) (eval (subst r' q'))
Proof
  rw []
  \\ irule exp_rel_eval
  \\ irule exp_rel_subst \\ rw []
  \\ gvs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_MAP] \\ rw []
  \\ first_x_assum drule \\ rw []
  \\ rpt (pairarg_tac \\ gvs [])
QED

Theorem thunk_exists[simp,local]:
  ∃k. is_anyThunk k
Proof
  qrefine `Thunk _` \\ simp [is_anyThunk_def, dest_anyThunk_def]
QED

Theorem undelay_next_thm[local]:
  ∀k v c s w d t.
    ($= +++ v_rel) v w ∧
    cont_rel_delayed exp_rel c d ∧
    state_rel_delayed v_rel s t ∧
    next_delayed k v c s ≠ Err ⇒
      ∃ck. next_rel (next_delayed k v c s) (next (k + ck) w d t)
Proof
  ho_match_mp_tac next_delayed_ind \\ rw []
  \\ simp [Once next_delayed_def]
  \\ Cases_on ‘v = INL Type_error ∨
               v = INL Diverge ∨
               (∃x y. v = INR (Constructor x y)) ∨
               (∃x y. v = INR (Closure x y)) ∨
               (∃x y. v = INR (Recclosure x y)) ∨
               (∃t. v = INR (Thunk t)) ∨
               (∃a. v = INR (Atom a)) ∨
               (∃t. v = INR (DoTick t))’
  >- ((* Error *)
    rgs [Once next_delayed_def]
    \\ Cases_on ‘w’ \\ rgs [Once thunk_semanticsTheory.next_def]
    \\ gs [Once next_delayed_def])
  \\ gvs []
  \\ Cases_on `v` \\ gvs []
  >- (CASE_TAC \\ gvs [])
  \\ Cases_on ‘w’ \\ gvs []
  \\ Cases_on ‘y’ \\ gvs []
  \\ TRY (Cases_on `m` \\ gvs [])
  >~ [`Monadic Ret _`] >- (
    `LENGTH l = 1` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ simp [Once next_def]
    \\ rgs [Once next_delayed_def, with_value_def]
    \\ imp_res_tac exp_rel_eval
    \\ rpt (CASE_TAC \\ gvs [])
    >- (qexists `0` \\ simp [])
    >- (qexists `0` \\ simp [])
    \\ gvs [apply_closure_def, with_value_def]
    \\ imp_res_tac exp_rel_eval \\ gvs []
    \\ rpt (CASE_TAC \\ gvs [])
    >- (imp_res_tac v_rel_anyClosure \\ gvs [])
    \\ first_x_assum irule \\ rw []
    \\ drule_all v_rel_dest_anyClosure \\ rw []
    \\ gvs [exp_rel_subst_LIST_REL])
  >~ [`Monadic Ret (MAP Value _)`] >- (
    `LENGTH vs = 1` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ simp [Once next_def]
    \\ rgs [Once next_delayed_def, with_value_def]
    \\ imp_res_tac exp_rel_eval
    \\ rpt (CASE_TAC \\ gvs [])
    >- (qexists `0` \\ simp [])
    >- (qexists `0` \\ simp [])
    \\ gvs [apply_closure_def, with_value_def]
    \\ imp_res_tac exp_rel_eval \\ gvs []
    \\ rpt (CASE_TAC \\ gvs [])
    >- (imp_res_tac v_rel_anyClosure \\ gvs [])
    \\ first_x_assum irule \\ rw []
    \\ drule_all v_rel_dest_anyClosure \\ rw []
    \\ gvs [exp_rel_subst_LIST_REL])
  >~ [`Monadic Raise _`] >- (
    `LENGTH l = 1` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ simp [Once next_def]
    \\ rgs [Once next_delayed_def, with_value_def]
    \\ imp_res_tac exp_rel_eval
    \\ rpt (CASE_TAC \\ gvs [])
    >- (qexists `0` \\ simp [])
    >- (qexists `0` \\ simp [])
    \\ gvs [apply_closure_def, with_value_def]
    \\ imp_res_tac exp_rel_eval \\ gvs []
    \\ rpt (CASE_TAC \\ gvs [])
    >- (imp_res_tac v_rel_anyClosure \\ gvs [])
    \\ first_x_assum irule \\ rw []
    \\ drule_all v_rel_dest_anyClosure \\ rw []
    \\ gvs [exp_rel_subst_LIST_REL])
  >~ [`Monadic Raise (MAP Value _)`] >- (
    `LENGTH vs = 1` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ simp [Once next_def]
    \\ rgs [Once next_delayed_def, with_value_def]
    \\ imp_res_tac exp_rel_eval
    \\ rpt (CASE_TAC \\ gvs [])
    >- (qexists `0` \\ simp [])
    >- (qexists `0` \\ simp [])
    \\ gvs [apply_closure_def, with_value_def]
    \\ imp_res_tac exp_rel_eval \\ gvs []
    \\ rpt (CASE_TAC \\ gvs [])
    >- (imp_res_tac v_rel_anyClosure \\ gvs [])
    \\ first_x_assum irule \\ rw []
    \\ drule_all v_rel_dest_anyClosure \\ rw []
    \\ gvs [exp_rel_subst_LIST_REL])
  >~ [`Bind`] >- (
    `LENGTH l = 2` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ CASE_TAC \\ gvs [] \\ simp [Once next_def]
    >- (qexists `0` \\ simp [])
    \\ rgs [Once next_delayed_def]
    \\ first_x_assum irule \\ simp [exp_rel_eval])
  >~ [`Handle`] >- (
    `LENGTH l = 2` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ CASE_TAC \\ gvs [] \\ simp [Once next_def]
    >- (qexists `0` \\ simp [])
    \\ rgs [Once next_delayed_def]
    \\ first_x_assum irule \\ simp [exp_rel_eval])
  >~ [`Act`] >- (
    `LENGTH l = 1` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ simp [Once next_def]
    \\ rgs [Once next_delayed_def, with_atoms_def]
    \\ rpt (CASE_TAC \\ gvs [])
    >- (
      Cases_on `k = 0` \\ gvs []
      >- (qexists `0` \\ simp [])
      \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ qrefine `ck + 1` \\ simp [Once next_def, with_atoms_def]
      \\ gvs [result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval h` \\ Cases_on `eval y` \\ gvs [])
    \\ Cases_on `k = 0` \\ gvs []
    \\ qrefine `ck + 1` \\ gvs []
    \\ simp [eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
    \\ simp [Once next_def, with_atoms_def]
    \\ gvs [result_map_def]
    \\ imp_res_tac exp_rel_eval \\ gvs []
    \\ Cases_on `eval h` \\ Cases_on `eval y` \\ gvs []
    \\ qpat_x_assum `v_rel y'' y'3'` assume_tac
    \\ Cases_on `y''` \\ Cases_on `y'3'`
    \\ rgs [Once v_rel_cases, get_atoms_def])
  >~ [`Alloc`] >- (
    `LENGTH l = 2` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ simp [Once next_def]
    \\ rgs [Once next_delayed_def, with_atoms_def]
    \\ rpt (CASE_TAC \\ gvs [])
    >- (qexists `0` \\ simp [])
    >- (qexists `0` \\ simp [])
    >- (
      simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ qrefine `ck + 1` \\ simp [Once next_def, with_atoms_def]
      \\ gvs [result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval h` \\ Cases_on `eval y`
      \\ Cases_on `eval h'` \\ Cases_on `eval y'` \\ gvs []
      \\ Cases_on `x` \\ gvs [])
    >- (
      qrefine `ck + 1` \\ gvs []
      \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def]
      \\ gvs [result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval h` \\ Cases_on `eval y`
      \\ Cases_on `eval h'` \\ Cases_on `eval y'` \\ gvs []
      >- (Cases_on `x` \\ gvs [] \\ Cases_on `x''` \\ gvs [])
      >- (Cases_on `x` \\ gvs [])
      >- (Cases_on `x` \\ gvs [])
      \\ qpat_x_assum `v_rel h'' y'3'` assume_tac
      \\ Cases_on `h''` \\ Cases_on `y'3'`
      \\ rgs [Once v_rel_cases, get_atoms_def, is_anyThunk_def,
              dest_anyThunk_def]
      \\ qrefine `ck + 1` \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, result_map_def]
      \\ simp [apply_closure_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, dest_anyClosure_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, subst1_def]
      \\ first_x_assum irule \\ rw [] \\ gvs [state_rel_delayed_def]
      \\ ntac 2 (simp [Once exp_rel_cases])
      \\ gvs [LIST_REL_EL_EQN])
    \\ qrefine `ck + 1` \\ gvs []
    \\ simp [eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
    \\ simp [Once next_def]
    \\ gvs [result_map_def]
    \\ imp_res_tac exp_rel_eval \\ gvs []
    \\ Cases_on `eval h` \\ Cases_on `eval y`
    \\ Cases_on `eval h'` \\ Cases_on `eval y'` \\ gvs []
    >- (Cases_on `x` \\ gvs [] \\ Cases_on `x''` \\ gvs [])
    >- (Cases_on `x` \\ gvs [])
    >- (Cases_on `x` \\ gvs [])
    \\ qpat_x_assum `v_rel h'' y'3'` assume_tac
    \\ Cases_on `h''` \\ Cases_on `y'3'`
    \\ rgs [Once v_rel_cases, get_atoms_def, is_anyThunk_def, dest_anyThunk_def]
    \\ (
      qrefine `ck + 1` \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, result_map_def]
      \\ simp [apply_closure_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, dest_anyClosure_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, subst1_def]
      \\ first_x_assum irule \\ rw [] \\ gvs [state_rel_delayed_def]
      >- (gvs [LIST_REL_EL_EQN, EL_REPLICATE, is_anyThunk_def,
               dest_anyThunk_def]
          \\ simp [Once v_rel_cases])
      \\ ntac 2 (simp [Once exp_rel_cases])
      \\ gvs [LIST_REL_EL_EQN]))
  >~ [`Length`] >- (
    `LENGTH l = 1` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ simp [Once next_def]
    \\ rgs [Once next_delayed_def, with_atoms_def, result_map_def]
    \\ rpt (CASE_TAC \\ gvs [])
    >- (
      Cases_on `k = 0` \\ gvs []
      >- (qexists `0` \\ simp [])
      \\ qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, with_atoms_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval y` \\ gvs [])
    >- (qexists `0` \\ simp [])
    \\ qrefine `ck + 1` \\ simp [eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
    \\ simp [Once next_def, with_atoms_def, result_map_def]
    \\ imp_res_tac exp_rel_eval \\ gvs []
    \\ Cases_on `eval h` \\ Cases_on `eval y` \\ gvs []
    >- (Cases_on `x'` \\ gvs [])
    \\ qpat_x_assum `v_rel y' y''` assume_tac
    \\ Cases_on `y'` \\ Cases_on `y''`
    \\ rgs [Once v_rel_cases, get_atoms_def]
    \\ CASE_TAC \\ gvs [state_rel_delayed_def, LIST_REL_EL_EQN]
    \\ qrefine `ck + 1` \\ simp [Once next_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, result_map_def]
    \\ simp [apply_closure_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, dest_anyClosure_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, subst1_def]
    \\ first_x_assum irule \\ rw []
    >- (qexists `[Loc n]` \\ simp [])
    \\ ntac 2 (simp [Once exp_rel_cases]))
  >~ [`Deref`] >- (
    `LENGTH l = 2` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss]
    \\ simp [Once next_def]
    \\ rgs [Once next_delayed_def, with_atoms_def, result_map_def]
    \\ rpt (CASE_TAC \\ gvs [])
    >- (
      Cases_on `k = 0` \\ gvs []
      >- (qexists `0` \\ simp [])
      \\ qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, with_atoms_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval y` \\ gvs []
      \\ Cases_on `eval h'` \\ Cases_on `eval y'` \\ gvs [])
    >- (
      Cases_on `k = 0` \\ gvs []
      >- (qexists `0` \\ simp [])
      \\ qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, with_atoms_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval y'` \\ gvs []
      \\ Cases_on `eval h` \\ Cases_on `eval y` \\ gvs [])
    >- (qexists `0` \\ simp [])
    >- (
      qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, with_atoms_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval h'` \\ Cases_on `eval y'` \\ gvs []
      >- (Cases_on `x'` \\ gvs [])
      \\ Cases_on `eval h` \\ Cases_on `eval y` \\ gvs []
      >- (Cases_on `x'` \\ gvs [])
      \\ qpat_x_assum `v_rel y'4' y'5'` assume_tac
      \\ Cases_on `y'4'` \\ Cases_on `y'5'`
      \\ rgs [Once v_rel_cases, get_atoms_def]
      \\ gvs [state_rel_delayed_def, LIST_REL_EL_EQN]
      \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ qrefine `ck + 1` \\ simp []
      \\ first_x_assum irule \\ rw []
      >- (qexists `[Loc n; Int i]` \\ simp [])
      \\ simp [Once exp_rel_cases]
      \\ `n < LENGTH t` by gvs []
      \\ first_x_assum drule \\ rw []
      \\ `Num i < LENGTH (EL n s)` by intLib.COOPER_TAC
      \\ first_x_assum drule \\ rw [])
    >- (
      qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, with_atoms_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval h'` \\ Cases_on `eval y'` \\ gvs []
      >- (Cases_on `x'` \\ gvs [])
      \\ Cases_on `eval h` \\ Cases_on `eval y` \\ gvs []
      >- (Cases_on `x'` \\ gvs [])
      \\ qpat_x_assum `v_rel y'4' y'5'` assume_tac
      \\ Cases_on `y'4'` \\ Cases_on `y'5'`
      \\ rgs [Once v_rel_cases, get_atoms_def]
      \\ gvs [state_rel_delayed_def, LIST_REL_EL_EQN]
      \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, result_map_def]
      \\ qrefine `ck + 1` \\ simp []
      \\ simp [apply_closure_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, dest_anyClosure_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, subst1_def]
      \\ last_x_assum irule \\ rw []
      >- (
        ntac 2 (goal_assum drule \\ rw [])
        \\ qexists `[Loc n; Int i]` \\ simp [])
      \\ ntac 2 (simp [Once exp_rel_cases])
      \\ simp [monad_cns_def])
    \\ qrefine `ck + 1` \\ simp [eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
    \\ simp [Once next_def, with_atoms_def, result_map_def]
    \\ imp_res_tac exp_rel_eval \\ gvs []
    \\ Cases_on `eval h'` \\ Cases_on `eval y'` \\ gvs []
    >- (Cases_on `x'` \\ gvs [])
    \\ Cases_on `eval h` \\ Cases_on `eval y` \\ gvs []
    >- (Cases_on `x'` \\ gvs [])
    \\ qpat_x_assum `v_rel y'4' y'5'` assume_tac
    \\ Cases_on `y'4'` \\ Cases_on `y'5'`
    \\ rgs [Once v_rel_cases, get_atoms_def]
    \\ gvs [state_rel_delayed_def, LIST_REL_EL_EQN]
    \\ simp [Once next_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, result_map_def]
    \\ qrefine `ck + 1` \\ simp []
    \\ simp [apply_closure_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, dest_anyClosure_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, subst1_def]
    \\ first_x_assum irule \\ rw []
    >- (
      ntac 2 (goal_assum drule \\ rw [])
      \\ qexists `[Loc n; Int i]` \\ simp [])
    \\ ntac 2 (simp [Once exp_rel_cases])
    \\ simp [monad_cns_def])
  >~ [`Update`] >- (
    `LENGTH l = 3` by (CCONTR_TAC \\ gvs [Once next_delayed_def])
    \\ gvs [LENGTH_EQ_NUM_compute, numeral_less_thm, SF DNF_ss, LUPDATE_DEF]
    \\ simp [Once next_def]
    \\ rgs [Once next_delayed_def, with_atoms_def, result_map_def]
    \\ rpt (CASE_TAC \\ gvs [])
    >- (
      Cases_on `k = 0` \\ gvs []
      >- (qexists `0` \\ simp [])
      \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def]
      \\ qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval y` \\ gvs []
      \\ Cases_on `eval h'` \\ Cases_on `eval y'` \\ gvs []
      \\ Cases_on `eval h''` \\ Cases_on `eval y''` \\ gvs [])
    >- (
      Cases_on `k = 0` \\ gvs []
      >- (qexists `0` \\ simp [])
      \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def]
      \\ qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval y'` \\ gvs []
      \\ Cases_on `eval h` \\ Cases_on `eval y` \\ gvs []
      \\ Cases_on `eval h''` \\ Cases_on `eval y''` \\ gvs [])
  >- (
      Cases_on `k = 0` \\ gvs []
      >- (qexists `0` \\ simp [])
      \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def]
      \\ qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval y''` \\ gvs []
      \\ Cases_on `eval h` \\ Cases_on `eval y` \\ gvs []
      \\ Cases_on `eval h'` \\ Cases_on `eval y'` \\ gvs [])
  >- (qexists `0` \\ simp [])
  >- (
      Cases_on `eval h` \\ gvs [] >- (Cases_on `x` \\ gvs [])
      \\ Cases_on `eval h'` \\ gvs [] >- (Cases_on `x` \\ gvs [])
      \\ Cases_on `eval h''` \\ gvs [] >- (Cases_on `x` \\ gvs [])
      \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def]
      \\ qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval y` \\ Cases_on `eval y'` \\ Cases_on `eval y''`
      \\ gvs []
      \\ qpat_x_assum `v_rel y'3' y'6'` assume_tac
      \\ Cases_on `y'3'` \\ Cases_on `y'6'`
      \\ rgs [Once v_rel_cases, get_atoms_def, state_rel_delayed_def,
              LIST_REL_EL_EQN]
      \\ qrefine `ck + 1` \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, result_map_def]
      \\ qrefine `ck + 1` \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, result_map_def]
      \\ qrefine `ck + 1` \\ simp [apply_closure_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, dest_anyClosure_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, subst1_def]
      \\ first_x_assum irule \\ rw [EL_LUPDATE]
      >- (IF_CASES_TAC \\ gvs [])
      >- (IF_CASES_TAC \\ gvs [])
      \\ ntac 2 (simp [Once exp_rel_cases])
      \\ simp [monad_cns_def])
  >- (
      Cases_on `eval h` \\ gvs [] >- (Cases_on `x` \\ gvs [])
      \\ Cases_on `eval h'` \\ gvs [] >- (Cases_on `x` \\ gvs [])
      \\ Cases_on `eval h''` \\ gvs [] >- (Cases_on `x` \\ gvs [])
      \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def]
      \\ qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval y` \\ Cases_on `eval y'` \\ Cases_on `eval y''`
      \\ gvs []
      \\ qpat_x_assum `v_rel y'3' y'6'` assume_tac
      \\ Cases_on `y'3'` \\ Cases_on `y'6'`
      \\ rgs [Once v_rel_cases, get_atoms_def, state_rel_delayed_def,
              LIST_REL_EL_EQN]
      \\ qrefine `ck + 1` \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, result_map_def]
      \\ qrefine `ck + 1` \\ simp [apply_closure_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, dest_anyClosure_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, subst1_def]
      \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ qrefine `ck + 1` \\ simp []
      \\ first_x_assum irule \\ rw []
      \\ ntac 2 (simp [Once exp_rel_cases])
      \\ simp [monad_cns_def])
  >- (
      Cases_on `eval h` \\ gvs [] >- (Cases_on `x` \\ gvs [])
      \\ Cases_on `eval h'` \\ gvs [] >- (Cases_on `x` \\ gvs [])
      \\ Cases_on `eval h''` \\ gvs [] >- (Cases_on `x` \\ gvs [])
      \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def]
      \\ qrefine `ck + 1` \\ simp [eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ simp [Once next_def, result_map_def]
      \\ imp_res_tac exp_rel_eval \\ gvs []
      \\ Cases_on `eval y` \\ Cases_on `eval y'` \\ Cases_on `eval y''`
      \\ gvs []
      \\ qpat_x_assum `v_rel y'3' y'6'` assume_tac
      \\ Cases_on `y'3'` \\ Cases_on `y'6'`
      \\ rgs [Once v_rel_cases, get_atoms_def, state_rel_delayed_def,
              LIST_REL_EL_EQN]
      \\ qrefine `ck + 1` \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, result_map_def]
      \\ qrefine `ck + 1` \\ simp [apply_closure_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, dest_anyClosure_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def, subst1_def]
      \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ simp [eval_to_def]
      \\ qrefine `ck + 1` \\ simp []
      \\ first_x_assum irule \\ rw []
      \\ ntac 2 (simp [Once exp_rel_cases])
      \\ simp [monad_cns_def]))
QED

Theorem undelay_next_action:
  ($= +++ v_rel) v w ∧
  cont_rel_delayed exp_rel c d ∧
  state_rel_delayed v_rel s t ⇒
    next_action_delayed v c s ≠ Err ⇒
      next_rel (next_action_delayed v c s) (next_action w d t)
Proof
  rw[]
  \\ `∀k. next_delayed k v c s ≠ Err` by (
    CCONTR_TAC \\ qpat_x_assum `next_action_delayed _ _ _ ≠ _` mp_tac
    \\ gvs [next_action_delayed_def] \\ DEEP_INTRO_TAC some_intro \\ rw []
    >- (drule next_delayed_next_delayed \\ disch_then $ qspec_then `k` mp_tac
        \\ simp [])
    >- (qexists `k` \\ simp []))
  \\ qpat_x_assum `next_action_delayed _ _ _ ≠ Err` mp_tac
  \\ simp [next_action_delayed_def] \\ DEEP_INTRO_TAC some_intro
  \\ reverse $ rw []
  >- (
    rw [next_action_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ `next_delayed x v c s ≠ Err` by simp []
    \\ drule_all_then assume_tac undelay_next_thm \\ gvs []
    \\ drule next_less_eq \\ disch_then $ qspec_then `ck + x` mp_tac
    \\ gvs [])
  \\ `next_delayed x v c s ≠ Err` by simp []
  \\ drule_all_then assume_tac undelay_next_thm \\ gvs []
  \\ simp [next_action_def] \\ DEEP_INTRO_TAC some_intro \\ rw [] \\ gvs []
  \\ drule next_next
  \\ disch_then $ qspec_then `ck + x` assume_tac
  \\ Cases_on `next_delayed x v c s` \\ Cases_on `next (ck + x) w d t` \\ gvs []
QED

Theorem interp_action_return[local]:
  interp (INR (Monadic Ret [Lit (Str y)]))
    (BC (Lam "v" (Monad Ret [Delay (Var "v")])) cont) st =
  interp (INR (Monadic Ret [Delay $ Value $ Atom $ Str y])) cont st
Proof
  simp [Once interp_def, next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ reverse $ rw []
  >- (
    pop_assum mp_tac
    \\ simp [Once next_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, result_map_def]
    \\ pop_assum $ qspec_then `SUC n` $ assume_tac o GEN_ALL \\ gvs []
    \\ pop_assum mp_tac
    \\ simp [apply_closure_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, dest_anyClosure_def]
    \\ pop_assum mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, subst1_def]
    \\ simp [Once interp_def, next_action_def])
  \\ reverse $ CASE_TAC \\ gvs []
  >- (
    Cases_on `x` \\ gvs []
    >- (
      pop_assum mp_tac
      \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ rw []
      \\ gvs [eval_to_def, result_map_def])
    \\ pop_assum mp_tac
    \\ simp [Once next_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, result_map_def]
    \\ pop_assum mp_tac
    \\ simp [apply_closure_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, dest_anyClosure_def]
    \\ pop_assum mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, subst1_def]
    \\ simp [Once interp_def, next_action_def]
    \\ DEEP_INTRO_TAC some_intro \\ reverse $ rw []
    >- (qexists `n` \\ rw [])
    \\ qmatch_asmsub_abbrev_tac `next _ v _ _ ≠ Div`
    \\ `next x v cont st = Err` by (
      `next n v cont st ≠ Div` by gvs []
      \\ dxrule_all next_next
      \\ rw [])
    \\ unabbrev_all_tac \\ gvs [])
  >- (
    Cases_on `x` \\ gvs []
    >- (
      pop_assum mp_tac
      \\ simp [Once next_def, with_value_def, eval_def]
      \\ DEEP_INTRO_TAC some_intro \\ rw []
      \\ gvs [eval_to_def, result_map_def])
    \\ pop_assum mp_tac
    \\ simp [Once next_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, result_map_def]
    \\ pop_assum mp_tac
    \\ simp [apply_closure_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, dest_anyClosure_def]
    \\ pop_assum mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, subst1_def]
    \\ simp [Once interp_def, next_action_def]
    \\ DEEP_INTRO_TAC some_intro \\ reverse $ rw []
    >- (qexists `n` \\ rw [])
    \\ qmatch_asmsub_abbrev_tac `next _ v _ _ ≠ Div`
    \\ `next x v cont st = Ret` by (
      `next n v cont st ≠ Div` by gvs []
      \\ dxrule_all next_next
      \\ rw [])
    \\ unabbrev_all_tac \\ gvs [])
  \\ Cases_on `x` \\ gvs []
  >- (
    pop_assum mp_tac
    \\ simp [Once next_def, with_value_def, eval_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ gvs [eval_to_def, result_map_def])
  \\ pop_assum mp_tac
  \\ simp [Once next_def, with_value_def, eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ gvs [eval_to_def, result_map_def]
  \\ pop_assum mp_tac
  \\ simp [apply_closure_def, with_value_def, eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ gvs [eval_to_def, dest_anyClosure_def]
  \\ pop_assum mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ gvs [eval_to_def, subst1_def]
  \\ simp [SimpRHS, Once interp_def, next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ reverse $ rw []
  >- (qexists `n` \\ rw [])
  \\ qmatch_asmsub_abbrev_tac `next _ v _ _ ≠ Div`
  \\ `next x v cont st = Act e c l` by (
    `next n v cont st ≠ Div` by gvs []
    \\ dxrule_all next_next
    \\ rw [])
  \\ unabbrev_all_tac \\ gvs []
QED

Theorem undelay_interp[local]:
  ($= +++ v_rel) v w ∧
  cont_rel_delayed exp_rel c d ∧
  state_rel_delayed v_rel s t ∧
  safe_itree (interp_delayed v c s) ⇒
    interp_delayed v c s = interp w d t
Proof
  rw [Once itreeTheory.itree_bisimulation]
  \\ qexists_tac ‘
    λt1 t2.
      safe_itree t1 ∧
      (t1 = t2 ∨
       ∃v c s w d t.
         t1 = interp_delayed v c s ∧
         t2 = interp w d t ∧
         interp_delayed v c s ≠ Ret Error ∧
         ($= +++ v_rel) v w ∧
         cont_rel_delayed exp_rel c d ∧ state_rel_delayed v_rel s t)’
  \\ rw []
  >- (
    disj2_tac
    \\ irule_at Any EQ_REFL
    \\ irule_at Any EQ_REFL \\ gs []
    \\ strip_tac
    \\ gs [Once safe_itree_cases])
  >- (
    ‘next_action_delayed v' c' s' ≠ Err’
      by (strip_tac
          \\ qpat_x_assum ‘interp_delayed v' _ _ ≠ _’ mp_tac
          \\ rw [Once interp_delayed_def])
    \\ drule_all_then assume_tac undelay_next_action
    \\ qpat_x_assum ‘Ret _ = _’ mp_tac
    \\ once_rewrite_tac [interp_def, interp_delayed_def]
    \\ Cases_on ‘next_action_delayed v' c' s'’
    \\ Cases_on ‘next_action w' d' t''’ \\ gvs [])
  >- (
    ‘next_action_delayed v' c' s' ≠ Err’
      by (strip_tac
          \\ qpat_x_assum ‘interp_delayed v' _ _ = _’ mp_tac
          \\ rw [Once interp_delayed_def])
    \\ drule_all_then assume_tac undelay_next_action
    \\ qpat_x_assum ‘_ = Div’ mp_tac
    \\ once_rewrite_tac [interp_def, interp_delayed_def]
    \\ Cases_on ‘next_action_delayed v' c' s'’
    \\ Cases_on ‘next_action w' d' t''’ \\ gvs [])
  >- (
    rgs [Once safe_itree_cases])
  \\ ‘next_action_delayed v' c' s' ≠ Err’
    by (strip_tac
        \\ qpat_x_assum ‘interp_delayed v' _ _ ≠ _’ mp_tac
        \\ rw [Once interp_delayed_def])
  \\ drule_all_then assume_tac undelay_next_action
  \\ qpat_x_assum ‘Vis _ _ = _’ mp_tac
  \\ rw [Once interp_def, Once interp_delayed_def]
  \\ Cases_on ‘next_action_delayed v' c' s'’
  \\ Cases_on ‘next_action w' d' t''’ \\ gvs []
  \\ rgs [Once safe_itree_cases]
  \\ rw [] \\ CASE_TAC \\ gs [] \\ rw []
  \\ disj2_tac
  \\ irule_at Any EQ_REFL
  \\ simp [interp_action_return]
  \\ irule_at Any EQ_REFL \\ simp[Once exp_rel_cases]
  \\ first_x_assum (qspec_then ‘INR y’ assume_tac)
  \\ rgs [Once safe_itree_cases]
  \\ irule exp_rel_Delay \\ irule exp_rel_LitVal
QED

Theorem semantics_fail[local]:
  safe_itree (semantics_delayed x c s) ⇒
    eval x ≠ INL Type_error
Proof
  simp [semantics_delayed_def, Once interp_delayed_def,
        next_action_delayed_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ rw [] \\ strip_tac \\ gs []
  \\ rgs [Once next_delayed_def]
  \\ rgs [Once safe_itree_cases]
QED

Theorem undelay_semantics:
  exp_rel x y ∧
  closed x ∧
  safe_itree (semantics_delayed x Done []) ⇒
    semantics_delayed x Done [] = semantics y Done []
Proof
  strip_tac
  \\ drule_then assume_tac semantics_fail
  \\ gvs [semantics_delayed_def, semantics_def]
  \\ irule undelay_interp \\ gvs []
  \\ simp [state_rel_delayed_def]
  \\ irule_at Any exp_rel_eval \\ gs []
QED
