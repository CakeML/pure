(*
  The fourth in a series of transformations to simplify case-compilation from
  pureLang to thunkLang. See:
  - [thunk_case_liftProofScript.sml]
  - [thunk_case_d2bProofScript.sml]
  - [thunk_case_inlProofScript.sml]
  - [thunk_case_projProofScript.sml]
  for the others.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_case_unboxProof";

val _ = numLib.prefer_num ();

Theorem SUM_REL_THM[local,simp] = sumTheory.SUM_REL_THM;

Theorem PAIR_REL_def[local,simp] = pairTheory.PAIR_REL;

Inductive exp_rel:
(* Force replacement *)
[exp_rel_Unbox:]
  (∀v.
     exp_rel (Force (Delay (Var v))) (Tick (Var v)))
[exp_rel_Unbox_Value:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Force (Delay (Value v))) (Tick (Value w)))
(* Boilerplate: *)
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
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y))
[exp_rel_Let:]
  (∀b x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let b x1 y1) (Let b x2 y2))
[exp_rel_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL exp_rel [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2))
[exp_rel_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys))
[exp_rel_Monad:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad mop xs) (Monad mop ys))
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
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x))
[v_rel_Constructor:]
  (∀vs ws.
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
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) (DoTick w))
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 exp_rel x y) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n))
[v_rel_Thunk:]
  (∀x y.
     exp_rel x y ⇒
       v_rel (Thunk x) (Thunk y))
End

Theorem v_rel_cases[local] = CONJUNCT2 exp_rel_cases;

Theorem v_rel_def[simp] =
  [ “v_rel (Closure s x) z”,
    “v_rel z (Closure s x)”,
    “v_rel (Recclosure s x) z”,
    “v_rel z (Recclosure s x)”,
    “v_rel (Constructor s x) z”,
    “v_rel z (Constructor s x)”,
    “v_rel (Monadic mop xs) z”,
    “v_rel z (Monadic mop ys)”,
    “v_rel (Atom s) z”,
    “v_rel z (Atom s)”,
    “v_rel (Thunk s) z”,
    “v_rel z (Thunk s)” ]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem exp_rel_subst:
  ∀vs x ws y.
    MAP FST vs = MAP FST ws ∧
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    exp_rel x y ⇒
      exp_rel (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) s) (ALOOKUP (REVERSE ws) s)’
      suffices_by (
        strip_tac
        \\ gs [OPTREL_def, exp_rel_Var, exp_rel_Value])
    \\ irule LIST_REL_OPTREL
    \\ gs [LIST_REL_CONJ, ELIM_UNCURRY, EVERY2_MAP]
    \\ last_x_assum mp_tac
    \\ pop_assum kall_tac
    \\ qid_spec_tac ‘ws’
    \\ Induct_on ‘vs’ \\ simp []
    \\ Cases_on ‘ws’ \\ simp [])
  >- ((* Prim *)
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
  >- ( (* Monad *)
    rw[Once exp_rel_cases] >> gvs[subst_def] >>
    irule exp_rel_Monad >>
    rw[LIST_REL_EL_EQN] >> imp_res_tac LIST_REL_LENGTH >> gvs[EL_MAP] >>
    gvs[MEM_EL, PULL_EXISTS] >> last_x_assum irule >> rw[] >> gvs[LIST_REL_EL_EQN]
    )
  >- ((* If *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_If \\ fs [])
  >- ((* App *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_App \\ fs [])
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ gs [subst_def]
    \\ irule exp_rel_Lam
    \\ first_x_assum irule
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ simp [FORALL_PROD])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ gs [subst_def]
    \\ irule exp_rel_Let \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases] \\ gs []
    \\ gs [subst_def]
    \\ irule exp_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ simp [FORALL_PROD])
  >- ((* Letrec *)
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_Letrec
    \\ gvs [EVERY2_MAP, LAMBDA_PROD]
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ first_x_assum (irule_at Any)
    \\ `MAP FST f = MAP FST g`
      by (irule LIST_EQ
          \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST g)’ \\ fs []
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ irule_at Any LIST_REL_FILTER
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD] \\ rw []
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER, SF SFY_ss]
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD])
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Delay \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def, FILTER_T, ELIM_UNCURRY, exp_rel_Force,
             exp_rel_Unbox_Value]
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      suffices_by (
        strip_tac
        \\ gs [OPTREL_def, exp_rel_Var, exp_rel_Unbox,
               exp_rel_Unbox_Value])
    \\ irule LIST_REL_OPTREL
    \\ gs [LIST_REL_CONJ, ELIM_UNCURRY, EVERY2_MAP]
    \\ qpat_x_assum ‘MAP FST vs = _’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qid_spec_tac ‘ws’
    \\ Induct_on ‘vs’ \\ simp []
    \\ Cases_on ‘ws’ \\ simp [])
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def, exp_rel_Value])
  >- ((* MkTick *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_MkTick \\ gs [])
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
  >~ [‘Var v’] >- (
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Value v’] >- (
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
    >- ((* Closure *)
      IF_CASES_TAC \\ gs []
      \\ rename1 ‘(_ +++ _) (_ _ (subst1 s u1 e1)) (_ _ (subst1 s u2 e2))’
      \\ ‘[s,u1] = [] ++ [s,u1]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ ‘[s,u2] = [] ++ [s,u2]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ first_x_assum irule \\ gs [closed_subst]
      \\ irule_at Any exp_rel_subst
      \\ first_assum (irule_at Any) \\ gs [])
        (* Recclosure *)
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
      by (irule LIST_REL_OPTREL \\ gs []
          \\ gs [ELIM_UNCURRY, LIST_REL_CONJ])
    \\ gs [OPTREL_def]
    \\ rgs [Once exp_rel_cases]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_subst
    \\ first_assum (irule_at Any)
    \\ simp [EVERY2_MAP, LAMBDA_PROD]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ csimp [FORALL_PROD]
    \\ simp [closed_subst, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM
             FST_THM]
    \\ irule_at Any LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY])
  >~ [‘Lam s x’] >- (
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def, v_rel_def])
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
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_subst \\ gs [])
  >~ [‘Letrec f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def, closed_subst, MAP_MAP_o, combinTheory.o_DEF,
             LAMBDA_PROD, GSYM FST_THM]
    \\ irule_at Any exp_rel_subst
    \\ simp [subst_funs_def, closed_subst, MAP_MAP_o, combinTheory.o_DEF,
             LAMBDA_PROD, GSYM FST_THM, EVERY2_MAP]
    \\ irule_at Any LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY])
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
  >~ [‘Force x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    >- (
      once_rewrite_tac [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ simp [Once eval_to_def]
      \\ simp [Once eval_to_def]
      \\ simp [dest_anyThunk_def, subst_funs_def, eval_to_def])
    >- ((* Unbox *)
      once_rewrite_tac [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ simp [Once eval_to_def, subst_funs_def]
      \\ once_rewrite_tac [eval_to_def]
      \\ simp [dest_anyThunk_def, eval_to_def])
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
        \\ ‘OPTREL exp_rel
                   (ALOOKUP (REVERSE xs) s)
                   (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL \\ gs []
              \\ gs [ELIM_UNCURRY, LIST_REL_CONJ])
        \\ gs [OPTREL_def]
        \\ rgs [Once exp_rel_cases]
        \\ first_x_assum irule
        \\ simp [subst_funs_def]
        \\ irule_at Any exp_rel_subst
        \\ gs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
               GSYM FST_THM]
        \\ irule_at Any LIST_REL_mono
        \\ csimp [FORALL_PROD]
        \\ first_assum (irule_at Any)
        \\ simp []
        \\ irule LIST_EQ
        \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY])
      \\ first_x_assum irule
      \\ simp [subst_funs_def, SF SFY_ss])
    \\ ‘∃y. dest_Tick w = SOME y’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_cases])
    \\ gs []
    \\ first_x_assum irule
    \\ rw [Once exp_rel_cases]
    \\ rw [Once exp_rel_cases]
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [Once v_rel_cases])
  >~ [‘Delay x’] >- (
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def])
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
    \\ simp [eval_to_def]
    \\ Cases_on ‘op’ \\ gs [EVERY_EL]
    >- ((* Cons *)
      gs [result_map_def, MEM_MAP, PULL_EXISTS, LIST_REL_EL_EQN, MEM_EL]
      \\ IF_CASES_TAC \\ gs []
      >- (
        gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gvs []
        \\ rw [] \\ gs [])
      \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        >- (
          rename1 ‘j < LENGTH ys’
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ Cases_on ‘eval_to k (EL j xs)’ \\ gs [])
        \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ rw [] \\ gs []
        \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
        \\ last_x_assum $ drule_all
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
      \\ IF_CASES_TAC \\ gs [])
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
  >~ [‘Monad mop xs’]
  >- (rw[Once exp_rel_cases] >> gvs[eval_to_def])
QED

Theorem exp_rel_eval[local] =
  Q.INST [‘allow_error’|->‘T’] eval_to_eval_lift
  |>  SIMP_RULE (srw_ss ()) []
  |> Lib.C MATCH_MP exp_rel_eval_to;

Theorem unbox_apply_closure[local]:
  exp_rel x y ∧
  v_rel v2 w2 ∧
  (∀x y.
     ($= +++ v_rel) x y ⇒
       next_rel v_rel exp_rel (f x) (g y)) ⇒
    next_rel v_rel exp_rel (apply_closure x v2 f) (apply_closure y w2 g)
Proof
  rw[thunk_semanticsTheory.apply_closure_def] >>
  gvs[thunk_semanticsTheory.with_value_def] >>
  dxrule_all_then assume_tac exp_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[] >- (CASE_TAC >> gvs[]) >>
  rename1 `eval x = INR v1` >> rename1 `eval y = INR w1`
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [dest_anyClosure_def]
  >- (
    first_x_assum irule \\ gs []
    \\ irule exp_rel_eval
    \\ irule exp_rel_subst \\ gs [])
  \\ rename1 ‘LIST_REL _ xs ys’
  \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
    by (irule LIST_REL_OPTREL
        \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
  \\ gs [OPTREL_def]
  \\ qpat_x_assum ‘exp_rel x0 y0’ mp_tac
  \\ rw [Once exp_rel_cases] \\ gs []
  \\ first_x_assum irule \\ gs []
  \\ irule exp_rel_eval
  \\ irule exp_rel_subst
  \\ gs [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  \\ irule_at Any LIST_EQ
  \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
QED

Theorem unbox_rel_ok[local]:
  rel_ok T v_rel exp_rel
Proof
  rw [rel_ok_def]
  >- ((* ∀x. f x ≠ Err from rel_ok prevents this case *)
    simp [unbox_apply_closure])
  >- (
    gs [Once v_rel_cases])
  >- ((* Equal literals are related *)
    simp [exp_rel_Prim])
  >- ((* Equal 0-arity conses are related *)
    simp [exp_rel_Prim])
  >- ((* v_rel x y ⇒ exp_rel (Value x) (Value y) *)
    simp [exp_rel_Value])
QED

Theorem unbox_sim_ok[local]:
  sim_ok T v_rel exp_rel
Proof
  rw [sim_ok_def]
  \\ simp [exp_rel_eval]
  \\ irule exp_rel_subst \\ gs []
QED

Theorem case_unbox_semantics:
  exp_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics
  \\ irule_at Any unbox_sim_ok
  \\ irule_at Any unbox_rel_ok \\ gs []
QED

val _ = export_theory ();
