(*
  The second in a series of transformations to simplify case-compilation from
  pureLang to thunkLang. See:
  - [thunk_case_liftProofScript.sml]
  - [thunk_case_inlProofScript.sml]
  - [thunk_case_unboxProofScript.sml]
  - [thunk_case_projProofScript.sml]
  for the others.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_case_d2bProof";

val _ = set_grammar_ancestry ["finite_map", "pred_set", "rich_list",
                              "thunkLang", "wellorder", "thunkLangProps"];

val _ = numLib.prefer_num ();

Theorem SUM_REL_THM[local,simp] = sumTheory.SUM_REL_THM;

Theorem PAIR_REL_def[local,simp] = pairTheory.PAIR_REL;

Inductive exp_rel:
(* Delay-to-Box *)
[exp_rel_D2B:]
  (∀v w x1 x2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ∧
     v ≠ w ⇒
       exp_rel (Let (SOME v) (Delay x1)
                        (Let (SOME w) (Force (Var v)) y1))
                   (Let (SOME w) x2
                        (Let (SOME v) (Delay (Var w)) y2)))
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
    “v_rel (Thunk x) z” ]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem exp_rel_freevars:
  exp_rel x y ⇒ freevars x = freevars y
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ freevars x = freevars y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- rw []
  \\ ho_match_mp_tac exp_rel_strongind
  \\ simp [freevars_def]
  \\ rw []
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs [])
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs []
    \\ fs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN,
           Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
    \\ rw [] \\ gs [EL_MAP, ELIM_UNCURRY, SF CONJ_ss, SF SFY_ss])
  >- (
    Cases_on ‘bv’ \\ gs [freevars_def])
  >- (
    ‘MAP freevars xs = MAP freevars ys’
      suffices_by rw [SF ETA_ss]
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
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
  >- ((* Var *)
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
  >- ((* Prim *)
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw [])
  >- ((* Monad *)
    rw[Once exp_rel_cases] >> gvs[subst_def] >>
    rw[Once exp_rel_cases] >>
    gvs[LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS]
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
    \\ gvs [subst_def]
    \\ irule exp_rel_Lam
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases] \\ gs []
    >- (
      last_x_assum (drule_then (qspec_then ‘Delay x2’ mp_tac))
      \\ simp [Once exp_rel_cases, PULL_EXISTS, subst_def]
      \\ simp [Once exp_rel_cases, PULL_EXISTS]
      \\ strip_tac
      \\ gs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
      \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
      \\ ‘LIST_REL v_rel (MAP SND (FILTER (λ(n,x). P n) vs))
                             (MAP SND (FILTER (λ(n,x). P n) ws))’
        by (gs [EVERY2_MAP]
            \\ irule LIST_REL_FILTER \\ gs []
            \\ gs [LIST_REL_EL_EQN])
      \\ first_x_assum drule
      \\ simp [MAP_FST_FILTER, ELIM_UNCURRY]
      \\ disch_then (qspec_then ‘Let (SOME w) (Force (Var s)) y2’ mp_tac)
      \\ simp [Once exp_rel_cases]
      \\ simp [Once exp_rel_cases]
      \\ simp [Once exp_rel_cases]
      \\ simp [Once exp_rel_cases, PULL_EXISTS, subst_def,
               GSYM FILTER_REVERSE, ALOOKUP_FILTER, LAMBDA_PROD]
      \\ simp [Once exp_rel_cases]
      \\ simp [Once exp_rel_cases]
      \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) s) (ALOOKUP (REVERSE ws) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ]
            \\ qpat_x_assum ‘MAP _ _ = _’ mp_tac
            \\ qid_spec_tac ‘ws’
            \\ qid_spec_tac ‘vs’
            \\ Induct \\ simp []
            \\ gen_tac \\ Cases \\ simp [])
      \\ gs [OPTREL_def, FILTER_FILTER, LAMBDA_PROD]
      \\ rw [] \\ gs []
      \\ irule exp_rel_D2B
      \\ gs [AC CONJ_COMM CONJ_ASSOC])
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Letrec *)
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
  >- ((* Delay *)
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
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Force \\ fs [])
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ rw [Once exp_rel_cases])
  >- ((* MkTick *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_MkTick
    \\ first_x_assum irule \\ gs [])
QED

Definition d2b_goal_def:
  d2b_goal k x =
    ∀y.
      exp_rel x y ∧
      (∀k. eval_to k x ≠ INL Type_error) ⇒
      ∃j.
        ($= +++ v_rel)
          (eval_to (j + k) x)
          (eval_to k y)
End

Theorem eval_to_WF_IND[local] =
  WF_IND
  |> GEN_ALL
  |> Q.ISPEC ‘eval_to_wo’
  |> REWRITE_RULE [eval_to_wo_WF]
  |> Q.SPEC ‘UNCURRY d2b_goal’
  |> SIMP_RULE std_ss [FORALL_PROD]

Theorem exp_rel_eval_to:
  ∀k x. d2b_goal k x
Proof
  ho_match_mp_tac eval_to_WF_IND
  \\ once_rewrite_tac [d2b_goal_def]
  \\ gen_tac
  \\ Cases \\ gs []
  >~ [‘Var v’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘App f x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x y’
    \\ simp [eval_to_def]
    \\ ‘∀k. eval_to k x ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ first_x_assum (qspec_then ‘j’ mp_tac)
          \\ simp [eval_to_def])
    \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k) x’
      \\ gs [])
    \\ ‘∃u1. eval_to k y = INR u1’
      by (Cases_on ‘eval_to k y’ \\ gs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ simp []
    \\ ‘∀k. eval_to k f ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (App _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ ‘eval_to (j1 + k + j) f = eval_to j f’
            by (irule eval_to_mono \\ gs [])
          \\ ‘eval_to (j1 + k + j) x = eval_to (j1 + k) x’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs [])
          \\ qexists_tac ‘j1 + k + j’ \\ simp []
          \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + k) f) (eval_to k g)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ ‘∃u2. eval_to (j1 + k) x = INR u2’
      by (Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ gs []
    \\ Cases_on ‘eval_to k g’ \\ gs []
    >- (
      rename1 ‘_ = INL err’
      \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k) f’ \\ gvs []
      \\ Cases_on ‘eval_to k x = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k) x = eval_to k x’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k x’ \\ gs []
      \\ Cases_on ‘eval_to k f’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ gs []
        \\ qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k) f = eval_to k f’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k f’ \\ gs [])
    \\ rename1 ‘eval_to k g = INR v1’
    \\ ‘∃v2. eval_to (j2 + k) f = INR v2’
      by (Cases_on ‘eval_to (j2 + k) f’ \\ gs [])
    \\ gs []
    \\ ‘∀j. eval_to (j + j1 + k) x = eval_to (j1 + k) x’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ ‘∀j. eval_to (j + j2 + k) f = eval_to (j2 + k) f’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Cases_on ‘dest_anyClosure v1’ \\ gs []
    >- (
      qexists_tac ‘j1 + j2’ \\ gs []
      \\ once_rewrite_tac [DECIDE “j1 + (j2 + k) = j2 + (j1 + k)”]
      \\ gs []
      \\ Cases_on ‘v2’ \\ Cases_on ‘v1’ \\ gvs [dest_anyClosure_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs [])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘subst (ws2 ++ [s2,w2]) b2’
    \\ ‘∃b1 ws1. dest_anyClosure v2 = INR (s2,b1,ws1) ∧
                 exp_rel b1 b2 ∧
                 LIST_REL (λ(f,v) (g,w). f = g ∧ v_rel v w) ws1 ws2’
      by (Cases_on ‘v2’ \\ Cases_on ‘v1’ \\ gvs [dest_anyClosure_def]
          \\ rename1 ‘LIST_REL _ xs ys’
          \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL \\ gs [])
          \\ gs [OPTREL_def]
          \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gs []
          \\ gvs [EVERY2_MAP, LAMBDA_PROD]
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j x = eval_to 0 x’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ Cases_on ‘eval_to 0 f = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j f = eval_to 0 f’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ qexists_tac ‘0’ \\ simp [])
    \\ ‘∀k. eval_to k (subst (ws1 ++ [s2,u2]) b1) ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (App _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j1 + j2 + j + k’ \\ gs []
          \\ once_rewrite_tac
            [DECIDE “j + (j1 + (j2 + k)) = (j + j1) + (j2 + k)”] \\ gs []
          \\ once_rewrite_tac
            [DECIDE “j + (j1 + (j2 + k)) = (j + j2) + (j1 + k)”] \\ gs []
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ simp [])
    \\ Cases_on ‘eval_to (k - 1) (subst (ws2 ++ [s2,w2]) b2) = INL Diverge’
    >- (
      Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x = eval_to k x’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) f = eval_to k f’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ ‘∀j. j + k - 1 = j + (k - 1)’
        by gs []
      \\ asm_simp_tac bool_ss []
      \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def]
      \\ irule exp_rel_subst
      \\ gs [EVERY2_MAP, LIST_REL_CONJ, ELIM_UNCURRY]
      \\ irule LIST_EQ
      \\ gvs [EL_MAP, LIST_REL_EL_EQN])
    \\ Q.REFINE_EXISTS_TAC ‘j1 + j2 + j’ \\ gs []
    \\ once_rewrite_tac
      [DECIDE “j + (j1 + (j2 + k)) = (j + j2) + (j1 + k)”] \\ gs []
    \\ once_rewrite_tac
      [DECIDE “j + (j1 + (j2 + k)) = (j + j1) + (j2 + k)”] \\ gs []
    \\ qmatch_goalsub_abbrev_tac ‘_ (eval_to _ X1) (eval_to _ X2)’
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) X1) (eval_to (k - 1) X2)’
      by (first_x_assum irule
          \\ gs [Abbr ‘X1’, Abbr ‘X2’, eval_to_wo_def]
          \\ irule exp_rel_subst
          \\ gvs [EVERY2_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY]
          \\ irule LIST_EQ
          \\ gs [EL_MAP])
    \\ qexists_tac ‘j’
    \\ ‘eval_to (j + k - 1) X1 ≠ INL Diverge’
      by (strip_tac \\ Cases_on ‘eval_to (k - 1) X2’ \\ gs [])
    \\ drule_then (qspec_then ‘j + j1 + j2 + k - 1’ assume_tac) eval_to_mono
    \\ gs [])
  >~ [‘Lam s x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Letrec f x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ rename1 ‘exp_rel x y’
    \\ ‘∀j. j + k - 1 = j + (k - 1)’
      by gs []
    \\ asm_simp_tac std_ss []
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def, exp_size_def, subst_funs_def]
    \\ irule_at Any exp_rel_subst
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
             GSYM FST_THM]
    \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
    \\ irule_at Any LIST_EQ
    \\ gs [EL_MAP]
    \\ qx_gen_tac ‘j’
    \\ strip_tac
    \\ qpat_x_assum ‘∀k. eval_to _ (Letrec _ _) ≠ _’ mp_tac
    \\ simp [eval_to_def, subst_funs_def]
    \\ qexists_tac ‘j + 1’ \\ simp [ELIM_UNCURRY])
  >~ [‘Force x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x y’
    \\ CONV_TAC (QUANT_CONV (LAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ CONV_TAC (QUANT_CONV (RAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def]
          \\ qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
          \\ simp [Once eval_to_def]
          \\ qexists_tac ‘j + 1’ \\ simp []
          \\ ‘eval_to (j + 1) x = eval_to j x’
            suffices_by rw []
          \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘eval_to k y = INL Diverge’
    >- (
      Cases_on ‘eval_to k x = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x = eval_to k x’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k x’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gvs []
    >- (
      qexists_tac ‘j’
      \\ simp [])
    \\ rename1 ‘v_rel v w’
    \\ ‘OPTREL v_rel (dest_Tick v) (dest_Tick w)’
      by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
          \\ gs [Once (CONJUNCT2 exp_rel_cases)])
    \\ gs [OPTREL_def]
    >~ [‘dest_Tick _ = SOME _’] >- (
      Cases_on ‘eval_to (k - 1) (Force (Value y0)) = INL Diverge’
      >- (
        Cases_on ‘eval_to k x = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k) x = eval_to k x’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ gs []
        \\ ‘∀j. j + k - 1 = j + (k - 1)’
          by gs []
        \\ asm_simp_tac std_ss []
        \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
        \\ first_x_assum irule
        \\ simp [eval_to_wo_def]
        \\ irule_at Any exp_rel_Force
        \\ irule_at Any exp_rel_Value
        \\ gs []
        \\ qx_gen_tac ‘j’
        \\ strip_tac
        \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _ ’ mp_tac
        \\ simp [Once eval_to_def]
        \\ qexists_tac ‘j + k’
        \\ asm_simp_tac std_ss []
        \\ simp []
        \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
        \\ irule eval_to_mono \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ qsuff_tac ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1))
                                           (Force (Value x0)))
                                  (eval_to ( k - 1)
                                           (Force (Value y0)))’
      >- (
        disch_then (qx_choose_then ‘j1’ assume_tac)
        \\ ‘eval_to (j1 + j + k - 1) (Force (Value x0)) =
            eval_to (j1 + k - 1) (Force (Value x0))’
          by (irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs []
              \\ Cases_on ‘eval_to (k - 1) (Force (Value y0))’ \\ gs [])
        \\ qexists_tac ‘j1’ \\ gs [])
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def, exp_size_def]
      \\ irule_at Any exp_rel_Force
      \\ irule_at Any exp_rel_Value \\ gs []
      \\ qx_gen_tac ‘j1’
      \\ strip_tac
      \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _ ’ mp_tac
      \\ simp [Once eval_to_def]
      \\ qexists_tac ‘j + (j1 + k)’
      \\ asm_simp_tac std_ss []
      \\ simp []
      \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
      \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘dest_anyThunk w’ \\ gs []
    >- (
      qexists_tac ‘j’ \\ gs []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ rgs [Once exp_rel_cases])
    \\ pairarg_tac \\ gvs []
    \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
    >- (
      rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ rgs [Once exp_rel_cases] \\ rw []
      \\ rename1 ‘exp_rel x1 y1’
      THEN (
        Cases_on ‘eval_to (k - 1) (subst_funs binds y1) = INL Diverge’
        >- (
          Cases_on ‘eval_to k x = INL Diverge’
          >- (
            qexists_tac ‘0’
            \\ simp [])
          \\ ‘∀j1. eval_to (j1 + k) x = eval_to (j + k) x’
            by (gen_tac
                \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
                \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
                \\ gs [])
          \\ gs []
          \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
          \\ asm_simp_tac std_ss []
          \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
          \\ first_x_assum irule
          \\ gs [eval_to_wo_def, subst_funs_def]
          \\ irule_at Any exp_rel_subst
          \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                   EVERY2_MAP]
          \\ gvs [LIST_REL_EL_EQN, LIST_REL_CONJ, ELIM_UNCURRY]
          \\ irule_at Any LIST_EQ \\ gvs [EL_MAP]
          \\ qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
          \\ simp [Once eval_to_def]
          \\ qexists_tac ‘j + k’
          \\ simp [dest_anyThunk_def, subst_funs_def, ELIM_UNCURRY]
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ gs [])
        \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
        \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) (subst_funs xs x1))
                                   (eval_to (k - 1) (subst_funs binds y1))’
          suffices_by (
            disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ ‘eval_to (j1 + j + k - 1) (subst_funs xs x1) =
                eval_to (j1 + k - 1) (subst_funs xs x1)’
              by (irule eval_to_mono \\ gs []
                  \\ strip_tac \\ gs []
                  \\ Cases_on ‘eval_to (k - 1) (subst_funs binds y1)’ \\ gs [])
            \\ qexists_tac ‘j1’ \\ gs [])
        \\ first_x_assum irule
        \\ gs [eval_to_wo_def, subst_funs_def]
        \\ irule_at Any exp_rel_subst
        \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                 EVERY2_MAP]
        \\ gvs [LIST_REL_EL_EQN, LIST_REL_CONJ, ELIM_UNCURRY]
        \\ irule_at Any LIST_EQ \\ gvs [EL_MAP]
        \\ qx_gen_tac ‘j1’
        \\ strip_tac
        \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
        \\ simp [Once eval_to_def]
        \\ qexists_tac ‘j + (j1 + k)’
        \\ asm_simp_tac std_ss []
        \\ simp [dest_anyThunk_def, subst_funs_def, ELIM_UNCURRY]
        \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
        \\ irule eval_to_mono \\ gs []))
    \\ simp [subst_funs_def]
    \\ Cases_on ‘v’ \\ gs [v_rel_def]
    \\ rename1 ‘exp_rel x1 y1’
    \\ Cases_on ‘eval_to (k - 1) y1 = INL Diverge’
    >- (
    Cases_on ‘eval_to k x = INL Diverge’
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀j. eval_to (j + k) x = eval_to k x’
      by (gen_tac \\ irule eval_to_mono \\ gs [])
    \\ gvs []
    \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
    \\ asm_simp_tac std_ss []
    \\ qpat_assum `_ = INL Diverge` (SUBST1_TAC o SYM)
    \\ first_x_assum irule
    \\ gs [eval_to_wo_def]
    \\ qx_gen_tac ‘j’
    \\ strip_tac
    \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
    \\ simp [Once eval_to_def]
    \\ qexists_tac ‘j + k’
    \\ asm_simp_tac std_ss []
    \\ simp [dest_anyThunk_def, subst_funs_def]
    \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
    \\ irule eval_to_mono \\ gs [])
    \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
      by (gen_tac \\ irule eval_to_mono \\ gs [])
    \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1)
                           (eval_to (k - 1) y1)’
      suffices_by (
      disch_then (qx_choose_then ‘j1’ assume_tac)
      \\ ‘eval_to (j1 + j + k - 1) x1 =
          eval_to (j1 + k - 1) x1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs []
            \\ Cases_on ‘eval_to (k - 1) y1’ \\ gs [])
      \\ qexists_tac ‘j1’ \\ gs [])
    \\ first_x_assum irule
    \\ gs [eval_to_wo_def]
    \\ qx_gen_tac ‘j1’
    \\ strip_tac
    \\ qpat_x_assum ‘∀k. eval_to _ (Force _) ≠ _’ mp_tac
    \\ simp [Once eval_to_def]
    \\ qexists_tac ‘j + (j1 + k)’
    \\ asm_simp_tac std_ss []
    \\ simp [dest_anyThunk_def, subst_funs_def]
    \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
    \\ irule eval_to_mono \\ gs [])
  >~ [‘If x1 y1 z1’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (If _ _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j + 1’ \\ gs [])
    \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + (k - 1)) x1)
                                (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >- (
      rename1 ‘_ = INL err’
      \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gvs []
      \\ qexists_tac ‘j1’ \\ simp [])
    \\ IF_CASES_TAC \\ gs []
    >- (
      ‘∀k. eval_to k y1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (If _ _ _) ≠ _’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + j1 + k’ \\ gs []
            \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j1 + k - 1) x1’
              suffices_by (
                rw []
                \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
                \\ qpat_assum ‘eval_to j y1 = _’ (SUBST1_TAC o SYM)
                \\ irule eval_to_mono \\ gs [])
            \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + (k - 1)) y1)
                                  (eval_to (k - 1) y2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k - 1) y1’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘eval_to (j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
          by (drule_then (qspec_then ‘j1 + k - 1’ assume_tac ) eval_to_mono
              \\ drule_then (qspec_then ‘j2 + k - 1’ assume_tac ) eval_to_mono
              \\ gs [])
        \\ qexists_tac ‘j2’ \\ gs []
        \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
      \\ qexists_tac ‘j1 + j2’
      \\ ‘eval_to (j1 + j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
      \\ ‘eval_to (j1 + j2 + k - 1) y1 = eval_to (j2 + k - 1) y1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j2 + k - 1) y1’ \\ gs [])
    \\ IF_CASES_TAC \\ gs []
    >- (
      ‘∀k. eval_to k z1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (If _ _ _) ≠ _’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + j1 + k’ \\ gs []
            \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j1 + k - 1) x1’
              suffices_by (
                rw []
                \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
                \\ qpat_assum ‘eval_to j z1 = _’ (SUBST1_TAC o SYM)
                \\ irule eval_to_mono \\ gs [])
            \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + (k - 1)) z1)
                                  (eval_to (k - 1) z2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) z2’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k - 1) z1’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘eval_to (j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
          by (drule_then (qspec_then ‘j1 + k - 1’ assume_tac ) eval_to_mono
              \\ drule_then (qspec_then ‘j2 + k - 1’ assume_tac ) eval_to_mono
              \\ gs [])
        \\ qexists_tac ‘j2’ \\ gs []
        \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
      \\ qexists_tac ‘j1 + j2’
      \\ ‘eval_to (j1 + j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
      \\ ‘eval_to (j1 + j2 + k - 1) z1 = eval_to (j2 + k - 1) z1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j2 + k - 1) z1’ \\ gs [])
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [])
  >~ [‘Delay x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘MkTick x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x y’
    \\ simp [eval_to_def]
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + k) x) (eval_to k y)’
      suffices_by (
        disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gs []
        \\ irule v_rel_DoTick \\ gs [])
    \\ first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def]
    \\ rpt strip_tac
    \\ first_x_assum (qspec_then ‘k’ mp_tac)
    \\ simp [eval_to_def])
  >~ [‘Value v’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Let bv x1 y1’] >- (
    Cases_on ‘bv’
    >~ [‘Let (SOME s) x1 y1’] >- (
      strip_tac
      \\ rw [Once exp_rel_cases]
      >- ((* D2B *) cheat
(*        pop_assum mp_tac
        \\ simp [Once eval_to_def]
        \\ simp [Once eval_to_def, subst_def]
        \\ simp [Once eval_to_def]
        \\ simp [Once eval_to_def]
        \\ simp [Once eval_to_def, dest_anyThunk_def, subst_funs_def]
        \\ strip_tac
        \\ rename1 ‘exp_rel x1 x2’ \\ rename1 ‘exp_rel y1 y2’
        \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
          by (qx_gen_tac ‘j’
              \\ strip_tac
              \\ qpat_x_assum ‘∀k. _ ≠ _’ mp_tac \\ simp []
              \\ qexists_tac ‘j + 3’ \\ simp [])
        \\ once_rewrite_tac [eval_to_def]
        \\ IF_CASES_TAC \\ gs []
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ simp [Once eval_to_def, subst_def]
        \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + (k - 1)) x1)
                                    (eval_to (k - 1) x2)’
          by (first_x_assum irule
              \\ simp [eval_to_wo_def])
        \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
        >- (
          rename1 ‘_ = INL err’
          \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
          \\ simp [Once eval_to_def, Once eval_to_def, Once eval_to_def,
                   dest_anyThunk_def, subst_funs_def]
          \\ qexists_tac ‘j1 + 2’
          \\ simp [])
        \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
        \\ rename1 ‘v_rel v u’
        \\ ‘∀k. eval_to k (subst1 w v (subst1 s (Thunk x1) y1)) ≠
                INL Type_error’
          by (qx_gen_tac ‘j’
              \\ strip_tac
              \\ qpat_x_assum ‘∀k. (COND _ _ _) ≠ _’ mp_tac \\ simp []
              \\ qexists_tac ‘j + j1 + k + 2’
              \\ simp []
              \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j1 + k -1) x1’
                by (irule eval_to_mono \\ gs []) \\ gs []
              \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
              \\ irule eval_to_mono \\ simp [])
        \\ qpat_x_assum ‘∀k. COND _ _ _ ≠ _’ kall_tac
        \\ once_rewrite_tac [eval_to_def] \\ simp []
        \\ IF_CASES_TAC \\ gs []
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ once_rewrite_tac [eval_to_def] \\ simp []
        \\ once_rewrite_tac [eval_to_def]
        \\ simp [dest_anyThunk_def, subst_funs_def]
        \\ simp [Once subst1_commutes]
        \\ qmatch_goalsub_abbrev_tac ‘_ _ (eval_to _ X2)’
        \\ Cases_on ‘eval_to (k - 2) X2 = INL Diverge’ \\ gs [Abbr ‘X2’]
        >- (
          Cases_on ‘eval_to (k - 3) x1 = INL Diverge’ \\ gs []
          >- (
            qexists_tac ‘0’
            \\ simp [])
          \\ ‘∀j. eval_to (j + k - 3) x1 = eval_to (j1 + k - 1) x1’
            by (qx_gen_tac ‘j2’
                \\ drule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono
                \\ drule_then (qspec_then ‘j2 + k - 3’ assume_tac) eval_to_mono
                \\ gs [])
          \\ gs []
          \\ Cases_on ‘k ≤ 2’ \\ gs []
          >- (
            qexists_tac ‘0’
            \\ simp [])
          \\ ‘∀j. j + k - 2 = j + (k - 2)’ by gs []
          \\ asm_simp_tac std_ss []
          \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
          \\ first_x_assum irule
          \\ simp [eval_to_wo_def, subst1_commutes]
          \\ irule exp_rel_subst \\ simp []
          \\ irule exp_rel_subst \\ simp []
          \\ irule v_rel_D2B
          \\ gs [SF SFY_ss])
        \\ Q.REFINE_EXISTS_TAC ‘2 + j’ \\ simp []
        \\ qabbrev_tac ‘X1 = subst1 s (Thunk x1) (subst1 w v y1) ’
        \\ qmatch_goalsub_abbrev_tac ‘_ _ (eval_to _ X2)’
        \\ ‘∃j2. ($= +++ v_rel) (eval_to (j2 + (k - 2)) X1)
                                    (eval_to (k - 2) X2)’
          by (first_x_assum irule
              \\ gs [Abbr ‘X1’, Abbr ‘X2’, eval_to_wo_def, subst1_commutes]
              \\ irule exp_rel_subst \\ simp []
              \\ irule exp_rel_subst \\ simp []
              \\ irule v_rel_D2B
              \\ gs [SF SFY_ss])
        \\ qexists_tac ‘j1 + j2’
        \\ ‘eval_to (j1 + j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
          by (irule eval_to_mono \\ gs [])
        \\ gs []
        \\ Cases_on ‘eval_to (j2 + k - 2) X1’ \\ gs [subst1_commutes]
        >- (
          rename1 ‘_ = INL err’ \\ Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to (k - 2) X2’ \\ gs [])
        \\ Cases_on ‘eval_to (k - 2) X2’ \\ gs []
        \\ ‘eval_to (j1 + j2 + k) X1 = eval_to (j2 + k - 2) X1’
          suffices_by rw []
        \\ irule eval_to_mono \\ gs []*))
      \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
        by (qx_gen_tac ‘j’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + 1’
            \\ simp [])
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1)
                                 (eval_to (k - 1) x2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      >- (
        qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
        by (gen_tac \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ rename1 ‘v_rel u v’
      \\ ‘∀k. eval_to k (subst1 s u y1) ≠ INL Type_error’
        by (qx_gen_tac ‘j1’
            \\ strip_tac
            \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + j1 + k’ \\ simp []
            \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
            \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to (k - 1) (subst1 s v y2) = INL Diverge’
      >- (
        Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (k - 1) x1’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
        \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
        \\ asm_simp_tac std_ss []
        \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
        \\ first_x_assum irule
        \\ rgs [eval_to_wo_def]
        \\ irule exp_rel_subst \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) (eval_to _ lhs) (eval_to _ rhs)’
      \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) lhs)
                                 (eval_to (k - 1) rhs)’
        suffices_by (
          disch_then (qx_choose_then ‘j1’ assume_tac)
          \\ qexists_tac ‘j1’
          \\ ‘eval_to (j + j1 + k - 1) lhs = eval_to (j1 + k - 1) lhs’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs []
                \\ Cases_on ‘eval_to (k - 1) rhs’ \\ gs [])
          \\ gs [])
      \\ first_x_assum irule
      \\ unabbrev_all_tac
      \\ gs [eval_to_wo_def, subst1_commutes]
      \\ irule exp_rel_subst \\ gs [])
    \\ strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j + 1’
          \\ simp [])
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) x1) (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >- (
      qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
    \\ ‘∀k. eval_to k y1 ≠ INL Type_error’
      by (qx_gen_tac ‘j1’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j1 + j + k’ \\ simp []
          \\ ‘eval_to (j + (j1 + k) - 1) x1 = eval_to (j + k - 1) x1’
            by (irule eval_to_mono \\ gs [])
          \\ simp []
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ simp [])
    \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (k - 1) x1’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
      \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
      \\ asm_simp_tac std_ss []
      \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def])
    \\ ‘∀j1. eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
      by (gen_tac \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Q.REFINE_EXISTS_TAC ‘j + j1’ \\ gs []
    \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
    \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) (eval_to _ lhs) (eval_to _ rhs)’
    \\ ‘∃j. ($= +++ v_rel) (eval_to (j + (k - 1)) lhs)
                               (eval_to (k - 1) rhs)’
      suffices_by (
        disch_then (qx_choose_then ‘j1’ assume_tac)
        \\ qexists_tac ‘j1’
        \\ ‘eval_to (j + j1 + k - 1) lhs = eval_to (j1 + k - 1) lhs’
          by (irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs []
              \\ Cases_on ‘eval_to (k - 1) rhs’ \\ gs [])
        \\ gs [])
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def])
  >~ [‘Prim op xs’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ gvs [LIST_REL_EL_EQN]
    \\ ‘∀n. n < LENGTH xs ⇒ ∀k. eval_to k (EL n xs) ≠ INL Type_error’
      by (ntac 2 strip_tac
          \\ qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ Cases_on ‘op’ \\ gs []
          >- (
            simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
            \\ qexists_tac ‘j’
            \\ gs [SF SFY_ss])
          >- (
            IF_CASES_TAC \\ gs []
            \\ gs [DECIDE “n < 1n ⇔ n = 0”]
            \\ gvs [LENGTH_EQ_NUM_compute]
            \\ qexists_tac ‘j + 1’
            \\ simp [])
          >- (
            IF_CASES_TAC \\ gs []
            \\ gs [DECIDE “n < 1n ⇔ n = 0”]
            \\ gvs [LENGTH_EQ_NUM_compute]
            \\ qexists_tac ‘j + 1’
            \\ simp [])
          \\ qexists_tac ‘j + 1’ \\ simp []
          \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
          \\ ‘result_map f xs = INL Type_error’
            suffices_by rw []
          \\ simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
          \\ gs [Abbr ‘f’]
          \\ IF_CASES_TAC \\ gs [])
    \\ ‘∀j. j ≤ k ⇒
          ∀n. n < LENGTH xs ⇒
            ∃m. ($= +++ v_rel) (eval_to (m + j) (EL n xs))
                                   (eval_to j (EL n ys))’
      by (qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ kall_tac
          \\ rpt (pop_assum mp_tac)
          \\ qid_spec_tac ‘ys’
          \\ Induct_on ‘xs’ \\ simp []
          \\ Cases_on ‘ys’ \\ simp []
          \\ qx_gen_tac ‘x’
          \\ rpt strip_tac
          \\ rename1 ‘_ _ (_ _ (EL _ (y::ys)))’
          \\ last_x_assum (qspec_then ‘ys’ mp_tac)
          \\ simp [AND_IMP_INTRO]
          \\ impl_tac
          >- (
            reverse conj_tac
            >- (
              qx_gen_tac ‘m’ \\ strip_tac
              \\ first_x_assum (qspec_then ‘SUC m’ assume_tac)
              \\ gs [])
            \\ reverse conj_tac
            >- (
              qx_gen_tac ‘m’ \\ strip_tac
              \\ first_x_assum (qspec_then ‘SUC m’ assume_tac)
              \\ first_x_assum (qspec_then ‘SUC m’ assume_tac)
              \\ gs [])
            \\ qx_gen_tac ‘k1’ \\ qx_gen_tac ‘x1’ \\ rw []
            \\ gvs [eval_to_wo_def]
            \\ first_x_assum (irule_at Any)
            \\ gs [exp_size_def])
          \\ strip_tac
          \\ Cases_on ‘n’ \\ gs []
          \\ once_rewrite_tac [arithmeticTheory.ADD_COMM]
          \\ first_x_assum (irule_at Any)
          \\ simp [eval_to_wo_def, exp_size_def]
          \\ qpat_x_assum ‘∀n. n < SUC _ ⇒ _’ (qspec_then ‘0’ assume_tac)
          \\ gs []
          \\ qpat_x_assum ‘∀n. n < SUC _ ⇒ _’ (qspec_then ‘0’ assume_tac)
          \\ gs [])
    \\ last_x_assum kall_tac
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      first_x_assum (qspec_then ‘k’ assume_tac) \\ gs []
      \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ kall_tac
      \\ ‘∃j. ($= +++ (LIST_REL v_rel))
                (result_map (λx. eval_to (j + k) x) xs)
                (result_map (λx. eval_to k x) ys)’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’
          \\ Cases_on ‘result_map (λx. eval_to (j + k) x ) xs’
          \\ Cases_on ‘result_map (λx. eval_to k x) ys’ \\ gs [])
      \\ ‘result_map (λx. eval_to k x) ys ≠ INL Type_error’
        by (gvs [result_map_def, CaseEq "bool"]
            \\ strip_tac
            \\ gs [Once MEM_EL, PULL_EXISTS, EL_MAP]
            \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
            \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs [])
      \\ Cases_on ‘result_map (λx. eval_to k x) ys’ \\ gs []
      >- (
        rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs []
        \\ gs [result_map_def, MEM_EL, PULL_EXISTS, CaseEq "bool", EL_MAP,
               SF CONJ_ss]
        \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs []
        \\ qexists_tac ‘j’
        \\ simp [SF SFY_ss])
      \\ gs [result_map_def, MEM_EL, PULL_EXISTS, CaseEq "bool", EL_MAP,
             SF CONJ_ss]
      \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ ‘∃m. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to (k + m) (EL n xs))
                                   (eval_to k (EL n ys))’
        suffices_by (
          disch_then (qx_choose_then ‘m’ assume_tac)
          \\ qexists_tac ‘m’
          \\ IF_CASES_TAC \\ gs []
          >- (
            first_x_assum (drule_then assume_tac) \\ gs []
            \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
          \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
          \\ rw [EVERY2_MAP, LIST_REL_EL_EQN]
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
          >- (
            rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
          \\ Cases_on ‘eval_to (k + m) (EL n xs)’ \\ gs [])
      \\ gvs []
      \\ rpt (pop_assum mp_tac)
      \\ qid_spec_tac ‘ys’
      \\ Induct_on ‘xs’ \\ simp []
      \\ Cases_on ‘ys’ \\ simp []
      \\ qx_gen_tac ‘x’
      \\ rename1 ‘_ (EL _ _) (EL _ (y::ys))’ \\ rw []
      \\ first_x_assum (qspec_then ‘ys’ mp_tac)
      \\ simp [AND_IMP_INTRO]
      \\ impl_tac
      >- (
        rw []
        \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
        \\ res_tac \\ fs []
        \\ gs [SF SFY_ss])
      \\ disch_then (qx_choose_then ‘m’ assume_tac)
      \\ qpat_x_assum ‘∀n. _ ⇒ ∃m. _’ (qspec_then ‘0’ mp_tac)
      \\ simp []
      \\ disch_then (qx_choose_then ‘m1’ assume_tac)
      \\ qexists_tac ‘m + m1’
      \\ Cases \\ gs []
      >- (
        ‘eval_to (k + (m + m1)) x = eval_to (k + m1) x’
          by (irule eval_to_mono \\ simp []
              \\ strip_tac \\ gs []
              \\ Cases_on ‘eval_to k y’ \\ gs []
              \\ ‘0 < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs [])
        \\ gs [])
      \\ strip_tac
      \\ rename1 ‘n < LENGTH ys’
      \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
      \\ res_tac \\ fs []
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
      >- (
        rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
      \\ ‘eval_to (k + (m + m1)) (EL n xs) = eval_to (k + m) (EL n xs)’
        by (irule eval_to_mono \\ simp []
            \\ strip_tac \\ gs [])
      \\ gs [])
    >- ((* IsEq *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
        \\ qexists_tac ‘m’ \\ simp [])
      \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ qexists_tac ‘m’ \\ simp []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* Proj *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
        \\ qexists_tac ‘m’ \\ simp [])
      \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ qexists_tac ‘m’ \\ simp []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* AtomOp *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ Cases_on ‘k = 0’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [result_map_def, MEM_MAP, GSYM NOT_NULL_MEM, NULL_EQ]
        \\ Cases_on ‘xs’ \\ Cases_on ‘ys’ \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [])
      \\ qabbrev_tac ‘f = λj x. case eval_to (j + k - 1) x of
                                  INR (Atom l) => INR l
                                | INL err => INL err
                                | _ => INL Type_error’
      \\ qabbrev_tac ‘g = λx. case eval_to (k - 1) x of
                                INR (Atom l) => INR l
                              | INL err => INL err
                              | _ => INL Type_error’
      \\ gs []
      \\ ‘∃j. result_map (f j) xs = result_map g ys’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’
          \\ simp [SF ETA_ss]
          \\ Cases_on ‘result_map g ys’ \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [])
      \\ ‘∀j. result_map (f j) xs ≠ INL Type_error’
        by (rpt strip_tac
            \\ gs [result_map_def, MEM_EL, EL_MAP, SF CONJ_ss,
                   CaseEq "bool", Abbr ‘f’]
            \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ INL _’ mp_tac \\ simp []
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j + k’
            \\ simp [result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS]
            \\ IF_CASES_TAC \\ gs [])
      \\ qpat_x_assum ‘∀k. eval_to _ (Prim _ _) ≠ _’ kall_tac
      \\ Cases_on ‘result_map g ys = INL Diverge’ \\ gs []
      >- (
        unabbrev_all_tac \\ gs []
        \\ rgs [result_map_def, CaseEq "bool", MEM_MAP]
        \\ rgs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ gvs [MEM_EL, PULL_EXISTS]
        \\ first_x_assum drule
        \\ pop_assum mp_tac
        \\ rpt CASE_TAC \\ gvs []
        \\ rw []
        \\ last_x_assum (drule_then assume_tac)
        \\ last_x_assum (drule_then assume_tac)
        \\ last_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
        \\ qexists_tac ‘j’
        \\ qexists_tac ‘n’
        \\ CASE_TAC \\ gs [])
      \\ rgs [result_map_def, MEM_EL, EL_MAP, SF CONJ_ss, Once (CaseEq "bool"),
              DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      >- (
        ‘F’ suffices_by rw []
        \\ unabbrev_all_tac
        \\ gs [CaseEq "bool", DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ first_x_assum (drule_then (qx_choose_then ‘m’ assume_tac))
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’
        \\ Cases_on ‘eval_to (m + k - 1) (EL n xs)’ \\ gs []
        \\ first_x_assum (drule_then (qspec_then ‘m’ assume_tac))
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [])
      \\ rgs [Once (CaseEq "bool"), DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to (j + k - 1) (EL n xs))
                                   (eval_to (k - 1) (EL n ys))’
        by (unabbrev_all_tac
            \\ rpt (pop_assum mp_tac)
            \\ qid_spec_tac ‘ys’
            \\ Induct_on ‘xs’ \\ simp []
            \\ qx_gen_tac ‘x’
            \\ Cases \\ simp []
            \\ rename1 ‘eval_to (k - 1) (EL _ (y::ys))’
            \\ rw []
            \\ last_x_assum (qspec_then ‘ys’ mp_tac)
            \\ simp [AND_IMP_INTRO, GSYM CONJ_ASSOC]
            \\ impl_tac
            >- (
              rw []
              \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs []
              \\ gs [SF SFY_ss])
            \\ disch_then (qx_choose_then ‘j’ assume_tac)
            \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + k - 1) x)
                                        (eval_to (k - 1) y)’
              by (‘0 < SUC (LENGTH ys)’ by gs []
                  \\ res_tac \\ fs []
                  \\ qexists_tac ‘m’ \\ simp [])
            \\ qexists_tac ‘j + j1’
            \\ Cases \\ gs []
            >- (
              ‘eval_to (j + (j1 + k) - 1) x = eval_to (j1 + k - 1) x’
                by (irule eval_to_mono \\ gs []
                    \\ strip_tac \\ gs []
                    \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
                    \\ ‘0 < SUC (LENGTH ys)’ by gs []
                    \\ res_tac \\ fs []
                    \\ gs [])
              \\ gs [])
            \\ qmatch_goalsub_rename_tac ‘n < LENGTH ys’
            \\ strip_tac
            \\ ‘eval_to (j + (j1 + k) - 1) (EL n xs) =
                eval_to (j + k - 1) (EL n xs)’
              by (irule eval_to_mono \\ gs []
                  \\ strip_tac \\ gs []
                  \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
                  \\ res_tac \\ fs []
                  \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs [])
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ unabbrev_all_tac
      \\ gs [result_map_def, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF]
      \\ IF_CASES_TAC \\ rgs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ IF_CASES_TAC \\ rgs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      >- (
        first_x_assum (drule_then assume_tac)
        \\ gvs [CaseEqs ["sum", "v", "err"]]
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs [])
      \\ rw []
      >- (
        rpt (first_x_assum (drule_then assume_tac))
        \\ first_x_assum (qspec_then ‘j + k - 1’ assume_tac)
        \\ gvs [CaseEqs ["sum", "v", "err"]]
        \\ Cases_on ‘eval_to (j + k - 1) (EL n xs)’
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs []
        >- (
          strip_tac \\ gs [])
        \\ rename1 ‘v_rel u v’
        \\ first_x_assum (qspec_then ‘j’ assume_tac) \\ gs []
        \\ Cases_on ‘u’ \\ Cases_on ‘v’ \\ gs [])
      \\ irule_at Any LIST_EQ
      \\ rw [EL_MAP]
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ first_x_assum (qspec_then ‘j’ assume_tac)
      \\ rpt CASE_TAC \\ gs []))
  >~ [`Monad mop xs`]
  >- (strip_tac >> rw[Once exp_rel_cases] >> gvs[eval_to_def])
QED

Theorem exp_rel_eval_to[allow_rebind] =
  REWRITE_RULE [d2b_goal_def] exp_rel_eval_to;

Theorem exp_rel_eval:
  exp_rel x y ∧
  eval x ≠ INL Type_error ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ dxrule_then assume_tac eval_not_error
  \\ simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘MAX k j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
    \\ ‘eval_to (m + MAX k j) x = eval_to k x’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to (MAX k j) y = eval_to j y’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to \\ gs [])
  \\ rename1 ‘_ _ (eval_to k x)’
  \\ drule_all_then
    (qspec_then ‘k’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
  \\ Cases_on ‘eval_to (k + m) x’ \\ gvs []
  \\ drule_then (qspec_then ‘k + m’ assume_tac) eval_to_mono \\ gs []
QED

Theorem d2b_apply_closure[local]:
  exp_rel x y ∧
  v_rel v2 w2 ∧
  apply_closure x v2 f ≠ Err ∧
  f (INL Type_error) = Err ∧
  (∀x y.
     ($= +++ v_rel) x y ∧ f x ≠ Err ⇒
       next_rel v_rel exp_rel (f x) (g y)) ⇒
    next_rel v_rel exp_rel
             (apply_closure x v2 f)
             (apply_closure y w2 g)
Proof
  rw[thunk_semanticsTheory.apply_closure_def] >>
  gvs[thunk_semanticsTheory.with_value_def] >>
  `eval x ≠ INL Type_error` by (CCONTR_TAC >> gvs[]) >>
  dxrule_all_then assume_tac exp_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[] >- (CASE_TAC >> gvs[]) >>
  rename1 `eval x = INR v1` >> rename1 `eval y = INR w1`
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [dest_anyClosure_def]
  >- (
    first_x_assum irule \\ gs []
    \\ irule exp_rel_eval
    \\ gs [closed_subst]
    \\ irule_at Any exp_rel_subst \\ gs []
    \\ strip_tac \\ gs [])
  \\ rename1 ‘LIST_REL _ xs ys’
  \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
    by (irule LIST_REL_OPTREL
        \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
  \\ gs [OPTREL_def]
  \\ qpat_x_assum ‘exp_rel x0 y0’ mp_tac
  \\ rw [Once exp_rel_cases] \\ gs []
  \\ first_x_assum irule \\ gs []
  \\ irule exp_rel_eval
  \\ irule_at Any exp_rel_subst
  \\ gs [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  \\ irule_at Any LIST_EQ
  \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
  \\ strip_tac \\ gs []
QED

Theorem d2b_rel_ok[local]:
  rel_ok F v_rel exp_rel
Proof
  rw [rel_ok_def]
  >- ((* ∀x. f x ≠ Err from rel_ok prevents this case *)
    simp [d2b_apply_closure])
  >- ((* Equal literals are related *)
    simp [exp_rel_Prim])
  >- ((* Equal 0-arity conses are related *)
    simp [exp_rel_Prim])
  >- ((* v_rel x y ⇒ exp_rel (Value x) (Value y) *)
    simp [exp_rel_Value])
QED

Theorem d2b_sim_ok[local]:
  sim_ok F v_rel exp_rel
Proof
  rw [sim_ok_def]
  \\ simp [exp_rel_eval]
  \\ irule exp_rel_subst \\ gs []
QED

Theorem case_d2b_semantics:
  exp_rel x y ∧
  closed x ∧
  pure_semantics$safe_itree (semantics x Done []) ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics
  \\ irule_at Any d2b_sim_ok
  \\ irule_at Any d2b_rel_ok \\ gs []
QED

val _ = export_theory ();
