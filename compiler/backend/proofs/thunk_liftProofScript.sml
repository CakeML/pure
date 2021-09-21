(*
  The first in a series of transformations to simplify case-compilation from
  pureLang to thunkLang. See:
  - [thunk_d2bProofScript.sml]
  - [thunk_inlProofScript.sml]
  - [thunk_unboxProofScript.sml]
  - [thunk_caseProofScript.sml]
  for the others.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_liftProof";

val _ = numLib.prefer_num ();

Overload IsEq = “λs i (x: exp). Prim (IsEq s i) [x]”;

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;

Theorem PAIR_REL_def[local,simp] = quotient_pairTheory.PAIR_REL;

Inductive exp_rel:
(* Lifting case: *)
[exp_rel_Lift:]
  (∀x1 x2 y1 y2 z1 z2 w.
     w ∉ freevars y1 ∪ freevars z1 ∧
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ∧
     exp_rel z1 z2 ⇒
       exp_rel (Tick (If (IsEq s i x1) y1 z1))
               (Let (SOME w) (Tick (Tick x2))
                             (If (IsEq s i (Var w)) y2 z2))) ∧
(* Boilerplate: *)
[exp_rel_App:]
  (∀f g x y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f x) (App g y)) ∧
[exp_rel_Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y)) ∧
[exp_rel_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y)) ∧
[exp_rel_Let:]
  (∀bv x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let bv x1 y1) (Let bv x2 y2)) ∧
[exp_rel_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL exp_rel [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys)) ∧
[exp_rel_Delay:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Delay x) (Delay y)) ∧
[exp_rel_Box:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Box x) (Box y)) ∧
[exp_rel_Force:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Force x) (Force y)) ∧
[exp_rel_MkTick:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (MkTick x) (MkTick y)) ∧
[exp_rel_Var:]
  (∀v.
     exp_rel (Var v) (Var v)) ∧
[exp_rel_Value:]
  (∀v w.
     v_rel v w ⇒
     exp_rel (Value v) (Value w)) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x)) ∧
[v_rel_Constructor:]
  (∀vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ⇒
       v_rel (Closure s x) (Closure s y)) ∧
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) (DoTick w)) ∧
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Thunk_INR:]
  (∀x y.
     exp_rel x y ⇒
       v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_Thunk_INL:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INL v)) (Thunk (INL w)))
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
    “v_rel (Atom x) z”,
    “v_rel z (Atom x)”,
    “v_rel (Thunk (INL x)) z”,
    “v_rel z (Thunk (INL x))”,
    “v_rel (Thunk (INR x)) z”,
    “v_rel z (Thunk (INR x))” ]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem exp_rel_freevars:
  exp_rel x y ⇒ freevars x = freevars y
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ freevars x = freevars y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- rw []
  \\ ho_match_mp_tac exp_rel_strongind \\ simp [freevars_def]
  \\ rw []
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs []
    \\ rw [] \\ gs [])
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
    rw [Once exp_rel_cases]
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
    >- ((* Lifting *)
      simp [subst_def, ELIM_UNCURRY, GSYM FILTER_REVERSE]
      \\ simp [LAMBDA_PROD, ALOOKUP_FILTER]
      \\ imp_res_tac exp_rel_freevars \\ gs []
      \\ gs [ELIM_UNCURRY, FILTER_T] \\ gs [LAMBDA_PROD]
      \\ irule exp_rel_Lift \\ gs []
      \\ simp [freevars_subst]
      \\ ‘DISJOINT {w} (freevars y2) ∧ DISJOINT {w} (freevars z2)’
        by gs [IN_DISJOINT]
      \\ imp_res_tac subst_remove \\ gs []
      \\ first_x_assum (drule_then (qspec_then ‘If (IsEq s i x2) y2 z2’ mp_tac))
      \\ simp [Once exp_rel_cases, PULL_EXISTS, subst_def]
      \\ simp [Once exp_rel_cases, PULL_EXISTS]
      \\ simp [Once exp_rel_cases, PULL_EXISTS]
      \\ simp [Once exp_rel_cases, PULL_EXISTS])
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
  >- ((* Box *)
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_Box
    \\ first_x_assum irule \\ gs [])
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
    \\ Cases_on ‘eval_to k f’ \\ Cases_on ‘eval_to k g’ \\ gvs []
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyClosure_def]
    >- ((* Closure *)
      IF_CASES_TAC \\ gs []
      \\ rename1 ‘(_ +++ _) (_ _ (subst1 s u1 e1)) (_ _ (subst1 s u2 e2))’
      \\ ‘[s,u1] = [] ++ [s,u1]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ ‘[s,u2] = [] ++ [s,u2]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ first_x_assum irule \\ gs []
      \\ irule exp_rel_subst \\ gs [])
        (* Recclosure *)
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                       (ALOOKUP (REVERSE ys) s)’
      by (irule LIST_REL_OPTREL \\ gs [])
    \\ gs [OPTREL_def]
    \\ gvs [Once exp_rel_cases]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ irule exp_rel_subst \\ gs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP,
                                  LAMBDA_PROD, GSYM FST_THM]
    \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
    \\ irule LIST_EQ \\ gvs [EL_MAP])
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
    >- ((* Lifting *)
      gs [eval_to_def, subst_funs_def, subst_def]
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ first_x_assum
        (qspec_then ‘If (IsEq s i x2) y2 z2’ mp_tac)
      \\ simp [Once exp_rel_cases, eval_to_def]
      \\ simp [Once exp_rel_cases]
      \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) LHS RHS’
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) LHS RHS2’
      \\ ‘RHS = RHS2’
        suffices_by (rw [] \\ first_x_assum irule)
      \\ unabbrev_all_tac
      \\ Cases_on ‘eval_to (k - 3) x2’ \\ gs []
      \\ rename1 ‘_ = INR res’ \\ Cases_on ‘dest_Constructor res’ \\ gs []
      \\ pairarg_tac \\ gvs []
      \\ DEP_REWRITE_TAC [subst1_notin_frees]
      \\ imp_res_tac exp_rel_freevars \\ gs [])
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
  >~ [‘Box x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
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
        \\ gvs [Once exp_rel_cases]
        \\ first_x_assum irule
        \\ simp [subst_funs_def]
        \\ irule exp_rel_subst \\ gs [MAP_MAP_o, combinTheory.o_DEF,
                                      EVERY2_MAP, LAMBDA_PROD, GSYM FST_THM]
        \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
        \\ irule LIST_EQ \\ gvs [EL_MAP])
      \\ CASE_TAC \\ gs []
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
    \\ simp [eval_to_def]
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      gs [result_map_def, MEM_MAP, PULL_EXISTS, LIST_REL_EL_EQN, MEM_EL]
      \\ IF_CASES_TAC \\ gs []
      >- (
        gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gvs []
        \\ rw [] \\ gs [])
      \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        >- (
          rename1 ‘m < LENGTH ys’
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
        \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ rw [] \\ gs []
        \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
      \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
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
QED

val _ = export_theory ();

