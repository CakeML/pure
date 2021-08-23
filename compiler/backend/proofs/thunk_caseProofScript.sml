(*
  The ultimate goal of this proof script is to prove that it is possible to
  elimiate the unnecessary thunk allocations that are introduced by the
  pure_to_thunk compiler when it compiles Case-expressions. This is achieved
  by a series of small transformations.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_caseProof";

val _ = numLib.prefer_num ();

Overload Tick = “λx: exp. Letrec [] x”;

Overload IsEq = “λs i (x: exp). Prim (IsEq s i) [x]”;

Theorem subst_FILTER[local]:
  w ∉ freevars x ⇒
    subst (FILTER (λ(n,x). n ≠ w) vs) x = subst vs x
Proof
  strip_tac
  \\ ‘DISJOINT {w} (freevars x)’ by gs []
  \\ drule_all subst_remove
  \\ gs []
QED

Theorem subst1_notin_frees:
  n ∉ freevars x ⇒
    subst1 n v x = x
Proof
  strip_tac
  \\ drule subst_FILTER
  \\ disch_then (qspec_then ‘[n,v]’ mp_tac)
  \\ simp []
QED

Theorem subst1_commutes:
  n ≠ m ⇒ subst1 n v (subst1 m w x) = subst1 m w (subst1 n v x)
Proof
  cheat
QED

(* -------------------------------------------------------------------------
 * exp_rel_lift:
 * ------------------------------------------------------------------------- *)

Inductive exp_rel_lift:
(* Lifting case: *)
[exp_rel_lift_Lift:]
  (∀x1 x2 y1 y2 z1 z2 w.
     w ∉ freevars y1 ∪ freevars z1 ∧
     exp_rel_lift x1 x2 ∧
     exp_rel_lift y1 y2 ∧
     exp_rel_lift z1 z2 ⇒
       exp_rel_lift (Tick (If (IsEq s i x1) y1 z1))
               (Let (SOME w) (Tick (Tick x2)) (If (IsEq s i (Var w)) y2 z2))) ∧
(* Boilerplate: *)
[exp_rel_lift_App:]
  (∀f g x y.
     exp_rel_lift f g ∧
     exp_rel_lift x y ⇒
       exp_rel_lift (App f x) (App g y)) ∧
[exp_rel_lift_Lam:]
  (∀s x y.
     exp_rel_lift x y ⇒
       exp_rel_lift (Lam s x) (Lam s y)) ∧
[exp_rel_lift_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel_lift x y) f g ∧
     exp_rel_lift x y ⇒
       exp_rel_lift (Letrec f x) (Letrec g y)) ∧
[exp_rel_lift_Let:]
  (∀bv x1 y1 x2 y2.
     exp_rel_lift x1 x2 ∧
     exp_rel_lift y1 y2 ⇒
       exp_rel_lift (Let bv x1 y1) (Let bv x2 y2)) ∧
[exp_rel_lift_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL exp_rel_lift [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel_lift (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_lift_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel_lift xs ys ⇒
       exp_rel_lift (Prim op xs) (Prim op ys)) ∧
[exp_rel_lift_Delay:]
  (∀x y.
     exp_rel_lift x y ⇒
       exp_rel_lift (Delay x) (Delay y)) ∧
[exp_rel_lift_Box:]
  (∀x y.
     exp_rel_lift x y ⇒
       exp_rel_lift (Box x) (Box y)) ∧
[exp_rel_lift_Force:]
  (∀x y.
     exp_rel_lift x y ⇒
       exp_rel_lift (Force x) (Force y)) ∧
[exp_rel_lift_MkTick:]
  (∀x y.
     exp_rel_lift x y ⇒
       exp_rel_lift (MkTick x) (MkTick y)) ∧
[exp_rel_lift_Var:]
  (∀v.
     exp_rel_lift (Var v) (Var v)) ∧
[exp_rel_lift_Value:]
  (∀v w.
     v_rel_lift v w ⇒
     exp_rel_lift (Value v) (Value w)) ∧
[v_rel_lift_Atom:]
  (∀x.
     v_rel_lift (Atom x) (Atom x)) ∧
[v_rel_lift_Constructor:]
  (∀vs ws.
     LIST_REL v_rel_lift vs ws ⇒
       v_rel_lift (Constructor s vs) (Constructor s ws)) ∧
[v_rel_lift_Closure:]
  (∀s x y.
     exp_rel_lift x y ⇒
       v_rel_lift (Closure s x) (Closure s y)) ∧
[v_rel_lift_DoTick:]
  (∀v w.
     v_rel_lift v w ⇒
       v_rel_lift (DoTick v) (DoTick w)) ∧
[v_rel_lift_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel_lift x y) f g ⇒
       v_rel_lift (Recclosure f n) (Recclosure g n)) ∧
[v_rel_lift_Thunk_INR:]
  (∀x y.
     exp_rel_lift x y ⇒
       v_rel_lift (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_lift_Thunk_INL:]
  (∀v w.
     v_rel_lift v w ⇒
       v_rel_lift (Thunk (INL v)) (Thunk (INL w)))
End

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;

Theorem PAIR_REL_def[local,simp] = quotient_pairTheory.PAIR_REL;

Theorem v_rel_lift_cases[local] = CONJUNCT2 exp_rel_lift_cases;

(* Boilerplate *)
Theorem v_rel_lift_def[simp]:
  (v_rel_lift (Closure s x) z ⇔ ∃y. z = Closure s y ∧ exp_rel_lift x y) ∧
  (v_rel_lift z (Closure s x) ⇔ ∃y. z = Closure s y ∧ exp_rel_lift y x) ∧
  (v_rel_lift (Constructor s vs) z ⇔ ∃ws. z = Constructor s ws ∧
                                     LIST_REL v_rel_lift vs ws) ∧
  (v_rel_lift z (Constructor s vs) ⇔ ∃ws. z = Constructor s ws ∧
                                     LIST_REL v_rel_lift ws vs) ∧
  (v_rel_lift (Recclosure f n) z ⇔ ∃g. z = Recclosure g n ∧
                                  LIST_REL ($= ### exp_rel_lift) f g) ∧
  (v_rel_lift z (Recclosure f n) ⇔ ∃g. z = Recclosure g n ∧
                                  LIST_REL ($= ### exp_rel_lift) g f) ∧
  (v_rel_lift (Atom a) z ⇔ z = Atom a) ∧
  (v_rel_lift z (Atom a) ⇔ z = Atom a) ∧
  (v_rel_lift (Thunk (INL v)) z ⇔ ∃w. z = Thunk (INL w) ∧ v_rel_lift v w) ∧
  (v_rel_lift z (Thunk (INL v)) ⇔ ∃w. z = Thunk (INL w) ∧ v_rel_lift w v) ∧
  (v_rel_lift (Thunk (INR x)) z ⇔ ∃y. z = Thunk (INR y) ∧ exp_rel_lift x y) ∧
  (v_rel_lift z (Thunk (INR x)) ⇔ ∃y. z = Thunk (INR y) ∧ exp_rel_lift y x)
Proof
  strip_tac \\ rw [Once v_rel_lift_cases]
  \\ rw [Once v_rel_lift_cases, EQ_IMP_THM]
  \\ rw [Once v_rel_lift_cases, EVERY2_refl_EQ]
  \\ pairarg_tac \\ gvs []
QED

Theorem exp_rel_lift_freevars:
  exp_rel_lift x y ⇒ freevars x = freevars y
Proof
  qsuff_tac ‘
    (∀x y. exp_rel_lift x y ⇒ freevars x = freevars y) ∧
    (∀v w. v_rel_lift v w ⇒ T)’
  >- rw []
  \\ ho_match_mp_tac exp_rel_lift_strongind \\ simp [freevars_def]
  \\ rw []
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs []
    \\ metis_tac [])
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs []
    \\ fs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN,
           Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
    \\ rw [] \\ gs [EL_MAP, ELIM_UNCURRY, SF CONJ_ss]
    \\ metis_tac [])
  >- (
    Cases_on ‘bv’ \\ gs [freevars_def])
  >- (
    ‘MAP freevars xs = MAP freevars ys’
      suffices_by rw [SF ETA_ss]
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
QED

Theorem exp_rel_lift_subst:
  ∀vs x ws y.
    LIST_REL v_rel_lift (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    exp_rel_lift x y ⇒
      exp_rel_lift (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel_lift _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_lift_cases, subst_def] \\ gs []
    \\ ‘OPTREL v_rel_lift (ALOOKUP (REVERSE vs) s) (ALOOKUP (REVERSE ws) s)’
      by (irule LIST_REL_OPTREL
          \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ]
          \\ pop_assum mp_tac
          \\ qid_spec_tac ‘ws’
          \\ qid_spec_tac ‘vs’
          \\ Induct \\ simp []
          \\ gen_tac \\ Cases \\ simp [])
    \\ gs [OPTREL_def]
    \\ rw [Once exp_rel_lift_cases])
  >- ((* Prim *)
    rw [Once exp_rel_lift_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_lift_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw [])
  >- ((* If *)
    rw [Once exp_rel_lift_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_lift_If \\ fs [])
  >- ((* App *)
    rw [Once exp_rel_lift_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_lift_App \\ fs [])
  >- ((* Lam *)
    rw [Once exp_rel_lift_cases]
    \\ gvs [subst_def]
    \\ irule exp_rel_lift_Lam
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs [])
  >- ((* Let NONE *)
    rw [Once exp_rel_lift_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_lift_Let \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_lift_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_lift_Let \\ gs []
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs [])
  >- ((* Letrec *)
    rw [Once exp_rel_lift_cases] \\ gs []
    >- ((* Lifting *)
      simp [subst_def, ELIM_UNCURRY, GSYM FILTER_REVERSE]
      \\ simp [LAMBDA_PROD, ALOOKUP_FILTER]
      \\ imp_res_tac exp_rel_lift_freevars \\ gs []
      \\ gs [subst_FILTER]
      \\ irule exp_rel_lift_Lift \\ gs []
      \\ simp [freevars_subst]
      \\ gs [ELIM_UNCURRY]
      \\ first_x_assum (drule_then (qspec_then ‘If (IsEq s i x2) y2 z2’ mp_tac))
      \\ simp [Once exp_rel_lift_cases, PULL_EXISTS, subst_def]
      \\ simp [Once exp_rel_lift_cases, PULL_EXISTS]
      \\ simp [Once exp_rel_lift_cases, PULL_EXISTS]
      \\ simp [Once exp_rel_lift_cases, PULL_EXISTS]
      \\ rw [] \\ gs [])
    \\ simp [subst_def]
    \\ irule exp_rel_lift_Letrec
    \\ gvs [EVERY2_MAP, LAMBDA_PROD]
    \\ first_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ `MAP FST f = MAP FST g`
      by (irule LIST_EQ
          \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST g)’ \\ fs []
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ simp [SF ETA_ss]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ rw []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER, SF SFY_ss, SF ETA_ss]
    \\ irule LIST_REL_FILTER \\ gs [ELIM_UNCURRY])
  >- ((* Delay *)
    rw [Once exp_rel_lift_cases]
    \\ simp [subst_def, exp_rel_lift_Value, exp_rel_lift_Delay, SF SFY_ss]
    \\ qmatch_asmsub_abbrev_tac ‘LIST_REL R _ _’
    \\ ‘OPTREL R (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_OPTREL
          \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ, Abbr ‘R’]
          \\ pop_assum mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘ws’ \\ Induct_on ‘vs’ \\ Cases_on ‘ws’ \\ simp [])
    \\ gvs [Abbr ‘R’, OPTREL_def, exp_rel_lift_Var, exp_rel_lift_Value])
  >- ((* Box *)
    rw [Once exp_rel_lift_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_lift_Box
    \\ first_x_assum irule \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_lift_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_lift_Force \\ fs [])
  >- ((* Value *)
    rw [Once exp_rel_lift_cases]
    \\ simp [subst_def]
    \\ rw [Once exp_rel_lift_cases])
  >- ((* MkTick *)
    rw [Once exp_rel_lift_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_lift_MkTick
    \\ first_x_assum irule \\ gs [])
QED

Theorem exp_rel_lift_eval_to:
  ∀k x y.
    exp_rel_lift x y ⇒
      ($= +++ v_rel_lift)
        (eval_to k x)
        (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ simp []
  \\ rpt conj_tac \\ rpt gen_tac
  >~ [‘Value v’] >- (
    rw [Once exp_rel_lift_cases]
    \\ simp [eval_to_def])
  >~ [‘Var n’] >- (
    rw [Once exp_rel_lift_cases]
    \\ simp [eval_to_def])
  >~ [‘App f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_lift_cases] \\ gs []
    \\ rename1 ‘exp_rel_lift x y’
    \\ gs [eval_to_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k f’ \\ Cases_on ‘eval_to k g’ \\ gvs []
    \\ rename1 ‘v_rel_lift v w’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyClosure_def]
    >- ((* Closure *)
      IF_CASES_TAC \\ gs []
      \\ rename1 ‘(_ +++ _) (_ _ (subst1 s u1 e1)) (_ _ (subst1 s u2 e2))’
      \\ ‘[s,u1] = [] ++ [s,u1]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ ‘[s,u2] = [] ++ [s,u2]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ first_x_assum irule \\ gs []
      \\ irule exp_rel_lift_subst \\ gs [])
        (* Recclosure *)
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘OPTREL exp_rel_lift (ALOOKUP (REVERSE xs) s)
                       (ALOOKUP (REVERSE ys) s)’
      by (irule LIST_REL_OPTREL \\ gs [])
    \\ gs [OPTREL_def]
    \\ gvs [Once exp_rel_lift_cases]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ irule exp_rel_lift_subst \\ gs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP,
                                  LAMBDA_PROD, GSYM FST_THM]
    \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
    \\ irule LIST_EQ \\ gvs [EL_MAP])
  >~ [‘Lam s x’] >- (
    rw [Once exp_rel_lift_cases]
    \\ gs [eval_to_def])
  >~ [‘Let NONE x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_lift_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
  >~ [‘Let (SOME n) x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_lift_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ irule exp_rel_lift_subst \\ gs [])
  >~ [‘If x1 y1 z1’] >- (
    strip_tac
    \\ rw [Once exp_rel_lift_cases] \\ gs []
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
    \\ rw [Once exp_rel_lift_cases] \\ gs []
    >- ((* Lifting *)
      gs [eval_to_def, subst_funs_def, subst_def]
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ first_x_assum
        (qspec_then ‘If (IsEq s i x2) y2 z2’ mp_tac)
      \\ simp [Once exp_rel_lift_cases, eval_to_def]
      \\ simp [Once exp_rel_lift_cases]
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
      \\ imp_res_tac exp_rel_lift_freevars \\ gs [])
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def]
    \\ irule exp_rel_lift_subst \\ gs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP,
                                  LAMBDA_PROD, GSYM FST_THM]
    \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
    \\ irule LIST_EQ \\ gvs [EL_MAP])
  >~ [‘Delay x’] >- (
    rw [Once exp_rel_lift_cases] \\ gs []
    \\ simp [eval_to_def])
  >~ [‘Box x’] >- (
    strip_tac
    \\ rw [Once exp_rel_lift_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel_lift x y’
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
  >~ [‘Force x’] >- (
    strip_tac
    \\ rw [Once exp_rel_lift_cases] \\ gs []
    \\ rename1 ‘exp_rel_lift x y’
    \\ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘v_rel_lift v w’
    \\ Cases_on ‘dest_Tick v’ \\ gs []
    >- (
      ‘dest_Tick w = NONE’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_lift_cases])
      \\ gs []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
      >- (
        rename1 ‘LIST_REL _ xs ys’
        \\ ‘OPTREL exp_rel_lift (ALOOKUP (REVERSE xs) s)
                           (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL \\ gs [])
        \\ gs [OPTREL_def]
        \\ gvs [Once exp_rel_lift_cases]
        \\ first_x_assum irule
        \\ simp [subst_funs_def]
        \\ irule exp_rel_lift_subst \\ gs [MAP_MAP_o, combinTheory.o_DEF,
                                      EVERY2_MAP, LAMBDA_PROD, GSYM FST_THM]
        \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
        \\ irule LIST_EQ \\ gvs [EL_MAP])
      \\ CASE_TAC \\ gs []
      \\ first_x_assum irule
      \\ simp [subst_funs_def])
    \\ ‘∃y. dest_Tick w = SOME y’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_lift_cases])
    \\ gs []
    \\ first_x_assum irule
    \\ rw [Once exp_rel_lift_cases]
    \\ rw [Once exp_rel_lift_cases]
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [Once v_rel_lift_cases])
  >~ [‘MkTick x’] >- (
    strip_tac
    \\ rw [Once exp_rel_lift_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel_lift x y’
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rw [Once v_rel_lift_cases])
  >~ [‘Prim op xs’] >- (
    strip_tac
    \\ rw [Once exp_rel_lift_cases] \\ gs []
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
      \\ rename1 ‘exp_rel_lift x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_lift v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* Proj *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1n ⇔ n = 0”]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel_lift x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_lift v w’
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

(* -------------------------------------------------------------------------
 * exp_rel_d2b:
 *
 * Replace “Delay” with “Box” when an expression is immediately forced. Uses
 * less clock ticks on the right side.
 * (Induction does not go through in the exp_rel_d2b_eval_to proof)
 * ------------------------------------------------------------------------- *)

Inductive exp_rel_d2b:
(* Delay-to-Box *)
[exp_rel_d2b_D2B:]
  (∀v w x1 x2.
     exp_rel_d2b x1 x2 ∧
     exp_rel_d2b y1 y2 ∧
     v ≠ w ⇒
       exp_rel_d2b (Let (SOME v) (Delay x1)
                        (Let (SOME w) (Force (Var v)) y1))
                   (Let (SOME w) (Tick (Tick x2))
                        (Let (SOME v) (Box (Var w)) y2))) ∧
[v_rel_d2b_D2B:]
  (∀x v w k.
     eval_to k x = INR v ∧
     v_rel_d2b v w ⇒
       v_rel_d2b (Thunk (INR x)) (Thunk (INL w))) ∧
(* Boilerplate: *)
[exp_rel_d2b_App:]
  (∀f g x y.
     exp_rel_d2b f g ∧
     exp_rel_d2b x y ⇒
       exp_rel_d2b (App f x) (App g y)) ∧
[exp_rel_d2b_Lam:]
  (∀s x y.
     exp_rel_d2b x y ⇒
       exp_rel_d2b (Lam s x) (Lam s y)) ∧
[exp_rel_d2b_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel_d2b x y) f g ∧
     exp_rel_d2b x y ⇒
       exp_rel_d2b (Letrec f x) (Letrec g y)) ∧
[exp_rel_d2b_Let:]
  (∀bv x1 y1 x2 y2.
     exp_rel_d2b x1 x2 ∧
     exp_rel_d2b y1 y2 ⇒
       exp_rel_d2b (Let bv x1 y1) (Let bv x2 y2)) ∧
[exp_rel_d2b_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL exp_rel_d2b [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel_d2b (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_d2b_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel_d2b xs ys ⇒
       exp_rel_d2b (Prim op xs) (Prim op ys)) ∧
[exp_rel_d2b_Delay:]
  (∀x y.
     exp_rel_d2b x y ⇒
       exp_rel_d2b (Delay x) (Delay y)) ∧
[exp_rel_d2b_Box:]
  (∀x y.
     exp_rel_d2b x y ⇒
       exp_rel_d2b (Box x) (Box y)) ∧
[exp_rel_d2b_Force:]
  (∀x y.
     exp_rel_d2b x y ⇒
       exp_rel_d2b (Force x) (Force y)) ∧
[exp_rel_d2b_MkTick:]
  (∀x y.
     exp_rel_d2b x y ⇒
       exp_rel_d2b (MkTick x) (MkTick y)) ∧
[exp_rel_d2b_Var:]
  (∀v.
     exp_rel_d2b (Var v) (Var v)) ∧
[exp_rel_d2b_Value:]
  (∀v w.
     v_rel_d2b v w ⇒
     exp_rel_d2b (Value v) (Value w)) ∧
[v_rel_d2b_Atom:]
  (∀x.
     v_rel_d2b (Atom x) (Atom x)) ∧
[v_rel_d2b_Constructor:]
  (∀vs ws.
     LIST_REL v_rel_d2b vs ws ⇒
       v_rel_d2b (Constructor s vs) (Constructor s ws)) ∧
[v_rel_d2b_Closure:]
  (∀s x y.
     exp_rel_d2b x y ⇒
       v_rel_d2b (Closure s x) (Closure s y)) ∧
[v_rel_d2b_DoTick:]
  (∀v w.
     v_rel_d2b v w ⇒
       v_rel_d2b (DoTick v) (DoTick w)) ∧
[v_rel_d2b_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel_d2b x y) f g ⇒
       v_rel_d2b (Recclosure f n) (Recclosure g n)) ∧
[v_rel_d2b_Thunk_INR:]
  (∀x y.
     exp_rel_d2b x y ⇒
       v_rel_d2b (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_d2b_Thunk_INL:]
  (∀v w.
     v_rel_d2b v w ⇒
       v_rel_d2b (Thunk (INL v)) (Thunk (INL w)))
End

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;

Theorem PAIR_REL_def[local,simp] = quotient_pairTheory.PAIR_REL;

Theorem v_rel_d2b_cases[local] = CONJUNCT2 exp_rel_d2b_cases;

(* Boilerplate *)
Theorem v_rel_d2b_def[simp]:
  (v_rel_d2b (Closure s x) z ⇔ ∃y. z = Closure s y ∧ exp_rel_d2b x y) ∧
  (v_rel_d2b z (Closure s x) ⇔ ∃y. z = Closure s y ∧ exp_rel_d2b y x) ∧
  (v_rel_d2b (Constructor s vs) z ⇔ ∃ws. z = Constructor s ws ∧
                                     LIST_REL v_rel_d2b vs ws) ∧
  (v_rel_d2b z (Constructor s vs) ⇔ ∃ws. z = Constructor s ws ∧
                                     LIST_REL v_rel_d2b ws vs) ∧
  (v_rel_d2b (Recclosure f n) z ⇔ ∃g. z = Recclosure g n ∧
                                  LIST_REL ($= ### exp_rel_d2b) f g) ∧
  (v_rel_d2b z (Recclosure f n) ⇔ ∃g. z = Recclosure g n ∧
                                  LIST_REL ($= ### exp_rel_d2b) g f) ∧
  (v_rel_d2b (Atom a) z ⇔ z = Atom a) ∧
  (v_rel_d2b z (Atom a) ⇔ z = Atom a) ∧
  (v_rel_d2b (Thunk (INL v)) z ⇔ ∃w. z = Thunk (INL w) ∧ v_rel_d2b v w) ∧
  (*
  (v_rel_d2b z (Thunk (INL v)) ⇔ ∃w. z = Thunk (INL w) ∧ v_rel_d2b w v) ∧
  (v_rel_d2b (Thunk (INR x)) z ⇔ ∃y. z = Thunk (INR y) ∧ exp_rel_d2b x y) ∧ *)
  (v_rel_d2b z (Thunk (INR x)) ⇔ ∃y. z = Thunk (INR y) ∧ exp_rel_d2b y x)
Proof
  strip_tac \\ rw [Once v_rel_d2b_cases]
  \\ rw [Once v_rel_d2b_cases, EQ_IMP_THM]
  \\ rw [Once v_rel_d2b_cases, EVERY2_refl_EQ]
  \\ pairarg_tac \\ gvs []
QED

Theorem exp_rel_d2b_freevars:
  exp_rel_d2b x y ⇒ freevars x = freevars y
Proof
  qsuff_tac ‘
    (∀x y. exp_rel_d2b x y ⇒ freevars x = freevars y) ∧
    (∀v w. v_rel_d2b v w ⇒ T)’
  >- rw []
  \\ ho_match_mp_tac exp_rel_d2b_strongind
  \\ simp [freevars_def]
  \\ rw []
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs []
    \\ metis_tac [])
  >- (
    rw [EXTENSION, EQ_IMP_THM] \\ gs []
    \\ fs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN,
           Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
    \\ rw [] \\ gs [EL_MAP, ELIM_UNCURRY, SF CONJ_ss]
    \\ metis_tac [])
  >- (
    Cases_on ‘bv’ \\ gs [freevars_def])
  >- (
    ‘MAP freevars xs = MAP freevars ys’
      suffices_by rw [SF ETA_ss]
    \\ irule LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
QED

Theorem exp_rel_d2b_subst:
  ∀vs x ws y.
    LIST_REL v_rel_d2b (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    exp_rel_d2b x y ⇒
      exp_rel_d2b (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel_d2b _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_d2b_cases, subst_def] \\ gs []
    \\ ‘OPTREL v_rel_d2b (ALOOKUP (REVERSE vs) s) (ALOOKUP (REVERSE ws) s)’
      by (irule LIST_REL_OPTREL
          \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ]
          \\ pop_assum mp_tac
          \\ qid_spec_tac ‘ws’
          \\ qid_spec_tac ‘vs’
          \\ Induct \\ simp []
          \\ gen_tac \\ Cases \\ simp [])
    \\ gs [OPTREL_def]
    \\ rw [Once exp_rel_d2b_cases])
  >- ((* Prim *)
    rw [Once exp_rel_d2b_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_d2b_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw [])
  >- ((* If *)
    rw [Once exp_rel_d2b_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_d2b_If \\ fs [])
  >- ((* App *)
    rw [Once exp_rel_d2b_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_d2b_App \\ fs [])
  >- ((* Lam *)
    rw [Once exp_rel_d2b_cases]
    \\ gvs [subst_def]
    \\ irule exp_rel_d2b_Lam
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs [])
  >- ((* Let NONE *)
    rw [Once exp_rel_d2b_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_d2b_Let \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_d2b_cases] \\ gs []
    >- (
      last_x_assum (drule_then (qspec_then ‘Delay x2’ mp_tac))
      \\ simp [Once exp_rel_d2b_cases, PULL_EXISTS, subst_def]
      \\ simp [Once exp_rel_d2b_cases, PULL_EXISTS]
      \\ strip_tac
      \\ gs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
      \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
      \\ ‘LIST_REL v_rel_d2b (MAP SND (FILTER (λ(n,x). P n) vs))
                             (MAP SND (FILTER (λ(n,x). P n) ws))’
        by (gs [EVERY2_MAP]
            \\ irule LIST_REL_FILTER \\ gs [])
      \\ first_x_assum drule
      \\ simp [MAP_FST_FILTER, ELIM_UNCURRY]
      \\ disch_then (qspec_then ‘Let (SOME w) (Force (Var s)) y2’ mp_tac)
      \\ simp [Once exp_rel_d2b_cases]
      \\ simp [Once exp_rel_d2b_cases]
      \\ simp [Once exp_rel_d2b_cases]
      \\ simp [Once exp_rel_d2b_cases, PULL_EXISTS, subst_def,
               GSYM FILTER_REVERSE, ALOOKUP_FILTER, LAMBDA_PROD]
      \\ simp [Once exp_rel_d2b_cases]
      \\ simp [Once exp_rel_d2b_cases]
      \\ ‘OPTREL v_rel_d2b (ALOOKUP (REVERSE vs) s) (ALOOKUP (REVERSE ws) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ]
            \\ qpat_x_assum ‘MAP _ _ = _’ mp_tac
            \\ qid_spec_tac ‘ws’
            \\ qid_spec_tac ‘vs’
            \\ Induct \\ simp []
            \\ gen_tac \\ Cases \\ simp [])
      \\ gs [OPTREL_def, FILTER_FILTER, LAMBDA_PROD]
      \\ rw [] \\ gs []
      \\ irule exp_rel_d2b_D2B
      \\ gs [AC CONJ_COMM CONJ_ASSOC])
    \\ simp [subst_def]
    \\ irule exp_rel_d2b_Let \\ gs []
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs [])
  >- ((* Letrec *)
    rw [Once exp_rel_d2b_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_d2b_Letrec
    \\ gvs [EVERY2_MAP, LAMBDA_PROD]
    \\ first_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ `MAP FST f = MAP FST g`
      by (irule LIST_EQ
          \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST g)’ \\ fs []
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ simp [SF ETA_ss]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ rw []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER, SF SFY_ss, SF ETA_ss]
    \\ irule LIST_REL_FILTER \\ gs [ELIM_UNCURRY])
  >- ((* Delay *)
    rw [Once exp_rel_d2b_cases]
    \\ simp [subst_def, exp_rel_d2b_Value, exp_rel_d2b_Delay, SF SFY_ss]
    \\ qmatch_asmsub_abbrev_tac ‘LIST_REL R _ _’
    \\ ‘OPTREL R (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_OPTREL
          \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ, Abbr ‘R’]
          \\ pop_assum mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘ws’ \\ Induct_on ‘vs’ \\ Cases_on ‘ws’ \\ simp [])
    \\ gvs [Abbr ‘R’, OPTREL_def, exp_rel_d2b_Var, exp_rel_d2b_Value])
  >- ((* Box *)
    rw [Once exp_rel_d2b_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_d2b_Box
    \\ first_x_assum irule \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_d2b_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_d2b_Force \\ fs [])
  >- ((* Value *)
    rw [Once exp_rel_d2b_cases]
    \\ simp [subst_def]
    \\ rw [Once exp_rel_d2b_cases])
  >- ((* MkTick *)
    rw [Once exp_rel_d2b_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_d2b_MkTick
    \\ first_x_assum irule \\ gs [])
QED

(* TODO We need a different induction theorem for this proof, but this looks
 *      terrible...
 *)

Definition eval_to_wo_def:
  eval_to_wo = inv_image ($< LEX $<) (I ## exp_size)
End

Theorem eval_to_wo_WF[local]:
  WF eval_to_wo
Proof
  rw [eval_to_wo_def]
  \\ irule relationTheory.WF_inv_image
  \\ irule WF_LEX \\ gs []
QED

Theorem eval_to_wo_def = REWRITE_RULE [LEX_DEF] eval_to_wo_def;

Theorem eval_to_WF_IND[local] =
  WF_IND
  |> GEN_ALL
  |> Q.ISPEC ‘eval_to_wo’
  |> REWRITE_RULE [eval_to_wo_WF]
  |> Q.SPEC ‘λ(k, x). ∀y. exp_rel_d2b x y ⇒ ∃j.
              ($= +++ v_rel_d2b) (eval_to (j + k) x) (eval_to k y)’
  |> SIMP_RULE std_ss [FORALL_PROD]

Theorem exp_rel_d2b_eval_to:
  ∀k x y.
    exp_rel_d2b x y ⇒
    ∃j.
      ($= +++ v_rel_d2b)
        (eval_to (j + k) x)
        (eval_to k y)
Proof
  ho_match_mp_tac eval_to_WF_IND
  \\ gen_tac
  \\ Cases \\ gs []
  >~ [‘Var v’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ simp [eval_to_def])
  >~ [‘App f x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ rename1 ‘exp_rel_d2b x y’
    \\ simp [eval_to_def]
    \\ ‘∃j1. ($= +++ v_rel_d2b) (eval_to (j1 + k) f) (eval_to k g)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ ‘∃j2. ($= +++ v_rel_d2b) (eval_to (j2 + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k g’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k) f’ \\ gs [])
    \\ ‘∀j. eval_to (j + j1 + k) f = eval_to (j1 + k) f’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Cases_on ‘eval_to k y’ \\ gs []
    >- (
      rename1 ‘_ = INL err’
      \\ Cases_on ‘err = Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘eval_to (j2 + k) f = eval_to (j1 + k) f’
          by (drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
              \\ drule_then (qspec_then ‘j2 + k’ assume_tac) eval_to_mono
              \\ gs [])
        \\ qexists_tac ‘j2’
        \\ Cases_on ‘eval_to (j1 + k) f’ \\ gs []
        \\ Cases_on ‘eval_to (j2 + k) x’ \\ gs [])
      \\ Cases_on ‘err’ \\ gs []
      \\ ‘∀j. eval_to (j + j2 + k) x = eval_to (j2 + k) x’
        by (strip_tac
            \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ qexists_tac ‘j1 + j2’
      \\ Cases_on ‘eval_to (j1 + k) f’ \\ gs []
      \\ Cases_on ‘eval_to (j2 + k) x’ \\ gs []
      \\ once_rewrite_tac [DECIDE “j1 + (j2 + k) = j2 + (j1 + k)”]
      \\ gs [])
    \\ ‘∀j. eval_to (j + j2 + k) x = eval_to (j2 + k) x’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k) f’ \\ Cases_on ‘eval_to (j2 + k) x’ \\ gs []
    \\ rename1 ‘dest_anyClosure w’
    \\ Cases_on ‘dest_anyClosure w’ \\ gs []
    >- (
      qexists_tac ‘j1 + j2’ \\ gs []
      \\ once_rewrite_tac [DECIDE “j1 + (j2 + k) = j2 + (j1 + k)”]
      \\ gs []
      \\ rename1 ‘v_rel_d2b v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyClosure_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel_d2b (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel_d2b x0 _’ mp_tac
      \\ rw [Once exp_rel_d2b_cases] \\ gs [])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘v_rel_d2b v w’
    \\ rename1 ‘subst (ws2 ++ [s2,w2]) b2’
    \\ ‘∃b1 ws1. dest_anyClosure v = INR (s2,b1,ws1) ∧
                 exp_rel_d2b b1 b2 ∧
                 LIST_REL (λ(f,v) (g,w). f = g ∧ v_rel_d2b v w) ws1 ws2’
      by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyClosure_def]
          \\ rename1 ‘LIST_REL _ xs ys’
          \\ ‘OPTREL exp_rel_d2b (ALOOKUP (REVERSE xs) s)
                                 (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL \\ gs [])
          \\ gs [OPTREL_def]
          \\ qpat_x_assum ‘exp_rel_d2b x0 _’ mp_tac
          \\ rw [Once exp_rel_d2b_cases] \\ gs []
          \\ gvs [EVERY2_MAP, LAMBDA_PROD]
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval_to 0 f = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j f = eval_to 0 f’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j x = eval_to 0 x’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ qexists_tac ‘0’ \\ simp [])
    \\ Cases_on ‘eval_to (k - 1) (subst (ws2 ++ [s2,w2]) b2) = INL Diverge’
    >- (
      Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) f = eval_to k f’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x = eval_to k x’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ gs []
      \\ ‘∀j. j + k - 1 = j + (k - 1)’
        by gs []
      \\ asm_simp_tac bool_ss []
      \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def]
      \\ irule exp_rel_d2b_subst
      \\ gs [EVERY2_MAP, LIST_REL_CONJ, ELIM_UNCURRY]
      \\ irule LIST_EQ
      \\ gvs [EL_MAP, LIST_REL_EL_EQN])
    \\ Q.REFINE_EXISTS_TAC ‘j1 + j2 + j’ \\ gs []
    \\ once_rewrite_tac [DECIDE “j + (j1 + (j2 + k)) = (j + j2) + (j1 + k)”]
    \\ gs []
    \\ once_rewrite_tac [DECIDE “j + (j1 + (j2 + k)) = (j + j1) + (j2 + k)”]
    \\ gs []
    \\ qmatch_goalsub_abbrev_tac ‘_ (eval_to _ X1) (eval_to _ X2)’
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) X1) (eval_to (k - 1) X2)’
      by (first_x_assum irule
          \\ gs [Abbr ‘X1’, Abbr ‘X2’, eval_to_wo_def]
          \\ irule exp_rel_d2b_subst
          \\ gvs [EVERY2_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY]
          \\ irule LIST_EQ
          \\ gs [EL_MAP])
    \\ qexists_tac ‘j’
    \\ ‘eval_to (j + k - 1) X1 ≠ INL Diverge’
      by (strip_tac
          \\ Cases_on ‘eval_to (k - 1) X2’ \\ gs [])
    \\ drule_then (qspec_then ‘j + j1 + j2 + k - 1’ assume_tac) eval_to_mono
    \\ gs [])
  >~ [‘Lam s x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ simp [eval_to_def])
  >~ [‘Letrec f x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ rename1 ‘exp_rel_d2b x y’
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) (subst_funs f x))
                               (eval_to (k - 1) (subst_funs g y))’
      suffices_by rw []
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def, exp_size_def, subst_funs_def]
    \\ irule_at Any exp_rel_d2b_subst
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
             GSYM FST_THM]
    \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN]
    \\ irule LIST_EQ
    \\ gs [EL_MAP])
  >~ [‘Force x’] >- (
    strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ rename1 ‘exp_rel_d2b x y’
    \\ CONV_TAC (QUANT_CONV (LAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ CONV_TAC (QUANT_CONV (RAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
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
    \\ rename1 ‘v_rel_d2b v w’
    \\ ‘OPTREL v_rel_d2b (dest_Tick v) (dest_Tick w)’
      by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
          \\ gs [Once (CONJUNCT2 exp_rel_d2b_cases)])
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
          \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1))
                                              (Force (Value x0)))
                                     (eval_to (k - 1)
                                              (Force (Value y0)))’
            suffices_by rw []
          \\ first_x_assum irule
          \\ simp [eval_to_wo_def]
          \\ irule exp_rel_d2b_Force
          \\ irule exp_rel_d2b_Value
          \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ qsuff_tac ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1))
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
      \\ irule exp_rel_d2b_Force
      \\ irule exp_rel_d2b_Value \\ gs [])
    \\ Cases_on ‘dest_anyThunk w’ \\ gs []
    >- (
      qexists_tac ‘j’ \\ gs []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel_d2b (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ gs [Once exp_rel_d2b_cases])
    \\ pairarg_tac \\ gvs []
    \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
    >- (
      rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel_d2b (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ gvs [Once exp_rel_d2b_cases]
      \\ rename1 ‘exp_rel_d2b x1 y1’
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
          \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
          \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) (subst_funs xs x1))
                                     (eval_to (k - 1) (subst_funs binds y1))’
            suffices_by rw []
          \\ first_x_assum irule
          \\ gs [eval_to_wo_def, subst_funs_def]
          \\ irule exp_rel_d2b_subst
          \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                   EVERY2_MAP]
          \\ gvs [LIST_REL_EL_EQN, LIST_REL_CONJ, ELIM_UNCURRY]
          \\ irule LIST_EQ \\ gvs [EL_MAP])
        \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
        \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) (subst_funs xs x1))
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
        \\ irule exp_rel_d2b_subst
        \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                 EVERY2_MAP]
        \\ gvs [LIST_REL_EL_EQN, LIST_REL_CONJ, ELIM_UNCURRY]
        \\ irule LIST_EQ \\ gvs [EL_MAP]))
    \\ simp [subst_funs_def]
    \\ reverse CASE_TAC \\ gs []
    >- (
      rename1 ‘exp_rel_d2b x1 y1’
      \\ Cases_on ‘eval_to (k - 1) y1 = INL Diverge’
      >- (
        Cases_on ‘eval_to k x = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k) x = eval_to k x’
          by (gen_tac \\ irule eval_to_mono \\ gs [])
        \\ gvs []
        \\ qpat_assum `_ = INL Diverge` (SUBST1_TAC o SYM)
        \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) x1)
                                   (eval_to (k - 1) y1)’
          suffices_by rw []
        \\ first_x_assum irule
        \\ gs [eval_to_wo_def])
      \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
        by (gen_tac \\ irule eval_to_mono \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) x1)
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
      \\ gs [eval_to_wo_def])
    \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
      by (gen_tac \\ irule eval_to_mono \\ gs [])
    \\ Q.REFINE_EXISTS_TAC ‘j + j1’ \\ gs []
    \\ gvs [Once (CONJUNCT2 exp_rel_d2b_cases)]
    \\ rename1 ‘eval_to k1 x1 = INR v1’
    \\ qexists_tac ‘j1 + k1’
    \\ ‘eval_to (k + k1 + j + j1 - 1) x1 = eval_to k1 x1’
      by (irule eval_to_mono \\ gs [])
    \\ gs [])
  >~ [‘Let bv x1 y1’] >- (
    Cases_on ‘bv’
    >~ [‘Let (SOME s) x1 y1’] >- (
      strip_tac
      \\ rw [Once exp_rel_d2b_cases]
      >- ((* D2B *)
        rename1 ‘exp_rel_d2b x1 x2’ \\ rename1 ‘exp_rel_d2b y1 y2’
        \\ simp [Once eval_to_def, Once eval_to_def, Once eval_to_def]
        \\ IF_CASES_TAC \\ gs []
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ simp [Once eval_to_def, subst_funs_def, Once eval_to_def]
        \\ simp [subst_def, Once eval_to_def, Once eval_to_def]
        \\ simp [Once eval_to_def, dest_anyThunk_def, subst_funs_def]
        \\ IF_CASES_TAC \\ gs []
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ IF_CASES_TAC \\ gs []
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 3)) x1)
                                   (eval_to (k - 3) x2)’
          by (first_x_assum irule \\ simp [eval_to_wo_def])
          \\ Cases_on ‘eval_to (k - 3) x2’ \\ gs []
        >- (
          qexists_tac ‘j’
          \\ Cases_on ‘eval_to (j + k - 3) x1’ \\ gs [])
        \\ simp [eval_to_def]
        \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) _ (eval_to k1 rhs)’
        \\ Cases_on ‘eval_to k1 rhs = INL Diverge’ \\ unabbrev_all_tac
        >- (
          Cases_on ‘eval_to (k - 3) x1 = INL Diverge’
          >- (
            qexists_tac ‘0’
            \\ simp [])
          \\ ‘∀j. eval_to (j + k - 3) x1 = eval_to (k - 3) x1’
            by (gen_tac \\ irule eval_to_mono \\ gs [])
          \\ Cases_on ‘eval_to (k - 3) x1’ \\ gs []
          \\ ‘∀j. j + k - 2 = j + (k - 2)’ by gs []
          \\ asm_simp_tac std_ss []
          \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
          \\ first_x_assum irule
          \\ gs [eval_to_wo_def, subst1_commutes]
          \\ irule exp_rel_d2b_subst \\ gs []
          \\ irule exp_rel_d2b_subst \\ gs []
          \\ irule v_rel_d2b_D2B
          \\ first_assum (irule_at Any) \\ gs [])
        \\ ‘∀j1. eval_to (j1 + j + k - 3) x1 = eval_to (j + k - 3) x1’
          by (gen_tac \\ irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs [])
        \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
        \\ Cases_on ‘eval_to (j + k - 3) x1’ \\ gs []
        \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) (eval_to _ lhs) (eval_to _ rhs)’
        \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 2)) lhs)
                                   (eval_to (k - 2) rhs)’
          suffices_by (
            disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ qexists_tac ‘j1’
            \\ ‘eval_to (j + j1 + k - 2) lhs = eval_to (j1 + k - 2) lhs’
              by (irule eval_to_mono \\ gs []
                  \\ strip_tac \\ gs []
                  \\ Cases_on ‘eval_to (k - 2) rhs’ \\ gs [])
            \\ gs [])
        \\ first_x_assum irule
        \\ unabbrev_all_tac
        \\ gs [eval_to_wo_def, subst1_commutes]
        \\ irule exp_rel_d2b_subst \\ gs []
        \\ irule exp_rel_d2b_subst \\ gs []
        \\ irule v_rel_d2b_D2B
        \\ first_assum (irule_at Any) \\ gs [])
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) x1)
                                 (eval_to (k - 1) x2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      >- (
        qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
        by (gen_tac \\ irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (k - 1) (subst1 s y y2) = INL Diverge’
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
        \\ gs [eval_to_wo_def]
        \\ irule exp_rel_d2b_subst \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘j1 + j’ \\ gs []
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘(_ +++ _) (eval_to _ lhs) (eval_to _ rhs)’
      \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) lhs)
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
      \\ irule exp_rel_d2b_subst \\ gs [])
    \\ strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) x1) (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >- (
      qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs [])
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
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) lhs)
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
  >~ [‘If x1 y1 z1’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∃j1. ($= +++ v_rel_d2b) (eval_to (j1 + (k - 1)) x1)
                                (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ ‘∃j2. ($= +++ v_rel_d2b) (eval_to (j2 + (k - 1)) y1)
                                (eval_to (k - 1) y2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ ‘∃j3. ($= +++ v_rel_d2b) (eval_to (j3 + (k - 1)) z1)
                                (eval_to (k - 1) z2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
    \\ ‘∀j. eval_to (j + j1 + k - 1) x1 = eval_to (j1 + k - 1) x1’
      by (strip_tac
          \\ irule eval_to_mono \\ simp []
          \\ strip_tac \\ gs [])
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gvs []
      \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (j1 + k - 1) x1’
          by (qx_gen_tac ‘j’
              \\ drule_then (qspec_then ‘j + k - 1’ assume_tac) eval_to_mono
              \\ drule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono
              \\ gs [])
        \\ simp [SF SFY_ss])
      \\ ‘∀j. eval_to (j2 + j + k - 1) y1 = eval_to (j2 + k - 1) y1’
        by (strip_tac
            \\ irule eval_to_mono \\ simp []
            \\ strip_tac \\ gs []
            \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs [])
      \\ qexists_tac ‘j1 + j2’ \\ gs []
      \\ once_rewrite_tac [DECIDE “j1 + (j2 + k) - 1 = j2 + (j1 + k) - 1”]
      \\ gs [])
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gvs []
      \\ Cases_on ‘eval_to (k - 1) z2 = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (j1 + k - 1) x1’
          by (qx_gen_tac ‘j’
              \\ drule_then (qspec_then ‘j + k - 1’ assume_tac) eval_to_mono
              \\ drule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono
              \\ gs [])
        \\ simp [SF SFY_ss])
      \\ ‘∀j. eval_to (j3 + j + k - 1) z1 = eval_to (j3 + k - 1) z1’
        by (strip_tac
            \\ irule eval_to_mono \\ simp []
            \\ strip_tac \\ gs []
            \\ Cases_on ‘eval_to (k - 1) z2’ \\ gs [])
      \\ qexists_tac ‘j1 + j3’ \\ gs []
      \\ once_rewrite_tac [DECIDE “j1 + (j3 + k) - 1 = j3 + (j1 + k) - 1”]
      \\ gs [])
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [])
  >~ [‘Delay x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ simp [eval_to_def])
  >~ [‘Box x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ rename1 ‘exp_rel_d2b x y’
    \\ simp [eval_to_def]
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ qexists_tac ‘j’
    \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
  >~ [‘MkTick x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ rename1 ‘exp_rel_d2b x y’
    \\ simp [eval_to_def]
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ qexists_tac ‘j’
    \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ irule v_rel_d2b_DoTick \\ gs [])
  >~ [‘Value v’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ simp [eval_to_def])
  >~ [‘Prim op xs’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ simp [eval_to_def]
    \\ gvs [LIST_REL_EL_EQN]
    \\ ‘∀j. j ≤ k ⇒
          ∀n. n < LENGTH xs ⇒
            ∃m. ($= +++ v_rel_d2b) (eval_to (m + j) (EL n xs))
                                   (eval_to j (EL n ys))’
      by (rpt (pop_assum mp_tac)
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
          \\ gs [])
    \\ last_x_assum kall_tac
    \\ Cases_on ‘op’ \\ gs []
    \\ cheat) (*
    >- ((* Cons *)
      first_x_assum (qspec_then ‘k’ assume_tac) \\ gs []
      \\ Cases_on ‘result_map (eval_to k) ys = INL Diverge’ \\ gs []
      >- (
        gs [result_map_def, CaseEq "bool", MEM_MAP, MEM_EL, PULL_EXISTS]
        \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\
      )
      \\ gvs [result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac) \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gvs []
        \\ rw [] \\ gs [])
      \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        rw [] \\ gs []
        >- (
          first_x_assum (drule_then assume_tac) \\ gs []
          \\ first_x_assum (drule_then assume_tac) \\ gs []
          \\ rename1 ‘m < LENGTH ys’
          \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
        \\ fs [DECIDE “A ⇒ ¬(a < b) ⇔ (a < b) ⇒ ¬A”]
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
      \\ fs [DECIDE “A ⇒ ¬(a < b) ⇔ (a < b) ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ fs [DECIDE “A ⇒ ¬(a < b) ⇔ (a < b) ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ simp [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP]
      \\ rw [LIST_REL_EL_EQN]
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum (drule_then assume_tac)
      \\ (Cases_on ‘eval_to k (EL n xs)’ \\
          Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
      \\ rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
    >- ((* IsEq *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel_d2b x y’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_d2b v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* Proj *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel_d2b x y’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_d2b v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* AtomOp *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ ‘MAP f xs = MAP f ys’
        suffices_by (
          rw [result_map_def]
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [])
      \\ irule LIST_EQ
      \\ rw [EL_MAP, Abbr ‘f’]
      \\ first_x_assum (drule_then assume_tac)
      \\ rpt CASE_TAC \\ gs [])) *)
QED

val _ = export_theory ();

