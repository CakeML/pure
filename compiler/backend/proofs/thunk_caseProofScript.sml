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

Overload Proj = “λs i (x: exp). Prim (Proj s i) [x]”;

Overload Seq = “λx: exp. λy. Let NONE x y”;

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
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
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
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Letrec *)
    rw [Once exp_rel_lift_cases] \\ gs []
    >- ((* Lifting *)
      simp [subst_def, ELIM_UNCURRY, GSYM FILTER_REVERSE]
      \\ simp [LAMBDA_PROD, ALOOKUP_FILTER]
      \\ imp_res_tac exp_rel_lift_freevars \\ gs []
      \\ gs [ELIM_UNCURRY, FILTER_T] \\ gs [LAMBDA_PROD]
      \\ irule exp_rel_lift_Lift \\ gs []
      \\ simp [freevars_subst]
      \\ ‘DISJOINT {w} (freevars y2) ∧ DISJOINT {w} (freevars z2)’
        by gs [IN_DISJOINT]
      \\ imp_res_tac subst_remove \\ gs []
      \\ first_x_assum (drule_then (qspec_then ‘If (IsEq s i x2) y2 z2’ mp_tac))
      \\ simp [Once exp_rel_lift_cases, PULL_EXISTS, subst_def]
      \\ simp [Once exp_rel_lift_cases, PULL_EXISTS]
      \\ simp [Once exp_rel_lift_cases, PULL_EXISTS]
      \\ simp [Once exp_rel_lift_cases, PULL_EXISTS])
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
                   (Let (SOME w) x2
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
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
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
            \\ irule LIST_REL_FILTER \\ gs []
            \\ gs [LIST_REL_EL_EQN])
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
    \\ irule LIST_REL_FILTER \\ fs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
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

Definition d2b_goal_def:
  d2b_goal k x =
    ∀y.
      exp_rel_d2b x y ∧
      (∀k. eval_to k x ≠ INL Type_error) ⇒
      ∃j.
        ($= +++ v_rel_d2b)
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

Theorem exp_rel_d2b_eval_to:
  ∀k x. d2b_goal k x
Proof
  ho_match_mp_tac eval_to_WF_IND
  \\ once_rewrite_tac [d2b_goal_def]
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
    \\ ‘∀k. eval_to k f ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ first_x_assum (qspec_then ‘j’ mp_tac)
          \\ simp [eval_to_def])
    \\ ‘∃j1. ($= +++ v_rel_d2b) (eval_to (j1 + k) f) (eval_to k g)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k) f’
      \\ gs [])
    \\ ‘∃u1. eval_to k g = INR u1’
      by (Cases_on ‘eval_to k g’ \\ gs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to (j1 + k) f’ \\ gs [])
    \\ simp []
    \\ ‘∀k. eval_to k x ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (App _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ ‘eval_to (j1 + k + j) x = eval_to j x’
            by (irule eval_to_mono \\ gs [])
          \\ ‘eval_to (j1 + k + j) f = eval_to (j1 + k) f’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs [])
          \\ qexists_tac ‘j1 + k + j’ \\ simp []
          \\ Cases_on ‘eval_to (j1 + k) f’ \\ gs [])
    \\ ‘∃j2. ($= +++ v_rel_d2b) (eval_to (j2 + k) x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ ‘∃u2. eval_to (j1 + k) f = INR u2’
      by (Cases_on ‘eval_to (j1 + k) f’ \\ gs [])
    \\ gs []
    \\ Cases_on ‘eval_to k y’ \\ gs []
    >- (
      rename1 ‘_ = INL err’
      \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (j2 + k) x’ \\ gvs []
      \\ Cases_on ‘eval_to k f = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k) f = eval_to k f’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k f’ \\ gs []
      \\ Cases_on ‘eval_to k x’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ gs []
        \\ qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k) x = eval_to k x’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k x’ \\ gs [])
    \\ rename1 ‘eval_to k y = INR v1’
    \\ ‘∃v2. eval_to (j2 + k) x = INR v2’
      by (Cases_on ‘eval_to (j2 + k) x’ \\ gs [])
    \\ gs []
    \\ ‘∀j. eval_to (j + j1 + k) f = eval_to (j1 + k) f’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ ‘∀j. eval_to (j + j2 + k) x = eval_to (j2 + k) x’
      by (strip_tac
          \\ irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Cases_on ‘dest_anyClosure u1’ \\ gs []
    >- (
      qexists_tac ‘j1 + j2’ \\ gs []
      \\ once_rewrite_tac [DECIDE “j1 + (j2 + k) = j2 + (j1 + k)”]
      \\ gs []
      \\ Cases_on ‘u2’ \\ Cases_on ‘u1’ \\ gvs [dest_anyClosure_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel_d2b (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL \\ gs [])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel_d2b x0 _’ mp_tac
      \\ rw [Once exp_rel_d2b_cases] \\ gs [])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘subst (ws2 ++ [s2,w2]) b2’
    \\ ‘∃b1 ws1. dest_anyClosure u2 = INR (s2,b1,ws1) ∧
                 exp_rel_d2b b1 b2 ∧
                 LIST_REL (λ(f,v) (g,w). f = g ∧ v_rel_d2b v w) ws1 ws2’
      by (Cases_on ‘u2’ \\ Cases_on ‘u1’ \\ gvs [dest_anyClosure_def]
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
    \\ ‘∀k. eval_to k (subst (ws1 ++ [s2,v2]) b1) ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (App _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j1 + j2 + j + k’ \\ gs []
          \\ once_rewrite_tac
            [DECIDE “j + (j1 + (j2 + k)) = (j + j2) + (j1 + k)”] \\ gs []
          \\ once_rewrite_tac
            [DECIDE “j + (j1 + (j2 + k)) = (j + j1) + (j2 + k)”] \\ gs []
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ simp [])
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
    \\ once_rewrite_tac
      [DECIDE “j + (j1 + (j2 + k)) = (j + j2) + (j1 + k)”] \\ gs []
    \\ once_rewrite_tac
      [DECIDE “j + (j1 + (j2 + k)) = (j + j1) + (j2 + k)”] \\ gs []
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
      by (strip_tac \\ Cases_on ‘eval_to (k - 1) X2’ \\ gs [])
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
    \\ ‘∀j. j + k - 1 = j + (k - 1)’
      by gs []
    \\ asm_simp_tac std_ss []
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def, exp_size_def, subst_funs_def]
    \\ irule_at Any exp_rel_d2b_subst
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
    \\ rw [Once exp_rel_d2b_cases]
    \\ rename1 ‘exp_rel_d2b x y’
    \\ CONV_TAC (QUANT_CONV (LAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ CONV_TAC (QUANT_CONV (RAND_CONV (SIMP_CONV std_ss [Once eval_to_def])))
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + k) x) (eval_to k y)’
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
        \\ ‘∀j. j + k - 1 = j + (k - 1)’
          by gs []
        \\ asm_simp_tac std_ss []
        \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
        \\ first_x_assum irule
        \\ simp [eval_to_wo_def]
        \\ irule_at Any exp_rel_d2b_Force
        \\ irule_at Any exp_rel_d2b_Value
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
      \\ irule_at Any exp_rel_d2b_Force
      \\ irule_at Any exp_rel_d2b_Value \\ gs []
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
          \\ ‘∀j. j + k - 1 = j + (k - 1)’ by gs []
          \\ asm_simp_tac std_ss []
          \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
          \\ first_x_assum irule
          \\ gs [eval_to_wo_def, subst_funs_def]
          \\ irule_at Any exp_rel_d2b_subst
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
        \\ irule_at Any exp_rel_d2b_subst
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
    \\ ‘∀j1. eval_to (j1 + j + k) x = eval_to (j + k) x’
      by (gen_tac \\ irule eval_to_mono \\ gs [])
    \\ Q.REFINE_EXISTS_TAC ‘j + j1’ \\ gs []
    \\ gvs [Once (CONJUNCT2 exp_rel_d2b_cases)]
    \\ rename1 ‘eval_to k1 x1 = INR v1’
    \\ qexists_tac ‘j1 + k1’
    \\ ‘eval_to (k + k1 + j + j1 - 1) x1 = eval_to k1 x1’
      by (irule eval_to_mono \\ gs [])
    \\ gs [])
  >~ [‘If x1 y1 z1’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
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
    \\ ‘∃j1. ($= +++ v_rel_d2b) (eval_to (j1 + (k - 1)) x1)
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
      \\ ‘∃j2. ($= +++ v_rel_d2b) (eval_to (j2 + (k - 1)) y1)
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
      \\ ‘∃j2. ($= +++ v_rel_d2b) (eval_to (j2 + (k - 1)) z1)
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
    \\ rename1 ‘v_rel_d2b v w’
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs []
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
      suffices_by (
        disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
    \\ first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def]
    \\ rpt strip_tac
    \\ first_x_assum (qspec_then ‘k’ mp_tac)
    \\ simp [eval_to_def])
  >~ [‘MkTick x’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ rename1 ‘exp_rel_d2b x y’
    \\ simp [eval_to_def]
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + k) x) (eval_to k y)’
      suffices_by (
        disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k) x’ \\ Cases_on ‘eval_to k y’ \\ gs []
        \\ irule v_rel_d2b_DoTick \\ gs [])
    \\ first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def]
    \\ rpt strip_tac
    \\ first_x_assum (qspec_then ‘k’ mp_tac)
    \\ simp [eval_to_def])
  >~ [‘Value v’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
    \\ simp [eval_to_def])
  >~ [‘Let bv x1 y1’] >- (
    Cases_on ‘bv’
    >~ [‘Let (SOME s) x1 y1’] >- (
      strip_tac
      \\ rw [Once exp_rel_d2b_cases]
      >- ((* D2B *)
        pop_assum mp_tac
        \\ simp [Once eval_to_def]
        \\ simp [Once eval_to_def, subst_def]
        \\ simp [Once eval_to_def]
        \\ simp [Once eval_to_def]
        \\ simp [Once eval_to_def, dest_anyThunk_def, subst_funs_def]
        \\ strip_tac
        \\ rename1 ‘exp_rel_d2b x1 x2’ \\ rename1 ‘exp_rel_d2b y1 y2’
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
        \\ ‘∃j1. ($= +++ v_rel_d2b) (eval_to (j1 + (k - 1)) x1)
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
        \\ rename1 ‘v_rel_d2b v u’
        \\ ‘∀k. eval_to k (subst1 w v (subst1 s (Thunk (INR x1)) y1)) ≠
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
          \\ irule exp_rel_d2b_subst \\ simp []
          \\ irule exp_rel_d2b_subst \\ simp []
          \\ irule v_rel_d2b_D2B
          \\ gs [SF SFY_ss])
        \\ Q.REFINE_EXISTS_TAC ‘2 + j’ \\ simp []
        \\ qabbrev_tac ‘X1 = subst1 s (Thunk (INR x1)) (subst1 w v y1) ’
        \\ qmatch_goalsub_abbrev_tac ‘_ _ (eval_to _ X2)’
        \\ ‘∃j2. ($= +++ v_rel_d2b) (eval_to (j2 + (k - 2)) X1)
                                    (eval_to (k - 2) X2)’
          by (first_x_assum irule
              \\ gs [Abbr ‘X1’, Abbr ‘X2’, eval_to_wo_def, subst1_commutes]
              \\ irule exp_rel_d2b_subst \\ simp []
              \\ irule exp_rel_d2b_subst \\ simp []
              \\ irule v_rel_d2b_D2B
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
        \\ irule eval_to_mono \\ gs [])
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
      \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
      \\ rename1 ‘v_rel_d2b u v’
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
    \\ ‘∀k. eval_to k x1 ≠ INL Type_error’
      by (qx_gen_tac ‘j’
          \\ strip_tac
          \\ qpat_x_assum ‘∀k. eval_to _ (Let _ _ _) ≠ INL Type_error’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j + 1’
          \\ simp [])
    \\ ‘∃j. ($= +++ v_rel_d2b) (eval_to (j + (k - 1)) x1) (eval_to (k - 1) x2)’
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
  >~ [‘Prim op xs’] >- (
    ntac 2 strip_tac
    \\ rw [Once exp_rel_d2b_cases]
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
            ∃m. ($= +++ v_rel_d2b) (eval_to (m + j) (EL n xs))
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
      \\ ‘∃j. ($= +++ (LIST_REL v_rel_d2b))
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
                ($= +++ v_rel_d2b) (eval_to (k + m) (EL n xs))
                                   (eval_to k (EL n ys))’
        suffices_by (
          disch_then (qx_choose_then ‘m’ assume_tac)
          \\ qexists_tac ‘m’
          \\ IF_CASES_TAC \\ gs []
          >- (
            first_x_assum (drule_then assume_tac) \\ gs []
            \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
          \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
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
      \\ rename1 ‘exp_rel_d2b x y’
      \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
        \\ qexists_tac ‘m’ \\ simp [])
      \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
      \\ rename1 ‘v_rel_d2b v w’
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
      \\ rename1 ‘exp_rel_d2b x y’
      \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      >- (
        rename1 ‘_ = INL err’
        \\ Cases_on ‘err’ \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
        \\ qexists_tac ‘m’ \\ simp [])
      \\ Cases_on ‘eval_to (k + m - 1) x’ \\ gs []
      \\ rename1 ‘v_rel_d2b v w’
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
        \\ gs [result_map_def, CaseEq "bool", MEM_MAP]
        \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
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
      \\ gs [result_map_def, MEM_EL, EL_MAP, SF CONJ_ss, Once (CaseEq "bool"),
             DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      >- (
        ‘F’ suffices_by rw []
        \\ unabbrev_all_tac
        \\ gs [CaseEq "bool", DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ first_x_assum (drule_then (qx_choose_then ‘m’ assume_tac))
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’
        \\ Cases_on ‘eval_to (m + k - 1) (EL n xs)’ \\ gs []
        \\ first_x_assum (drule_then (qspec_then ‘m’ assume_tac))
        \\ rename1 ‘v_rel_d2b v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [])
      \\ gs [Once (CaseEq "bool"), DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel_d2b) (eval_to (j + k - 1) (EL n xs))
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
            \\ ‘∃j1. ($= +++ v_rel_d2b) (eval_to (j1 + k - 1) x)
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
      \\ IF_CASES_TAC \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
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
        \\ rename1 ‘v_rel_d2b u v’
        \\ first_x_assum (qspec_then ‘j’ assume_tac) \\ gs []
        \\ Cases_on ‘u’ \\ Cases_on ‘v’ \\ gs [])
      \\ irule_at Any LIST_EQ
      \\ rw [EL_MAP]
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ first_x_assum (qspec_then ‘j’ assume_tac)
      \\ rpt CASE_TAC \\ gs []))
QED

Theorem exp_rel_d2b_eval_to = REWRITE_RULE [d2b_goal_def] exp_rel_d2b_eval_to;

(* -------------------------------------------------------------------------
 * exp_rel_inl:
 *
 * Inline forced Box-thunks under a Let.
 * ------------------------------------------------------------------------- *)

Definition ok_binder_def[simp]:
  ok_binder (Lam s x) = T ∧
  ok_binder (Box x) = T ∧
  ok_binder (Delay x) = T ∧
  ok_binder _ = F
End

Inductive exp_rel_inl:
(* Inlining *)
[exp_rel_inl_Inline:]
  (∀m v.
     v ∈ m ⇒
       exp_rel_inl m (Var v) (Box (Var v))) ∧
[exp_rel_inl_Inline_Value:]
  (∀m v w.
     v_rel_inl v w ⇒
       exp_rel_inl m (Value (Thunk (INL v))) (Box (Value w))) ∧
[exp_rel_inl_NoInline:]
  (∀m v.
     v ∉ m ⇒
       exp_rel_inl m (Var v) (Var v)) ∧
[exp_rel_inl_Bind:]
  (∀m v w y1 y2.
     exp_rel_inl (v INSERT m) y1 y2 ∧
     w ∉ m ⇒
       exp_rel_inl m (Let (SOME v) (Box (Var w)) y1)
                     (Let (SOME v) (Var w) y2)) ∧
[exp_rel_inl_Bind_Value:]
  (∀m v x1 x2 y1 y2.
     exp_rel_inl (v INSERT m) y1 y2 ∧
     v_rel_inl x1 x2 ⇒
       exp_rel_inl m (Let (SOME v) (Box (Value x1)) y1)
                     (Let (SOME v) (Value x2) y2)) ∧
(* Boilerplate: *)
[exp_rel_inl_App:]
  (∀m f g x y.
     exp_rel_inl m f g ∧
     exp_rel_inl m x y ⇒
       exp_rel_inl m (App f x) (App g y)) ∧
[exp_rel_inl_Lam:]
  (∀m s x y.
     exp_rel_inl (m DELETE s) x y ⇒
       exp_rel_inl m (Lam s x) (Lam s y)) ∧
[exp_rel_inl_Letrec:]
  (∀m m1 f g x y.
     m1 = m DIFF set (MAP FST f) ∧
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ ok_binder x ∧ exp_rel_inl m1 x y) f g ∧
     exp_rel_inl m1 x y ⇒
       exp_rel_inl m (Letrec f x) (Letrec g y)) ∧
[exp_rel_inl_Let_SOME:]
  (∀m bv x1 y1 x2 y2.
     exp_rel_inl m x1 x2 ∧
     exp_rel_inl (m DELETE bv) y1 y2 ⇒
       exp_rel_inl m (Let (SOME bv) x1 y1) (Let (SOME bv) x2 y2)) ∧
[exp_rel_inl_Let_NONE:]
  (∀m x1 y1 x2 y2.
     exp_rel_inl m x1 x2 ∧
     exp_rel_inl m y1 y2 ⇒
       exp_rel_inl m (Let NONE x1 y1) (Let NONE x2 y2)) ∧
[exp_rel_inl_If:]
  (∀m x1 x2 y1 y2 z1 z2.
     LIST_REL (exp_rel_inl m) [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel_inl m (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_inl_Prim:]
  (∀m op xs ys.
     LIST_REL (exp_rel_inl m) xs ys ⇒
       exp_rel_inl m (Prim op xs) (Prim op ys)) ∧
[exp_rel_inl_Delay:]
  (∀m x y.
     exp_rel_inl m x y ⇒
       exp_rel_inl m (Delay x) (Delay y)) ∧
[exp_rel_inl_Box:]
  (∀m x y.
     exp_rel_inl m x y ⇒
       exp_rel_inl m (Box x) (Box y)) ∧
[exp_rel_inl_Force:]
  (∀m x y.
     exp_rel_inl m x y ⇒
       exp_rel_inl m (Force x) (Force y)) ∧
[exp_rel_inl_MkTick:]
  (∀m x y.
     exp_rel_inl m x y ⇒
       exp_rel_inl m (MkTick x) (MkTick y)) ∧
[exp_rel_inl_Value:]
  (∀m v w.
     v_rel_inl v w ⇒
       exp_rel_inl m (Value v) (Value w)) ∧
[v_rel_inl_Atom:]
  (∀x.
     v_rel_inl (Atom x) (Atom x)) ∧
[v_rel_inl_Constructor:]
  (∀vs ws.
     LIST_REL v_rel_inl vs ws ⇒
       v_rel_inl (Constructor s vs) (Constructor s ws)) ∧
[v_rel_inl_Closure:]
  (∀s x y.
     exp_rel_inl EMPTY x y ∧
     freevars x ⊆ {s} ⇒
       v_rel_inl (Closure s x) (Closure s y)) ∧
[v_rel_inl_DoTick:]
  (∀v w.
     v_rel_inl v w ⇒
       v_rel_inl (DoTick v) (DoTick w)) ∧
[v_rel_inl_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 freevars x ⊆ set (MAP FST f) ∧
                 fn = gn ∧
                 ok_binder x ∧
                 exp_rel_inl EMPTY x y) f g ⇒
       v_rel_inl (Recclosure f n) (Recclosure g n)) ∧
[v_rel_inl_Thunk_INR:]
  (∀x y.
     exp_rel_inl EMPTY x y ∧
     closed x ⇒
       v_rel_inl (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_inl_Thunk_INL:]
  (∀v w.
     v_rel_inl v w ⇒
       v_rel_inl (Thunk (INL v)) (Thunk (INL w)))
End

Theorem v_rel_inl_cases[local] = CONJUNCT2 exp_rel_inl_cases;

Theorem v_rel_inl_def[simp] =
  [ “v_rel_inl (Closure s x) z”,
    “v_rel_inl z (Closure s x)”,
    “v_rel_inl (Recclosure s x) z”,
    “v_rel_inl z (Recclosure s x)”,
    “v_rel_inl (Constructor s x) z”,
    “v_rel_inl z (Constructor s x)”,
    “v_rel_inl (Atom s) z”,
    “v_rel_inl z (Atom s)”,
    “v_rel_inl (Thunk (INL s)) z”,
    “v_rel_inl z (Thunk (INL s))”,
    “v_rel_inl (Thunk (INR s)) z”,
    “v_rel_inl z (Thunk (INR s))” ]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_inl_cases])
  |> LIST_CONJ;

Theorem exp_rel_inl_freevars:
  m ∩ freevars x = m1 ∩ freevars x ∧
  exp_rel_inl m x y ⇒
    exp_rel_inl m1 x y
Proof
  qsuff_tac ‘
    (∀m x y.
       exp_rel_inl m x y ⇒
       ∀m1.
         m ∩ freevars x = m1 ∩ freevars x ⇒
           exp_rel_inl m1 x y) ∧
    (∀v w. v_rel_inl v w ⇒ T)’
  >- (
    rw [SF SFY_ss])
  \\ ho_match_mp_tac exp_rel_inl_strongind \\ simp []
  \\ rw []
  >- ((* Inline *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Inline
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, SF SFY_ss])
  >- ((* Inline Value *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Inline_Value \\ gs [])
  >- ((* NoInline *)
    gs [freevars_def]
    \\ irule exp_rel_inl_NoInline
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, SF SFY_ss])
  >- ((* Let Bind *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Bind
    \\ first_assum (irule_at Any)
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP]
    \\ metis_tac [])
  >- ((* Let Bind Value *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Bind_Value \\ gs []
    \\ first_assum (irule_at Any)
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP])
  >- ((* App *)
    gs [freevars_def]
    \\ irule exp_rel_inl_App \\ gs []
    \\ first_x_assum (irule_at Any)
    \\ first_x_assum (irule_at Any)
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP])
  >- ((* Lam *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Lam \\ gs []
    \\ first_x_assum irule
    \\ gs [SUBSET_DEF, INTER_DEF, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP])
  >- ((* Letrec *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Letrec \\ gs []
    (*\\ qmatch_asmsub_rename_tac ‘m2 ⊆ m’*)
    (*\\ qexists_tac ‘m2 ∩ freevars (Letrec f x)’*)
    \\ first_x_assum (irule_at (Pos last))
    \\ irule_at Any LIST_REL_mono
    \\ first_x_assum (irule_at (Pos (el 2)))
    \\ rw []
    >- (
      gvs [ELIM_UNCURRY]
      \\ first_x_assum irule
      \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP, SUBSET_DEF,
             IN_DISJOINT, freevars_def, ELIM_UNCURRY, MEM_MAP]
      \\ metis_tac [])
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP, SUBSET_DEF,
           IN_DISJOINT, freevars_def, ELIM_UNCURRY, MEM_MAP]
    \\ metis_tac [])
  >- ((* Let SOME *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Let_SOME \\ gs []
    \\ first_x_assum (irule_at Any)
    \\ first_x_assum (irule_at Any)
    \\ qmatch_asmsub_rename_tac ‘freevars x1 DIFF _’
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP, SUBSET_DEF])
  >- ((* Let NONE *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Let_NONE
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM])
  >- ((* If *)
    gs [freevars_def]
    \\ irule exp_rel_inl_If \\ gs []
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM])
  >- ((* Prim *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Prim \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ rw [] \\ gs []
    \\ first_x_assum irule \\ rw []
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM, MEM_MAP]
    \\ metis_tac [])
  >- ((* Delay *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Delay \\ gs [])
  >- ((* Box *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Box \\ gs [])
  >- ((* Force *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Force \\ gs [])
  >- ((* MkTick *)
    gs [freevars_def]
    \\ irule exp_rel_inl_MkTick \\ gs [])
  >- ((* Value *)
    gs [freevars_def]
    \\ irule exp_rel_inl_Value \\ gs [])
QED

Theorem ok_binder_subst[local,simp]:
  ∀x. ok_binder x ⇒ ok_binder (subst vs x)
Proof
  Cases \\ simp [subst_def]
QED

Theorem exp_rel_inl_subst:
  ∀vs x ws y m.
    MAP FST vs = MAP FST ws ∧
    LIST_REL (λ(f,v) (g,w).
      (f ∈ m ⇒ v_rel_inl v (Thunk (INL w))) ∧
      (f ∉ m ⇒ v_rel_inl v w)) vs ws ∧
    exp_rel_inl m x y ⇒
      exp_rel_inl m (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel_inl _ _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_inl_cases]
    \\ simp [subst_def]
    >- ((* s ∈ m *)
      rpt CASE_TAC \\ gs []
      \\ imp_res_tac ALOOKUP_SOME \\ gs [ALOOKUP_NONE, MAP_REVERSE,
                                         exp_rel_inl_Inline]
      \\ drule_then (qspec_then ‘REVERSE vs’ mp_tac) ALOOKUP_SOME_EL_2
      \\ gvs [MAP_REVERSE, EL_REVERSE, LIST_REL_EL_EQN, SF CONJ_ss]
      \\ strip_tac
      \\ qmatch_asmsub_abbrev_tac ‘EL k vs’
      \\ ‘k < LENGTH ws’ by gs [Abbr ‘k’]
      \\ first_x_assum (drule_then assume_tac)
      \\ rpt (pairarg_tac \\ gvs [])
      \\ irule exp_rel_inl_Inline_Value
      \\ gs [])
        (* s ∉ m *)
    \\ rpt CASE_TAC \\ gs []
    \\ imp_res_tac ALOOKUP_SOME \\ gs [ALOOKUP_NONE, MAP_REVERSE,
                                       exp_rel_inl_NoInline]
    \\ irule exp_rel_inl_Value
    \\ drule_then (qspec_then ‘REVERSE vs’ mp_tac) ALOOKUP_SOME_EL_2
    \\ gvs [MAP_REVERSE, EL_REVERSE, LIST_REL_EL_EQN, SF CONJ_ss]
    \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac ‘EL k vs’
    \\ ‘k < LENGTH ws’ by gs [Abbr ‘k’]
    \\ first_x_assum (drule_then assume_tac)
    \\ rpt (pairarg_tac \\ gvs []))
  >- ((* Prim *)
    rw [Once exp_rel_inl_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_inl_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ first_x_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* If *)
    rw [Once exp_rel_inl_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_inl_If \\ fs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs [SF SFY_ss])
  >- ((* App *)
    rw [Once exp_rel_inl_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_inl_App \\ fs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs [SF SFY_ss])
  >- ((* Lam *)
    rw [Once exp_rel_inl_cases]
    \\ gs [subst_def]
    \\ irule exp_rel_inl_Lam
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ simp [FORALL_PROD]
    \\ rw [] \\ gs [Abbr ‘P’])
  >- ((* Let NONE *)
    rw [Once exp_rel_inl_cases]
    \\ gs [subst_def]
    \\ irule exp_rel_inl_Let_NONE \\ fs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs [SF SFY_ss])
  >- ((* Let SOME + Let Bind *)
    rw [Once exp_rel_inl_cases] \\ gs []
    >- ((* Let Bind *)
      simp [subst_def]
      \\ rpt CASE_TAC \\ gs []
      \\ imp_res_tac ALOOKUP_SOME \\ gs [ALOOKUP_NONE, MAP_REVERSE]
      \\ (irule exp_rel_inl_Bind ORELSE irule exp_rel_inl_Bind_Value) \\ gs []
      \\ first_x_assum (irule_at (Pos last))
      \\ gvs [MAP_FST_FILTER, EVERY2_MAP, LAMBDA_PROD]
      \\ rw []
      >~ [‘v_rel_inl v1 v2’] >- (
        drule_then (qspec_then ‘REVERSE vs’ mp_tac) ALOOKUP_SOME_EL_2
        \\ gvs [MAP_REVERSE, LIST_REL_EL_EQN, EL_REVERSE, SF CONJ_ss]
        \\ rw []
        \\ qmatch_asmsub_abbrev_tac  ‘EL k vs’
        \\ ‘k < LENGTH ws’ by gs [Abbr ‘k’]
        \\ first_x_assum (drule_then assume_tac)
        \\ gvs [ELIM_UNCURRY])
      \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
      \\ irule LIST_REL_FILTER \\ gs []
      \\ irule LIST_REL_mono
      \\ first_x_assum (irule_at Any)
      \\ simp [FORALL_PROD]
      \\ rw [] \\ gs [Abbr ‘P’])
    >- (
      simp [subst_def]
      \\ irule exp_rel_inl_Bind_Value \\ gs []
      \\ first_x_assum irule
      \\ gvs [MAP_FST_FILTER, EVERY2_MAP, LAMBDA_PROD]
      \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
      \\ irule LIST_REL_FILTER \\ gs []
      \\ irule LIST_REL_mono
      \\ first_x_assum (irule_at Any)
      \\ simp [FORALL_PROD]
      \\ rw [] \\ gs [Abbr ‘P’])
    \\ simp [subst_def]
    \\ irule exp_rel_inl_Let_SOME \\ simp []
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ simp [FORALL_PROD]
    \\ rw [] \\ gs [Abbr ‘P’])
  >- ((* Letrec *)
    rw [Once exp_rel_inl_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_inl_Letrec
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
    rw [Once exp_rel_inl_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_inl_Delay
    \\ first_x_assum irule \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Box *)
    rw [Once exp_rel_inl_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_inl_Box
    \\ first_x_assum irule \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_inl_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_inl_Force
    \\ first_x_assum irule \\ gs [])
  >- ((* Value *)
    rw [Once exp_rel_inl_cases]
    \\ simp [subst_def, exp_rel_inl_Value, exp_rel_inl_Inline_Value])
  >- ((* MkTick *)
    rw [Once exp_rel_inl_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_inl_MkTick
    \\ first_x_assum irule \\ gs []
    \\ first_assum (irule_at Any))
QED

Theorem exp_rel_inl_eval_to:
  ∀k x y m.
    closed x ∧
    exp_rel_inl m x y ⇒
      ($= +++ v_rel_inl)
        (eval_to k x)
        (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ simp []
  \\ rpt conj_tac \\ rpt gen_tac
  >~ [‘Value v’] >- (
    rw [Once exp_rel_inl_cases]
    \\ simp [eval_to_def])
  >~ [‘App f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_inl_cases] \\ gs []
    \\ rename1 ‘exp_rel_inl _ x y’
    \\ gs [eval_to_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k f’ \\ Cases_on ‘eval_to k g’ \\ gvs []
    \\ rename1 ‘v_rel_inl v w’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyClosure_def]
    >- ((* Closure *)
      IF_CASES_TAC \\ gs []
      \\ rename1 ‘(_ +++ _) (_ _ (subst1 s u1 e1)) (_ _ (subst1 s u2 e2))’
      \\ ‘[s,u1] = [] ++ [s,u1]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ ‘[s,u2] = [] ++ [s,u2]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ first_x_assum irule \\ gs [closed_subst]
      \\ irule_at Any exp_rel_inl_subst
      \\ first_assum (irule_at Any) \\ gs [])
        (* Recclosure *)
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘OPTREL (exp_rel_inl EMPTY) (ALOOKUP (REVERSE xs) s)
                                   (ALOOKUP (REVERSE ys) s)’
      by (irule LIST_REL_OPTREL \\ gs []
          \\ gs [ELIM_UNCURRY, LIST_REL_CONJ])
    \\ gs [OPTREL_def]
    \\ gvs [Once exp_rel_inl_cases]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_inl_subst
    \\ first_assum (irule_at Any)
    \\ simp [EVERY2_MAP, LAMBDA_PROD]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ csimp [FORALL_PROD]
    \\ simp [closed_subst, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM
             FST_THM]
    \\ irule_at Any LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ gvs [freevars_def, SUBSET_DEF, SF ETA_ss, SF DNF_ss, DISJ_SYM,
            DISJ_EQ_IMP])
  >~ [‘Lam s x’] >- (
    rw [Once exp_rel_inl_cases]
    \\ gs [eval_to_def, v_rel_inl_def]
    \\ irule exp_rel_inl_freevars
    \\ gs [SUBSET_DEF, EXTENSION]
    \\ first_assum (irule_at Any)
    \\ rw [Once DISJ_SYM, DISJ_EQ_IMP])
  >~ [‘Let NONE x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_inl_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any))
  >~ [‘Let (SOME n) x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_inl_cases] \\ gs []
    >- ((* Bind Value *)
      simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ first_x_assum irule
      \\ simp [closed_subst]
      \\ irule_at Any exp_rel_inl_subst \\ gs []
      \\ first_assum (irule_at Any) \\ gs [])
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ simp [closed_subst]
    \\ irule_at Any exp_rel_inl_subst
    \\ first_assum (irule_at Any)
    \\ simp [])
  >~ [‘Letrec f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_inl_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def, closed_subst, MAP_MAP_o, combinTheory.o_DEF,
             LAMBDA_PROD, GSYM FST_THM]
    \\ irule_at Any exp_rel_inl_subst
    \\ simp [subst_funs_def, closed_subst, MAP_MAP_o, combinTheory.o_DEF,
             LAMBDA_PROD, GSYM FST_THM, EVERY2_MAP]
    \\ rw [RIGHT_EXISTS_AND_THM]
    >- (
      irule LIST_EQ
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY])
    \\ first_assum (irule_at Any)
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD, MEM_MAP, EXISTS_PROD, DISJ_EQ_IMP, SF CONJ_ss,
             SF SFY_ss] \\ rw []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD] \\ rw []
    \\ gs [BIGUNION, SUBSET_DEF, MEM_MAP, EXISTS_PROD, PULL_EXISTS,
           SF SFY_ss]
    \\ irule_at Any exp_rel_inl_freevars
    \\ first_assum (irule_at Any)
    \\ rw [IN_INTER, EXTENSION, MEM_MAP, EXISTS_PROD, PULL_EXISTS,
           Once DISJ_SYM, DISJ_EQ_IMP, SF SFY_ss])
  >~ [‘If x1 y1 z1’] >- (
    strip_tac
    \\ rw [Once exp_rel_inl_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [v_rel_inl_def]
    \\ IF_CASES_TAC \\ gs [v_rel_inl_def])
  >~ [‘Force x’] >- (
    strip_tac
    \\ rw [Once exp_rel_inl_cases] \\ gs []
    \\ rename1 ‘exp_rel_inl m x y’
    \\ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘v_rel_inl v w’
    \\ Cases_on ‘dest_Tick v’ \\ gs []
    >- (
      ‘dest_Tick w = NONE’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_inl_cases])
      \\ gs []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
      >- (
        rename1 ‘LIST_REL _ xs ys’
        \\ ‘OPTREL (λx0 y0. ok_binder x0 ∧
                            exp_rel_inl EMPTY x0 y0)
                   (ALOOKUP (REVERSE xs) s)
                   (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL \\ gs []
              \\ gs [ELIM_UNCURRY, LIST_REL_CONJ])
        \\ gs [OPTREL_def]
        \\ gvs [Once exp_rel_inl_cases]
        \\ first_x_assum irule
        \\ simp [subst_funs_def]
        \\ irule_at Any exp_rel_inl_subst
        \\ gs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
               GSYM FST_THM]
        \\ irule_at Any LIST_REL_mono
        \\ csimp [FORALL_PROD]
        \\ first_assum (irule_at Any)
        \\ first_assum (irule_at Any)
        \\ simp []
        \\ ‘MAP FST xs = MAP FST ys’
          by (irule LIST_EQ
              \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY])
        \\ gs [DISJOINT_ALT, MEM_MAP, PULL_EXISTS, FORALL_PROD,
               DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”, SF SFY_ss]
        \\ simp [closed_subst]
        \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
               LIST_REL_EL_EQN]
        \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
        \\ first_x_assum (drule_then assume_tac)
        \\ gs [ELIM_UNCURRY, freevars_def])
      \\ CASE_TAC \\ gs []
      \\ first_x_assum irule
      \\ simp [subst_funs_def, SF SFY_ss])
    \\ ‘∃y. dest_Tick w = SOME y’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_inl_cases])
    \\ gs []
    \\ first_x_assum irule
    \\ rw [Once exp_rel_inl_cases]
    \\ rw [Once exp_rel_inl_cases]
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [Once v_rel_inl_cases])
  >~ [‘Delay x’] >- (
    rw [Once exp_rel_inl_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ irule exp_rel_inl_freevars
    \\ first_assum (irule_at Any)
    \\ gs [closed_def])
  >~ [‘Box x’] >- (
    strip_tac
    \\ rw [Once exp_rel_inl_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel_inl m x y’
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
  >~ [‘MkTick x’] >- (
    strip_tac
    \\ rw [Once exp_rel_inl_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel_inl m x y’
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rw [Once v_rel_inl_cases])
  >~ [‘Prim op xs’] >- (
    strip_tac
    \\ rw [Once exp_rel_inl_cases] \\ gs []
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
      \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        >- (
          rename1 ‘j < LENGTH ys’
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ Cases_on ‘eval_to k (EL j xs)’ \\ gs [])
        \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ rw [] \\ gs []
        \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_then assume_tac) \\ gs []
        \\ first_x_assum (drule_all_then assume_tac) \\ gs []
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
      \\ first_x_assum (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to k (EL n xs)’
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
      \\ rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
    >- ((* IsEq *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1n ⇔ n = 0”]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel_inl m x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_inl v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* Proj *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1n ⇔ n = 0”]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel_inl m x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_inl v w’
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
      \\ first_x_assum (drule_all_then assume_tac)
      \\ rpt CASE_TAC \\ gs []))
QED

(* -------------------------------------------------------------------------
 * exp_rel_unbox:
 *
 * Remove immediately forced thunks introduced by exp_rel_inl.
 * ------------------------------------------------------------------------- *)

Inductive exp_rel_unbox:
(* Force replacement *)
[exp_rel_unbox_Unbox:]
  (∀v.
     exp_rel_unbox (Force (Box (Var v))) (Tick (Var v))) ∧
[exp_rel_unbox_Unbox_Value:]
  (∀v w.
     v_rel_unbox v w ⇒
       exp_rel_unbox (Force (Box (Value v))) (Tick (Value w))) ∧
(* Boilerplate: *)
[exp_rel_unbox_App:]
  (∀f g x y.
     exp_rel_unbox f g ∧
     exp_rel_unbox x y ⇒
       exp_rel_unbox (App f x) (App g y)) ∧
[exp_rel_unbox_Lam:]
  (∀s x y.
     exp_rel_unbox x y ⇒
       exp_rel_unbox (Lam s x) (Lam s y)) ∧
[exp_rel_unbox_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 ok_binder x ∧
                 exp_rel_unbox x y) f g ∧
     exp_rel_unbox x y ⇒
       exp_rel_unbox (Letrec f x) (Letrec g y)) ∧
[exp_rel_unbox_Let:]
  (∀b x1 y1 x2 y2.
     exp_rel_unbox x1 x2 ∧
     exp_rel_unbox y1 y2 ⇒
       exp_rel_unbox (Let b x1 y1) (Let b x2 y2)) ∧
[exp_rel_unbox_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL exp_rel_unbox [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel_unbox (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_unbox_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel_unbox xs ys ⇒
       exp_rel_unbox (Prim op xs) (Prim op ys)) ∧
[exp_rel_unbox_Delay:]
  (∀x y.
     exp_rel_unbox x y ⇒
       exp_rel_unbox (Delay x) (Delay y)) ∧
[exp_rel_unbox_Box:]
  (∀x y.
     exp_rel_unbox x y ⇒
       exp_rel_unbox (Box x) (Box y)) ∧
[exp_rel_unbox_Force:]
  (∀x y.
     exp_rel_unbox x y ⇒
       exp_rel_unbox (Force x) (Force y)) ∧
[exp_rel_unbox_MkTick:]
  (∀x y.
     exp_rel_unbox x y ⇒
       exp_rel_unbox (MkTick x) (MkTick y)) ∧
[exp_rel_unbox_Var:]
  (∀v.
     exp_rel_unbox (Var v) (Var v)) ∧
[exp_rel_unbox_Value:]
  (∀v w.
     v_rel_unbox v w ⇒
       exp_rel_unbox (Value v) (Value w)) ∧
[v_rel_unbox_Atom:]
  (∀x.
     v_rel_unbox (Atom x) (Atom x)) ∧
[v_rel_unbox_Constructor:]
  (∀vs ws.
     LIST_REL v_rel_unbox vs ws ⇒
       v_rel_unbox (Constructor s vs) (Constructor s ws)) ∧
[v_rel_unbox_Closure:]
  (∀s x y.
     exp_rel_unbox x y ⇒
       v_rel_unbox (Closure s x) (Closure s y)) ∧
[v_rel_unbox_DoTick:]
  (∀v w.
     v_rel_unbox v w ⇒
       v_rel_unbox (DoTick v) (DoTick w)) ∧
[v_rel_unbox_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 ok_binder x ∧
                 exp_rel_unbox x y) f g ⇒
       v_rel_unbox (Recclosure f n) (Recclosure g n)) ∧
[v_rel_unbox_Thunk_INR:]
  (∀x y.
     exp_rel_unbox x y ⇒
       v_rel_unbox (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_unbox_Thunk_INL:]
  (∀v w.
     v_rel_unbox v w ⇒
       v_rel_unbox (Thunk (INL v)) (Thunk (INL w)))
End

Theorem v_rel_unbox_cases[local] = CONJUNCT2 exp_rel_unbox_cases;

Theorem v_rel_unbox_def[simp] =
  [ “v_rel_unbox (Closure s x) z”,
    “v_rel_unbox z (Closure s x)”,
    “v_rel_unbox (Recclosure s x) z”,
    “v_rel_unbox z (Recclosure s x)”,
    “v_rel_unbox (Constructor s x) z”,
    “v_rel_unbox z (Constructor s x)”,
    “v_rel_unbox (Atom s) z”,
    “v_rel_unbox z (Atom s)”,
    “v_rel_unbox (Thunk (INL s)) z”,
    “v_rel_unbox z (Thunk (INL s))”,
    “v_rel_unbox (Thunk (INR s)) z”,
    “v_rel_unbox z (Thunk (INR s))” ]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_unbox_cases])
  |> LIST_CONJ;

Theorem exp_rel_unbox_subst:
  ∀vs x ws y.
    MAP FST vs = MAP FST ws ∧
    LIST_REL v_rel_unbox (MAP SND vs) (MAP SND ws) ∧
    exp_rel_unbox x y ⇒
      exp_rel_unbox (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel_unbox _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_unbox_cases]
    \\ simp [subst_def]
    \\ ‘OPTREL v_rel_unbox (ALOOKUP (REVERSE vs) s) (ALOOKUP (REVERSE ws) s)’
      suffices_by (
        strip_tac
        \\ gs [OPTREL_def, exp_rel_unbox_Var, exp_rel_unbox_Value])
    \\ irule LIST_REL_OPTREL
    \\ gs [LIST_REL_CONJ, ELIM_UNCURRY, EVERY2_MAP]
    \\ last_x_assum mp_tac
    \\ pop_assum kall_tac
    \\ qid_spec_tac ‘ws’
    \\ Induct_on ‘vs’ \\ simp []
    \\ Cases_on ‘ws’ \\ simp [])
  >- ((* Prim *)
    rw [Once exp_rel_unbox_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_unbox_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* If *)
    rw [Once exp_rel_unbox_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_unbox_If \\ fs [])
  >- ((* App *)
    rw [Once exp_rel_unbox_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_unbox_App \\ fs [])
  >- ((* Lam *)
    rw [Once exp_rel_unbox_cases]
    \\ gs [subst_def]
    \\ irule exp_rel_unbox_Lam
    \\ first_x_assum irule
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ simp [FORALL_PROD])
  >- ((* Let NONE *)
    rw [Once exp_rel_unbox_cases]
    \\ gs [subst_def]
    \\ irule exp_rel_unbox_Let \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_unbox_cases] \\ gs []
    \\ gs [subst_def]
    \\ irule exp_rel_unbox_Let \\ gs []
    \\ first_x_assum irule
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ simp [FORALL_PROD])
  >- ((* Letrec *)
    rw [Once exp_rel_unbox_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_unbox_Letrec
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
    rw [Once exp_rel_unbox_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_unbox_Delay \\ gs [])
  >- ((* Box *)
    rw [Once exp_rel_unbox_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_unbox_Box \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_unbox_cases]
    \\ simp [subst_def, FILTER_T, ELIM_UNCURRY, exp_rel_unbox_Force,
             exp_rel_unbox_Unbox_Value]
    \\ ‘OPTREL v_rel_unbox (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      suffices_by (
        strip_tac
        \\ gs [OPTREL_def, exp_rel_unbox_Var, exp_rel_unbox_Unbox,
               exp_rel_unbox_Unbox_Value])
    \\ irule LIST_REL_OPTREL
    \\ gs [LIST_REL_CONJ, ELIM_UNCURRY, EVERY2_MAP]
    \\ qpat_x_assum ‘MAP FST vs = _’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qid_spec_tac ‘ws’
    \\ Induct_on ‘vs’ \\ simp []
    \\ Cases_on ‘ws’ \\ simp [])
  >- ((* Value *)
    rw [Once exp_rel_unbox_cases]
    \\ simp [subst_def, exp_rel_unbox_Value])
  >- ((* MkTick *)
    rw [Once exp_rel_unbox_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_unbox_MkTick \\ gs [])
QED

Theorem exp_rel_unbox_eval_to:
  ∀k x y m.
    exp_rel_unbox x y ⇒
      ($= +++ v_rel_unbox)
        (eval_to k x)
        (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ simp []
  \\ rpt conj_tac \\ rpt gen_tac
  >~ [‘Var v’] >- (
    rw [Once exp_rel_unbox_cases]
    \\ simp [eval_to_def])
  >~ [‘Value v’] >- (
    rw [Once exp_rel_unbox_cases]
    \\ simp [eval_to_def])
  >~ [‘App f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_unbox_cases] \\ gs []
    \\ rename1 ‘exp_rel_unbox x y’
    \\ gs [eval_to_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k f’ \\ Cases_on ‘eval_to k g’ \\ gvs []
    \\ rename1 ‘v_rel_unbox v w’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyClosure_def]
    >- ((* Closure *)
      IF_CASES_TAC \\ gs []
      \\ rename1 ‘(_ +++ _) (_ _ (subst1 s u1 e1)) (_ _ (subst1 s u2 e2))’
      \\ ‘[s,u1] = [] ++ [s,u1]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ ‘[s,u2] = [] ++ [s,u2]’ by gs [] \\ pop_assum SUBST1_TAC
      \\ first_x_assum irule \\ gs [closed_subst]
      \\ irule_at Any exp_rel_unbox_subst
      \\ first_assum (irule_at Any) \\ gs [])
        (* Recclosure *)
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘OPTREL exp_rel_unbox (ALOOKUP (REVERSE xs) s)
                             (ALOOKUP (REVERSE ys) s)’
      by (irule LIST_REL_OPTREL \\ gs []
          \\ gs [ELIM_UNCURRY, LIST_REL_CONJ])
    \\ gs [OPTREL_def]
    \\ gvs [Once exp_rel_unbox_cases]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_unbox_subst
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
    rw [Once exp_rel_unbox_cases]
    \\ gs [eval_to_def, v_rel_unbox_def])
  >~ [‘Let NONE x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_unbox_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
  >~ [‘Let (SOME n) x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_unbox_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ irule_at Any exp_rel_unbox_subst \\ gs [])
  >~ [‘Letrec f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_unbox_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def, closed_subst, MAP_MAP_o, combinTheory.o_DEF,
             LAMBDA_PROD, GSYM FST_THM]
    \\ irule_at Any exp_rel_unbox_subst
    \\ simp [subst_funs_def, closed_subst, MAP_MAP_o, combinTheory.o_DEF,
             LAMBDA_PROD, GSYM FST_THM, EVERY2_MAP]
    \\ irule_at Any LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY])
  >~ [‘If x1 y1 z1’] >- (
    strip_tac
    \\ rw [Once exp_rel_unbox_cases] \\ gs []
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
    \\ rw [Once exp_rel_unbox_cases] \\ gs []
    >- (
      once_rewrite_tac [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ simp [Once eval_to_def]
      \\ simp [Once eval_to_def]
      \\ simp [subst_funs_def, eval_to_def])
    >- ((* Unbox *)
      once_rewrite_tac [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ simp [Once eval_to_def, subst_funs_def]
      \\ once_rewrite_tac [eval_to_def]
      \\ simp [dest_anyThunk_def])
    \\ rename1 ‘exp_rel_unbox x y’
    \\ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘v_rel_unbox v w’
    \\ Cases_on ‘dest_Tick v’ \\ gs []
    >- (
      ‘dest_Tick w = NONE’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_unbox_cases])
      \\ gs []
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
      >- (
        rename1 ‘LIST_REL _ xs ys’
        \\ ‘OPTREL (λx0 y0. ok_binder x0 ∧
                            exp_rel_unbox x0 y0)
                   (ALOOKUP (REVERSE xs) s)
                   (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL \\ gs []
              \\ gs [ELIM_UNCURRY, LIST_REL_CONJ])
        \\ gs [OPTREL_def]
        \\ gvs [Once exp_rel_unbox_cases]
        \\ first_x_assum irule
        \\ simp [subst_funs_def]
        \\ irule_at Any exp_rel_unbox_subst
        \\ gs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
               GSYM FST_THM]
        \\ irule_at Any LIST_REL_mono
        \\ csimp [FORALL_PROD]
        \\ first_assum (irule_at Any)
        \\ simp []
        \\ irule LIST_EQ
        \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY])
      \\ CASE_TAC \\ gs []
      \\ first_x_assum irule
      \\ simp [subst_funs_def, SF SFY_ss])
    \\ ‘∃y. dest_Tick w = SOME y’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_unbox_cases])
    \\ gs []
    \\ first_x_assum irule
    \\ rw [Once exp_rel_unbox_cases]
    \\ rw [Once exp_rel_unbox_cases]
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [Once v_rel_unbox_cases])
  >~ [‘Delay x’] >- (
    rw [Once exp_rel_unbox_cases] \\ gs []
    \\ simp [eval_to_def])
  >~ [‘Box x’] >- (
    strip_tac
    \\ rw [Once exp_rel_unbox_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel_unbox x y’
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
  >~ [‘MkTick x’] >- (
    strip_tac
    \\ rw [Once exp_rel_unbox_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel_unbox x y’
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rw [Once v_rel_unbox_cases])
  >~ [‘Prim op xs’] >- (
    strip_tac
    \\ rw [Once exp_rel_unbox_cases] \\ gs []
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
      \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        >- (
          rename1 ‘j < LENGTH ys’
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_all_then assume_tac)
          \\ Cases_on ‘eval_to k (EL j xs)’ \\ gs [])
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
      \\ rename1 ‘exp_rel_unbox x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_unbox v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* Proj *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1n ⇔ n = 0”]
      \\ IF_CASES_TAC \\ gs []
      \\ rename1 ‘exp_rel_unbox x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_unbox v w’
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
 * exp_rel_case: remove the final double-thunks introduced by pure2thunk.
 * Like the relation in thunk_unthunkProof, except it lets us turn some
 * 'double' thunks like this one:
 *
 *   Delay (Force (Proj s i (Var v)))
 *
 * into this one:
 *
 *   Proj s i (Var v)
 *
 * TODO:
 * - the clocks line up in the Proj case, but the code on the right side
 *   can diverge inside the Let. the new program always needs one extra
 *   clock to get past the second Proj, but if we give it extra then the clocks
 *   wont line up when we get to x/y.
 * - v_rel_case_Proj becomes an issue in Force. it might help generalizing it
 *
 * ------------------------------------------------------------------------- *)

Inductive exp_rel_case:
(* Proj *)
[exp_rel_case_Proj:]
  (∀x y s i v w.
     exp_rel_case x y ⇒
       exp_rel_case (Seq (Proj s i (Var v))
                         (Let (SOME w) (Delay (Force (Proj s i (Var v)))) x))
                    (Seq (Proj s i (Var v))
                         (Let (SOME w) (MkTick (Proj s i (Var v))) y))) ∧
[exp_rel_case_Proj_Value:]
  (∀x y s i u v w.
     exp_rel_case x y ∧
     v_rel_case u v ⇒
       exp_rel_case (Seq (Proj s i (Value u))
                         (Let (SOME w) (Delay (Force (Proj s i (Value u)))) x))
                    (Seq (Proj s i (Value v))
                         (Let (SOME w) (MkTick (Proj s i (Value v))) y))) ∧
[v_rel_case_Proj:]
  (∀xs ys s i.
     i < LENGTH xs ∧
     v_rel_case (EL i xs) (EL i ys) ⇒
       v_rel_case (Thunk (INR (Force (Proj s i (Value (Constructor s xs))))))
                  (DoTick (EL i ys))) ∧
(* Boilerplate: *)
[exp_rel_case_App:]
  (∀f g x y.
     exp_rel_case f g ∧
     exp_rel_case x y ⇒
       exp_rel_case (App f x) (App g y)) ∧
[exp_rel_case_Lam:]
  (∀s x y.
     exp_rel_case x y ⇒
       exp_rel_case (Lam s x) (Lam s y)) ∧
[exp_rel_case_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 (*ok_binder x ∧*)
                 exp_rel_case x y) f g ∧
     exp_rel_case x y ⇒
       exp_rel_case (Letrec f x) (Letrec g y)) ∧
[exp_rel_case_Let_SOME:]
  (∀bv x1 y1 x2 y2.
     exp_rel_case x1 x2 ∧
     exp_rel_case y1 y2 ⇒
       exp_rel_case (Let (SOME bv) x1 y1) (Let (SOME bv) x2 y2)) ∧
[exp_rel_case_Let_NONE:]
  (∀x1 y1 x2 y2.
     exp_rel_case x1 x2 ∧
     exp_rel_case y1 y2 ⇒
       exp_rel_case (Let NONE x1 y1) (Let NONE x2 y2)) ∧
[exp_rel_case_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL exp_rel_case [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel_case (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_case_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel_case xs ys ⇒
       exp_rel_case (Prim op xs) (Prim op ys)) ∧
[exp_rel_case_Delay:]
  (∀x y.
     exp_rel_case x y ⇒
       exp_rel_case (Delay x) (Delay y)) ∧
[exp_rel_case_Box:]
  (∀x y.
     exp_rel_case x y ⇒
       exp_rel_case (Box x) (Box y)) ∧
[exp_rel_case_Force:]
  (∀x y.
     exp_rel_case x y ⇒
       exp_rel_case (Force x) (Force y)) ∧
[exp_rel_case_MkTick:]
  (∀x y.
     exp_rel_case x y ⇒
       exp_rel_case (MkTick x) (MkTick y)) ∧
[exp_rel_case_Var:]
  (∀v.
     exp_rel_case (Var v) (Var v)) ∧
[exp_rel_case_Value:]
  (∀v w.
     v_rel_case v w ⇒
       exp_rel_case (Value v) (Value w)) ∧
[v_rel_case_Atom:]
  (∀x.
     v_rel_case (Atom x) (Atom x)) ∧
[v_rel_case_Constructor:]
  (∀vs ws.
     LIST_REL v_rel_case vs ws ⇒
       v_rel_case (Constructor s vs) (Constructor s ws)) ∧
[v_rel_case_Closure:]
  (∀s x y.
     exp_rel_case x y ∧
     freevars x ⊆ {s} ⇒
       v_rel_case (Closure s x) (Closure s y)) ∧
[v_rel_case_DoTick:]
  (∀v w.
     v_rel_case v w ⇒
       v_rel_case (DoTick v) (DoTick w)) ∧
[v_rel_case_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 freevars x ⊆ set (MAP FST f) ∧
                 fn = gn ∧
                 ok_binder x ∧
                 exp_rel_case x y) f g ⇒
       v_rel_case (Recclosure f n) (Recclosure g n)) ∧
[v_rel_case_Thunk_INR:]
  (∀x y.
     exp_rel_case x y ∧
     closed x ⇒
       v_rel_case (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_case_Thunk_INL:]
  (∀v w.
     v_rel_case v w ⇒
       v_rel_case (Thunk (INL v)) (Thunk (INL w)))
End

Theorem v_rel_case_cases[local] = CONJUNCT2 exp_rel_case_cases;

Theorem v_rel_case_def[simp] =
  [ “v_rel_case (Closure s x) z”,
    “v_rel_case z (Closure s x)”,
    “v_rel_case (Recclosure s x) z”,
    “v_rel_case z (Recclosure s x)”,
    “v_rel_case (Constructor s x) z”,
    “v_rel_case z (Constructor s x)”,
    “v_rel_case (DoTick x) z”,
    “v_rel_case z (DoTick x)”,
    “v_rel_case (Atom s) z”,
    “v_rel_case z (Atom s)”,
    “v_rel_case (Thunk (INL s)) z”,
    “v_rel_case z (Thunk (INL s))”,
    “v_rel_case (Thunk (INR s)) z”,
    “v_rel_case z (Thunk (INR s))” ]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_case_cases])
  |> LIST_CONJ;

Theorem exp_rel_case_subst:
  ∀vs x ws y m.
    MAP FST vs = MAP FST ws ∧
    LIST_REL v_rel_case (MAP SND vs) (MAP SND ws) ∧
    exp_rel_case x y ⇒
      exp_rel_case (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel_case _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ ‘OPTREL v_rel_case (ALOOKUP (REVERSE vs) s) (ALOOKUP (REVERSE ws) s)’
      suffices_by (
        strip_tac
        \\ gs [OPTREL_def, exp_rel_case_Var, exp_rel_case_Value])
    \\ irule LIST_REL_OPTREL
    \\ gs [LIST_REL_CONJ, ELIM_UNCURRY, EVERY2_MAP]
    \\ qpat_x_assum ‘MAP FST vs = _’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qid_spec_tac ‘ws’
    \\ Induct_on ‘vs’ \\ simp []
    \\ Cases_on ‘ws’ \\ simp [])
  >- ((* Prim *)
    rw [Once exp_rel_case_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_case_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw [])
  >- ((* If *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_case_If \\ simp [])
  >- ((* App *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_case_App \\ gs [])
  >- ((* Lam *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_case_Lam \\ gs []
    \\ first_x_assum irule
    \\ qabbrev_tac ‘P = λn. n ≠ s’
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ irule LIST_REL_FILTER \\ gs []
    \\ gvs [LIST_REL_EL_EQN])
  >- ((* Let NONE *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ qmatch_asmsub_rename_tac ‘exp_rel_case x y’
    >- ((* Proj *)
      ‘exp_rel_case (subst (FILTER (λ(n,x). n ≠ w) vs) x)
                    (subst (FILTER (λ(n,x). n ≠ w) ws) y)’
        by (first_x_assum
              (drule_then
                (qspec_then ‘Let (SOME w) (Delay (Force (Proj s i (Var v)))) y’
                 mp_tac))
            \\ simp [Once exp_rel_case_cases, PULL_EXISTS, subst_def]
            \\ ntac 5 (simp [Once exp_rel_case_cases, PULL_EXISTS]))
      \\ ‘OPTREL v_rel_case (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
        by (irule LIST_REL_OPTREL
            \\ gs [LIST_REL_CONJ, ELIM_UNCURRY, EVERY2_MAP]
            \\ qpat_x_assum ‘MAP FST vs = _’ mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ qid_spec_tac ‘ws’
            \\ Induct_on ‘vs’ \\ simp []
            \\ Cases_on ‘ws’ \\ simp [])
      \\ gs [OPTREL_def, exp_rel_case_Proj, exp_rel_case_Proj_Value])
    >- (
      ‘exp_rel_case (subst (FILTER (λ(n,x). n ≠ w) vs) x)
                    (subst (FILTER (λ(n,x). n ≠ w) ws) y)’
        by (first_x_assum
              (drule_then
                (qspec_then ‘Let (SOME w)
                                 (Delay (Force (Proj s i (Value v)))) y’
                 mp_tac))
            \\ simp [Once exp_rel_case_cases, PULL_EXISTS, subst_def]
            \\ ntac 5 (simp [Once exp_rel_case_cases, PULL_EXISTS]))
      \\ gs [exp_rel_case_Proj_Value])
    \\ irule exp_rel_case_Let_NONE \\ gs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_case_Let_SOME \\ gs []
    \\ first_x_assum irule
    \\ qabbrev_tac ‘P = λn. n ≠ s’
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >- ((* Letrec *)
    rw [Once exp_rel_case_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_case_Letrec
    \\ first_x_assum (irule_at Any)
    \\ ‘MAP FST f = MAP FST g’
      by (irule LIST_EQ
          \\ gvs [EL_MAP, LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ gvs [EVERY2_MAP, MAP_FST_FILTER]
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST g)’ \\ gs []
    \\ irule_at Any LIST_REL_FILTER \\ gs []
    \\ conj_tac
    >- gvs [LIST_REL_EL_EQN]
    \\ irule_at Any LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ simp [FORALL_PROD] \\ rw []
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER, SF SFY_ss]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >- ((* Delay *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_case_Delay \\ gs [])
  >- ((* Box *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_case_Box \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_case_Force
    \\ first_x_assum irule \\ gs [])
  >- ((* Value *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_case_Value \\ gs [])
  >- ((* MkTick *)
    rw [Once exp_rel_case_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_case_MkTick
    \\ first_x_assum irule \\ gs [])
QED

Definition case_goal_def:
  case_goal k x =
    ∀y.
      closed x ∧
      exp_rel_case x y ⇒
      ($= +++ v_rel_case)
        (eval_to k x)
        (eval_to k y)
End

Theorem eval_to_WF_IND[local] =
  WF_IND
  |> GEN_ALL
  |> Q.ISPEC ‘eval_to_wo’
  |> REWRITE_RULE [eval_to_wo_WF]
  |> Q.SPEC ‘UNCURRY case_goal’
  |> SIMP_RULE std_ss [FORALL_PROD]

Theorem exp_rel_case_eval_to:
  ∀k x. case_goal k x
Proof
  ho_match_mp_tac eval_to_WF_IND
  \\ simp [case_goal_def]
  \\ gen_tac \\ Cases \\ simp []
  >~ [‘Let bv x y’] >- (
    Cases_on ‘bv’ \\ gs []
    >~ [‘Let NONE x1 y1’] >- (
      strip_tac
      \\ rw [Once exp_rel_case_cases] \\ gs []
      >~ [‘Proj s i (Value u)’] >- (
        once_rewrite_tac [eval_to_def]
        \\ IF_CASES_TAC \\ gs []
        \\ CONV_TAC (BINOP_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
        \\ IF_CASES_TAC \\ gs []
        \\ CONV_TAC (BINOP_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
        \\ Cases_on ‘u’ \\ Cases_on ‘v’ \\ gs []
        \\ rename1 ‘LIST_REL _ xs ys’
        \\ gvs [LIST_REL_EL_EQN]
        \\ IF_CASES_TAC \\ gvs []
        \\ first_x_assum (drule_then assume_tac)
        \\ simp [eval_to_def]
        \\ ‘2 < k’ by cheat \\ gs []
        \\ first_x_assum irule
        \\ simp [closed_subst, eval_to_wo_def]
        \\ irule exp_rel_case_subst \\ simp []
        \\ first_assum (irule_at Any) \\ gs [])
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ ‘($= +++ v_rel_case) (eval_to (k - 1) x1) (eval_to (k - 1) x2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def])
  \\ rename1 ‘Let (SOME n) x1 y1’
  \\ strip_tac
  \\ rw [Once exp_rel_case_cases]
  \\ simp [eval_to_def]
  \\ IF_CASES_TAC \\ gs []
  \\ ‘($= +++ v_rel_case) (eval_to (k - 1) x1) (eval_to (k - 1) x2)’
    by (first_x_assum irule \\ simp [eval_to_wo_def])
  \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
  \\ first_x_assum irule
  \\ simp [eval_to_wo_def, closed_subst]
  \\ irule exp_rel_case_subst \\ gs [])
  >~ [‘Value v’] >- (
    strip_tac
    \\ rw [Once exp_rel_case_cases]
    \\ simp [eval_to_def])
  >~ [‘Delay x’] >- (
    strip_tac
    \\ rw [Once exp_rel_case_cases]
    \\ simp [eval_to_def])
  >~ [‘Prim op xs’] >- (
    strip_tac
    \\ rw [Once exp_rel_case_cases]
    \\ ‘∀j. j ≤ k ⇒
          ∀n. n < LENGTH xs ⇒
            ($= +++ v_rel_case) (eval_to j (EL n xs)) (eval_to j (EL n ys))’
      by (rpt strip_tac
          \\ first_x_assum irule
          \\ simp [eval_to_wo_def, exp_size_def]
          \\ gs [EVERY_EL, LIST_REL_EL_EQN]
          \\ rw [DISJ_EQ_IMP]
          \\ ‘MEM (EL n xs) xs’
            by (simp [MEM_EL]
                \\ first_assum (irule_at Any)
                \\ gs [])
          \\ drule_then assume_tac (CONJUNCT1 exp_size_lemma)
          \\ gs [])
    \\ simp [eval_to_def]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      first_x_assum (qspec_then ‘k’ assume_tac)
      \\ ‘($= +++ LIST_REL v_rel_case) (result_map (eval_to k) xs)
                                       (result_map (eval_to k) ys)’
        suffices_by (
          rw [SF ETA_ss]
          \\ Cases_on ‘result_map (eval_to k) xs’
          \\ Cases_on ‘result_map (eval_to k) ys’ \\ gs [])
      \\ Cases_on ‘result_map (eval_to k) xs’ \\ gs []
      >- (
        gvs [result_map_def, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP,
             CaseEq "bool", SF CONJ_ss]
        \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ ‘($= +++ v_rel_case) (eval_to k (EL n xs)) (eval_to k (EL n ys))’
          by gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gvs [SF SFY_ss]
        \\ IF_CASES_TAC \\ gs []
        \\ rename1 ‘m < LENGTH ys’
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
      \\ Cases_on ‘result_map (eval_to k) ys’ \\ gs []
      >- (
        gvs [result_map_def, CaseEq "bool", MEM_EL, EL_MAP,
             DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ gvs [result_map_def, CaseEq "bool", MEM_EL, EL_MAP,
              DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”,
              EVERY2_MAP]
      \\ rw [LIST_REL_EL_EQN]
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ Cases_on ‘eval_to k (EL n xs)’
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
      \\ rename1 ‘err ≠ Type_error’
      \\ Cases_on ‘err’ \\ gs [])
    >- ((* IsEq *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1n ⇔ n = 0”]
      \\ rename1 ‘exp_rel_case x y’
      \\ IF_CASES_TAC \\ gs []
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_case v1 v2’ \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs []
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* Proj *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1n ⇔ n = 0”]
      \\ rename1 ‘exp_rel_case x y’
      \\ IF_CASES_TAC \\ gs []
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel_case v1 v2’ \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs []
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* AtomOp *)
      Cases_on ‘k = 0’ \\ gs []
      >- (
        simp [result_map_def, MEM_MAP, GSYM NOT_NULL_MEM, NULL_EQ]
        \\ Cases_on ‘xs’ \\ Cases_on ‘ys’ \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [])
      \\ first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘result_map f’
      \\ ‘MAP f xs = MAP f ys’
        suffices_by (
          strip_tac
          \\ gs [result_map_def, MEM_MAP]
          \\ IF_CASES_TAC \\ gs []
          \\ IF_CASES_TAC \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [])
      \\ irule LIST_EQ
      \\ rw [EL_MAP, SF CONJ_ss, Abbr ‘f’]
      \\ first_x_assum (drule_then assume_tac)
      \\ rpt CASE_TAC \\ gs []))
  >~ [‘Force x’] >- (
    strip_tac
    \\ rw [Once exp_rel_case_cases]
    \\ once_rewrite_tac [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ rename1 ‘exp_rel_case x y’
    \\ ‘($= +++ v_rel_case) (eval_to k x) (eval_to k y)’
      by (first_x_assum irule
          \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘v_rel_case v w’
    \\ Cases_on ‘dest_Tick v’ \\ gs []
    >- (
      Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
      >- (
        rename1 ‘LIST_REL _ xs ys’
        \\ ‘OPTREL exp_rel_case (ALOOKUP (REVERSE xs) s)
                                (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
        \\ gs [OPTREL_def]
        \\ qpat_x_assum ‘exp_rel_case x0 _’ mp_tac
        \\ rw [Once exp_rel_case_cases] \\ gs []
        \\ first_x_assum irule \\ simp [subst_funs_def]
        \\ irule_at Any exp_rel_case_subst
        \\ irule_at Any LIST_EQ
        \\ simp [closed_subst, eval_to_wo_def, MAP_MAP_o, combinTheory.o_DEF,
                 LAMBDA_PROD, GSYM FST_THM, EVERY2_MAP]
        \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP]
        \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
        \\ first_x_assum (drule_then assume_tac)
        \\ gs [freevars_def])
      >- (
        CASE_TAC \\ gs []
        \\ simp [subst_funs_def]
        \\ first_x_assum irule
        \\ simp [eval_to_wo_def])
      \\ cheat (* stuck *))
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def]
    \\ irule exp_rel_case_Force
    \\ irule exp_rel_case_Value \\ gs [])
  \\ cheat
QED

Theorem exp_rel_case_eval_to =
  REWRITE_RULE [case_goal_def] exp_rel_case_eval_to;

val _ = export_theory ();

