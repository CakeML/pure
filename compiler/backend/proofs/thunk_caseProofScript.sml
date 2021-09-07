(*
  The fifth in a series of transformations to simplify case-compilation from
  pureLang to thunkLang. See:
  - [thunk_liftProofScript.sml]
  - [thunk_d2bProofScript.sml]
  - [thunk_inlProofScript.sml]
  - [thunk_unboxProofScript.sml]
  for the others.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_caseProof";

val _ = numLib.prefer_num ();

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;

Theorem PAIR_REL_def[local,simp] = quotient_pairTheory.PAIR_REL;

Overload Tick = “λx: exp. Letrec [] x”;

Overload Proj = “λs i (x: exp). Prim (Proj s i) [x]”;

Overload Seq = “λx: exp. λy. Let NONE x y”;

(* -------------------------------------------------------------------------
 * TODO:
 * - the clocks line up in the Proj case, but the code on the right side
 *   can diverge inside the Let. the new program always needs one extra
 *   clock to get past the second Proj, but if we give it extra then the clocks
 *   wont line up when we get to x/y.
 * - v_rel_Proj becomes an issue in Force. it might help generalizing it
 *
 * ------------------------------------------------------------------------- *)

Definition ok_binder_def[simp]:
  ok_binder (Lam s x) = T ∧
  ok_binder (Box x) = T ∧
  ok_binder (Delay x) = T ∧
  ok_binder _ = F
End

Inductive exp_inv:
[exp_inv_Var:]
  (∀v.
     exp_inv (Var v)) ∧
[exp_inv_Cons:]
  (∀s xs.
     EVERY (λx. exp_inv x ∧ ∃y. x = Delay y) xs ⇒
       exp_inv (Prim (Cons s) xs)) ∧
[exp_inv_Prim:]
  (∀op xs.
     (∀s. op ≠ Cons s) ∧
     EVERY exp_inv xs ⇒
       exp_inv (Prim op xs)) ∧
[exp_inv_App:]
  (∀f g.
     exp_inv f ∧
     exp_inv g ⇒
       exp_inv (App f g)) ∧
[exp_inv_Lam:]
  (∀s x.
     exp_inv x ⇒
       exp_inv (Lam s x)) ∧
[exp_inv_Letrec:]
  (∀f x.
     EVERY (λx. exp_inv x ∧ ok_binder x) (MAP SND f) ∧
     exp_inv x ⇒
       exp_inv (Letrec f x)) ∧
[exp_inv_Let:]
  (∀bv x y.
     exp_inv x ∧
     exp_inv y ⇒
       exp_inv (Let bv x y)) ∧
[exp_inv_If:]
  (∀x y z.
     exp_inv x ∧
     exp_inv y ∧
     exp_inv z ⇒
       exp_inv (If x y z)) ∧
[exp_inv_Delay:]
  (∀x.
     exp_inv x ⇒
       exp_inv (Delay x)) ∧
[exp_inv_Box:]
  (∀x.
     exp_inv x ⇒
       exp_inv (Box x)) ∧
[exp_inv_Force:]
  (∀x.
     exp_inv x ⇒
       exp_inv (Force x)) ∧
[exp_inv_Value:]
  (∀v.
     v_inv v ⇒
       exp_inv (Value v)) ∧
[exp_inv_MkTick:]
  (∀x.
     exp_inv x ⇒
       exp_inv (MkTick x)) ∧
[v_inv_Constructor:]
  (∀s vs.
     EVERY (λx. ∃y. x = Thunk (INR y) ∧ exp_inv y) vs ⇒
       v_inv (Constructor s vs)) ∧
[v_inv_Closure:]
  (∀s x.
     exp_inv x ⇒
       v_inv (Closure s x)) ∧
[v_inv_Recclosure:]
  (∀f n.
     EVERY (λx. exp_inv x ∧ ok_binder x) (MAP SND f) ⇒
       v_inv (Recclosure f n)) ∧
[v_inv_Thunk_INL:]
  (∀v.
     v_inv v ⇒
       v_inv (Thunk (INL v))) ∧
[v_inv_Thunk_INR:]
  (∀x.
     exp_inv x ⇒
       v_inv (Thunk (INR x))) ∧
[v_inv_Atom:]
  (∀x.
     v_inv (Atom x)) ∧
[v_inv_DoTick:]
  (∀v.
     v_inv v ⇒
       v_inv (DoTick v))
End

Theorem exp_inv_def[simp] =
  [ “exp_inv (Var v)”,
    “exp_inv (Prim op xs)”,
    “exp_inv (App f g)”,
    “exp_inv (Lam s x)”,
    “exp_inv (Letrec f x)”,
    “exp_inv (Let bv x y)”,
    “exp_inv (If x y z)”,
    “exp_inv (Delay x)”,
    “exp_inv (Box x)”,
    “exp_inv (Force x)”,
    “exp_inv (Value v)”,
    “exp_inv (MkTick x)” ]
  |> map (SIMP_CONV (srw_ss ()) [Once exp_inv_cases])
  |> LIST_CONJ;

Theorem v_inv_def[simp] =
  [ “v_inv (Constructor s vs)”,
    “v_inv (Closure s x)”,
    “v_inv (Recclosure f n)”,
    “v_inv (Thunk (INL v))”,
    “v_inv (Thunk (INR x))”,
    “v_inv (Atom x)”,
    “v_inv (DoTick v)” ]
  |> map (SIMP_CONV (srw_ss ()) [Once exp_inv_cases])
  |> LIST_CONJ;

Inductive exp_rel:
(* Proj *)
[exp_rel_Proj:]
  (∀x y s i v w.
     exp_rel x y ⇒
       exp_rel (Seq (Proj s i (Var v))
                    (Let (SOME w) (Delay (Force (Proj s i (Var v)))) x))
               (Seq (Proj s i (Var v))
                    (Let (SOME w) (MkTick (Proj s i (Var v))) y))) ∧
[exp_rel_Proj_Value:]
  (∀x y s i u v w.
     exp_rel x y ∧
     v_rel u v ⇒
       exp_rel (Seq (Proj s i (Value u))
                    (Let (SOME w) (Delay (Force (Proj s i (Value u)))) x))
               (Seq (Proj s i (Value v))
                    (Let (SOME w) (MkTick (Proj s i (Value v))) y))) ∧
[v_rel_Proj:]
  (∀xs s i.
     i < LENGTH xs ∧
     v_rel (EL i xs) v ⇒
       v_rel (Thunk (INR (Force (Proj s i (Value (Constructor s xs))))))
             (DoTick v)) ∧
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
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y)) ∧
[exp_rel_Let_SOME:]
  (∀bv x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let (SOME bv) x1 y1) (Let (SOME bv) x2 y2)) ∧
[exp_rel_Let_NONE:]
  (∀x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let NONE x1 y1) (Let NONE x2 y2)) ∧
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
     exp_rel x y ∧
     freevars x ⊆ {s} ⇒
       v_rel (Closure s x) (Closure s y)) ∧
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) (DoTick w)) ∧
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 freevars x ⊆ set (MAP FST f) ∧
                 fn = gn ∧
                 exp_rel x y) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Thunk_INR:]
  (∀x y.
     exp_rel x y ∧
     closed x ⇒
       v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_Thunk_INL:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INL v)) (Thunk (INL w)))
End

Theorem v_rel_cases[local] = CONJUNCT2 exp_rel_cases;

Theorem v_rel_def[simp] =
  [ “v_rel (Closure s x) z”,
    “v_rel z (Closure s x)”,
    “v_rel (Recclosure s x) z”,
    “v_rel z (Recclosure s x)”,
    “v_rel (Constructor s x) z”,
    “v_rel z (Constructor s x)”,
    “v_rel (DoTick x) z”,
    “v_rel z (DoTick x)”,
    “v_rel (Atom s) z”,
    “v_rel z (Atom s)”,
    “v_rel (Thunk (INL s)) z”,
    “v_rel z (Thunk (INL s))”,
    “v_rel (Thunk (INR s)) z”,
    “v_rel z (Thunk (INR s))” ]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem exp_rel_subst:
  ∀vs x ws y m.
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
    \\ qpat_x_assum ‘MAP FST vs = _’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qid_spec_tac ‘ws’
    \\ Induct_on ‘vs’ \\ simp []
    \\ Cases_on ‘ws’ \\ simp [])
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
    \\ irule exp_rel_If \\ simp [])
  >- ((* App *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_App \\ gs [])
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Lam \\ gs []
    \\ first_x_assum irule
    \\ qabbrev_tac ‘P = λn. n ≠ s’
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ irule LIST_REL_FILTER \\ gs []
    \\ gvs [LIST_REL_EL_EQN])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ qmatch_asmsub_rename_tac ‘exp_rel x y’
    >- ((* Proj *)
      ‘exp_rel (subst (FILTER (λ(n,x). n ≠ w) vs) x)
                    (subst (FILTER (λ(n,x). n ≠ w) ws) y)’
        by (first_x_assum
              (drule_then
                (qspec_then ‘Let (SOME w) (Delay (Force (Proj s i (Var v)))) y’
                 mp_tac))
            \\ simp [Once exp_rel_cases, PULL_EXISTS, subst_def]
            \\ ntac 5 (simp [Once exp_rel_cases, PULL_EXISTS]))
      \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
        by (irule LIST_REL_OPTREL
            \\ gs [LIST_REL_CONJ, ELIM_UNCURRY, EVERY2_MAP]
            \\ qpat_x_assum ‘MAP FST vs = _’ mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ qid_spec_tac ‘ws’
            \\ Induct_on ‘vs’ \\ simp []
            \\ Cases_on ‘ws’ \\ simp [])
      \\ gs [OPTREL_def, exp_rel_Proj, exp_rel_Proj_Value])
    >- (
      ‘exp_rel (subst (FILTER (λ(n,x). n ≠ w) vs) x)
                    (subst (FILTER (λ(n,x). n ≠ w) ws) y)’
        by (first_x_assum
              (drule_then
                (qspec_then ‘Let (SOME w)
                                 (Delay (Force (Proj s i (Value v)))) y’
                 mp_tac))
            \\ simp [Once exp_rel_cases, PULL_EXISTS, subst_def]
            \\ ntac 5 (simp [Once exp_rel_cases, PULL_EXISTS]))
      \\ gs [exp_rel_Proj_Value])
    \\ irule exp_rel_Let_NONE \\ gs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let_SOME \\ gs []
    \\ first_x_assum irule
    \\ qabbrev_tac ‘P = λn. n ≠ s’
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >- ((* Letrec *)
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_Letrec
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
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Delay \\ gs [])
  >- ((* Box *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Box \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Force
    \\ first_x_assum irule \\ gs [])
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Value \\ gs [])
  >- ((* MkTick *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_MkTick
    \\ first_x_assum irule \\ gs [])
QED

Definition case_goal_def:
  case_goal k x =
    ∀y.
      closed x ∧
      exp_inv x ∧
      exp_rel x y ⇒
      ($= +++ (λv w. v_inv v ∧ v_rel v w))
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

Theorem exp_rel_eval_to:
  ∀k x. case_goal k x
Proof
  ho_match_mp_tac eval_to_WF_IND
  \\ simp [case_goal_def]
  \\ gen_tac \\ Cases \\ simp []
  >~ [‘Let bv x y’] >- (
    Cases_on ‘bv’ \\ gs []
    >~ [‘Let NONE x1 y1’] >- (
      strip_tac
      \\ rw [Once exp_rel_cases] \\ gs []
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
        \\ conj_tac >- cheat (* exp_inv_subst *)
        \\ irule exp_rel_subst \\ simp []
        \\ first_assum (irule_at Any) \\ gs [])
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ ‘($= +++ (λv w. v_inv v ∧ v_rel v w)) (eval_to (k - 1) x1)
                                               (eval_to (k - 1) x2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def])
    \\ rename1 ‘Let (SOME n) x1 y1’
    \\ strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ ‘($= +++ (λv w. v_inv v ∧ v_rel v w)) (eval_to (k - 1) x1)
                                             (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def, closed_subst]
    \\ conj_tac >- cheat (* exp_inv_subst *)
    \\ irule exp_rel_subst \\ gs [])
  >~ [‘Value v’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Delay x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Prim op xs’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ ‘∀j. j ≤ k ⇒
          ∀n. n < LENGTH xs ⇒
            ($= +++ (λv w. v_inv v ∧ v_rel v w)) (eval_to j (EL n xs))
                                                 (eval_to j (EL n ys))’
      by (rpt strip_tac
          \\ first_x_assum irule
          \\ simp [eval_to_wo_def, exp_size_def]
          \\ gs [EVERY_EL, LIST_REL_EL_EQN]
          \\ rw [DISJ_EQ_IMP]
          \\ ‘n < LENGTH xs’ by gs []
          \\ drule (SIMP_RULE (srw_ss()) [MEM_EL, PULL_EXISTS]
                                         (CONJUNCT1 exp_size_lemma))
          \\ gs [])
    \\ simp [eval_to_def]
    \\ imp_res_tac LIST_REL_LENGTH
    >- ((* Cons *)
      first_x_assum (qspec_then ‘k’ assume_tac)
      \\ ‘($= +++ LIST_REL (λv w. v_inv v ∧ v_rel v w ∧ ∃x. v = Thunk (INR x)))
                           (result_map (eval_to k) xs)
                           (result_map (eval_to k) ys)’
        suffices_by (
          rw [SF ETA_ss]
          \\ Cases_on ‘result_map (eval_to k) xs’
          \\ Cases_on ‘result_map (eval_to k) ys’ \\ gs []
          \\ gvs [EVERY_EL, LIST_REL_EL_EQN] \\ rw []
          \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs [])
      \\ Cases_on ‘result_map (eval_to k) xs’ \\ gs []
      >- (
        gvs [result_map_def, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP,
             CaseEq "bool", SF CONJ_ss]
        \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ ‘($= +++ (λv w. v_inv v ∧ v_rel v w)) (eval_to k (EL n xs))
                                                 (eval_to k (EL n ys))’
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
      \\ simp [LIST_REL_EL_EQN]
      \\ ntac 2 strip_tac
      \\ gvs [EVERY_EL]
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs []
      \\ gs [eval_to_def]
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [EVERY_EL]
      \\ first_assum (irule_at Any) \\ gs [])
    \\ Cases_on ‘op’ \\ gs []
    >- ((* IsEq *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1n ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v1 v2’ \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs []
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* Proj *)
      first_x_assum (qspec_then ‘k - 1’ assume_tac) \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1n ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v1 v2’ \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs []
      \\ gvs [LIST_REL_EL_EQN, EVERY_EL]
      \\ IF_CASES_TAC \\ gs []
      \\ first_x_assum (drule_then strip_assume_tac) \\ gs [])
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
    \\ rw [Once exp_rel_cases]
    \\ once_rewrite_tac [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ rename1 ‘exp_rel x y’
    \\ ‘($= +++ (λv w. v_inv v ∧ v_rel v w)) (eval_to k x) (eval_to k y)’
      by (first_x_assum irule
          \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘dest_Tick v’ \\ gs []
    >~ [‘dest_Tick v = SOME u’] >- (
      Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def]
      \\ irule exp_rel_Force
      \\ irule exp_rel_Value \\ gs [])
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
    >- ((* Recclosure *)
      rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
                              (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs []
      \\ first_x_assum irule \\ simp [subst_funs_def]
      \\ irule_at Any exp_rel_subst
      \\ irule_at Any LIST_EQ
      \\ simp [closed_subst, eval_to_wo_def, MAP_MAP_o, combinTheory.o_DEF,
               LAMBDA_PROD, GSYM FST_THM, EVERY2_MAP]
      \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP]
      \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
      \\ first_x_assum (drule_then assume_tac)
      \\ gs [freevars_def]
      \\ cheat (* exp_inv_subst *))
    >- ((* Thunk *)
      CASE_TAC \\ gs []
      \\ simp [subst_funs_def]
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def])
    \\ simp [subst_funs_def]
    \\ gvs [EVERY_EL]
    \\ ‘∃z1. EL i xs = Thunk (INR z1) ∧ exp_inv z1’
      by gs []
    \\ once_rewrite_tac [eval_to_def] \\ simp []
    \\ IF_CASES_TAC \\ simp []
    \\ simp [Once eval_to_def]
    \\ simp [Once eval_to_def, dest_anyThunk_def, subst_funs_def]
    \\ simp [Once eval_to_def]
    \\ CASE_TAC \\ gs []
    >- (
      first_x_assum irule
      \\ simp [eval_to_wo_def])
    \\ cheat (* repetition of the last case again but one level deeper *))
  \\ cheat
QED

Theorem exp_rel_eval_to =
  REWRITE_RULE [case_goal_def] exp_rel_eval_to;

val _ = export_theory ();

