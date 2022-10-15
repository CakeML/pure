(*
  The fifth in a series of transformations to simplify case-compilation from
  pureLang to thunkLang. See:
  - [thunk_case_liftProofScript.sml]
  - [thunk_case_d2bProofScript.sml]
  - [thunk_case_inlProofScript.sml]
  - [thunk_case_unboxProofScript.sml]
  for the others.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory;

val _ = new_theory "thunk_case_projProof";

val _ = set_grammar_ancestry [
  "finite_map", "pred_set", "rich_list", "thunkLang", "wellorder",
   "quotient_sum", "quotient_pair", "thunkLangProps", "thunk_semantics" ];

val _ = numLib.prefer_num ();

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;

Theorem PAIR_REL_def[local,simp] = quotient_pairTheory.PAIR_REL;

Definition ok_binder_def[simp]:
  ok_binder (Lam s x) = T ∧
  ok_binder (Box x) = T ∧
  ok_binder (Delay x) = T ∧
  ok_binder _ = F
End

Inductive exp_rel:
(* Proj *)
[exp_rel_Proj:]
  (∀x y s i j v w b.
     i < j ∧
     exp_rel x y ⇒
       exp_rel (Seq (If (IsEq s j b (Var v)) Unit Fail)
                    (Let (SOME w) (Tick (Delay (Force (Proj s i (Var v))))) x))
               (Seq (If (IsEq s j b (Var v)) Unit Fail)
                    (Let (SOME w) (MkTick (Proj s i (Var v))) y))) ∧
[exp_rel_Proj_Value:]
  (∀x y s i j u v w b.
     i < j ∧
     exp_rel x y ∧
     v_rel u v ⇒
       exp_rel (Seq (If (IsEq s j b (Value u)) Unit Fail)
                    (Let (SOME w) (Tick (Delay (Force (Proj s i (Value u))))) x))
               (Seq (If (IsEq s j b (Value v)) Unit Fail)
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
                 exp_rel x y ∧
                 ok_binder x) f g ∧
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
[exp_rel_Cons:]
  (∀s xs ys.
     LIST_REL (λx y. exp_rel x y ∧ ∃z. x = Delay z) xs ys ⇒
       exp_rel (Prim (Cons s) xs) (Prim (Cons s) ys)) ∧
[exp_rel_Prim:]
  (∀op xs ys.
     (∀s. op ≠ Cons s) ∧
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
     LIST_REL (λv w. v_rel v w ∧ ∃x. v = Thunk (INR x)) vs ws ⇒
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
                 exp_rel x y ∧
                 ok_binder x) f g ⇒
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

Theorem ok_binder_subst[local,simp]:
  ∀x. ok_binder x ⇒ ok_binder (subst vs x)
Proof
  Cases \\ simp [subst_def]
QED

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
    \\ (irule exp_rel_Cons ORELSE irule exp_rel_Prim)
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ simp [subst_def])
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
        by (first_x_assum (drule_then
              (qspec_then ‘Let (SOME w)
                               (Tick (Delay (Force (Proj s i (Var v))))) y’
               mp_tac))
            \\ simp [Once exp_rel_cases, PULL_EXISTS, subst_def]
            \\ ntac 6 (simp [Once exp_rel_cases, PULL_EXISTS]))
      \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
        by (irule LIST_REL_OPTREL
            \\ gs [LIST_REL_CONJ, ELIM_UNCURRY, EVERY2_MAP]
            \\ qpat_x_assum ‘MAP FST vs = _’ mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ qid_spec_tac ‘ws’
            \\ Induct_on ‘vs’ \\ simp []
            \\ Cases_on ‘ws’ \\ simp [])
      \\ gs [OPTREL_def, exp_rel_Proj, exp_rel_Proj_Value,
             ELIM_UNCURRY, FILTER_T])
    >- (
      ‘exp_rel (subst (FILTER (λ(n,x). n ≠ w) vs) x)
               (subst (FILTER (λ(n,x). n ≠ w) ws) y)’
        by (first_x_assum (drule_then
              (qspec_then ‘Let (SOME w)
                               (Tick (Delay (Force (Proj s i (Value v))))) y’
               mp_tac))
            \\ simp [Once exp_rel_cases, PULL_EXISTS, subst_def]
            \\ ntac 6 (simp [Once exp_rel_cases, PULL_EXISTS]))
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
      exp_rel x y ⇒
      ($= +++ v_rel)
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
  >~ [‘App f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘($= +++ v_rel) (eval_to k x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ ‘($= +++ v_rel) (eval_to k f) (eval_to k g)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k f’ \\ Cases_on ‘eval_to k g’ \\ gs []
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyClosure_def]
    >- ((* Closure *)
      IF_CASES_TAC \\ gs []
      \\ first_x_assum irule
      \\ simp [closed_subst, eval_to_wo_def]
      \\ irule exp_rel_subst
      \\ simp [])
        (* Recclosure *)
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
      by (irule LIST_REL_OPTREL
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
    \\ gs [OPTREL_def]
    \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [closed_subst, eval_to_wo_def]
    \\ irule_at Any exp_rel_subst
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
             EVERY2_MAP]
    \\ irule_at Any LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    \\ dxrule_then kall_tac ALOOKUP_SOME_REVERSE_EL
    \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ gvs [freevars_def, SUBSET_DEF]
    \\ rw [Once DISJ_COMM, DISJ_EQ_IMP])
  >~ [‘Lam s x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
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
        \\ IF_CASES_TAC \\ gs []
        \\ CONV_TAC (BINOP_CONV (SIMP_CONV (srw_ss()) [Once eval_to_def]))
        \\ Cases_on ‘u’ \\ Cases_on ‘v’ \\ gvs []
        \\ rename1 ‘s1 = s2 ⇒ _’ \\ Cases_on ‘s1 = s2’ \\ simp [eval_to_def]
        \\ gvs [LIST_REL_EL_EQN, eval_to_def, result_map_def, subst_funs_def]
        \\ IF_CASES_TAC \\ gs [subst_funs_def]
        \\ first_x_assum irule
        \\ simp [closed_subst, eval_to_wo_def]
        \\ irule exp_rel_subst \\ gs [])
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ ‘($= +++ v_rel) (eval_to (k - 1) x1) (eval_to (k - 1) x2)’
        by (first_x_assum irule \\ simp [eval_to_wo_def])
      \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
      \\ first_x_assum irule
      \\ simp [eval_to_wo_def])
    \\ rename1 ‘Let (SOME n) x1 y1’
    \\ strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ ‘($= +++ v_rel) (eval_to (k - 1) x1) (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def, closed_subst]
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
            ($= +++ v_rel) (eval_to j (EL n xs)) (eval_to j (EL n ys))’
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
      \\ ‘($= +++ LIST_REL (λv w. v_rel v w ∧ ∃x. v = Thunk (INR x)))
                           (result_map (eval_to k) xs)
                           (result_map (eval_to k) ys)’
        suffices_by (
          rw [SF ETA_ss]
          \\ Cases_on ‘result_map (eval_to k) xs’
          \\ Cases_on ‘result_map (eval_to k) ys’ \\ gs []
          \\ gvs [LIST_REL_EL_EQN] \\ rw []
          \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs [])
      \\ Cases_on ‘result_map (eval_to k) xs’ \\ gs []
      >- (
        gvs [result_map_def, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP,
             CaseEq "bool", SF CONJ_ss]
        \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ ‘($= +++ v_rel) (eval_to k (EL n xs)) (eval_to k (EL n ys))’
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
      \\ gvs [LIST_REL_EL_EQN]
      \\ ntac 2 strip_tac
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs []
      \\ gs [eval_to_def]
      \\ Cases_on ‘eval_to k (EL n xs)’
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
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
      \\ ntac 3 (IF_CASES_TAC \\ gs []))
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
    \\ ‘($= +++ v_rel) (eval_to k x) (eval_to k y)’
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
    \\ Cases_on ‘dest_Tick w’ \\ gs []
    >~ [‘dest_Tick w = SOME u’] >- (
      Cases_on ‘v’ \\ gvs []
      \\ simp [dest_anyThunk_def, subst_funs_def]
      \\ CASE_TAC \\ gvs []
      \\ ‘($= +++ v_rel)
            (eval_to (k - 1) (Force (Value (EL i xs))))
            (eval_to (k - 1) (Force (Value u)))’
        by (first_x_assum irule
            \\ gvs [eval_to_wo_def]
            \\ irule exp_rel_Force
            \\ irule exp_rel_Value \\ gs [])
      \\ pop_assum mp_tac
      \\ once_rewrite_tac [eval_to_def] \\ simp []
      \\ IF_CASES_TAC \\ gs []
      \\ simp [Once eval_to_def]
      \\ strip_tac
      \\ simp [Once eval_to_def]
      \\ simp [Once eval_to_def])
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [dest_anyThunk_def]
    >- ((* Recclosure *)
      rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
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
      \\ dxrule_then kall_tac ALOOKUP_SOME_REVERSE_EL
      \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
      \\ first_x_assum (drule_then assume_tac)
      \\ gs [freevars_def])
        (* Thunk *)
    \\ CASE_TAC \\ gs []
    \\ simp [subst_funs_def]
    \\ first_x_assum irule
    \\ simp [eval_to_wo_def])
  >~ [‘MkTick x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘($= +++ v_rel) (eval_to k x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
  >~ [‘Box x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘($= +++ v_rel) (eval_to k x) (eval_to k y)’
      by (first_x_assum irule \\ simp [eval_to_wo_def, exp_size_def])
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
  >~ [‘If x1 y1 z1’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ ‘($= +++ v_rel) (eval_to (k - 1) x1) (eval_to (k - 1) x2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ ‘($= +++ v_rel) (eval_to (k - 1) y1) (eval_to (k - 1) y2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ ‘($= +++ v_rel) (eval_to (k - 1) z1) (eval_to (k - 1) z2)’
      by (first_x_assum irule \\ simp [eval_to_wo_def])
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [])
  >~ [‘Letrec f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def, closed_subst, eval_to_wo_def]
    \\ irule_at Any exp_rel_subst
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ irule_at Any LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, BIGUNION, MEM_EL, PULL_EXISTS,
            EL_MAP, EVERY2_MAP, SUBSET_DEF, SF CONJ_ss]
    \\ rw [] \\ gs [SF SFY_ss])
QED

Theorem exp_rel_eval_to =
  REWRITE_RULE [case_goal_def] exp_rel_eval_to;

Theorem exp_rel_eval:
  closed x ∧
  exp_rel x y ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ irule eval_to_eval_lift
  \\ qexists_tac ‘λx y. closed x ∧ exp_rel x y’
  \\ qexists_tac ‘T’ \\ rw []
  \\ irule exp_rel_eval_to \\ gs []
QED

Definition cont_rel_def[simp]:
  cont_rel Done Done = T ∧
  cont_rel (BC v c) (BC w d) = (v_rel v w ∧ cont_rel c d) ∧
  cont_rel (HC v c) (HC w d) = (v_rel v w ∧ cont_rel c d) ∧
  cont_rel _ _ = F
End

Definition state_rel_def:
  state_rel = LIST_REL (LIST_REL (λv w. v_rel v w ∧ ∃x. v = Thunk (INR x)))
End

Definition next_rel_def[simp]:
  next_rel (Act a c s) (Act b d t) =
    (a = b ∧ cont_rel c d ∧ state_rel s t) ∧
  next_rel Ret Ret = T ∧
  next_rel Div Div = T ∧
  next_rel Err Err = T ∧
  next_rel (_: (string # string) next_res) _ = F
End

Theorem case_proj_next:
  ∀k v c s w d t.
    ($= +++ v_rel) v w ∧
    cont_rel c d ∧
    state_rel s t ⇒
      next_rel (next k v c s) (next k w d t)
Proof
  ho_match_mp_tac next_ind \\ rw []
  \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs []
  >- (
    simp [next_def]
    \\ CASE_TAC \\ gs [])
  \\ rename1 ‘v_rel v w’
  \\ Cases_on ‘(∃s x. v = Closure s x) ∨
               (∃f n. v = Recclosure f n) ∨
               (∃x. v = Thunk x) ∨
               (∃x. v = Atom x) ∨
               (∃x. v = DoTick x)’
  >- (
    gvs [v_rel_def]
    >~ [‘Thunk x’] >-(
      Cases_on ‘x’ \\ gvs [v_rel_def]
      \\ simp [next_def])
    \\ simp [next_def])
  \\ fs []
  \\ ‘∃nm vs. v = Constructor nm vs’
    by (Cases_on ‘v’ \\ gs [])
  \\ gvs []
  \\ simp [Once next_def]
  \\ IF_CASES_TAC \\ gs []
  >- ((* Ret *)
    gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute]
    \\ qmatch_goalsub_abbrev_tac ‘next_rel X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ reverse (Cases_on ‘c’) \\ Cases_on ‘d’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      first_x_assum irule
      \\ gs [DECIDE “∀n. n < 1n ⇔ n = 0”])
    \\ rename1 ‘v_rel v1 w1’
    \\ simp [force_apply_closure_def]
    \\ ‘($= +++ v_rel) (force v1) (force w1)’
      by (simp [force_eval]
          \\ irule exp_rel_eval \\ gs []
          \\ irule exp_rel_Force
          \\ irule exp_rel_Value \\ gs [])
    \\ Cases_on ‘force v1’ \\ Cases_on ‘force w1’ \\ gs []
    >~ [‘INL err’] >- (
      Cases_on ‘err’ \\ gs [])
    \\ simp [apply_closure_def]
    \\ rename1 ‘v_rel v2 w2’
    \\ Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gvs [dest_anyClosure_def]
    >- (
      first_x_assum irule \\ gs []
      \\ irule exp_rel_eval
      \\ simp [closed_subst]
      \\ irule exp_rel_subst
      \\ gs [DECIDE “∀n. n < 1n ⇔ n = 0”])
    \\ rename [‘LIST_REL _ vs ws’, ‘ALOOKUP _ s’]
    \\ ‘OPTREL (λx0 y0. freevars x0 ⊆ set (MAP FST vs) ∧ exp_rel x0 y0)
               (ALOOKUP (REVERSE vs) s)
               (ALOOKUP (REVERSE ws) s)’
      by (irule LIST_REL_OPTREL
          \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN])
    \\ gs [OPTREL_def]
    \\ qpat_x_assum ‘exp_rel x0 y0’ mp_tac
    \\ rw [Once exp_rel_cases] \\ gs [freevars_def]
    \\ first_x_assum irule \\ gs []
    \\ irule exp_rel_eval \\ simp [closed_subst]
    \\ irule_at Any exp_rel_subst
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
             EVERY2_MAP]
    \\ irule_at Any LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, SUBSET_DEF]
    \\ gs [DECIDE “∀n. n < 1n ⇔ n = 0”]
    \\ rw [DISJ_COMM, DISJ_EQ_IMP])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Raise *)
    gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute]
    \\ qmatch_goalsub_abbrev_tac ‘next_rel X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ Cases_on ‘c’ \\ Cases_on ‘d’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      first_x_assum irule
      \\ gs [DECIDE “∀n. n < 1n ⇔ n = 0”])
    \\ rename1 ‘v_rel v1 w1’
    \\ simp [force_apply_closure_def]
    \\ ‘($= +++ v_rel) (force v1) (force w1)’
      by (simp [force_eval]
          \\ irule exp_rel_eval \\ gs []
          \\ irule exp_rel_Force
          \\ irule exp_rel_Value \\ gs [])
    \\ Cases_on ‘force v1’ \\ Cases_on ‘force w1’ \\ gs []
    >~ [‘INL err’] >- (
      Cases_on ‘err’ \\ gs [])
    \\ simp [apply_closure_def]
    \\ rename1 ‘v_rel v2 w2’
    \\ Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gvs [dest_anyClosure_def]
    >- (
      first_x_assum irule \\ gs []
      \\ irule exp_rel_eval
      \\ simp [closed_subst]
      \\ irule exp_rel_subst
      \\ gs [DECIDE “∀n. n < 1n ⇔ n = 0”])
    \\ rename [‘LIST_REL _ vs ws’, ‘ALOOKUP _ s’]
    \\ ‘OPTREL (λx0 y0. freevars x0 ⊆ set (MAP FST vs) ∧ exp_rel x0 y0)
               (ALOOKUP (REVERSE vs) s)
               (ALOOKUP (REVERSE ws) s)’
      by (irule LIST_REL_OPTREL
          \\ gs [ELIM_UNCURRY, LIST_REL_EL_EQN])
    \\ gs [OPTREL_def]
    \\ qpat_x_assum ‘exp_rel x0 y0’ mp_tac
    \\ rw [Once exp_rel_cases] \\ gs [freevars_def]
    \\ first_x_assum irule \\ gs []
    \\ irule exp_rel_eval \\ simp [closed_subst]
    \\ irule_at Any exp_rel_subst
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
             EVERY2_MAP]
    \\ irule_at Any LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, SUBSET_DEF]
    \\ gs [DECIDE “∀n. n < 1n ⇔ n = 0”]
    \\ rw [DISJ_COMM, DISJ_EQ_IMP])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Bind *)
    gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
         DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”]
    \\ qmatch_goalsub_abbrev_tac ‘next_rel X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ IF_CASES_TAC \\ gs []
    \\ rename1 ‘v_rel (EL _ [v1; v2]) (EL _ [w1; w2])’
    \\ ‘v_rel v1 w1 ∧ v_rel v2 w2’
      by gvs [SF DNF_ss]
    \\ ‘($= +++ v_rel) (force v1) (force w1)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ first_x_assum irule \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Handle *)
    gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
         DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”]
    \\ qmatch_goalsub_abbrev_tac ‘next_rel X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ IF_CASES_TAC \\ gs []
    \\ rename1 ‘v_rel (EL _ [v1; v2]) (EL _ [w1; w2])’
    \\ ‘v_rel v1 w1 ∧ v_rel v2 w2’
      by gvs [SF DNF_ss]
    \\ ‘($= +++ v_rel) (force v1) (force w1)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ first_x_assum irule \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Act *)
    gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute]
    \\ rename1 ‘v_rel (EL _ [v]) (EL _ [w])’
    \\ ‘v_rel v w’
      by gs [DECIDE “∀n. n < 1n ⇔ n = 0”]
    \\ qmatch_goalsub_abbrev_tac ‘next_rel X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘($= +++ v_rel) (force v) (force w)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (
      Cases_on `x'` \\ gs[]
      )
    \\ rename1 ‘v_rel v1 w1’
    \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [get_atoms_def, v_rel_def]
    \\ CASE_TAC \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Alloc *)
    gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
         DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”]
    \\ qmatch_goalsub_abbrev_tac ‘next_rel X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ rename1 ‘v_rel (EL _ [v1; v2]) (EL _ [w1; w2])’
    \\ ‘v_rel v1 w1 ∧ v_rel v2 w2’
      by gvs [SF DNF_ss]
    \\ ‘($= +++ v_rel) (force v1) (force w1)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ simp [with_atoms_def, result_map_def]
    \\ Cases_on ‘force v1’ \\ Cases_on ‘force w1’ \\ gs []
    >- (
      Cases_on ‘x'’ \\ gs [])
    \\ rename1 ‘v_rel v3 w3’
    \\ Cases_on ‘v3’ \\ Cases_on ‘w3’ \\ gvs [get_atoms_def, v_rel_def]
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs []
    \\ first_x_assum irule
    \\ irule_at Any HD
    \\ simp [Once exp_rel_cases]
    \\ simp [Once exp_rel_cases]
    \\ gvs [state_rel_def, LIST_REL_REPLICATE_same, LIST_REL_EL_EQN]
    \\ rw [] \\ gvs [SF DNF_ss])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Length *)
    gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute]
    \\ rename1 ‘v_rel (EL _ [v]) (EL _ [w])’
    \\ ‘v_rel v w’
      by gs [DECIDE “∀n. n < 1n ⇔ n = 0”]
    \\ qmatch_goalsub_abbrev_tac ‘next_rel X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ simp [with_atoms_def, result_map_def]
    \\ ‘($= +++ v_rel) (force v) (force w)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ Cases_on ‘force v’ \\ Cases_on ‘force w’ \\ gs []
    >- (
      Cases_on ‘x'’ \\ gs[])
    \\ rename1 ‘v_rel v1 w1’
    \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [get_atoms_def, v_rel_def]
    \\ ‘LENGTH s = LENGTH t’
      by gs [state_rel_def, LIST_REL_EL_EQN]
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs []
    \\ rw [] \\ gs []
    \\ first_x_assum irule \\ gs []
    \\ irule_at Any HD
    \\ rw [Once exp_rel_cases]
    \\ gvs [LIST_REL_EL_EQN, state_rel_def])
  \\ IF_CASES_TAC \\ gs []
  >- ((* Deref *)
    gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
         DECIDE “∀x. x < 2n ⇔ x = 0 ∨ x = 1”]
    \\ qmatch_goalsub_abbrev_tac ‘next_rel X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ rename1 ‘v_rel (EL _ [v1; v2]) (EL _ [w1; w2])’
    \\ ‘v_rel v1 w1 ∧ v_rel v2 w2’
      by gvs [SF DNF_ss]
    \\ ‘($= +++ v_rel) (force v1) (force w1)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ ‘($= +++ v_rel) (force v2) (force w2)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ simp [with_atoms_def, result_map_def]
    \\ Cases_on ‘force v1’ \\ Cases_on ‘force w1’ \\ gs []
    >- (
      Cases_on `x'` \\ gs []
      \\ Cases_on ‘force v2’ \\ Cases_on ‘force w2’ \\ gs []
      \\ Cases_on `x''` \\ gs []
      )
    \\ rename1 ‘v_rel v3 w3’
    \\ ‘($= +++ v_rel) (force v2) (force w2)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ Cases_on ‘force v2’ \\ Cases_on ‘force w2’ \\ gs []
    >- (
      Cases_on ‘x'’ \\ gs [])
    \\ rename1 ‘v_rel v4 w4’
    \\ Cases_on ‘v3’ \\ Cases_on ‘w3’ \\ gvs [get_atoms_def, v_rel_def]
    \\ Cases_on ‘v4’ \\ Cases_on ‘w4’ \\ gvs [get_atoms_def, v_rel_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’
      by gvs [LIST_REL_EL_EQN, state_rel_def]
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ ‘LENGTH (EL n s) = LENGTH (EL n t)’
      by gvs [LIST_REL_EL_EQN, state_rel_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      first_assum irule \\ gs []
      \\ irule_at Any HD \\ gs []
      \\ irule_at Any HD \\ gs []
      \\ gvs [LIST_REL_EL_EQN, state_rel_def, arithmeticTheory.NOT_LESS,
              arithmeticTheory.LESS_OR_EQ]
      \\ first_x_assum drule_all \\ rw [] \\ gvs []
      \\ ‘Num i < LENGTH (EL n t)’
        by intLib.ARITH_TAC
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ gs [])
    \\ first_x_assum irule \\ gs []
    \\ first_assum (irule_at Any)
    \\ irule_at Any HD \\ simp []
    \\ irule_at Any HD \\ simp []
    \\ simp [Once exp_rel_cases]
    \\ intLib.ARITH_TAC)
  \\ IF_CASES_TAC \\ gs []
  >- ((* Update *)
    gvs [LIST_REL_EL_EQN, LENGTH_EQ_NUM_compute,
         DECIDE “∀x. x < 3n ⇔ x = 0 ∨ x = 1 ∨ x = 2”]
    \\ qmatch_goalsub_abbrev_tac ‘next_rel X’
    \\ simp [Once next_def] \\ simp [Abbr ‘X’]
    \\ rename1 ‘v_rel (EL _ [v1; v2; v3]) (EL _ [w1; w2; w3])’
    \\ ‘v_rel v1 w1 ∧ v_rel v2 w2 ∧ v_rel v3 w3’
      by gvs [SF DNF_ss]
    \\ ‘($= +++ v_rel) (force v1) (force w1)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ ‘($= +++ v_rel) (force v2) (force w2)’
      by (simp [force_eval]
          \\ irule exp_rel_eval
          \\ gs [exp_rel_Force, exp_rel_Value])
    \\ simp [with_atoms_def, result_map_def]
    \\ Cases_on ‘force v1’ \\ Cases_on ‘force w1’ \\ gs []
    >- (
      Cases_on `x'` \\ gs []
      \\ Cases_on ‘force v2’ \\ Cases_on ‘force w2’ \\ gs []
      \\ Cases_on `x''` \\ gs []
      )
    \\ rename1 ‘v_rel v4 w4’
    \\ Cases_on ‘force v2’ \\ Cases_on ‘force w2’ \\ gs []
    >- (
      Cases_on ‘x'’ \\ gs [])
    \\ rename1 ‘v_rel v5 w5’
    \\ Cases_on ‘v4’ \\ Cases_on ‘w4’ \\ gvs [get_atoms_def, v_rel_def]
    \\ Cases_on ‘v5’ \\ Cases_on ‘w5’ \\ gvs [get_atoms_def, v_rel_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    \\ ‘LENGTH s = LENGTH t’
      by gvs [LIST_REL_EL_EQN, state_rel_def]
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ ‘LENGTH (EL n s) = LENGTH (EL n t)’
      by gvs [LIST_REL_EL_EQN, state_rel_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      first_assum irule \\ gs []
      \\ irule_at Any HD \\ gs []
      \\ irule_at Any HD \\ gs []
      \\ gvs [LIST_REL_EL_EQN, state_rel_def, arithmeticTheory.NOT_LESS,
              arithmeticTheory.LESS_OR_EQ, EL_LUPDATE]
      \\ ‘Num i < LENGTH (EL n t)’
        by intLib.ARITH_TAC
      \\ rw [] \\ gs [EL_LUPDATE, exp_rel_Cons]
      \\ rw [] \\ gs []
      \\ gvs [SF DNF_ss])
    \\ first_x_assum irule \\ gs []
    \\ first_assum (irule_at Any)
    \\ irule_at Any HD \\ simp []
    \\ irule_at Any HD \\ simp []
    \\ simp [Once exp_rel_cases]
    \\ intLib.ARITH_TAC)
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rw [Once next_def] \\ gs []
QED

Theorem case_proj_next_action:
  ($= +++ v_rel) v w ∧
  cont_rel c d ∧
  state_rel s t ⇒
    next_rel (next_action v c s) (next_action w d t)
Proof
  strip_tac
  \\ rw [next_action_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ simp [PULL_FORALL]
  \\ qx_gen_tac ‘i’
  \\ qx_gen_tac ‘j’
  \\ qx_gen_tac ‘k’
  \\ rw []
  >- (
    drule_all_then assume_tac case_proj_next \\ gs []
    \\ drule_then (qspec_then ‘i’ mp_tac) next_next
    \\ impl_tac \\ rw [] \\ strip_tac
    \\ first_x_assum (qspec_then ‘i’ assume_tac)
    \\ Cases_on ‘next i w d t’ \\ gs [])
  \\ drule_all_then assume_tac case_proj_next \\ gs [SF SFY_ss]
QED

Theorem case_proj_interp:
  ($= +++ v_rel) v w ∧
  cont_rel c d ∧
  state_rel s t ⇒
    interp v c s = interp w d t
Proof
  strip_tac \\
  rw [Once itreeTheory.itree_bisimulation] >>
  qexists_tac `λt1 t2.
    (t1 = t2 ∨
     ∃v c s w d t.
       interp v c s = t1 ∧
       interp w d t = t2 ∧
       ($= +++ v_rel) v w ∧
       cont_rel c d ∧
       state_rel s t)` >>
  rw []
  >~ [‘interp v c s = interp w d t’] >- (
    disj2_tac >> rpt $ irule_at Any EQ_REFL >> simp[]
  )
  \\ drule_all case_proj_next_action \\ strip_tac
  >- (
    qpat_x_assum `_ = Ret _` mp_tac
    \\ once_rewrite_tac [interp_def]
    \\ Cases_on `next_action v' c' s'`
    \\ Cases_on `next_action w' d' t''` \\ gvs[])
  >- (
    qpat_x_assum `_ = Div` mp_tac >>
    once_rewrite_tac[interp_def] >>
    Cases_on `next_action v' c' s'` >> Cases_on `next_action w' d' t''` >>
    gvs[])
  >- (
    qpat_x_assum `_ = Vis _ _ ` mp_tac
    \\ rw [Once interp_def]
    \\ rw [Once interp_def]
    \\ Cases_on `next_action v' c' s'`
    \\ Cases_on `next_action w' d' t''` \\ gvs []
    \\ rw [] \\ gs []
    \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ disj2_tac
    \\ rpt (irule_at Any EQ_REFL) \\ simp []
    \\ rw [Once exp_rel_cases])
QED

Theorem case_proj_semantics:
  closed x ∧
  exp_rel x y ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ rw [semantics_def]
  \\ irule case_proj_interp
  \\ gs [cont_rel_def, state_rel_def]
  \\ irule exp_rel_eval \\ gs []
QED

Inductive compile_rel:
(* Proj *)
[compile_rel_Proj:]
  (∀x y s i j v w b.
     i < j ∧
     compile_rel x y ⇒
       compile_rel (Seq (If (IsEq s j b (Var v)) Unit Fail)
                    (Let (SOME w) (Delay (Force (Proj s i (Var v)))) x))
               (Seq (If (IsEq s j b (Var v)) Unit Fail)
                    (Let (SOME w) (Proj s i (Var v)) y))) ∧
(* Boilerplate: *)
[compile_rel_App:]
  (∀f g x y.
     compile_rel f g ∧
     compile_rel x y ⇒
       compile_rel (App f x) (App g y)) ∧
[compile_rel_Lam:]
  (∀s x y.
     compile_rel x y ⇒
       compile_rel (Lam s x) (Lam s y)) ∧
[compile_rel_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 compile_rel x y ∧
                 ok_binder x) f g ∧
     compile_rel x y ⇒
       compile_rel (Letrec f x) (Letrec g y)) ∧
[compile_rel_Let_SOME:]
  (∀bv x1 y1 x2 y2.
     compile_rel x1 x2 ∧
     compile_rel y1 y2 ⇒
       compile_rel (Let (SOME bv) x1 y1) (Let (SOME bv) x2 y2)) ∧
[compile_rel_Let_NONE:]
  (∀x1 y1 x2 y2.
     compile_rel x1 x2 ∧
     compile_rel y1 y2 ⇒
       compile_rel (Let NONE x1 y1) (Let NONE x2 y2)) ∧
[compile_rel_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL compile_rel [x1;y1;z1] [x2;y2;z2] ⇒
       compile_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[compile_rel_Cons:]
  (∀s xs ys.
     LIST_REL (λx y. compile_rel x y ∧ ∃z. x = Delay z) xs ys ⇒
       compile_rel (Prim (Cons s) xs) (Prim (Cons s) ys)) ∧
[compile_rel_Prim:]
  (∀op xs ys.
     (∀s. op ≠ Cons s) ∧
     LIST_REL compile_rel xs ys ⇒
       compile_rel (Prim op xs) (Prim op ys)) ∧
[compile_rel_Delay:]
  (∀x y.
     compile_rel x y ⇒
       compile_rel (Delay x) (Delay y)) ∧
[compile_rel_Box:]
  (∀x y.
     compile_rel x y ⇒
       compile_rel (Box x) (Box y)) ∧
[compile_rel_Force:]
  (∀x y.
     compile_rel x y ⇒
       compile_rel (Force x) (Force y)) ∧
[compile_rel_Var:]
  (∀v.
     compile_rel (Var v) (Var v))
End

Theorem compile_case_proj_semantics:
  closed x ∧
  compile_rel x y ⇒
    semantics x Done [] = semantics y Done []
Proof
  cheat
QED

val _ = export_theory ();
