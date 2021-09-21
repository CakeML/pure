(*
  The third in a series of transformations to simplify case-compilation from
  pureLang to thunkLang. See:
  - [thunk_case_liftProofScript.sml]
  - [thunk_case_d2bProofScript.sml]
  - [thunk_case_unboxProofScript.sml]
  - [thunk_case_projProofScript.sml]
  for the others.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_case_inlProof";

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
(* Inlining *)
[exp_rel_Inline:]
  (∀m v.
     v ∈ m ⇒
       exp_rel m (Var v) (Box (Var v))) ∧
[exp_rel_Inline_Value:]
  (∀m v w.
     v_rel v w ⇒
       exp_rel m (Value (Thunk (INL v))) (Box (Value w))) ∧
[exp_rel_NoInline:]
  (∀m v.
     v ∉ m ⇒
       exp_rel m (Var v) (Var v)) ∧
[exp_rel_Bind:]
  (∀m v w y1 y2.
     exp_rel (v INSERT m) y1 y2 ∧
     w ∉ m ⇒
       exp_rel m (Let (SOME v) (Box (Var w)) y1)
                     (Let (SOME v) (Var w) y2)) ∧
[exp_rel_Bind_Value:]
  (∀m v x1 x2 y1 y2.
     exp_rel (v INSERT m) y1 y2 ∧
     v_rel x1 x2 ⇒
       exp_rel m (Let (SOME v) (Box (Value x1)) y1)
                     (Let (SOME v) (Value x2) y2)) ∧
(* Boilerplate: *)
[exp_rel_App:]
  (∀m f g x y.
     exp_rel m f g ∧
     exp_rel m x y ⇒
       exp_rel m (App f x) (App g y)) ∧
[exp_rel_Lam:]
  (∀m s x y.
     exp_rel (m DELETE s) x y ⇒
       exp_rel m (Lam s x) (Lam s y)) ∧
[exp_rel_Letrec:]
  (∀m m1 f g x y.
     m1 = m DIFF set (MAP FST f) ∧
     LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ ok_binder x ∧ exp_rel m1 x y) f g ∧
     exp_rel m1 x y ⇒
       exp_rel m (Letrec f x) (Letrec g y)) ∧
[exp_rel_Let_SOME:]
  (∀m bv x1 y1 x2 y2.
     exp_rel m x1 x2 ∧
     exp_rel (m DELETE bv) y1 y2 ⇒
       exp_rel m (Let (SOME bv) x1 y1) (Let (SOME bv) x2 y2)) ∧
[exp_rel_Let_NONE:]
  (∀m x1 y1 x2 y2.
     exp_rel m x1 x2 ∧
     exp_rel m y1 y2 ⇒
       exp_rel m (Let NONE x1 y1) (Let NONE x2 y2)) ∧
[exp_rel_If:]
  (∀m x1 x2 y1 y2 z1 z2.
     LIST_REL (exp_rel m) [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel m (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_Prim:]
  (∀m op xs ys.
     LIST_REL (exp_rel m) xs ys ⇒
       exp_rel m (Prim op xs) (Prim op ys)) ∧
[exp_rel_Delay:]
  (∀m x y.
     exp_rel m x y ⇒
       exp_rel m (Delay x) (Delay y)) ∧
[exp_rel_Box:]
  (∀m x y.
     exp_rel m x y ⇒
       exp_rel m (Box x) (Box y)) ∧
[exp_rel_Force:]
  (∀m x y.
     exp_rel m x y ⇒
       exp_rel m (Force x) (Force y)) ∧
[exp_rel_MkTick:]
  (∀m x y.
     exp_rel m x y ⇒
       exp_rel m (MkTick x) (MkTick y)) ∧
[exp_rel_Value:]
  (∀m v w.
     v_rel v w ⇒
       exp_rel m (Value v) (Value w)) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x)) ∧
[v_rel_Constructor:]
  (∀vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Closure:]
  (∀s x y.
     exp_rel EMPTY x y ∧
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
                 ok_binder x ∧
                 exp_rel EMPTY x y) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Thunk_INR:]
  (∀x y.
     exp_rel EMPTY x y ∧
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
    “v_rel (Atom s) z”,
    “v_rel z (Atom s)”,
    “v_rel (Thunk (INL s)) z”,
    “v_rel z (Thunk (INL s))”,
    “v_rel (Thunk (INR s)) z”,
    “v_rel z (Thunk (INR s))” ]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem exp_rel_freevars:
  m ∩ freevars x = m1 ∩ freevars x ∧
  exp_rel m x y ⇒
    exp_rel m1 x y
Proof
  qsuff_tac ‘
    (∀m x y.
       exp_rel m x y ⇒
       ∀m1.
         m ∩ freevars x = m1 ∩ freevars x ⇒
           exp_rel m1 x y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- (
    rw [SF SFY_ss])
  \\ ho_match_mp_tac exp_rel_strongind \\ simp []
  \\ rw []
  >- ((* Inline *)
    gs [freevars_def]
    \\ irule exp_rel_Inline
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, SF SFY_ss])
  >- ((* Inline Value *)
    gs [freevars_def]
    \\ irule exp_rel_Inline_Value \\ gs [])
  >- ((* NoInline *)
    gs [freevars_def]
    \\ irule exp_rel_NoInline
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, SF SFY_ss])
  >- ((* Let Bind *)
    gs [freevars_def]
    \\ irule exp_rel_Bind
    \\ first_assum (irule_at Any)
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP]
    \\ strip_tac \\ gs [])
  >- ((* Let Bind Value *)
    gs [freevars_def]
    \\ irule exp_rel_Bind_Value \\ gs []
    \\ first_assum (irule_at Any)
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP])
  >- ((* App *)
    gs [freevars_def]
    \\ irule exp_rel_App \\ gs []
    \\ first_x_assum (irule_at Any)
    \\ first_x_assum (irule_at Any)
    \\ gs [INTER_DEF, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP])
  >- ((* Lam *)
    gs [freevars_def]
    \\ irule exp_rel_Lam \\ gs []
    \\ first_x_assum irule
    \\ gs [SUBSET_DEF, INTER_DEF, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP])
  >- ((* Letrec *)
    gs [freevars_def]
    \\ irule exp_rel_Letrec \\ gs []
    \\ first_x_assum (irule_at (Pos last))
    \\ irule_at Any LIST_REL_mono
    \\ first_x_assum (irule_at (Pos (el 2)))
    \\ rw []
    >- (
      gvs [ELIM_UNCURRY]
      \\ first_x_assum irule
      \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP, SUBSET_DEF,
             IN_DISJOINT, freevars_def, ELIM_UNCURRY, MEM_MAP]
      \\ gs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”, PULL_EXISTS]
      \\ rw [] \\ gs [SF DNF_ss]
      \\ first_x_assum irule
      \\ rw [] \\ gs []
      \\ first_assum (irule_at Any)
      \\ first_assum (irule_at Any)
      \\ gs [])
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP, SUBSET_DEF,
           IN_DISJOINT, freevars_def, ELIM_UNCURRY, MEM_MAP])
  >- ((* Let SOME *)
    gs [freevars_def]
    \\ irule exp_rel_Let_SOME \\ gs []
    \\ first_x_assum (irule_at Any)
    \\ first_x_assum (irule_at Any)
    \\ qmatch_asmsub_rename_tac ‘freevars x1 DIFF _’
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM, DISJ_EQ_IMP, SUBSET_DEF])
  >- ((* Let NONE *)
    gs [freevars_def]
    \\ irule exp_rel_Let_NONE
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM])
  >- ((* If *)
    gs [freevars_def]
    \\ irule exp_rel_If \\ gs []
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM])
  >- ((* Prim *)
    gs [freevars_def]
    \\ irule exp_rel_Prim \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ rw [] \\ gs []
    \\ first_x_assum irule \\ rw []
    \\ gs [IN_INTER, EXTENSION, EQ_IMP_THM, MEM_MAP]
    \\ rw [] \\ gs [SF DNF_ss]
    \\ first_x_assum irule \\ gs []
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Delay *)
    gs [freevars_def]
    \\ irule exp_rel_Delay \\ gs [])
  >- ((* Box *)
    gs [freevars_def]
    \\ irule exp_rel_Box \\ gs [])
  >- ((* Force *)
    gs [freevars_def]
    \\ irule exp_rel_Force \\ gs [])
  >- ((* MkTick *)
    gs [freevars_def]
    \\ irule exp_rel_MkTick \\ gs [])
  >- ((* Value *)
    gs [freevars_def]
    \\ irule exp_rel_Value \\ gs [])
QED

Theorem ok_binder_subst[local,simp]:
  ∀x. ok_binder x ⇒ ok_binder (subst vs x)
Proof
  Cases \\ simp [subst_def]
QED

Theorem exp_rel_subst:
  ∀vs x ws y m.
    MAP FST vs = MAP FST ws ∧
    LIST_REL (λ(f,v) (g,w).
      (f ∈ m ⇒ v_rel v (Thunk (INL w))) ∧
      (f ∉ m ⇒ v_rel v w)) vs ws ∧
    exp_rel m x y ⇒
      exp_rel m (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    >- ((* s ∈ m *)
      rpt CASE_TAC \\ gs []
      \\ imp_res_tac ALOOKUP_SOME \\ gs [ALOOKUP_NONE, MAP_REVERSE,
                                         exp_rel_Inline]
      \\ drule_then (qspec_then ‘REVERSE vs’ mp_tac) ALOOKUP_SOME_EL_2
      \\ gvs [MAP_REVERSE, EL_REVERSE, LIST_REL_EL_EQN, SF CONJ_ss]
      \\ strip_tac
      \\ qmatch_asmsub_abbrev_tac ‘EL k vs’
      \\ ‘k < LENGTH ws’ by gs [Abbr ‘k’]
      \\ first_x_assum (drule_then assume_tac)
      \\ rpt (pairarg_tac \\ gvs [])
      \\ irule exp_rel_Inline_Value
      \\ gs [])
        (* s ∉ m *)
    \\ rpt CASE_TAC \\ gs []
    \\ imp_res_tac ALOOKUP_SOME \\ gs [ALOOKUP_NONE, MAP_REVERSE,
                                       exp_rel_NoInline]
    \\ irule exp_rel_Value
    \\ drule_then (qspec_then ‘REVERSE vs’ mp_tac) ALOOKUP_SOME_EL_2
    \\ gvs [MAP_REVERSE, EL_REVERSE, LIST_REL_EL_EQN, SF CONJ_ss]
    \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac ‘EL k vs’
    \\ ‘k < LENGTH ws’ by gs [Abbr ‘k’]
    \\ first_x_assum (drule_then assume_tac)
    \\ rpt (pairarg_tac \\ gvs []))
  >- ((* Prim *)
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ first_x_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* If *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_If \\ fs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs [SF SFY_ss])
  >- ((* App *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_App \\ fs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs [SF SFY_ss])
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ gs [subst_def]
    \\ irule exp_rel_Lam
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ simp [FORALL_PROD]
    \\ rw [] \\ gs [Abbr ‘P’])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ gs [subst_def]
    \\ irule exp_rel_Let_NONE \\ fs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs []
    \\ first_x_assum (irule_at (Pos last)) \\ gs [SF SFY_ss])
  >- ((* Let SOME + Let Bind *)
    rw [Once exp_rel_cases] \\ gs []
    >- ((* Let Bind *)
      simp [subst_def]
      \\ rpt CASE_TAC \\ gs []
      \\ imp_res_tac ALOOKUP_SOME \\ gs [ALOOKUP_NONE, MAP_REVERSE]
      \\ (irule exp_rel_Bind ORELSE irule exp_rel_Bind_Value) \\ gs []
      \\ first_x_assum (irule_at (Pos last))
      \\ gvs [MAP_FST_FILTER, EVERY2_MAP, LAMBDA_PROD]
      \\ rw []
      >~ [‘v_rel v1 v2’] >- (
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
      \\ irule exp_rel_Bind_Value \\ gs []
      \\ first_x_assum irule
      \\ gvs [MAP_FST_FILTER, EVERY2_MAP, LAMBDA_PROD]
      \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
      \\ irule LIST_REL_FILTER \\ gs []
      \\ irule LIST_REL_mono
      \\ first_x_assum (irule_at Any)
      \\ simp [FORALL_PROD]
      \\ rw [] \\ gs [Abbr ‘P’])
    \\ simp [subst_def]
    \\ irule exp_rel_Let_SOME \\ simp []
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER \\ gs []
    \\ irule LIST_REL_mono
    \\ first_x_assum (irule_at Any)
    \\ simp [FORALL_PROD]
    \\ rw [] \\ gs [Abbr ‘P’])
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
    \\ irule exp_rel_Delay
    \\ first_x_assum irule \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Box *)
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_Box
    \\ first_x_assum irule \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Force
    \\ first_x_assum irule \\ gs [])
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def, exp_rel_Value, exp_rel_Inline_Value])
  >- ((* MkTick *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_MkTick
    \\ first_x_assum irule \\ gs []
    \\ first_assum (irule_at Any))
QED

Theorem exp_rel_eval_to:
  ∀k x y m.
    closed x ∧
    exp_rel m x y ⇒
      ($= +++ v_rel)
        (eval_to k x)
        (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ simp []
  \\ rpt conj_tac \\ rpt gen_tac
  >~ [‘Value v’] >- (
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘App f x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ rename1 ‘exp_rel _ x y’
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
      \\ first_x_assum irule \\ gs [closed_subst]
      \\ irule_at Any exp_rel_subst
      \\ first_assum (irule_at Any) \\ gs [])
        (* Recclosure *)
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘OPTREL (exp_rel EMPTY) (ALOOKUP (REVERSE xs) s)
                                   (ALOOKUP (REVERSE ys) s)’
      by (irule LIST_REL_OPTREL \\ gs []
          \\ gs [ELIM_UNCURRY, LIST_REL_CONJ])
    \\ gs [OPTREL_def]
    \\ gvs [Once exp_rel_cases]
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
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ gvs [freevars_def, SUBSET_DEF, SF ETA_ss, SF DNF_ss, DISJ_SYM,
            DISJ_EQ_IMP])
  >~ [‘Lam s x’] >- (
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def, v_rel_def]
    \\ irule exp_rel_freevars
    \\ gs [SUBSET_DEF, EXTENSION]
    \\ first_assum (irule_at Any)
    \\ rw [Once DISJ_SYM, DISJ_EQ_IMP])
  >~ [‘Let NONE x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any))
  >~ [‘Let (SOME n) x y’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    >- ((* Bind Value *)
      simp [eval_to_def]
      \\ IF_CASES_TAC \\ gs []
      \\ first_x_assum irule
      \\ simp [closed_subst]
      \\ irule_at Any exp_rel_subst \\ gs []
      \\ first_assum (irule_at Any) \\ gs [])
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ first_x_assum irule
    \\ simp [closed_subst]
    \\ irule_at Any exp_rel_subst
    \\ first_assum (irule_at Any)
    \\ simp [])
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
    \\ irule_at Any exp_rel_freevars
    \\ first_assum (irule_at Any)
    \\ rw [IN_INTER, EXTENSION, MEM_MAP, EXISTS_PROD, PULL_EXISTS,
           Once DISJ_SYM, DISJ_EQ_IMP, SF SFY_ss])
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
    \\ IF_CASES_TAC \\ gs [v_rel_def]
    \\ IF_CASES_TAC \\ gs [v_rel_def])
  >~ [‘Force x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ rename1 ‘exp_rel m x y’
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
        \\ ‘OPTREL (λx0 y0. ok_binder x0 ∧
                            exp_rel EMPTY x0 y0)
                   (ALOOKUP (REVERSE xs) s)
                   (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL \\ gs []
              \\ gs [ELIM_UNCURRY, LIST_REL_CONJ])
        \\ gs [OPTREL_def]
        \\ gvs [Once exp_rel_cases]
        \\ first_x_assum irule
        \\ simp [subst_funs_def]
        \\ irule_at Any exp_rel_subst
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
            \\ gs [Once v_rel_cases])
    \\ gs []
    \\ first_x_assum irule
    \\ rw [Once exp_rel_cases]
    \\ rw [Once exp_rel_cases]
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [Once v_rel_cases])
  >~ [‘Delay x’] >- (
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ irule exp_rel_freevars
    \\ first_assum (irule_at Any)
    \\ gs [closed_def])
  >~ [‘Box x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel m x y’
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs [])
  >~ [‘MkTick x’] >- (
    strip_tac
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel m x y’
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
      \\ rename1 ‘exp_rel m x y’
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
      \\ rename1 ‘exp_rel m x y’
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
      \\ first_x_assum (drule_all_then assume_tac)
      \\ rpt CASE_TAC \\ gs []))
QED

val _ = export_theory ();

