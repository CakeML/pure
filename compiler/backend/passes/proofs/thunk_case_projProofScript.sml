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
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory
     thunk_semantics_delayedTheory thunk_tickProofTheory
     thunk_untickProofTheory;

val _ = new_theory "thunk_case_projProof";

val _ = set_grammar_ancestry [
  "finite_map", "pred_set", "rich_list", "thunkLang", "wellorder",
  "thunkLangProps", "thunk_semantics", "thunk_semantics_delayed" ];

val _ = numLib.prefer_num ();

Theorem SUM_REL_THM[local,simp] = sumTheory.SUM_REL_THM;

Theorem PAIR_REL_def[local,simp] = pairTheory.PAIR_REL;

Inductive exp_rel:
(* Proj *)
[exp_rel_Proj:]
  (∀x y s i j v w b.
     i < j ∧
     exp_rel x y ⇒
       exp_rel (Seq (If (IsEq s j b (Var v)) Unit Fail)
                    (Let (SOME w) (Tick (Delay (Force (Proj s i (Var v))))) x))
               (Seq (If (IsEq s j b (Var v)) Unit Fail)
                    (Let (SOME w) (MkTick (Proj s i (Var v))) y)))
[exp_rel_Proj_Value:]
  (∀x y s i j u v w b.
     i < j ∧
     exp_rel x y ∧
     v_rel u v ⇒
       exp_rel (Seq (If (IsEq s j b (Value u)) Unit Fail)
                    (Let (SOME w) (Tick (Delay (Force (Proj s i (Value u))))) x))
               (Seq (If (IsEq s j b (Value v)) Unit Fail)
                    (Let (SOME w) (MkTick (Proj s i (Value v))) y)))
[v_rel_Proj:]
  (∀xs s i.
     i < LENGTH xs ∧
     v_rel (EL i xs) v ∧
     is_anyThunk v ⇒
       v_rel (Thunk (Force (Proj s i (Value (Constructor s xs)))))
             (DoTick v))
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
                 exp_rel x y ∧
                 ok_binder x) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y))
[exp_rel_Let_SOME:]
  (∀bv x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let (SOME bv) x1 y1) (Let (SOME bv) x2 y2))
[exp_rel_Let_NONE:]
  (∀x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let NONE x1 y1) (Let NONE x2 y2))
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
     LIST_REL (λv w. v_rel v w ∧ is_anyThunk v) vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws))
[v_rel_Monadic:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ∧ EVERY closed xs ⇒
     v_rel (Monadic mop xs) (Monadic mop ys))
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ∧
     freevars x ⊆ {s} ⇒
       v_rel (Closure s x) (Closure s y))
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) (DoTick w))
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 freevars x ⊆ set (MAP FST f) ∧
                 fn = gn ∧
                 exp_rel x y ∧
                 ok_binder x) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n))
[v_rel_Thunk:]
  (∀x y.
     exp_rel x y ∧
     closed x ⇒
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
    “v_rel (DoTick x) z”,
    “v_rel z (DoTick x)”,
    “v_rel (Atom s) z”,
    “v_rel z (Atom s)”,
    “v_rel (Thunk s) z”,
    “v_rel z (Thunk s)” ]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ;

Triviality LIST_REL_IMP_MAP_FST_EQ:
  ∀f g. LIST_REL P f g ∧ (∀x y. P x y ⇒ FST x = FST y) ⇒
        MAP FST f = MAP FST g
Proof
  Induct \\ fs [PULL_EXISTS]
QED

Theorem exp_rel_freevars:
  exp_rel x y ⇒ freevars x = freevars y
Proof
  qsuff_tac ‘(∀x y. exp_rel x y ⇒ freevars x = freevars y) ∧ (∀v1 v2. v_rel v1 v2 ⇒ T)’
  >- (rw [] \\ res_tac \\ fs [])
  \\ ho_match_mp_tac exp_rel_ind
  \\ rw [] \\ fs [freevars_def]
  >~ [‘ok_binder’] >-
   (drule LIST_REL_IMP_MAP_FST_EQ \\ fs [FORALL_PROD]
    \\ rw [] \\ AP_THM_TAC
    \\ ntac 4  AP_TERM_TAC
    \\ last_x_assum mp_tac
    \\ qid_spec_tac ‘g’
    \\ qid_spec_tac ‘f’
    \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD])
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘xs’
  \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD]
  \\ rw [] \\ res_tac \\ fs []
QED

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
    \\ irule exp_rel_Prim
    \\ gs [EVERY2_MAP, EVERY2_refl_EQ]
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw [])
  >- ((* Monad *)
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [subst_def]
    \\ irule exp_rel_Monad
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

Theorem LIST_REL_ignore:
  ∀l l'.
    LIST_REL
      (λ(fn,x) (gn,y).
           freevars x ⊆ set (MAP FST l) ∧ fn = gn ∧
           exp_rel x y ∧ ok_binder x) l l' ⇒
    LIST_REL (λ(fn,x) (gn,y). fn = gn ∧ exp_rel x y ∧ ok_binder x) l l'
Proof
  gvs [LIST_REL_EL_EQN] \\ rw []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ first_x_assum drule \\ rw []
QED

Theorem LIST_REL_split:
  ∀l l'.
    LIST_REL
      (λ(f,x) (g,y).
        freevars x ⊆ set (MAP FST l) ∧ f = g ∧ exp_rel x y ∧
        ok_binder x) l l' ⇒
    MAP FST l = MAP FST l' ∧ EVERY ok_binder (MAP SND l) ∧
    LIST_REL exp_rel (MAP SND l) (MAP SND l')
Proof
  rpt gen_tac \\ strip_tac
  \\ dxrule LIST_REL_ignore
  \\ map_every qid_spec_tac [‘l'’, ‘l’]
  \\ Induct \\ rw [] \\ gvs []
  \\ rpt $ (pairarg_tac \\ gvs [])
  \\ gvs [LIST_REL_EL_EQN, EVERY_EL, EL_MAP] \\ rw []
  \\ first_x_assum drule \\ rw []
  \\ rpt (pairarg_tac \\ gvs [])
QED

Theorem LIST_REL_ALOOKUP_REVERSE:
  ∀l l'.
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
  ‘(∀v w. exp_rel v w ⇒ T) ∧
   (∀v w. v_rel v w ⇒ (is_anyThunk w ⇔ is_anyThunk v))’
    suffices_by gvs []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw [] \\ gvs []
  \\ rw [is_anyThunk_def, dest_anyThunk_def]
  \\ gvs [is_anyThunk_def, dest_anyThunk_def, AllCaseEqs()]
  \\ dxrule LIST_REL_split \\ rpt strip_tac
  \\ drule_all_then (qspec_then ‘n’ mp_tac) LIST_REL_ALOOKUP_REVERSE
  \\ rpt strip_tac
  \\ rgs [Once exp_rel_cases]
  \\ Cases_on ‘ALOOKUP (REVERSE f) n’ \\ gvs []
QED

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
        \\ irule exp_rel_subst \\ gs []
        \\ first_x_assum drule \\ rw []
        \\ `is_anyThunk (EL i l)` by (rw [is_anyThunk_def, dest_anyThunk_def])
        \\ drule v_rel_anyThunk \\ gvs [])
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
  >~ [`Monad mop xs`]
  >- (
    rw[] >> pop_assum mp_tac >> rw[Once exp_rel_cases] >>
    gvs[eval_to_def]
    )
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
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      first_x_assum (qspec_then ‘k’ assume_tac)
      \\ ‘($= +++ LIST_REL v_rel) (result_map (eval_to k) xs)
                                  (result_map (eval_to k) ys)’
        suffices_by (
          rw [SF ETA_ss]
          \\ Cases_on ‘result_map (eval_to k) xs’
          \\ Cases_on ‘result_map (eval_to k) ys’ \\ gs []
          \\ rpt (CASE_TAC \\ gvs [])
          \\ gvs [EVERY_EL, EXISTS_MEM, MEM_EL, LIST_REL_EL_EQN]
          \\ ntac 2 (first_x_assum drule \\ rpt strip_tac)
          \\ drule v_rel_anyThunk \\ rw [])
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
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
      \\ Cases_on `x'` \\ gvs [])
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
      \\ rw [oneline sum_bind_def] \\ rpt (CASE_TAC \\ gvs [])
      >~ [`INL Type_error`] >- (drule eval_to_Force_anyThunk \\ rw [])
      \\ `($= +++ v_rel)
            (eval_to (k - 1) (Force (Proj s' i (Value (Constructor s' xs)))))
            (eval_to (k - 1) (Force (Value u)))`
        suffices_by gvs []
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
      \\ rw [oneline sum_bind_def] \\ rpt (CASE_TAC \\ gvs [])
      \\ ‘($= +++ v_rel)
            (eval_to (k - 1) (subst_funs xs x'))
            (eval_to (k - 1) (subst_funs ys y'))’
        suffices_by (
          gvs []
          \\ rpt strip_tac
          \\ drule v_rel_anyThunk \\ rw [])
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
    \\ simp [subst_funs_def]
    \\ rw [oneline sum_bind_def] \\ rpt (CASE_TAC \\ gvs [])
    \\ ‘($= +++ v_rel) (eval_to (k - 1) e) (eval_to (k - 1) e')’
      suffices_by (
        gvs []
        \\ rpt strip_tac
        \\ drule v_rel_anyThunk \\ rw [])
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

Theorem exp_rel_eval_to[allow_rebind] =
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

Overload closed_exp_rel = ``λx y. closed x ∧ exp_rel x y``

Theorem case_proj_apply_closure[local]:
  closed_exp_rel x y ∧
  v_rel v2 w2 ∧
  apply_closure x v2 f ≠ Err ∧
  f (INL Type_error) = Err ∧
  (∀x y.
     ($= +++ v_rel) x y ∧ f x ≠ Err ⇒
       next_rel v_rel closed_exp_rel (f x) (g y)) ⇒
    next_rel v_rel closed_exp_rel
             (apply_closure x v2 f)
             (apply_closure y w2 g)
Proof
  rw [apply_closure_def, with_value_def] >>
  `eval x ≠ INL Type_error` by (CCONTR_TAC >> gvs[]) >>
  drule_all_then assume_tac exp_rel_eval >>
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
  \\ ‘OPTREL (λx y. ok_binder x ∧ exp_rel x y ∧ freevars x ⊆ set (MAP FST xs))
             (ALOOKUP (REVERSE xs) s)
             (ALOOKUP (REVERSE ys) s)’
    by (irule LIST_REL_OPTREL
        \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY])
  \\ gs [OPTREL_def]
  \\ qpat_x_assum ‘exp_rel _ _ ’ mp_tac
  \\ rw [Once exp_rel_cases] \\ gs []
  \\ first_x_assum irule \\ gs []
  \\ irule exp_rel_eval
  \\ irule_at Any exp_rel_subst
  \\ gs [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  \\ irule_at Any LIST_EQ
  \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
  \\ simp[closed_subst, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
  \\ gvs[FST_THM, SUBSET_DEF, freevars_def] \\ metis_tac[]
QED

Theorem case_proj_rel_ok[local]:
  rel_ok F v_rel closed_exp_rel
Proof
  rw [rel_ok_def]
  >- ((* ∀x. f x ≠ Err from rel_ok prevents this case *)
    simp [case_proj_apply_closure])
  >- ( (* LIST_REL stuff *)
    gvs[LIST_REL_EL_EQN]
    )
  >- ((* Equal literals are related *)
    simp [exp_rel_Prim])
  >- ((* Equal 0-arity conses are related *)
    simp [exp_rel_Prim])
  >- ((* v_rel v1 v2 ⇒ exp_rel (Value v1) (Value v2) *)
    simp [exp_rel_Value])
  >- ( (* LIST_REL stuff *)
    gvs[LIST_REL_EL_EQN, EVERY_EL]
    )
QED

Theorem case_proj_sim_ok[local]:
  sim_ok F v_rel closed_exp_rel
Proof
  rw [sim_ok_def]
  \\ simp [exp_rel_eval]
  >- gvs[closed_subst, closed_def]
  \\ irule exp_rel_subst \\ gs []
QED

Theorem case_proj_semantics:
  exp_rel x y ∧
  closed x ∧
  pure_semantics$safe_itree (semantics x Done []) ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics
  \\ irule_at Any case_proj_sim_ok
  \\ irule_at Any case_proj_rel_ok \\ gs []
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
                    (Let (SOME w) (Proj s i (Var v)) y)))
(* Boilerplate: *)
[compile_rel_App:]
  (∀f g x y.
     compile_rel f g ∧
     compile_rel x y ⇒
       compile_rel (App f x) (App g y))
[compile_rel_Lam:]
  (∀s x y.
     compile_rel x y ⇒
       compile_rel (Lam s x) (Lam s y))
[compile_rel_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 compile_rel x y ∧
                 ok_binder x) f g ∧
     compile_rel x y ⇒
       compile_rel (Letrec f x) (Letrec g y))
[compile_rel_Let_SOME:]
  (∀bv x1 y1 x2 y2.
     compile_rel x1 x2 ∧
     compile_rel y1 y2 ⇒
       compile_rel (Let (SOME bv) x1 y1) (Let (SOME bv) x2 y2))
[compile_rel_Let_NONE:]
  (∀x1 y1 x2 y2.
     compile_rel x1 x2 ∧
     compile_rel y1 y2 ⇒
       compile_rel (Let NONE x1 y1) (Let NONE x2 y2))
[compile_rel_If:]
  (∀x1 x2 y1 y2 z1 z2.
     LIST_REL compile_rel [x1;y1;z1] [x2;y2;z2] ⇒
       compile_rel (If x1 y1 z1) (If x2 y2 z2))
[compile_rel_Prim:]
  (∀op xs ys.
     LIST_REL compile_rel xs ys ⇒
       compile_rel (Prim op xs) (Prim op ys))
[compile_rel_Monad:]
  (∀mop xs ys.
     LIST_REL compile_rel xs ys ⇒
       compile_rel (Monad mop xs) (Monad mop ys))
[compile_rel_Delay:]
  (∀x y.
     compile_rel x y ⇒
       compile_rel (Delay x) (Delay y))
[compile_rel_Force:]
  (∀x y.
     compile_rel x y ⇒
       compile_rel (Force x) (Force y))
[compile_rel_Var:]
  (∀v.
     compile_rel (Var v) (Var v))
End

Overload tick_rel = “thunk_tickProof$exp_rel”
Overload mktick_rel = “thunk_untickProof$exp_rel”

Theorem compile_rel_thm:
  ∀x y.
    compile_rel x y ⇒
    ∃x1 y1. tick_rel x x1 ∧ exp_rel x1 y1 ∧ mktick_rel y1 y
Proof
  Induct_on ‘compile_rel’ \\ rw []
  >-
   (irule_at Any exp_rel_Proj
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Let
    \\ irule_at Any thunk_tickProofTheory.exp_rel_If
    \\ rpt (irule_at Any thunk_tickProofTheory.exp_rel_Prim \\ fs [PULL_EXISTS])
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Var
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Let \\ fs []
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Tick
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Delay
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Force
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Prim \\ fs [PULL_EXISTS]
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Var
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Let
    \\ irule_at Any thunk_untickProofTheory.exp_rel_If \\ gvs [PULL_EXISTS]
    \\ rpt (irule_at Any thunk_untickProofTheory.exp_rel_Prim \\ gvs [PULL_EXISTS])
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Var
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Let \\ fs []
    \\ irule_at Any thunk_untickProofTheory.exp_rel_MkTick
    \\ rpt (irule_at Any thunk_untickProofTheory.exp_rel_Prim \\ gvs [PULL_EXISTS])
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Var)
  >~ [‘App’] >-
   (irule_at Any exp_rel_App
    \\ irule_at Any thunk_tickProofTheory.exp_rel_App
    \\ irule_at Any thunk_untickProofTheory.exp_rel_App
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  >~ [‘Lam’] >-
   (irule_at Any exp_rel_Lam
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Lam
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Lam
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  >~ [‘If’] >-
   (irule_at Any exp_rel_If
    \\ irule_at Any thunk_tickProofTheory.exp_rel_If
    \\ irule_at Any thunk_untickProofTheory.exp_rel_If \\ fs []
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  >~ [‘Force’] >-
   (irule_at Any exp_rel_Force
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Force
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Force \\ fs []
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  >~ [‘Var’] >-
   (irule_at Any exp_rel_Var
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Var
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Var \\ fs []
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  >~ [‘Let (SOME _)’] >-
   (irule_at Any exp_rel_Let_SOME
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Let
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Let \\ fs []
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  >~ [‘Let NONE’] >-
   (irule_at Any exp_rel_Let_NONE
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Let
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Let \\ fs []
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  >~ [‘Delay’] >-
   (irule_at Any exp_rel_Delay
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Delay
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Delay \\ fs []
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  >~ [‘Prim’] >-
   (irule_at Any exp_rel_Prim \\ fs []
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Prim
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Prim \\ fs []
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ first_x_assum dxrule \\ rw []
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  >~ [`Monad`]
  >- (irule_at Any exp_rel_Monad \\ fs []
    \\ irule_at Any thunk_tickProofTheory.exp_rel_Monad
    \\ irule_at Any thunk_untickProofTheory.exp_rel_Monad \\ fs []
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ first_x_assum dxrule \\ rw []
    \\ rpt $ first_assum $ irule_at $ Pos hd)
  \\ rename [‘Letrec’]
  \\ irule_at Any exp_rel_Letrec \\ fs []
  \\ irule_at Any thunk_tickProofTheory.exp_rel_Letrec
  \\ irule_at Any thunk_untickProofTheory.exp_rel_Letrec \\ fs []
  \\ rpt $ first_x_assum $ irule_at Any
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘g’
  \\ qid_spec_tac ‘f’
  \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
  \\ rw []
  \\ last_x_assum $ dxrule \\ rw []
  \\ rpt $ qpat_x_assum ‘LIST_REL _ _ _’ $ irule_at Any \\ fs []
  \\ last_assum $ irule_at Any
  \\ last_assum $ irule_at Any \\ fs []
  \\ Cases_on ‘p_2’ \\ gvs []
  \\ last_x_assum mp_tac
  \\ simp [Once compile_rel_cases] \\ strip_tac \\ gvs []
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ simp [Once thunk_tickProofTheory.exp_rel_cases]
  \\ simp [Once thunk_untickProofTheory.exp_rel_cases]
  \\ ntac 3 strip_tac
  \\ gvs [ok_bind_def]
  \\ fs [Once exp_rel_cases]
QED

Theorem compile_rel_closed:
  compile_rel x y ∧
  closed x ⇒
  closed y
Proof
  rw [] \\ drule_all compile_rel_thm \\ rw []
  \\ imp_res_tac exp_rel_freevars \\ gvs [closed_def]
  \\ imp_res_tac thunk_tickProofTheory.exp_rel_freevars \\ gvs []
  \\ imp_res_tac thunk_untickProofTheory.exp_rel_freevars \\ gvs []
QED

Theorem compile_case_proj_semantics:
  closed x ∧
  compile_rel x y ∧
  pure_semantics$safe_itree (semantics x Done []) ⇒
    semantics x Done [] = semantics y Done []
Proof
  rw [] \\ gvs []
  \\ drule_all compile_rel_thm \\ strip_tac
  \\ imp_res_tac tick_semantics
  \\ fs []
  \\ drule case_proj_semantics
  \\ impl_tac >-
   (imp_res_tac thunk_tickProofTheory.exp_rel_freevars
    \\ fs [closed_def])
  \\ strip_tac \\ gvs []
  \\ irule untick_semantics
  \\ fs []
  \\ imp_res_tac exp_rel_freevars \\ gvs [closed_def]
  \\ imp_res_tac thunk_tickProofTheory.exp_rel_freevars \\ gvs []
QED

val _ = export_theory ();
