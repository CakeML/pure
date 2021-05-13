(*
  This stage removes all suspended ticks introduced by thunk_subst_unthunk,
  and any other stage that has tampered with thunks.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     thunkLang_primitivesTheory dep_rewrite;
open pure_miscTheory thunk_substPropsTheory;

val _ = new_theory "thunk_subst_untickProof";

val _ = numLib.prefer_num ();

Inductive exp_rel:
[~Var:]
  (∀n.
     exp_rel (Var n) (Var n)) ∧
[~Value:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Value v) (Value w)) ∧
[~Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys)) ∧
[~App:]
  (∀f x g y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f x) (App g y)) ∧
[~Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y)) ∧
[~Letrec:]
  (∀f g x y.
     LIST_REL (λ(f,x) (g,y). f = g ∧ exp_rel x y) f g ∧
     exp_rel x y ⇒
     exp_rel (Letrec f x) (Letrec g y)) ∧
[~Let:]
  (∀s x1 y1 x2 y2.
     exp_rel x1 y1 ∧
     exp_rel x2 y2 ⇒
       exp_rel (Let s x1 x2) (Let s y1 y2)) ∧
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     LIST_REL exp_rel [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[~Delay:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Delay x) (Delay y)) ∧
[~Box:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Box x) (Box y)) ∧
[~Force:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Force x) (Force y)) ∧
[~MkTick:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (MkTick x) y) ∧
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ⇒
       v_rel (Closure s x) (Closure s y)) ∧
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(f,x) (g,y). f = g ∧ exp_rel x y) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Thunk_INR:]
  (∀x y.
     exp_rel x y ⇒
       v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_Thunk_INL:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INL v)) (Thunk (INL w))) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x)) ∧
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ∧
     properThunk v ⇒
       v_rel (DoTick v) w)
End

Theorem v_rel_def[simp]:
  (∀s vs.
     v_rel (Constructor s vs) w =
       ∃ws. w = Constructor s ws ∧
            LIST_REL v_rel vs ws) /\
  (∀s x.
     v_rel (Closure s x) w =
       ∃y. w = Closure s y ∧
           exp_rel x y) ∧
  (∀f n.
     v_rel (Recclosure f n) w =
       ∃g. w = Recclosure g n ∧
           LIST_REL (λ(f,x) (g,y). f = g ∧ exp_rel x y) f g) ∧
  (∀x.
     v_rel (Thunk (INR x)) w =
       ∃y. w = Thunk (INR y) ∧
           exp_rel x y) ∧
  (∀v w.
     v_rel (Thunk (INL v)) w =
       ∃u. w = Thunk (INL u) ∧
       v_rel v u) ∧
  (∀x.
     v_rel (Atom x) w =
       (w = Atom x)) ∧
  (∀v w.
     v_rel (DoTick v) w =
       (v_rel v w ∧
       properThunk v))
Proof
  rw [] \\ rw [Once exp_rel_cases]
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
    rw [Once exp_rel_cases, subst_def]
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) s) (ALOOKUP (REVERSE ws) s)’
      suffices_by (rw [OPTREL_def]
                   \\ gs [exp_rel_Var, exp_rel_Value])
    \\ irule LIST_REL_OPTREL
    \\ gs [EVERY2_MAP, LIST_REL_CONJ, ELIM_UNCURRY, Once LIST_EQ_REWRITE,
           LIST_REL_EL_EQN, EL_MAP])
  >- ((* Prim *)
    rw [Once exp_rel_cases] \\ simp [subst_def]
    \\ irule exp_rel_Prim
    \\ gvs [EVERY2_MAP, LIST_REL_EL_EQN, EL_MEM])
  >- ((* If *)
    rw [Once exp_rel_cases] \\ simp [subst_def]
    \\ irule exp_rel_If \\ fs [])
  >- ((* App *)
    rw [Once exp_rel_cases] \\ simp [subst_def]
    \\ irule exp_rel_App \\ fs [])
  >- ((* Lam *)
    rw [Once exp_rel_cases] \\ gvs [subst_def]
    \\ irule exp_rel_Lam
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs [])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases] \\ simp [subst_def]
    \\ irule exp_rel_Let \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ fs []
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs [])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ ‘MAP FST f = MAP FST g’
      by (fs [ELIM_UNCURRY, LIST_REL_CONJ]
          \\ irule LIST_EQ
          \\ gvs [LIST_REL_EL_EQN] \\ rw [EL_MAP])
    \\ irule exp_rel_Letrec
    \\ gvs [EVERY2_MAP, LAMBDA_PROD]
    \\ first_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST g)’ \\ fs []
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ irule_at Any LIST_REL_EL_MONO
    \\ first_assum (irule_at Any) \\ rw []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER]
    \\ gvs [MEM_EL, PULL_EXISTS]
    \\ rw [Once EQ_SYM_EQ]
    \\ first_assum (irule_at Any)
    \\ irule_at Any LIST_REL_FILTER \\ fs [])
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def, exp_rel_Delay])
  >- ((* Box *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def, exp_rel_Box])
  >- ((* Force *)
    rw [Once exp_rel_cases] \\ simp [subst_def]
    \\ irule exp_rel_Force \\ fs [])
  >- ((* Value *)
    rw [Once exp_rel_cases] \\ simp [subst_def]
    \\ rw [Once exp_rel_cases])
  >- ((* MkTick *)
    rw [Once exp_rel_cases] \\ simp [subst_def]
    \\ irule exp_rel_MkTick \\ fs [])
QED

Theorem v_rel_dest_Tick:
  v_rel v w ⇒ dest_Tick w = NONE
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ T) ∧
    (∀v w. v_rel v w ⇒ dest_Tick w = NONE)’
  >- rw [SF SFY_ss]
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
QED

Theorem properThunk_dest_anyThunk:
  ∀v. properThunk v ⇒
    ∃x ws. dest_anyThunk v = INR (INR x, ws)
Proof
  Induct \\ rw [] \\ simp [dest_anyThunk_def]
QED

Theorem properThunk_dest_Tick:
  ∀v. properThunk v ⇒
    dest_Tick v = NONE
Proof
  Induct \\ rw [] \\ simp []
QED


Theorem v_rel_properThunk:
  v_rel v w ∧
  properThunk v ⇒
    properThunk w
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ T) ∧
    (∀v w. v_rel v w ⇒ properThunk v ⇒ properThunk w)’
  >- (
    rw [SF SFY_ss])
  \\ ho_match_mp_tac exp_rel_strongind
  \\ rw [LIST_REL_EL_EQN, ELIM_UNCURRY]
  \\ drule_then (qspec_then ‘REVERSE g’ mp_tac) ALOOKUP_SOME_EL_2
  \\ impl_tac
  >- (
    simp [MAP_REVERSE]
    \\ irule LIST_EQ
    \\ gvs [EL_MAP])
  \\ strip_tac \\ gvs [EL_REVERSE]
  \\ qmatch_asmsub_abbrev_tac ‘EL m f’
  \\ ‘m < LENGTH g’ by fs [Abbr ‘m’]
  \\ first_x_assum (drule_then strip_assume_tac)
  \\ gs [Once exp_rel_cases]
QED

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ∧
    eval_to k x ≠ INL Type_error ⇒
      ∃j. ($= +++ v_rel)
            (eval_to k x)
            (eval_to (k + j) y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def])
  >- ((* Var *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def])
  >- ((* App *)
    rename1 ‘App x1 y1’
    \\ rw [Once exp_rel_cases] \\ gs []
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ rw [eval_to_def]
    \\ ‘eval_to k x1 ≠ INL Type_error’
      by (strip_tac \\ gs [eval_to_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to k x1 = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k) x2’ \\ gs [])
    \\ ‘∃v1. eval_to k x1 = INR v1’
      by (Cases_on ‘eval_to k x1’ \\ gs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs [])
    \\ ‘eval_to k y1 ≠ INL Type_error’
      by (strip_tac \\ gs [eval_to_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ Cases_on ‘eval_to k y1 = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to k x2 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to k x2’ \\ gs [])
      \\ ‘∀i. eval_to (i + k) x2 = eval_to k x2’
        by (strip_tac
            \\ irule eval_to_subst_mono \\ gs [])
      \\ Cases_on ‘eval_to k x2’ \\ gs []
      \\ qexists_tac ‘j2’
      \\ Cases_on ‘eval_to (j2 + k) y2’ \\ gs [])
    \\ ‘∃v2. eval_to k y1 = INR v2’
      by (Cases_on ‘eval_to k y1’ \\ gs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs [])
    \\ gs []
    \\ ‘∃s1 z1 w1. dest_anyClosure v1 = INR (s1, z1, w1)’
      by (Cases_on ‘v1’ \\ gs [dest_anyClosure_def, eval_to_def]
          \\ Cases_on ‘ALOOKUP (REVERSE l) s’ \\ gs []
          \\ CASE_TAC \\ gs [])
    \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval_to 0 x2 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j x2 = eval_to 0 x2’
        by (strip_tac
            \\ irule eval_to_subst_mono \\ gs [])
      \\ Cases_on ‘eval_to 0 y2 = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to 0 x2’ \\ gs [])
      \\ ‘∀j. eval_to j y2 = eval_to 0 y2’
        by (strip_tac
            \\ irule eval_to_subst_mono \\ gs [])
      \\ qexists_tac ‘0’
      \\ Cases_on ‘eval_to 0 x2’ \\ gs []
      \\ Cases_on ‘eval_to 0 y2’ \\ gs []
      \\ qpat_x_assum ‘v_rel v1 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gvs [dest_anyClosure_def]
      \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs [])
    \\ Cases_on ‘eval_to (k - 1) (subst (w1 ++ [s1,v2]) z1) = INL Diverge’
    >- (
      Cases_on ‘eval_to k x2 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x2 = eval_to k x2’
        by (strip_tac
            \\ irule eval_to_subst_mono \\ gs [])
      \\ Cases_on ‘eval_to k y2 = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to k x2’ \\ gs [])
      \\ ‘∀j. eval_to (j + k) y2 = eval_to k y2’
        by (strip_tac
            \\ irule eval_to_subst_mono \\ gs [])
      \\ Cases_on ‘eval_to k x2’ \\ gs []
      \\ Cases_on ‘eval_to k y2’ \\ gs []
      \\ rename1 ‘v_rel v1 u1’
      \\ ‘∃s2 z2 w2. dest_anyClosure u1 = INR (s2, z2, w2)’
        by (qpat_x_assum ‘v_rel v1 u1’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gs [dest_anyClosure_def, eval_to_def]
            \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
            \\ gs [OPTREL_def]
            \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gs [])
      \\ gs []
      \\ qpat_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
      \\ first_x_assum (irule_at Any) \\ simp []
      \\ irule_at Any exp_rel_subst
      \\ qpat_x_assum ‘v_rel v1 u1’ mp_tac
      \\ simp [Once exp_rel_cases] \\ strip_tac \\ gvs [dest_anyClosure_def]
      \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ simp [Once exp_rel_cases] \\ strip_tac \\ gvs []
      \\ simp [MAP_MAP_o, LAMBDA_PROD, combinTheory.o_DEF, GSYM FST_THM,
               EVERY2_MAP, Once exp_rel_cases, EVERY_MAP]
      \\ irule_at Any LIST_EQ
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
      \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
      \\ gvs [EVERY_EL, EL_MAP]
      \\ last_x_assum (drule_then assume_tac)
      \\ gs [])
    \\ ‘∀j. eval_to (j + j1 + j2 + k) y2 = eval_to (j2 + k) y2’
      by (strip_tac
          \\ irule eval_to_subst_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ ‘∀j. eval_to (j + j1 + j2 + k) x2 = eval_to (j1 + k) x2’
      by (strip_tac
          \\ irule eval_to_subst_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ Q.REFINE_EXISTS_TAC ‘j + j1 + j2’ \\ gs []
    \\ Cases_on ‘eval_to (j1 + k) x2’ \\ gs []
    \\ Cases_on ‘eval_to (j2 + k) y2’ \\ gs []
    \\ rename1 ‘v_rel v1 u1’
    \\ ‘∃s2 z2 w2. dest_anyClosure u1 = INR (s2, z2, w2)’
      by (qpat_x_assum ‘v_rel v1 u1’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gs [dest_anyClosure_def, eval_to_def]
          \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
          \\ gs [OPTREL_def]
          \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gs [])
    \\ rename1 ‘v_rel v2 u2’ \\ gs []
    \\ ‘exp_rel (subst (w1 ++ [s1,v2]) z1) (subst (w2 ++ [s2,u2]) z2)’
      suffices_by
        (strip_tac
         \\ first_x_assum drule
         \\ impl_tac
         >- (
           strip_tac \\ gs [eval_to_def])
         \\ disch_then (qx_choose_then ‘j3’ assume_tac)
         \\ ‘eval_to (j3 + k - 1) (subst (w2 ++ [s2,u2]) z2) ≠ INL Diverge’
           by (strip_tac
               \\ Cases_on ‘eval_to (k - 1) (subst (w1 ++ [s1,v2]) z1)’
               \\ gs [])
         \\ drule_then
           (qspec_then ‘j1 + j2 + j3 + k - 1’ assume_tac) eval_to_subst_mono
         \\ qexists_tac ‘j3’ \\ gs [])
    \\ irule_at Any exp_rel_subst
    \\ qpat_x_assum ‘v_rel v1 u1’ mp_tac
    \\ simp [Once exp_rel_cases] \\ strip_tac \\ gvs [dest_anyClosure_def]
    \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
    \\ gs [OPTREL_def]
    \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
    \\ simp [Once exp_rel_cases] \\ strip_tac \\ gvs []
    \\ simp [MAP_MAP_o, LAMBDA_PROD, combinTheory.o_DEF, GSYM FST_THM,
             EVERY2_MAP, EVERY_MAP, Once exp_rel_cases]
    \\ irule_at Any LIST_EQ
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
    \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
    \\ gs [EVERY_EL, EL_MAP]
    \\ last_x_assum (drule_then assume_tac)
    \\ gs [])
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def]
    \\ rw [Once exp_rel_cases])
  >- ((* Let NONE *)
    rename1 ‘Let NONE x1 x2’
    \\ rw [Once exp_rel_cases]
    \\ gs [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘eval_to (k - 1) x1 ≠ INL Type_error’
      by (strip_tac \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) x1 = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k - 1) y1’ \\ gs [])
    \\ ‘eval_to (k - 1) x2 ≠ INL Type_error’
      by (strip_tac
          \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs [eval_to_def]
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs [])
    \\ ‘∃v1. eval_to (k - 1) x1 = INR v1’
      by (Cases_on ‘eval_to (k - 1) x1’
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs[])
    \\ gs []
    \\ ‘eval_to (k - 1) x2 ≠ INL Type_error’
      by (strip_tac \\ gs [eval_to_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) x2 = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (k - 1) y1 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k - 1) y1 = eval_to (k - 1) y1’
        by (strip_tac
            \\ irule eval_to_subst_mono \\ gs [])
      \\ qexists_tac ‘j2’
      \\ Cases_on ‘eval_to (k - 1) y1’ \\ gs [])
    \\ ‘∃v2. eval_to (k - 1) x2 = INR v2’
      by (Cases_on ‘eval_to (k - 1) x2’
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs[])
    \\ gs []
    \\ ‘∀j2. eval_to (j1 + j2 + k - 1) y1 = eval_to (j1 + k - 1) y1’
      by (strip_tac
          \\ irule eval_to_subst_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ ‘∀j1. eval_to (j1 + j2 + k - 1) y2 = eval_to (j2 + k - 1) y2’
      by (strip_tac
          \\ irule eval_to_subst_mono \\ gs []
          \\ strip_tac \\ gs []
          \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
    \\ qexists_tac ‘j1 + j2’ \\ gs []
    \\ Cases_on ‘eval_to (j1 + k - 1) y1’ \\ gs [])
  >- ((* Let SOME *)
    rename1 ‘Let (SOME n) x1 x2’
    \\ rw [Once exp_rel_cases]
    \\ gs [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘eval_to (k - 1) x1 ≠ INL Type_error’
      by (strip_tac \\ gvs [eval_to_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) x1 = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k - 1) y1’ \\ gs [])
    \\ ‘∃v1. eval_to (k - 1) x1 = INR v1’
      by (Cases_on ‘eval_to (k - 1) x1’
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs[])
    \\ gs []
    \\ ‘eval_to (k - 1) (subst1 n v1 x2) ≠ INL Type_error’
      by (strip_tac
          \\ gs [eval_to_def])
    \\ ‘∃u1. eval_to (j1 + k - 1) y1 = INR u1’
      by (Cases_on ‘eval_to (j1 + k - 1) y1’
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs[])
    \\ gs []
    \\ ‘exp_rel (subst1 n v1 x2) (subst1 n u1 y2)’
      by (irule exp_rel_subst \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) (subst1 n v1 x2) = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (k - 1) y1 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k - 1) y1 = eval_to (k - 1) y1’
        by (strip_tac
            \\ irule eval_to_subst_mono \\ gs [])
      \\ qexists_tac ‘j2’
      \\ Cases_on ‘eval_to (k - 1) y1’ \\ gs [])
    \\ ‘∃v2. eval_to (k - 1) (subst1 n v1 x2) = INR v2’
      by (Cases_on ‘eval_to (k - 1) (subst1 n v1 x2)’
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs[])
    \\ gs []
    \\ ‘∀j2. eval_to (j1 + j2 + k - 1) y1 = eval_to (j1 + k - 1) y1’
      by (strip_tac
          \\ irule eval_to_subst_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ ‘∀j1. eval_to (j1 + j2 + k - 1) (subst1 n u1 y2) =
             eval_to (j2 + k - 1) (subst1 n u1 y2)’
      by (strip_tac
          \\ irule eval_to_subst_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ qexists_tac ‘j1 + j2’ \\ gs [])
  >- ((* If *)
    rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ rename1 ‘exp_rel z1 z2’
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ cheat)
  >- ((* Letrec *)
    cheat)
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def])
  >- ((* Box *)
    rw [Once exp_rel_cases] \\ gs [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘eval_to k x ≠ INL Type_error’
      by (strip_tac \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j1 + k) y’ \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ rename1 ‘exp_rel x y’
    \\ gs [Once eval_to_def]
    \\ ‘eval_to k x ≠ INL Type_error’
      by (strip_tac \\ gs [])
    \\ simp [Once eval_to_def]
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ rw [Once eval_to_def]
      \\ Cases_on ‘eval_to (j1 + k) y’ \\ gs [])
    \\ ‘∃v1. eval_to k x = INR v1’
      by (Cases_on ‘eval_to k x’
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs[])
    \\ Cases_on ‘eval_to (j1 + k) y’ \\ gs []
    \\ rename1 ‘v_rel v1 u1’
    \\ Cases_on ‘dest_Tick v1’ \\ gs []
    >- (
      simp [Once eval_to_def]
      \\ Cases_on ‘dest_anyThunk v1’ \\ gs []
      >- (
        qexists_tac ‘j1’
        \\ Cases_on ‘v1’ \\ gs [dest_anyThunk_def]
        \\ rename1 ‘ALOOKUP (REVERSE _) s’
        \\ drule_then (qspec_then ‘s’ assume_tac) LIST_REL_OPTREL
        \\ gs [OPTREL_def, CaseEq "exp"])
      \\ pairarg_tac \\ gvs []
      \\ ‘∃wx1 binds1. dest_anyThunk u1 = INR (wx1, binds1)’
        by (qpat_x_assum ‘v_rel v1 u1’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gs [dest_anyThunk_def]
            \\ rename1 ‘ALOOKUP (REVERSE _) s’
            \\ drule_then (qspec_then ‘s’ assume_tac) LIST_REL_OPTREL
            \\ gs [OPTREL_def]
            \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gs [])
      \\ BasicProvers.TOP_CASE_TAC \\ gs []
      >- (
        qexists_tac ‘j1’
        \\ qpat_x_assum ‘v_rel v1 u1’ mp_tac
        \\ rw [Once exp_rel_cases] \\ gvs [dest_anyThunk_def]
        \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
        \\ gs [OPTREL_def]
        \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
        \\ rw [Once exp_rel_cases] \\ gs [])
      \\ rename1 ‘subst_funs binds z’
      \\ ‘∃z1. wx1 = INR z1’
        by (qpat_x_assum ‘v_rel v1 u1’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gvs [dest_anyThunk_def]
            \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
            \\ gs [OPTREL_def]
            \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gvs [])
      \\ IF_CASES_TAC \\ gs []
      >- (
        Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to j y = eval_to j1 y’
          by (strip_tac
              \\ drule_then (qspec_then ‘j1’ assume_tac) eval_to_subst_mono
              \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_subst_mono
              \\ gs [])
        \\ simp []
        \\ qexists_tac ‘0’ \\ simp []
        \\ qpat_x_assum ‘v_rel v1 u1’ mp_tac
        \\ rw [Once exp_rel_cases] \\ gvs [])
      \\ ‘exp_rel (subst_funs binds z) (subst_funs binds1 z1)’
        by (simp [subst_funs_def]
            \\ irule_at Any exp_rel_subst
            \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                     EVERY2_MAP, EVERY_MAP, Once (CONJUNCT2 exp_rel_cases)]
            \\ irule_at Any LIST_EQ
            \\ qpat_x_assum ‘v_rel v1 u1’ mp_tac
            \\ simp [Once exp_rel_cases] \\ strip_tac
            \\ gvs [dest_anyThunk_def, EL_MAP, ELIM_UNCURRY,
                    LIST_REL_EL_EQN, SF CONJ_ss]
            \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE f) n) (ALOOKUP (REVERSE g) n)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [CaseEqs ["option", "exp"], LIST_REL_EL_EQN,
                          ELIM_UNCURRY])
            \\ gs [OPTREL_def]
            \\ gvs [CaseEqs ["option", "exp"], Once exp_rel_cases]
            \\ Cases_on ‘binds = []’ \\ gs []
            \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
            \\ gs [EVERY_EL] \\ rw []
            \\ last_x_assum (drule_then assume_tac)
            \\ gs [EL_MAP])
      \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
      \\ Cases_on ‘eval_to (k - 1) (subst_funs binds z) = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀j. eval_to (j + k) y = eval_to k y’
          by (strip_tac \\ irule eval_to_subst_mono \\ gs [])
        \\ Cases_on ‘eval_to k y’ \\ gs []
        \\ qexists_tac ‘j2’
        \\ qpat_x_assum ‘v_rel v1 u1’ mp_tac
        \\ rw [Once exp_rel_cases] \\ gs [])
      \\ ‘∀j1. eval_to (j1 + j2 + k - 1) (subst_funs binds1 z1) =
               eval_to (j2 + k - 1) (subst_funs binds1 z1)’
        by (strip_tac
            \\ irule eval_to_subst_mono \\ gs []
            \\ strip_tac \\ gs []
            \\ Cases_on ‘eval_to (k - 1) (subst_funs binds z)’ \\ gs [])
      \\ ‘∀j2. eval_to (j2 + j1 + k) y = eval_to (j1 + k) y’
        by (strip_tac
            \\ irule eval_to_subst_mono \\ gs [])
      \\ qexists_tac ‘j1 + j2’ \\ gs []
      \\ qpat_x_assum ‘v_rel v1 u1’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs [])
    \\ Cases_on ‘v1’ \\ gvs []
    \\ rename1 ‘v_rel v1 u1’
    \\ IF_CASES_TAC \\ gs []
    >- (
      gs []
      \\ simp [Once eval_to_def]
      \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j y = eval_to j1 y’
        by (qx_gen_tac ‘j’
            \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_subst_mono
            \\ drule_then (qspec_then ‘j1’ assume_tac) eval_to_subst_mono
            \\ gs [])
      \\ simp []
      \\ drule_then assume_tac v_rel_dest_Tick \\ gs []
      \\ ‘ISR (dest_anyThunk u1)’
        by (qpat_x_assum ‘v_rel v1 u1’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gvs [dest_anyThunk_def]
            \\ drule_then (qspec_then ‘n’ assume_tac) LIST_REL_OPTREL
            \\ gs [OPTREL_def]
            \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gs [])
      \\ Cases_on ‘dest_anyThunk u1’ \\ gs []
      \\ pairarg_tac \\ gvs []
      \\ qexists_tac ‘0’ \\ simp []
      \\ qpat_x_assum ‘v_rel v1 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gvs [dest_anyThunk_def]
      \\ rename1 ‘ALOOKUP (REVERSE g) s’
      \\ drule_then (qspec_then ‘s’ assume_tac) LIST_REL_OPTREL
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gvs [])
    \\ drule_then assume_tac v_rel_dest_Tick
    \\ drule_then assume_tac properThunk_dest_Tick
    \\ drule_then strip_assume_tac properThunk_dest_anyThunk
    \\ drule_all_then assume_tac v_rel_properThunk
    \\ drule_then assume_tac properThunk_dest_Tick
    \\ drule_then strip_assume_tac properThunk_dest_anyThunk
    \\ rename1 ‘dest_anyThunk v1 = INR (INR x1, ws1)’
    \\ rename1 ‘dest_anyThunk u1 = INR (INR x2, ws2)’
    \\ cheat)
  >- ((* MkTick *)
    rw [Once exp_rel_cases]
    \\ gs [Once eval_to_def]
    \\ simp [Once eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘eval_to k x ≠ INL Type_error’
      by (strip_tac \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ simp [Once eval_to_def])
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j1 + k) y’ \\ gs []
    \\ IF_CASES_TAC \\ gs [])
  >- ((* Prim *)
    cheat)
QED

Theorem exp_rel_eval:
  exp_rel x y ∧
  eval x ≠ INL Type_error ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ ‘eval_to (MAX k j) x ≠ INL Type_error’
      by (strip_tac
          \\ drule_then (qspec_then ‘MAX k j’ assume_tac) eval_to_subst_mono
          \\ gs [])
    \\ drule_all_then (qx_choose_then ‘m’ assume_tac) exp_rel_eval_to
    \\ ‘eval_to k x = eval_to (MAX k j) x’
      by (rw [Once EQ_SYM_EQ]
          \\ irule eval_to_subst_mono
          \\ simp [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to j y = eval_to (MAX k j + m) y’
      by (rw [Once EQ_SYM_EQ]
          \\ irule eval_to_subst_mono
          \\ simp [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ ‘eval_to j x ≠ INL Type_error’
      by (strip_tac \\ gs [])
    \\ drule_all_then (qx_choose_then ‘m’ assume_tac) exp_rel_eval_to
    \\ Cases_on ‘eval_to (m + j) y’ \\ gvs []
    \\ Cases_on ‘∃err. eval_to j y = INL err’ \\ gvs []
    >- (
      Cases_on ‘err’ \\ gs []
      \\ ‘eval_to j y ≠ INL Diverge’ by gs []
      \\ drule_then (qspec_then ‘j + m’ assume_tac) eval_to_subst_mono \\ gs [])
    \\ Cases_on ‘eval_to j y’ \\ gs []
    \\ ‘eval_to j y ≠ INL Diverge’ by gs []
    \\ drule_then (qspec_then ‘j + m’ assume_tac) eval_to_subst_mono \\ gs [])
  \\ rename1 ‘_ (eval_to k x)’
  \\ ‘eval_to k x ≠ INL Type_error’
    by (strip_tac \\ gs [])
  \\ drule_all_then (qx_choose_then ‘m’ assume_tac) exp_rel_eval_to
  \\ Cases_on ‘eval_to (m + k) y’ \\ gvs []
QED

val _ = export_theory ();

