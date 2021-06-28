(*
  This stage removes all suspended ticks introduced by thunk_unthunk,
  and any other stage that has tampered with thunks.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite;
open pure_miscTheory thunkLangPropsTheory;

val _ = new_theory "thunk_untickProof";

val _ = numLib.prefer_num ();

Definition is_Lam_def[simp]:
  is_Lam (Lam s x) = T ∧
  is_Lam _ = F
End

Definition is_Delay_def[simp]:
  is_Delay (Delay x) = T ∧
  is_Delay _ = F
End

Definition is_Box_def[simp]:
  is_Box (Box x) = T ∧
  is_Box _ = F
End

Definition ok_bind_def:
  ok_bind x = (is_Lam x ∨ is_Box x ∨ is_Delay x)
End

Theorem ok_bind_MkTick[simp]:
  ¬ok_bind (MkTick x)
Proof
  rw [ok_bind_def]
QED

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
     LIST_REL (λ(f,x) (g,y). f = g ∧ ok_bind x ∧ exp_rel x y) f g ∧
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
     LIST_REL (λ(f,x) (g,y). f = g ∧ ok_bind x ∧ exp_rel x y) f g ⇒
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
     v_rel v w ⇒
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
           LIST_REL (λ(f,x) (g,y). f = g ∧ ok_bind x ∧ exp_rel x y) f g) ∧
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
       v_rel v w)
Proof
  rw [] \\ rw [Once exp_rel_cases]
QED

Theorem v_rel_simps[simp]:
  ¬v_rel (Thunk x) (Constructor s l) ∧
  ¬v_rel (Thunk x) (Closure s z) ∧
  ¬v_rel (Thunk x) (Recclosure f n) ∧
  ¬v_rel (Thunk x) (Atom y) ∧
  ¬v_rel (Thunk x) (DoTick v)
Proof
  rw [] \\ rw [Once exp_rel_cases]
QED

Theorem ok_bind_subst[simp]:
  ∀x. ok_bind x ⇒ ok_bind (subst ws x)
Proof
  Cases \\ rw [ok_bind_def] \\ gs [subst_def]
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

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;
Theorem PAIR_REL_THM[local,simp] = quotient_pairTheory.PAIR_REL_THM;

fun psimp p ths =
  CONV_TAC (PATH_CONV p (SIMP_CONV (srw_ss()) ths));

Theorem v_rel_ticks:
  v_rel v w ⇒
    ∃n u. v = FUNPOW DoTick n u ∧
          (* (∀x. u ≠ DoTick x) ∧ *)
          dest_Tick u = NONE ∧
          v_rel u w
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ T) ∧
    ∀v w. v_rel v w ⇒
      ∃n u. v = FUNPOW DoTick n u ∧
            (* (∀x. u ≠ DoTick x) ∧ *)
            dest_Tick u = NONE ∧
            v_rel u w’
  >- (
    rw [])
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
  \\ TRY (
    qexists_tac ‘0’
    \\ gvs [LIST_REL_EL_EQN]
    \\ NO_TAC)
  \\ first_assum (irule_at Any) \\ simp []
  \\ qexists_tac ‘SUC n’
  \\ simp [arithmeticTheory.FUNPOW_SUC]
QED

Theorem dest_anyThunk_INL:
  dest_anyThunk v = INL err ⇒
    err = Type_error
Proof
  Cases_on ‘v’ \\ simp [dest_anyThunk_def]
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
QED

Theorem v_rel_dest_anyThunk:
  v_rel v w ∧
  dest_Tick v = NONE ⇒
    ($= +++ ((v_rel +++ exp_rel) ###
             LIST_REL (λ(f,x) (g,y). f = g ∧ ok_bind x ∧ exp_rel x y)))
      (dest_anyThunk v)
      (dest_anyThunk w)
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’ \\ rw [] \\ gvs [v_rel_def, dest_anyThunk_def]
  >- (
    rename1 ‘LIST_REL _ f g’
    \\ ‘OPTREL (λx y. ok_bind x ∧ exp_rel x y)
               (ALOOKUP (REVERSE f) s)
               (ALOOKUP (REVERSE g) s)’
      by (irule LIST_REL_OPTREL
          \\ gs [ELIM_UNCURRY, LIST_REL_CONJ])
    \\ gs [OPTREL_def]
    \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs [Once exp_rel_cases])
  \\ rename1 ‘_ (Thunk s1) (Thunk s2)’
  \\ Cases_on ‘s1’ \\ Cases_on ‘s2’ \\ gs []
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ∧
    (∀ck. eval_to ck x ≠ INL Type_error) ⇒
      ∃j. ($= +++ v_rel)
            (eval_to (j + k) x)
            (eval_to k y)
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
    \\ ‘∀ck. eval_to ck x1 ≠ INL Type_error’
      by (qx_gen_tac ‘ck’
          \\ strip_tac
          \\ first_x_assum (qspec_then ‘ck’ assume_tac)
          \\ gs [eval_to_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to k x2 = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k) x1’ \\ gs [])
    \\ ‘∃u1. eval_to k x2 = INR u1’
      by (Cases_on ‘eval_to k x2’ \\ gs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to (j1 + k) x1’ \\ gs [])
    \\ simp []
    \\ ‘∀ck. eval_to ck y1 ≠ INL Type_error’
      by (qx_gen_tac ‘ck’
          \\ strip_tac
          \\ qpat_x_assum ‘∀ck. eval_to ck (App _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ ‘eval_to (j1 + k + ck) y1 = eval_to ck y1’
            by (irule eval_to_mono \\ gs [])
          \\ ‘eval_to (j1 + k + ck) x1 = eval_to (j1 + k) x1’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs [])
          \\ qexists_tac ‘j1 + k + ck’ \\ simp []
          \\ Cases_on ‘eval_to k x2’ \\ Cases_on ‘eval_to (j1 + k) x1’ \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ gs []
    \\ ‘∃v1. eval_to (j1 + k) x1 = INR v1’
      by (Cases_on ‘eval_to (j1 + k) x1’ \\ gs [])
    \\ gs []
    \\ Cases_on ‘eval_to k y2 = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to k x1 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ ‘∀i. eval_to (i + k) x1 = eval_to k x1’
        by (strip_tac
            \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k x1’ \\ gs []
      \\ Cases_on ‘eval_to k y1 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k) y1 = eval_to k y1’
        by (strip_tac
            \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k y1’ \\ gs [])
    \\ ‘∃u2. eval_to k y2 = INR u2’
      by (Cases_on ‘eval_to k y2’ \\ Cases_on ‘eval_to (j2 + k) y1’ \\ gvs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs [])
    \\ ‘∃v2. eval_to (j2 + k) y1 = INR v2’
      by (Cases_on ‘eval_to (j2 + k) y1’ \\ gs [])
    \\ gs []
    \\ ‘∀i. eval_to (i + j1 + k) x1 = eval_to (j1 + k) x1’
      by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ ‘∀i. eval_to (i + j2 + k) y1 = eval_to (j2 + k) y1’
      by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ gs []
    \\ ‘∃s x1 w1 x2 w2. dest_anyClosure v1 = INR (s, x1, w1) ∧
                        dest_anyClosure u1 = INR (s, x2, w2) ∧
                        exp_rel x1 x2 ∧
                        LIST_REL (λ(f,v) (g,w). f = g ∧ v_rel v w) w1 w2’
      by (qpat_x_assum ‘∀ck. eval_to ck (App _ _) ≠ _’
            (qspec_then ‘1 + j1 + j2 + k’ mp_tac)
          \\ first_x_assum (qspec_then ‘1 + j1’ assume_tac)
          \\ first_x_assum (qspec_then ‘1 + j2’ assume_tac)
          \\ gs [eval_to_def]
          \\ qpat_x_assum ‘v_rel v1 u1’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gvs [dest_anyClosure_def]
          \\ rename1 ‘ALOOKUP (REVERSE f) n’
          \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE f) n)
                             (ALOOKUP (REVERSE g) n)’
            by (irule LIST_REL_OPTREL
                \\ gs [LIST_REL_CONJ, ELIM_UNCURRY])
          \\ gs [OPTREL_def]
          \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gs []
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP])
    \\ gs []
    \\ IF_CASES_TAC \\ gs []
    >- (
      Cases_on ‘eval_to 0 x1 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to j x1 = eval_to 0 x1’
        by (strip_tac
            \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to 0 y1 = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to 0 x1’ \\ gs [])
      \\ ‘∀j. eval_to j y1 = eval_to 0 y1’
        by (strip_tac
            \\ irule eval_to_mono \\ gs [])
      \\ qexists_tac ‘0’
      \\ Cases_on ‘eval_to 0 x1’ \\ gs [])
    \\ rename1 ‘exp_rel z1 z2’
    \\ ‘exp_rel (subst (w1 ++ [s,v2]) z1) (subst (w2 ++ [s,u2]) z2) ∧
        ∀ck. eval_to ck (subst (w1 ++ [s,v2]) z1) ≠ INL Type_error’
      by (irule_at Any exp_rel_subst
          \\ gvs [LIST_REL_CONJ, ELIM_UNCURRY, EVERY2_MAP]
          \\ irule_at Any LIST_EQ
          \\ gvs [EL_MAP, LIST_REL_EL_EQN]
          \\ qx_gen_tac ‘ck’ \\ strip_tac
          \\ qpat_x_assum ‘∀ck. eval_to ck (App _ _) ≠ _’ mp_tac \\ simp []
          \\ qpat_x_assum ‘∀i. eval_to _ y1 = _’
            (qspec_then ‘1 + ck + j1’ assume_tac)
          \\ qpat_x_assum ‘∀i. eval_to _ x1 = _’
            (qspec_then ‘1 + ck + j2’ assume_tac)
          \\ qexists_tac ‘1 + k + ck + j1 + j2’
          \\ gs [eval_to_def]
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j3’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) (subst (w2 ++ [s,u2]) z2) = INL Diverge’
    >- (
      Cases_on ‘eval_to k x1 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x1 = eval_to k x1’
        by (strip_tac
            \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k y1 = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to k x1’ \\ gs [])
      \\ ‘∀j. eval_to (j + k) y1 = eval_to k y1’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k x1’ \\ gs []
      \\ qexists_tac ‘j3’ \\ simp [])
    \\ ‘eval_to (j1 + j2 + j3 + k - 1) (subst (w1 ++ [s,v2]) z1) =
        eval_to (j3 + k - 1) (subst (w1 ++ [s,v2]) z1)’
      by (irule eval_to_mono \\ gs []
          \\ strip_tac
          \\ Cases_on ‘eval_to (k - 1) (subst (w2 ++ [s,u2]) z2)’ \\ gs [])
    \\ qexists_tac ‘j1 + j2 + j3’
    \\ qpat_x_assum ‘∀i. eval_to _ y1 = _’ (qspec_then ‘j1 + j3’ assume_tac)
    \\ qpat_x_assum ‘∀i. eval_to _ x1 = _’ (qspec_then ‘j2 + j3’ assume_tac)
    \\ gs [])
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def])
  >- ((* Let NONE *)
    rename1 ‘Let NONE x1 x2’
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀ck. eval_to ck x1 ≠ INL Type_error’
      by (qx_gen_tac ‘ck’ \\ strip_tac
          \\ qpat_x_assum ‘∀ck. eval_to _ _ ≠ _’ mp_tac \\ simp []
          \\ qexists_tac ‘1 + ck’
          \\ simp [eval_to_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) y1 = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
    \\ ‘∃u1. eval_to (k - 1) y1 = INR u1’
      by (first_x_assum (qspec_then ‘j1 + k - 1’ assume_tac)
          \\ Cases_on ‘eval_to (k - 1) y1’ \\ gs []
          \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs [])
    \\ gs []
    \\ ‘∃v1. eval_to (j1 + k - 1) x1 = INR v1’
      by (Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
    \\ ‘∀i. eval_to (i + j1 + k - 1) x1 = eval_to (j1 + k - 1) x1’
      by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ gs []
    \\ ‘∀ck. eval_to ck x2 ≠ INL Type_error’
      by (qx_gen_tac ‘ck’ \\ strip_tac
          \\ ‘eval_to (j1 + k - 1) x1 ≠ INL Diverge’ by gs []
          \\ drule_then (qspec_then ‘j1 + ck + k’ assume_tac) eval_to_mono
          \\ gs []
          \\ last_x_assum (qspec_then ‘j1 + ck + k’ mp_tac)
          \\ simp [eval_to_def]
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (k - 1) x1 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (k - 1) x1’
        by (strip_tac
            \\ irule eval_to_mono \\ gs [])
      \\ qexists_tac ‘j2’ \\ gs [])
    \\ ‘∃u2. eval_to (k - 1) y2 = INR u2’
      by (first_x_assum (qspec_then ‘j2 + k - 1’ assume_tac)
          \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs []
          \\ rename1 ‘INL err’ \\ Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to (j2 + k - 1) x2’ \\ gs [])
    \\ gs []
    \\ qexists_tac ‘j1 + j2’
    \\ qpat_x_assum ‘∀i. eval_to _ x1 = _’ (qspec_then ‘j2’ assume_tac) \\ gs []
    \\ ‘eval_to (j1 + j2 + k - 1) x2 = eval_to (j2 + k - 1) x2’
      by (irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ gs [])
  >- ((* Let SOME *)
    rename1 ‘Let (SOME n) x1 x2’
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀ck. eval_to ck x1 ≠ INL Type_error’
      by (qx_gen_tac ‘ck’ \\ strip_tac
          \\ qpat_x_assum ‘∀ck. eval_to _ _ ≠ _’ mp_tac \\ simp []
          \\ qexists_tac ‘1 + ck’
          \\ simp [eval_to_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) y1 = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
    \\ ‘∃u1. eval_to (k - 1) y1 = INR u1’
      by (first_x_assum (qspec_then ‘j1 + k - 1’ assume_tac)
          \\ Cases_on ‘eval_to (k - 1) y1’ \\ gs []
          \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ gs [])
    \\ gs []
    \\ ‘∃v1. eval_to (j1 + k - 1) x1 = INR v1’
      by (Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
    \\ ‘∀i. eval_to (i + j1 + k - 1) x1 = eval_to (j1 + k - 1) x1’
      by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ gs []
    \\ ‘exp_rel (subst1 n v1 x2) (subst1 n u1 y2) ∧
        ∀ck. eval_to ck (subst1 n v1 x2) ≠ INL Type_error’
      by (irule_at Any exp_rel_subst \\ gs []
          \\ qx_gen_tac ‘ck’ \\ strip_tac
          \\ ‘eval_to (j1 + k - 1) x1 ≠ INL Diverge’ by gs []
          \\ drule_then (qspec_then ‘j1 + ck + k’ assume_tac) eval_to_mono
          \\ gs []
          \\ last_x_assum (qspec_then ‘j1 + ck + k’ mp_tac)
          \\ simp [eval_to_def]
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) (subst1 n u1 y2) = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (k - 1) x1 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k - 1) x1 = eval_to (k - 1) x1’
        by (strip_tac
            \\ irule eval_to_mono \\ gs [])
      \\ qexists_tac ‘j2’ \\ gs [])
    \\ ‘eval_to (j1 + j2 + k - 1) (subst1 n v1 x2) =
        eval_to (j2 + k - 1) (subst1 n v1 x2)’
      by (irule eval_to_mono \\ gs []
          \\ strip_tac
          \\ Cases_on ‘eval_to (k - 1) (subst1 n u1 y2)’ \\ gs [])
    \\ qpat_x_assum ‘∀i. eval_to _ x1 = _’ (qspec_then ‘j2’ assume_tac)
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
    \\ ‘∀ck. eval_to ck x1 ≠ INL Type_error’
      by (qx_gen_tac ‘ck’
          \\ strip_tac
          \\ first_x_assum (qspec_then ‘ck + 1’ mp_tac)
          \\ simp [eval_to_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) x2 = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
    \\ ‘∃u1. eval_to (k - 1) x2 = INR u1’
      by (first_x_assum (qspec_then ‘j1 + k - 1’ assume_tac)
          \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
          \\ rename1 ‘INL err’ \\ Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
    \\ gs []
    \\ IF_CASES_TAC \\ gvs []
    >- (
      ‘∀ck. eval_to ck y1 ≠ INL Type_error’
        by (qx_gen_tac ‘ck’ \\ strip_tac
            \\ qpat_x_assum ‘∀ck. eval_to ck (If _ _ _) ≠ _’ mp_tac
            \\ simp [eval_to_def]
            \\ qexists_tac ‘j1 + ck + k’ \\ simp []
            \\ ‘eval_to (j1 + ck + k - 1) x1 = eval_to (j1 + k - 1) x1’
              by (irule eval_to_mono \\ gs []
                  \\ strip_tac \\ gs [])
            \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
            \\ rpt IF_CASES_TAC \\ gvs []
            \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
            \\ irule eval_to_mono \\ gs [])
      \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
      \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’
      >- (
        Cases_on `eval_to (k - 1) x1 = INL Diverge`
        >- (
          qexists_tac ‘0’
          \\ simp [])
        \\ ‘∀i. eval_to (i + k - 1) x1 = eval_to (k - 1) x1’
          by (strip_tac \\ irule eval_to_mono \\ gs [])
        \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
        \\ qexists_tac ‘j2’ \\ gs []
        \\ IF_CASES_TAC \\ gs []
        \\ IF_CASES_TAC \\ gs []
        \\ qpat_x_assum ‘∀ck. eval_to _ (If _ _ _) ≠ _’ mp_tac \\ simp []
        \\ qexists_tac ‘j1 + k’ \\ simp [eval_to_def])
      \\ ‘eval_to (j1 + j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ ‘eval_to (j1 + j2 + k - 1) y1 = eval_to (j2 + k - 1) y1’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs []
            \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs [])
      \\ qexists_tac ‘j1 + j2’ \\ gs []
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ ‘F’ suffices_by rw []
      \\ qpat_x_assum ‘∀ck. eval_to _ (If _ _ _) ≠ _’ mp_tac \\ simp []
      \\ qexists_tac ‘j1 + k’ \\ simp [eval_to_def])
    \\ ‘∀ck. eval_to ck z1 ≠ INL Type_error’
      by (qx_gen_tac ‘ck’ \\ strip_tac
          \\ qpat_x_assum ‘∀ck. eval_to ck (If _ _ _) ≠ _’ mp_tac
          \\ simp [eval_to_def]
          \\ qexists_tac ‘j1 + ck + k’ \\ simp []
          \\ ‘eval_to (j1 + ck + k - 1) x1 = eval_to (j1 + k - 1) x1’
            by (irule eval_to_mono \\ gs []
                \\ strip_tac \\ gs [])
          \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
          \\ rpt IF_CASES_TAC \\ gvs []
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ reverse IF_CASES_TAC \\ gvs []
    >- (
      ‘F’ suffices_by rw []
      \\ qpat_x_assum ‘∀ck. eval_to _ (If _ _ _) ≠ _’ mp_tac
      \\ simp [eval_to_def]
      \\ qexists_tac ‘j1 + k’
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
      \\ IF_CASES_TAC \\ gvs []
      \\ IF_CASES_TAC \\ gvs [])
    \\ Cases_on ‘eval_to (k - 1) z2 = INL Diverge’
    >- (
      Cases_on `eval_to (k - 1) x1 = INL Diverge`
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀i. eval_to (i + k - 1) x1 = eval_to (k - 1) x1’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
      \\ qexists_tac ‘j2’ \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ qpat_x_assum ‘∀ck. eval_to _ (If _ _ _) ≠ _’ mp_tac \\ simp []
      \\ qexists_tac ‘j1 + k’ \\ simp [eval_to_def])
    \\ ‘eval_to (j1 + j2 + k - 1) x1 = eval_to (j1 + k - 1) x1’
      by (irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs [])
    \\ ‘eval_to (j1 + j2 + k - 1) z1 = eval_to (j2 + k - 1) z1’
      by (irule eval_to_mono \\ gs []
          \\ strip_tac \\ gs []
          \\ Cases_on ‘eval_to (k - 1) z2’ \\ gs [])
    \\ qexists_tac ‘j1 + j2’ \\ gs []
    \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ ‘F’ suffices_by rw []
    \\ qpat_x_assum ‘∀ck. eval_to _ (If _ _ _) ≠ _’ mp_tac \\ simp []
    \\ qexists_tac ‘j1 + k’ \\ simp [eval_to_def])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (irule_at Any)
    \\ simp [subst_funs_def]
    \\ irule_at Any exp_rel_subst
    \\ irule_at Any LIST_EQ
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, SUBSET_DIFF_EMPTY,
             GSYM FST_THM, EVERY2_MAP]
    \\ gvs [ELIM_UNCURRY, EL_MAP, LIST_REL_EL_EQN]
    \\ qx_gen_tac ‘ck’ \\ strip_tac
    \\ qpat_x_assum ‘∀ck. eval_to ck (Letrec _ _) ≠ _’ mp_tac
    \\ simp [eval_to_def]
    \\ qexists_tac ‘ck + 1’ \\ gs [subst_funs_def, ELIM_UNCURRY])
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def])
  >- ((* Box *)
    rw [Once exp_rel_cases] \\ gs [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘∀ck. eval_to ck x ≠ INL Type_error’
      by (qx_gen_tac ‘ck’
          \\ strip_tac
          \\ first_x_assum (qspec_then ‘ck’ assume_tac)
          \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to k y’ \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
  >- ((* Force *)
    rw [Once exp_rel_cases] \\ rename1 ‘exp_rel x y’
    \\ psimp "rar" [Once eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [Once eval_to_def])
    \\ ‘∀ck. eval_to ck x ≠ INL Type_error’
      by (qx_gen_tac ‘ck’ \\ strip_tac
          \\ ‘eval_to ck x ≠ INL Diverge’ by gs []
          \\ drule_then (qspec_then ‘1 + ck’ assume_tac) eval_to_mono
          \\ first_x_assum (qspec_then ‘1 + ck’ mp_tac) \\ gs []
          \\ simp [Once eval_to_def])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to k y’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ simp [Once eval_to_def]
      \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs []
    \\ rename1 ‘v_rel v1 u1’
    \\ drule_then assume_tac v_rel_dest_Tick \\ gs []
    \\ qpat_x_assum ‘∀x y. exp_rel (Force _) _ ∧ _ ⇒ _’ kall_tac
    \\ drule_then strip_assume_tac v_rel_ticks \\ gvs []
    \\ qpat_x_assum ‘exp_rel x y’ kall_tac
    \\ qpat_x_assum ‘eval_to k y = _’ kall_tac
    \\ rpt (pop_assum mp_tac)
    \\ map_every qid_spec_tac [‘u1’,‘u’,‘x’,‘n’]
    \\ Induct \\ simp []
    >- (
      rw []
      \\ drule_all_then assume_tac v_rel_dest_anyThunk
      \\ Cases_on ‘dest_anyThunk u1’ \\ gs []
      >- (
        ‘F’ suffices_by rw []
        \\ qpat_x_assum ‘∀ck. eval_to ck (Force _) ≠ _’ mp_tac \\ simp []
        \\ simp [Once eval_to_def]
        \\ qexists_tac ‘j1 + k’ \\ simp []
        \\ Cases_on ‘dest_anyThunk u’ \\ gvs []
        \\ drule_then assume_tac dest_anyThunk_INL \\ gs [])
      \\ Cases_on ‘dest_anyThunk u’ \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ rename1 ‘_ yy (wx,binds)’
      \\ PairCases_on ‘yy’ \\ gvs []
      \\ Cases_on ‘wx’ \\ gs []
      >- (
        qexists_tac ‘j1’
        \\ simp [Once eval_to_def]
        \\ Cases_on ‘yy0’ \\ gs [])
    \\ Cases_on ‘yy0’ \\ gs []
    \\ rename1 ‘dest_anyThunk u1 = INR (INR y2, x2)’
    \\ rename1 ‘dest_anyThunk u = INR (INR y1, x1)’
    \\ ‘exp_rel (subst_funs x1 y1) (subst_funs x2 y2) ∧
        ∀ck. eval_to ck (subst_funs x1 y1) ≠ INL Type_error’
      by (simp [subst_funs_def]
          \\ irule_at Any exp_rel_subst
          \\ simp [EVERY2_MAP, LAMBDA_PROD, GSYM FST_THM, MAP_MAP_o,
                   combinTheory.o_DEF]
          \\ irule_at Any LIST_EQ
          \\ irule_at Any LIST_REL_mono
          \\ first_assum (irule_at Any)
          \\ simp [ELIM_UNCURRY, EL_MAP, SF CONJ_ss]
          \\ drule_then assume_tac LIST_REL_LENGTH \\ gs []
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY]
          \\ qx_gen_tac ‘ck’ \\ strip_tac
          \\ qpat_x_assum ‘∀ck. eval_to ck (Force _) ≠ _’ mp_tac \\ simp []
          \\ ‘eval_to (1 + ck + j1 + k) x = eval_to (j1 + k) x’
            by (irule eval_to_mono \\ gs [])
          \\ qexists_tac ‘1 + k + ck + j1’
          \\ gs [Once eval_to_def]
          \\ gs [subst_funs_def, ELIM_UNCURRY]
          \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
          \\ irule eval_to_mono \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) (subst_funs x2 y2) = INL Diverge’ \\ gs []
    >- (
      simp [Once eval_to_def]
      \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ ‘∀j. eval_to (j + k) x = eval_to (j1 + k) x’
        by (qx_gen_tac ‘j’
            \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
            \\ gs [])
      \\ gs [SF SFY_ss])
    \\ ‘eval_to (j2 + k - 1) (subst_funs x1 y1) ≠ INL Diverge’
      by (strip_tac \\ gvs []
          \\ Cases_on `eval_to (k - 1) (subst_funs x2 y2)` \\ gvs [v_rel_def])
    \\ drule_then (qspec_then ‘j1 + j2 + k - 1’ assume_tac) eval_to_mono
    \\ qexists_tac ‘j1 + j2’ \\ gs []
    \\ simp [Once eval_to_def]
    \\ ‘eval_to (j1 + j2 + k) x = eval_to (j1 + k) x’
      by (irule eval_to_mono \\ gs [])
    \\ gs [])
  \\ rw []
  \\ drule_all_then assume_tac v_rel_dest_anyThunk
  \\ gs [arithmeticTheory.FUNPOW_SUC]
  \\ ‘eval_to (j1 + k) (Value (FUNPOW DoTick n u)) = INR (FUNPOW DoTick n u)’
    by rw [Once eval_to_def]
  \\ first_x_assum (drule_at_then (Pos (el 4)) (drule_at (Pos (el 3))))
  \\ simp []
  \\ impl_tac
  >- (
    psimp "r" [Once eval_to_def] \\ simp []
    \\ qx_gen_tac ‘ck’ \\ strip_tac
    \\ qpat_x_assum ‘∀ck. eval_to ck (Force _) ≠ _’ mp_tac \\ simp []
    \\ ‘eval_to (1 + ck + j1 + k) x = eval_to (j1 + k) x’
      by (irule eval_to_mono \\ gs [])
    \\ qexists_tac ‘1 + k + ck + j1’
    \\ simp [Once eval_to_def] \\ gs []
    \\ qpat_assum ‘_ = INL Type_error’ (SUBST1_TAC o SYM)
    \\ irule eval_to_mono \\ gs [])
  \\ disch_then (qx_choose_then ‘j2’ assume_tac)
  \\ Cases_on ‘dest_anyThunk u1’ \\ gs []
  >- (
    drule_then assume_tac dest_anyThunk_INL \\ gvs []
    \\ qmatch_asmsub_abbrev_tac ‘eval_to _ bod’
    \\ ‘eval_to (j2 + k) bod ≠ INL Diverge’
      by (strip_tac \\ gs [])
    \\ drule_then (qspec_then ‘j1 + j2 + k’ assume_tac) eval_to_mono
    \\ ‘eval_to (j1 + j2 + k + 1) x = eval_to (j1 + k) x’
      by (irule eval_to_mono \\ gs [])
    \\ qexists_tac ‘j1 + j2 + 1’
    \\ simp [Once eval_to_def] \\ gs [])
  \\ Cases_on ‘dest_anyThunk u’ \\ gs []
  \\ pairarg_tac \\ gvs []
  \\ rename1 ‘_ yy (wx,binds)’
  \\ PairCases_on ‘yy’ \\ gvs []
  \\ Cases_on ‘wx’ \\ gs []
  >- (
    qmatch_asmsub_abbrev_tac ‘eval_to _ bod’
    \\ ‘eval_to (j2 + k) bod ≠ INL Diverge’
      by (strip_tac \\ gs [])
    \\ drule_then (qspec_then ‘j1 + j2 + k’ assume_tac) eval_to_mono
    \\ ‘eval_to (j1 + j2 + k + 1) x = eval_to (j1 + k) x’
      by (irule eval_to_mono \\ gs [])
    \\ qexists_tac ‘j1 + j2 + 1’
    \\ simp [Once eval_to_def] \\ gs [])
  \\ Cases_on ‘yy0’ \\ gs []
  \\ rename1 ‘dest_anyThunk u1 = INR (INR y2, x2)’
  \\ rename1 ‘dest_anyThunk u = INR (INR y1, x1)’
  \\ simp [Once eval_to_def]
  \\ Cases_on ‘eval_to (k - 1) (subst_funs x2 y2) = INL Diverge’ \\ gs []
  >- (
    Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ ‘∀j. eval_to (j + k) x = eval_to k x’
      by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ gs []
    \\ qexists_tac ‘j2 + 1’ \\ simp [])
  \\ qmatch_asmsub_abbrev_tac ‘(_ +++ _) (eval_to _ bod)’
  \\ ‘eval_to (j2 + k) bod ≠ INL Diverge’
    by (strip_tac \\ gs []
        \\ Cases_on ‘eval_to (k - 1) (subst_funs x2 y2)’ \\ gs [])
  \\ drule_then (qspec_then ‘j1 + j2 + k’ assume_tac) eval_to_mono
  \\ gs []
  \\ ‘eval_to (j1 + j2 + k + 1) x = eval_to (j1 + k) x’
    by (irule eval_to_mono \\ gs [])
  \\ qexists_tac ‘j1 + j2 + 1’ \\ gs [])
  >- ((* MkTick *)
    rw [Once exp_rel_cases] \\ gs [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘∀ck. eval_to ck x ≠ INL Type_error’
      by (qx_gen_tac ‘ck’
          \\ strip_tac
          \\ first_x_assum (qspec_then ‘ck’ assume_tac)
          \\ gs [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k) x’ \\ gs [])
    \\ qexists_tac ‘j1’
    \\ Cases_on ‘eval_to (j1 + k) x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum (qspec_then ‘j1 + k’ assume_tac) \\ gs [])
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    >- ((* Cons *)
      qabbrev_tac ‘f = λj. eval_to (j + k)’
      \\ simp [SF ETA_ss]
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ ‘∃j. ($= +++ (LIST_REL v_rel)) (result_map (f j) xs) (result_map g ys)’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’
          \\ Cases_on ‘result_map (f j) xs’
          \\ Cases_on ‘result_map g ys’ \\ gs [])
      \\ gvs [LIST_REL_EL_EQN, MEM_EL, MEM_MAP, PULL_EXISTS]
      \\ ‘∀ck. result_map (eval_to ck) xs ≠ INL Type_error’
        by (rpt strip_tac
            \\ qpat_x_assum ‘∀ck. eval_to _ (Prim _ _) ≠ _’ mp_tac \\ simp []
            \\ qexists_tac ‘ck’
            \\ simp [eval_to_def, SF ETA_ss])
      \\ ‘∀n. n < LENGTH xs ⇒ ∀ck. eval_to ck (EL n xs) ≠ INL Type_error’
        by (rpt strip_tac
            \\ gs [result_map_def, MEM_MAP, CaseEq "bool"]
            \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
            \\ gs [MEM_EL, PULL_EXISTS])
      \\ gs []
      \\ Cases_on ‘result_map g ys = INL Diverge’ \\ gs []
      >- (
        unabbrev_all_tac \\ gs []
        \\ gs [result_map_def, CaseEq "bool", MEM_MAP]
        \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ gvs [MEM_EL, PULL_EXISTS]
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_then drule)
        \\ disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ rw [] \\ gs []
        \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs [])
      \\ ‘∀n. n < LENGTH xs ⇒ eval_to k (EL n ys) ≠ INL Diverge’
        by (rpt strip_tac
            \\ gvs [result_map_def, CaseEq "bool", MEM_MAP, Abbr ‘g’, MEM_EL]
            \\ rename1 ‘eval_to k (EL m ys) = INL Type_error’
            \\ ntac 2 (pop_assum kall_tac)
            \\ first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum
              (drule_then (drule_then (qx_choose_then ‘j’ assume_tac)))
            \\ gs [Abbr ‘f’]
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ Cases_on ‘eval_to (j + k) (EL m xs)’ \\ gs [])
      \\ ‘∃j. ∀n. n < LENGTH xs ⇒
                  ($= +++ v_rel) (eval_to (j + k) (EL n xs))
                                 (eval_to k (EL n ys))’
        by (unabbrev_all_tac
            \\ rpt (pop_assum mp_tac)
            \\ qid_spec_tac ‘ys’
            \\ Induct_on ‘xs’ \\ simp []
            \\ qx_gen_tac ‘x’
            \\ Cases \\ simp []
            \\ rename1 ‘eval_to k (EL _ (y::ys))’
            \\ rw []
            \\ last_x_assum (qspec_then ‘ys’ mp_tac)
            \\ simp [AND_IMP_INTRO, GSYM CONJ_ASSOC]
            \\ impl_tac
            >- (
              rw []
              \\ TRY (
                rpt (qpat_x_assum ‘∀n. n < SUC _ ⇒ _’
                          (qspec_then ‘SUC n’ assume_tac)) \\ gs []
                \\ gs [eval_to_def, result_map_def, MEM_MAP, CaseEq "bool"]
                \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
                \\ rw [] \\ gs []
                \\ NO_TAC)
              \\ rpt strip_tac
              \\ gs [eval_to_def, result_map_def, MEM_MAP, CaseEq "bool"]
              \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
              \\ rw [] \\ gvs [MEM_EL, PULL_EXISTS]
              \\ first_x_assum (drule_then assume_tac)
              \\ first_x_assum (qspec_then ‘SUC n’ assume_tac) \\ gs [])
            \\ disch_then (qx_choose_then ‘j’ assume_tac)
            \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + k) x) (eval_to k y)’
              by (rpt (qpat_x_assum ‘∀n. n < SUC _ ⇒ _’
                    (qspec_then ‘0’ assume_tac)) \\ gs [])
            \\ qexists_tac ‘j + j1’
            \\ Cases \\ gs []
            >- (
              rpt (qpat_x_assum ‘∀n. n < SUC _ ⇒ _’
                    (qspec_then ‘0’ assume_tac)) \\ gs []
              \\ ‘eval_to (j1 + k) x ≠ INL Diverge’
                by (strip_tac \\ Cases_on ‘eval_to k y’ \\ gs [])
              \\ drule_then (qspec_then ‘j + j1 + k’ assume_tac)
                   eval_to_mono
              \\ gs [])
            \\ qmatch_goalsub_rename_tac ‘n < LENGTH ys’
            \\ strip_tac
            \\ rpt (qpat_x_assum ‘∀n. n < SUC _ ⇒ _’
                     (qspec_then ‘SUC n’ assume_tac)) \\ gs []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac)
            \\ ‘eval_to (j + k) (EL n xs) ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
            \\ drule_then (qspec_then ‘j + j1 + k’ assume_tac)
                 eval_to_mono
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ unabbrev_all_tac
      \\ qpat_x_assum ‘∀ck. result_map _ _ ≠ _’ (qspec_then ‘j + k’ assume_tac)
      \\ gs [result_map_def, CaseEq "bool", MEM_MAP, MAP_MAP_o,
             combinTheory.o_DEF]
      \\ fs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”]
      \\ gvs [MEM_EL, PULL_EXISTS]
      \\ IF_CASES_TAC \\ gs []
      \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ ‘∀n. n < LENGTH ys ⇒ eval_to (j + k) (EL n xs) ≠ INL Diverge’
        by (qx_gen_tac ‘m’
            \\ rpt strip_tac
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ Cases_on ‘eval_to k (EL m ys)’ \\ gs [])
      \\ csimp []
      \\ ‘∀n. n < LENGTH ys ⇒ eval_to k (EL n ys) ≠ INL Type_error’
        by (qx_gen_tac ‘m’
            \\ rpt strip_tac
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ Cases_on ‘eval_to (j + k) (EL m xs)’ \\ gs [])
      \\ csimp [EVERY2_MAP, LIST_REL_EL_EQN]
      \\ qx_gen_tac ‘m’ \\ strip_tac
      \\ first_x_assum (drule_then assume_tac) \\ gs []
      \\ first_x_assum (drule_then assume_tac) \\ gs []
      \\ first_x_assum (drule_then assume_tac) \\ gs []
      \\ Cases_on ‘eval_to k (EL m ys)’
      \\ Cases_on ‘eval_to (j + k) (EL m xs)’ \\ gs []
      \\ rename1 ‘_ = INL err’ \\ Cases_on ‘err’ \\ gs [])
    >- ((* IsEq *)
      IF_CASES_TAC \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum drule
      \\ impl_keep_tac
      >- (
        qx_gen_tac ‘ck’
        \\ strip_tac
        \\ first_x_assum (qspec_then ‘ck + 1’ mp_tac)
        \\ simp [eval_to_def])
      \\ disch_then (qx_choose_then ‘j’ assume_tac)
      \\ first_x_assum (qspec_then ‘j + k - 1’ assume_tac)
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v1 u1’
      \\ Cases_on ‘v1’ \\ Cases_on ‘u1’ \\ gvs []
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ last_x_assum (qspec_then ‘j + k’ mp_tac)
      \\ simp [Once eval_to_def])
    >- ((* Proj *)
      IF_CASES_TAC \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ simp [])
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum drule
      \\ impl_keep_tac
      >- (
        qx_gen_tac ‘ck’
        \\ strip_tac
        \\ first_x_assum (qspec_then ‘ck + 1’ mp_tac)
        \\ simp [eval_to_def])
      \\ disch_then (qx_choose_then ‘j’ assume_tac)
      \\ first_x_assum (qspec_then ‘j + k - 1’ assume_tac)
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v1 u1’
      \\ Cases_on ‘v1’ \\ Cases_on ‘u1’ \\ gvs []
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gs []
      \\ last_x_assum (qspec_then ‘j + k’ mp_tac)
      \\ simp [Once eval_to_def])
    >- ((* AtomOp *)
      Cases_on ‘k = 0’ \\ gs []
      >- (
        qexists_tac ‘0’ \\ simp []
        \\ gvs [LIST_REL_EL_EQN, result_map_def, MEM_MAP, GSYM NOT_NULL_MEM,
                NULL_EQ]
        \\ Cases_on ‘xs’ \\ Cases_on ‘ys’ \\ gvs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [])
      \\ qabbrev_tac ‘f = λj x. case eval_to (j + k - 1) x of
                                  INR (Atom l) => INR l
                                | INL err => INL err
                                | _ => INL Type_error’
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ simp [SF ETA_ss]
      \\ ‘∀j. result_map (f j) xs ≠ INL Type_error’
        by (rpt strip_tac
            \\ first_x_assum (qspec_then ‘k + j’ mp_tac)
            \\ simp [eval_to_def]
            \\ simp [SF ETA_ss])
      \\ ‘∀n. n < LENGTH xs ⇒ ∀ck. eval_to ck (EL n xs) ≠ INL Type_error’
        by (rpt strip_tac
            \\ last_x_assum (qspec_then ‘SUC ck’ mp_tac)
            \\ csimp [eval_to_def, result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS]
            \\ rw [] \\ gs [])
      \\ gs []
      \\ gvs [LIST_REL_EL_EQN]
      \\ ‘∃j. result_map (f j) xs = result_map g ys’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’ \\ simp []
          \\ Cases_on ‘result_map g ys’ \\ gs []
          \\ rpt CASE_TAC \\ gs [])
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
        \\ last_x_assum (drule_then drule)
        \\ disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ qexists_tac ‘n’
        \\ CASE_TAC \\ gs [])
      \\ ‘∀n. n < LENGTH xs ⇒ eval_to (k - 1) (EL n ys) ≠ INL Diverge’
        by (rpt strip_tac
            \\ gvs [Abbr ‘g’, result_map_def, CaseEq "bool", MEM_MAP, MEM_EL,
                    PULL_EXISTS]
            \\ first_x_assum (qspec_then ‘n’ assume_tac)
            \\ Cases_on `eval_to (k - 1) (EL n ys)` \\ gvs []
            \\ rename1 ‘m < LENGTH ys’
            \\ Cases_on ‘eval_to (k - 1) (EL m ys)’ \\ gvs []
            >- (
              first_x_assum (drule_all_then assume_tac)
              \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
              \\ gs [Abbr ‘f’]
              \\ first_x_assum (drule_then assume_tac)
              \\ Cases_on ‘eval_to (j + k - 1) (EL m xs)’ \\ gs [])
            \\ fs [DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”]
            \\ first_x_assum (drule_all_then assume_tac)
            \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
            \\ gs [Abbr ‘f’]
            \\ first_x_assum (drule_then assume_tac)
            \\ Cases_on ‘eval_to (j + k - 1) (EL m xs)’ \\ gs []
            \\ first_x_assum (drule_then (qspec_then ‘j’ assume_tac)) \\ gs []
            \\ rename1 ‘v_rel v w’
            \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [])
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                  ($= +++ v_rel) (eval_to (j + k - 1) (EL n xs))
                                 (eval_to (k - 1) (EL n ys))’
        by (unabbrev_all_tac
            \\ qpat_x_assum ‘∀ck. eval_to _ _ ≠ INL _’ kall_tac
            \\ ntac 4 (pop_assum mp_tac)
            \\ ntac 3 (last_x_assum mp_tac)
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
              \\ TRY (
                rpt (qpat_x_assum ‘∀n. n < SUC _ ⇒ _’
                          (qspec_then ‘SUC n’ assume_tac)) \\ gs []
                \\ gs [eval_to_def, result_map_def, MEM_MAP, CaseEq "bool"]
                \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
                \\ rw [] \\ gs []
                \\ NO_TAC)
              \\ strip_tac
              \\ gs [result_map_def, CaseEq "bool", MEM_MAP, MEM_EL,
                     PULL_EXISTS]
              \\ gs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
              \\ first_x_assum (drule_then assume_tac)
              \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
              \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs []
              \\ gs [CaseEqs ["sum", "v"]])
            \\ disch_then (qx_choose_then ‘j’ assume_tac)
            \\ ‘∃j1. ($= +++ v_rel) (eval_to (j1 + k - 1) x)
                                    (eval_to (k - 1) y)’
              by (rpt (qpat_x_assum ‘∀n. n < SUC _ ⇒ _’
                    (qspec_then ‘0’ assume_tac)) \\ gs [])
            \\ qexists_tac ‘j + j1’
            \\ Cases \\ gs []
            >- (
              rpt (qpat_x_assum ‘∀n. n < SUC _ ⇒ _’
                    (qspec_then ‘0’ assume_tac)) \\ gs []
              \\ ‘eval_to (j1 + k - 1) x ≠ INL Diverge’
                by (strip_tac \\ Cases_on ‘eval_to (k - 1) y’ \\ gs [])
              \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac)
                   eval_to_mono
              \\ gs [])
            \\ qmatch_goalsub_rename_tac ‘n < LENGTH ys’
            \\ strip_tac
            \\ rpt (qpat_x_assum ‘∀n. n < SUC _ ⇒ _’
                     (qspec_then ‘SUC n’ assume_tac)) \\ gs []
            \\ first_x_assum (drule_then assume_tac)
            \\ ‘eval_to (j + k - 1) (EL n xs) ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs [])
            \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac)
                 eval_to_mono
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ unabbrev_all_tac
      \\ gs [result_map_def, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF]
      \\ IF_CASES_TAC \\ gs []
      >- (
        gvs [MEM_EL, PULL_EXISTS]
        \\ rw [] \\ gs [CaseEq "bool"]
        \\ fs [DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”]
        \\ rpt (first_x_assum (drule_then strip_assume_tac))
        \\ first_x_assum (qspec_then ‘j’ assume_tac)
        \\ Cases_on ‘eval_to (j + k - 1) (EL n xs)’
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs [])
      \\ gs [DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”]
      \\ IF_CASES_TAC \\ gs []
      >- (
        gvs [MEM_EL, PULL_EXISTS]
        \\ gvs [CaseEq "bool"] \\ fs [DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”]
        THENL [
          ntac 2 (pop_assum kall_tac),
          ALL_TAC ]
        \\ rpt (first_x_assum (drule_then strip_assume_tac))
        \\ rename1 ‘EL n ys’
        \\ rename1 ‘j + k - 1’
        \\ first_x_assum (qspec_then ‘j’ assume_tac)
        \\ Cases_on ‘eval_to (j + k - 1) (EL n xs)’
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs []
        \\ rename1 ‘v_rel v w’ \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [])
      \\ IF_CASES_TAC \\ gs []
      >- (
        gvs [MEM_EL, PULL_EXISTS]
        \\ gvs [CaseEq "bool"] \\ fs [DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”]
        THENL [
          ntac 2 (pop_assum kall_tac),
          ALL_TAC ]
        \\ rpt (first_x_assum (drule_then strip_assume_tac))
        \\ rename1 ‘EL n ys’
        \\ rename1 ‘j + k - 1’
        \\ first_x_assum (qspec_then ‘j’ assume_tac)
        \\ Cases_on ‘eval_to (j + k - 1) (EL n xs)’
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’ \\ gs []
        \\ rename1 ‘v_rel v w’ \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [])
      \\ gvs [CaseEq "bool"]
      \\ fs [DECIDE “A ⇒ ¬MEM a b ⇔ MEM a b ⇒ ¬A”]
      \\ gs [MEM_EL, PULL_EXISTS]
      \\ irule_at Any LIST_EQ
      \\ rw [EL_MAP]
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ first_x_assum (qspec_then ‘j’ assume_tac)
      \\ rpt CASE_TAC \\ gs []))
QED

Theorem eval_not_error[local]:
  eval x ≠ INL Type_error ⇒
    ∀k. eval_to k x ≠ INL Type_error
Proof
  simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ qx_gen_tac ‘j’ \\ rw []
  \\ drule_then (qspec_then ‘k’ assume_tac) eval_to_mono
  \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
  \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_mono
  \\ Cases_on ‘j < k’ \\ gs []
QED

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

val _ = export_theory ();

