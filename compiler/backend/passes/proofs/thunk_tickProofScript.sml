(*
  Introducing and removing Ticks in thunkLang programs.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory;

val _ = new_theory "thunk_tickProof";

val _ = set_grammar_ancestry [
  "finite_map", "pred_set", "rich_list", "thunkLang", "quotient_sum",
  "quotient_pair", "thunkLangProps", "thunk_semantics" ];

Theorem SUM_REL_def[local,simp] = quotient_sumTheory.SUM_REL_def;

Theorem PAIR_REL_THM[local,simp] = quotient_pairTheory.PAIR_REL_THM;

val _ = numLib.prefer_num ();

Definition ok_bind_def[simp]:
  ok_bind (Delay x) = T ∧
  ok_bind (Lam s x) = T ∧
  ok_bind _ = F
End

Inductive exp_rel:
[~Var:]
  (∀n. exp_rel (Var n) (Var n)) ∧
[~Value:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Value v) (Value w)) ∧
[~Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys)) ∧
[~Monad:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Monad mop xs) (Monad mop ys)) ∧
[~App:]
  (∀f g x y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f x) (App g y)) ∧
[~Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y)) ∧
[~Letrec:]
  (∀f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y)) ∧
[~Let:]
  (∀opt x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let opt x1 y1) (Let opt x2 y2)) ∧
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ∧
     exp_rel z1 z2 ⇒
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
[~Tick:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel x (Tick y)) ∧
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Monadic:]
  (∀mop xs ys.
     LIST_REL exp_rel xs ys ⇒
       v_rel (Monadic mop xs) (Monadic mop ys)) ∧
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ⇒
       v_rel (Closure s x) (Closure s y)) ∧
[v_rel_Recclosure:]
  (∀f g n.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ⇒
       v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Thunk_INL:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INL v)) (Thunk (INL w))) ∧
[v_rel_Thunk_INR:]
  (∀x y.
     exp_rel x y ⇒
       v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x)) ∧
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) (DoTick w))
End

Theorem exp_rel_def =
  [“exp_rel (Var v) x”,
   “exp_rel (Value v) x”,
   “exp_rel (Prim op xs) x”,
   “exp_rel (Monad mop xs) x”,
   “exp_rel (App f x) y”,
   “exp_rel (Lam s x) y”,
   “exp_rel (Letrec f x) y”,
   “exp_rel (Let s x y) z”,
   “exp_rel (If x y z) w”,
   “exp_rel (Delay x) y”,
   “exp_rel (Box x) y”,
   “exp_rel (MkTick x) y”,
   “exp_rel (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once exp_rel_cases])
  |> LIST_CONJ;

Theorem v_rel_def =
  [“v_rel (Constructor s vs) v”,
   “v_rel (Monadic mop xs) v”,
   “v_rel (Closure s x) v”,
   “v_rel (Recclosure f n) v”,
   “v_rel (Atom x) v”,
   “v_rel (Thunk x) v”,
   “v_rel (DoTick x) v”]
  |> map (SIMP_CONV (srw_ss()) [Once exp_rel_cases])
  |> LIST_CONJ;

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ freevars x = freevars y) ∧
    ∀x y. v_rel x y ⇒ T’
  >- (rw [] \\ res_tac \\ fs [])
  \\ ho_match_mp_tac exp_rel_ind
  \\ fs [freevars_def] \\ rw []
  >~ [‘Let opt’]
  >- (Cases_on ‘opt’ \\ fs [freevars_def])
  >-
   (pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’ \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ first_x_assum drule
    \\ fs [EXTENSION] \\ metis_tac [])
  >-
   (pop_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’ \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ first_x_assum drule
    \\ fs [EXTENSION] \\ metis_tac [])
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
  \\ qid_spec_tac ‘f’
  \\ qid_spec_tac ‘g’ \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD]
  \\ rw []
  \\ rename [‘MAP SND ts = _ :: _’]
  \\ Cases_on ‘ts’ \\ gvs [UNCURRY]
QED

Theorem exp_rel_FUNPOW:
  ∀x y.
    exp_rel x y ∧
    (∀w. x ≠ Tick w) ⇒
      ∃n z.
        y = FUNPOW Tick n z ∧
        exp_rel x z ∧
        (∀w. z ≠ Tick w)
Proof
  ‘(∀x y.
      exp_rel x y ⇒
      (∀w. x ≠ Tick w) ⇒
        ∃n z.
          y = FUNPOW Tick n z ∧
          exp_rel x z ∧
          (∀w. z ≠ Tick w)) ∧
    (∀v w. v_rel v w ⇒ T)’
    suffices_by rw []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
  >~ [‘Var n’] >- (
    qexists_tac ‘0’
    \\ simp [exp_rel_Var])
  >~ [‘Value v’] >- (
    qexists_tac ‘0’
    \\ simp [exp_rel_Value])
  >~ [‘Prim op xs’] >- (
    qexists_tac ‘0’
    \\ irule_at Any exp_rel_Prim
    \\ gvs [LIST_REL_EL_EQN])
  >~ [`Monad mop xs`]
  >- (qexists_tac `0` >> irule_at Any exp_rel_Monad >> gvs[LIST_REL_EL_EQN])
  >~ [‘App f x’] >- (
    qexists_tac ‘0’
    \\ irule_at Any exp_rel_App
    \\ gs [])
  >~ [‘Lam s x’] >- (
    qexists_tac ‘0’
    \\ irule_at Any exp_rel_Lam
    \\ gs [])
  >~ [‘Letrec f x’] >- (
    qexists_tac ‘0’
    \\ irule_at Any exp_rel_Letrec
    \\ gvs [LIST_REL_EL_EQN]
    \\ strip_tac \\ gvs [])
  >~ [‘Let opt x y’] >- (
    qexists_tac ‘0’
    \\ irule_at Any exp_rel_Let
    \\ gs [])
  >~ [‘If x y z’] >- (
    qexists_tac ‘0’
    \\ irule_at Any exp_rel_If
    \\ gs [])
  >~ [‘Delay x’] >- (
    qexists_tac ‘0’
    \\ irule_at Any exp_rel_Delay
    \\ gs [])
  >~ [‘Box x’] >- (
    qexists_tac ‘0’
    \\ irule_at Any exp_rel_Box
    \\ gs [])
  >~ [‘Force x’] >- (
    qexists_tac ‘0’
    \\ irule_at Any exp_rel_Force
    \\ gs [])
  >~ [‘Tick x’] >- (
    gs []
    \\ first_x_assum (irule_at Any) \\ gs []
    \\ qexists_tac ‘SUC n’
    \\ simp [arithmeticTheory.FUNPOW_SUC])
QED

Theorem subst_empty[local,simp]:
  subst_funs [] x = x
Proof
  rw [subst_funs_def]
QED

Theorem eval_to_Tick[local]:
  ∀n k x. eval_to (k + n) (FUNPOW Tick n x) = eval_to k x
Proof
  Induct \\ rw [eval_to_def]
  \\ gs [arithmeticTheory.FUNPOW_SUC, eval_to_def, arithmeticTheory.ADD1]
QED

Theorem exp_rel_subst:
  ∀vs x ws y.
    MAP FST vs = MAP FST ws ∧
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    exp_rel x y ⇒
      exp_rel (subst vs x) (subst ws y)
Proof
  ‘(∀x y.
     exp_rel x y ⇒
     ∀vs ws.
       MAP FST vs = MAP FST ws ∧
       LIST_REL v_rel (MAP SND vs) (MAP SND ws) ⇒
         exp_rel (subst vs x) (subst ws y)) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
  >~ [‘Var v’] >- (
    rw [subst_def]
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_OPTREL
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
    \\ gs [OPTREL_def, exp_rel_Var, exp_rel_Value])
  >~ [‘Value v’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Value])
  >~ [‘Prim op xs’] >- (
    rw [subst_def]
    \\ irule exp_rel_Prim
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [`Monad mop xs`]
  >- (rw[subst_def] >> irule exp_rel_Monad >> gvs[LIST_REL_EL_EQN, EVERY2_MAP])
  >~ [‘App f x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_App])
  >~ [‘Lam s x’] >- (
    rw [subst_def]
    \\ irule exp_rel_Lam
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘Letrec f x’] >- (
    rw [subst_def]
    \\ irule exp_rel_Letrec
    \\ gvs [EVERY_MAP, EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
            GSYM FST_THM]
    \\ first_x_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER]
    \\ qabbrev_tac ‘P = λn. ¬MEM n (MAP FST g)’ \\ gs []
    \\ irule_at Any LIST_REL_FILTER
    \\ ‘∀f x. ok_bind x ⇒ ok_bind (subst f x)’
      by (ho_match_mp_tac subst_ind
          \\ rw [subst_def])
    \\ gvs [EVERY_EL, ELIM_UNCURRY]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ first_assum irule
    \\ gvs [MAP_FST_FILTER, LAMBDA_PROD]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘Let s x y’] >- (
    Cases_on ‘s’ \\ rw [subst_def]
    \\ irule exp_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER]
    \\ rename1 ‘_ ≠ s’
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ gs [EVERY2_MAP]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘If x y z’] >- (
    rw [subst_def]
    \\ gs [exp_rel_If])
  >~ [‘Delay x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Delay])
  >~ [‘Box x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Box])
  >~ [‘Force x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Force])
  >~ [‘Tick y’] >- (
    rw [subst_def]
    \\ irule exp_rel_Tick
    \\ gs [FILTER_T, ELIM_UNCURRY])
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ⇒
      ∃j. ($= +++ v_rel) (eval_to k x) (eval_to (k + j) y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  >~ [‘Var m’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def])
  >~ [‘Value v’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def])
  >~ [‘Lam s x’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def, v_rel_def])
  >~ [‘App f x’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac)) \\ gs []
    \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k) y’ \\ gs [])
    \\ Cases_on ‘eval_to k x’ \\ gs []
    >~ [‘INL err’] >- (
      Cases_on ‘err’ \\ gs []
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k) y’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
    \\ rename1 ‘v_rel v1 w1’
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac)) \\ gs []
    \\ Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to k x’ \\ gs []
        \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
        \\ ‘eval_to (j + k) y = eval_to k y’
          by (irule eval_to_mono \\ gs [])
        \\ gs [])
      \\ ‘∀j. eval_to (j + k) g = eval_to k g’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k g’ \\ gs [])
    \\ Cases_on ‘eval_to k f’ \\ gs []
    >~ [‘INL err’] >- (
      Cases_on ‘err’ \\ gs []
      \\ qexists_tac ‘j1 + j’
      \\ ‘eval_to (j1 + j + k) y = eval_to (j + k) y’
        by (irule eval_to_mono \\ gs [])
      \\ ‘eval_to (j1 + j + k) g = eval_to (j1 + k) g’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j1 + k) g’ \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k) g’ \\ gs []
    \\ rename1 ‘v_rel v2 w2’
    \\ ‘∀i. eval_to (i + j + k) y = eval_to (j + k) y’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ ‘∀i. eval_to (i + j1 + k) g = eval_to (j1 + k) g’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘dest_anyClosure v2’ \\ gs []
    >- (
      Q.REFINE_EXISTS_TAC ‘SUC i’ \\ gs []
      \\ first_x_assum (qspec_then ‘SUC j’ assume_tac)
      \\ first_x_assum (qspec_then ‘SUC j1’ assume_tac)
      \\ gs [arithmeticTheory.ADD1]
      \\ qexists_tac ‘j + j1’ \\ gs []
      \\ Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
      \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
      \\ gvs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs []
      \\ Cases_on ‘x0’ \\ gvs [])
    \\ pairarg_tac \\ gvs []
    \\ ‘∃body' binds'. dest_anyClosure w2 = INR (s,body',binds')’
      by (Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
          \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
          \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gvs [CaseEqs ["option", "exp"]]
          \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
          \\ gvs [EVERY_EL, EL_MAP]
          \\ first_x_assum (drule_then assume_tac)
          \\ gs [ok_bind_def])
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’ \\ gs []
      \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_mono \\ gs []
      \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j1’ assume_tac) eval_to_mono \\ gs [])
    \\ ‘exp_rel (subst (binds ++ [s,v1]) body) (subst (binds' ++ [s,w1]) body')’
      by (irule exp_rel_subst \\ gs []
          \\ Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gvs [dest_anyClosure_def,
                                                    v_rel_def]
          \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
          \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ gvs [CaseEqs ["option", "exp"], v_rel_def]
          \\ gs [Once exp_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                 GSYM FST_THM, EVERY2_MAP, v_rel_def]
          \\ gvs [LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP, ELIM_UNCURRY])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) (subst (binds ++ [s,v1]) body) = INL Diverge’
    >- (
      Cases_on ‘eval_to k y = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ ‘∀i. eval_to (i + k) y = eval_to k y’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ Cases_on ‘eval_to k g = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ ‘∀i. eval_to (i + k) g = eval_to k g’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ gs []
      \\ qexists_tac ‘j2’
      \\ Cases_on ‘eval_to (j2 + k - 1) (subst (binds' ++ [s,w1]) body')’
      \\ gs [])
    \\ qexists_tac ‘j1 + j2 + j’ \\ gs []
    \\ first_x_assum (qspec_then ‘j + j2’ assume_tac)
    \\ first_x_assum (qspec_then ‘j1 + j2’ assume_tac) \\ gs []
    \\ ‘eval_to (j2 + k - 1) (subst (binds' ++ [s,w1]) body') ≠ INL Diverge’
      by (strip_tac
          \\ Cases_on ‘eval_to (k - 1) (subst (binds ++ [s,v1]) body)’ \\ gs [])
    \\ drule_then (qspec_then ‘j1 + j2 + j + k - 1’ assume_tac) eval_to_mono
    \\ gs [])
  >~ [‘Seq x1 y1’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ gs [])
    \\ last_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
    >~ [‘INL err’] >- (
      Cases_on ‘eval_to (j + k - 1) x2’ \\ gs []
      \\ qexists_tac ‘j’
      \\ simp [])
    \\ last_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) y1 = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (k - 1) x2 = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ ‘∀i. eval_to (i + k - 1) x2 = eval_to (k - 1) x2’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
    \\ ‘eval_to (j1 + k - 1) y2 ≠ INL Diverge’
      by (strip_tac
          \\ Cases_on ‘eval_to (k - 1) y1’ \\ gs [])
    \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono \\ gs []
    \\ ‘eval_to (j + k - 1) x2 ≠ INL Diverge’
      by (strip_tac \\ gs [])
    \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono \\ gs []
    \\ qexists_tac ‘j + j1’ \\ gs []
    \\ Cases_on ‘eval_to (j + k - 1) x2’ \\ gs [])
  >~ [‘Let (SOME m) x1 y1’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ gs [])
    \\ last_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
    >~ [‘INL err’] >- (
      Cases_on ‘eval_to (j + k - 1) x2’ \\ gs []
      \\ qexists_tac ‘j’
      \\ simp [])
    \\ Cases_on ‘eval_to (j + k - 1) x2’ \\ gs []
    \\ rename1 ‘v_rel v1 w1’
    \\ ‘exp_rel (subst1 m v1 y1) (subst1 m w1 y2)’
      by (irule exp_rel_subst \\ gs [])
    \\ last_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) (subst1 m v1 y1) = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (k - 1) x2 = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ ‘∀i. eval_to (i + k - 1) x2 = eval_to (k - 1) x2’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
    \\ ‘eval_to (j1 + k - 1) (subst1 m w1 y2) ≠ INL Diverge’
      by (strip_tac
          \\ Cases_on ‘eval_to (k - 1) (subst1 m v1 y1)’ \\ gs [])
    \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono \\ gs []
    \\ ‘eval_to (j + k - 1) x2 ≠ INL Diverge’
      by (strip_tac \\ gs [])
    \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono \\ gs []
    \\ qexists_tac ‘j + j1’ \\ gs [])
  >~ [‘If x1 y1 z1’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ gs [])
    \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
    >~ [‘INL err’] >- (
      Cases_on ‘eval_to (j + k - 1) x2’ \\ gs []
      \\ qexists_tac ‘j’
      \\ simp [])
    \\ Cases_on ‘eval_to (j + k - 1) x2’ \\ gs []
    \\ rename1 ‘v_rel v1 w1’
    \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
    \\ first_x_assum (drule_then (qx_choose_then ‘j2’ assume_tac))
    \\ IF_CASES_TAC \\ gvs [v_rel_def]
    >- (
      Cases_on ‘eval_to (k - 1) y1 = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (k - 1) x2 = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ gs [])
        \\ ‘∀i. eval_to (i + k - 1) x2 = eval_to (k - 1) x2’
          by (strip_tac \\ irule eval_to_mono \\ gs [])
        \\ qexists_tac ‘j1’ \\ gs [])
      \\ ‘eval_to (j1 + k - 1) y2 ≠ INL Diverge’
        by (strip_tac \\ Cases_on ‘eval_to (k - 1) y1’ \\ gs [])
      \\ ‘eval_to (j1 + j + k - 1) x2 = eval_to (j + k - 1) x2’
        by (irule eval_to_mono \\ gs [])
      \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono
      \\ qexists_tac ‘j1 + j’ \\ gs [])
    \\ IF_CASES_TAC \\ gvs [v_rel_def]
    >- (
      Cases_on ‘eval_to (k - 1) z1 = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (k - 1) x2 = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ gs [])
        \\ ‘∀i. eval_to (i + k - 1) x2 = eval_to (k - 1) x2’
          by (strip_tac \\ irule eval_to_mono \\ gs [])
        \\ qexists_tac ‘j2’ \\ gs [])
      \\ ‘eval_to (j2 + k - 1) z2 ≠ INL Diverge’
        by (strip_tac \\ Cases_on ‘eval_to (k - 1) z1’ \\ gs [])
      \\ ‘eval_to (j2 + j + k - 1) x2 = eval_to (j + k - 1) x2’
        by (irule eval_to_mono \\ gs [])
      \\ drule_then (qspec_then ‘j + j2 + k - 1’ assume_tac) eval_to_mono
      \\ qexists_tac ‘j2 + j’ \\ gs [])
    \\ qexists_tac ‘j’ \\ gs []
    \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gs [v_rel_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs [])
  >~ [‘Letrec f x’] >- (
    Cases_on ‘f = []’ \\ gvs []
    >~ [‘exp_rel (Tick x) y’] >- (
      Cases_on ‘k = 0’ \\ gs []
      >- (
        gvs [Once exp_rel_def]
        \\ qexists_tac ‘0’
        \\ simp [eval_to_def])
      \\ ‘∃n z. 0 < n ∧ y = FUNPOW Tick n z ∧ exp_rel x z’
        by (‘(∀z y.
               exp_rel z y ⇒
               ∀x. z = Tick x ⇒
                 ∃n u. 0 < n ∧ y = FUNPOW Tick n u ∧ exp_rel x u) ∧
             (∀v w. v_rel v w ⇒ T)’
              suffices_by rw []
            \\ rpt (pop_assum kall_tac)
            \\ ho_match_mp_tac exp_rel_strongind \\ rw []
            >- (
             Cases_on ‘∃x. z = Tick x’ \\ gvs []
             >- (
               first_assum (irule_at (Pos last))
               \\ qexists_tac ‘SUC 0’ \\ gs [])
             \\ drule_all_then strip_assume_tac exp_rel_FUNPOW
             \\ gvs []
             \\ first_assum (irule_at Any)
             \\ qexists_tac ‘SUC n’
             \\ simp [arithmeticTheory.FUNPOW_SUC])
           \\ qexists_tac ‘SUC n’
           \\ qexists_tac ‘u’
           \\ simp [arithmeticTheory.FUNPOW_SUC])
      \\ ‘∃m. n = SUC m’ by (Cases_on ‘n’ \\ gs []) \\ gvs []
      \\ qpat_x_assum ‘exp_rel (Tick x) _’ kall_tac
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ simp [eval_to_def, arithmeticTheory.FUNPOW_SUC]
      \\ Q.REFINE_EXISTS_TAC ‘j + m’
      \\ ‘j + m + k - 1 = j + k - 1 + m’
        by gs []
      \\ pop_assum SUBST1_TAC
      \\ simp [eval_to_Tick])
    \\ dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ gs [])
    \\ first_x_assum (irule_at Any)
    \\ simp [subst_funs_def]
    \\ irule exp_rel_subst
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
             EVERY2_MAP, v_rel_def]
    \\ qpat_x_assum ‘MAP FST _ = _’ mp_tac
    \\ rw [Once LIST_EQ_REWRITE]
    \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY])
  >~ [‘Delay x’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def, v_rel_def])
  >~ [‘Box x’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘∃j. ($= +++ v_rel) (eval_to k x) (eval_to (j + k) y)’
      suffices_by (
        disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
        \\ simp [v_rel_def])
    \\ first_x_assum (irule_at Any) \\ gs [])
  >~ [‘Force x’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ rgs [Once exp_rel_def]
    \\ rename1 ‘exp_rel x y’ \\ gvs []
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick]
    \\ once_rewrite_tac [eval_to_def] \\ simp []
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
    \\ Cases_on ‘eval_to k x’ \\ gs []
    >~ [‘INL err’] >-(
      qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k) y’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
    \\ rename1 ‘v_rel v1 w1’
    \\ Cases_on ‘dest_Tick v1’ \\ gs []
    >- (
      Cases_on ‘dest_anyThunk v1’ \\ gs []
      >- (
        qexists_tac ‘j’ \\ gs []
        \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gs [dest_anyThunk_def, v_rel_def]
        \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
        \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
        \\ gvs [OPTREL_def]
        \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
        \\ rw [Once exp_rel_cases] \\ gs []
        \\ Cases_on ‘x0’ \\ gvs [])
      \\ pairarg_tac \\ gvs []
      \\ ‘∃wx' binds'. dest_anyThunk w1 = INR (wx', binds') ∧
                       (v_rel +++ exp_rel) wx wx' ∧
                       MAP FST binds = MAP FST binds' ∧
                       EVERY ok_bind (MAP SND binds) ∧
                       EVERY ok_bind (MAP SND binds') ∧
                       LIST_REL exp_rel (MAP SND binds) (MAP SND binds')’
        by (Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [dest_anyThunk_def, v_rel_def]
            \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
            \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
            \\ gvs [OPTREL_def]
            \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gvs []
            \\ Cases_on ‘x0’ \\ gvs []
            \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
            \\ gvs [EVERY_EL, EL_MAP]
            \\ first_x_assum (drule_then assume_tac)
            \\ gvs [ok_bind_def])
      \\ CASE_TAC \\ gs []
      >- (
        qexists_tac ‘j’ \\ simp []
        \\ CASE_TAC \\ gs []
        \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gs [dest_anyThunk_def])
      \\ Cases_on ‘wx'’ \\ gs []
      \\ rename1 ‘exp_rel x1 x2’
      \\ ‘exp_rel (subst_funs binds x1) (subst_funs binds' x2)’
        by (simp [subst_funs_def]
            \\ irule exp_rel_subst
            \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                   EVERY2_MAP, v_rel_def]
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EVERY_EL, EL_MAP,
                    LIST_EQ_REWRITE])
      \\ first_x_assum (drule_all_then (qx_choose_then ‘j2’ assume_tac))
      \\ Cases_on ‘eval_to (k - 1) (subst_funs binds x1) = INL Diverge’
      >- (
        Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ gs [])
        \\ ‘∀i. eval_to (i + k) y = eval_to k y’
          by (strip_tac \\ irule eval_to_mono \\ gs [])
        \\ gs []
        \\ reverse CASE_TAC
        >- (
          Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [dest_anyThunk_def])
        \\ qexists_tac ‘j2’ \\ gs [])
      \\ ‘eval_to (j2 + k - 1) (subst_funs binds' x2) ≠ INL Diverge’
        by (strip_tac
            \\ Cases_on ‘eval_to (k - 1) (subst_funs binds x1)’ \\ gs [])
      \\ drule_then (qspec_then ‘j2 + j1 + j + k - 1’ assume_tac) eval_to_mono
      \\ ‘eval_to (j2 + j1 + j + k) y = eval_to (j + k) y’
        by (irule eval_to_mono \\ gs [])
      \\ qexists_tac ‘j2 + j1 + j’ \\ gs []
      \\ CASE_TAC \\ gs []
      \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [dest_anyThunk_def])
    \\ rename1 ‘dest_Tick v1 = SOME v2’
    \\ ‘∃w2. dest_Tick w1 = SOME w2 ∧ v_rel v2 w2’
      by (Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [v_rel_def])
    \\ ‘exp_rel (Force (Value v2)) (Force (Value w2))’
      by simp [exp_rel_Force, exp_rel_Value]
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
    \\ Cases_on ‘eval_to (k - 1) (Force (Value v2)) = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to k y = INL Diverge’
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ ‘∀i. eval_to (i + k) y = eval_to k y’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
      \\ qexists_tac ‘j1’ \\ gs [])
    \\ ‘eval_to (j1 + k - 1) (Force (Value w2)) ≠ INL Diverge’
      by (strip_tac
          \\ Cases_on ‘eval_to (k - 1) (Force (Value v2))’ \\ gs [])
    \\ drule_then (qspec_then ‘j1 + j + k - 1’ assume_tac) eval_to_mono \\ gs []
    \\ ‘eval_to (j + j1 + k) y = eval_to (j + k) y’
      by (irule eval_to_mono \\ gs [])
    \\ qexists_tac ‘j1 + j’ \\ gs [])
  >~ [‘MkTick x’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def])
  >~ [`Monad mop xs`]
  >- (
    dxrule_then assume_tac exp_rel_FUNPOW >> gvs[] >> gvs[Once exp_rel_def] >>
    qexists `n` >> simp[eval_to_def, eval_to_Tick] >> simp[Once v_rel_def]
    )
  >~ [‘Prim op xs’] >- (
    dxrule_then assume_tac exp_rel_FUNPOW \\ gvs []
    \\ gvs [Once exp_rel_def]
    \\ Q.REFINE_EXISTS_TAC ‘j + n’
    \\ once_rewrite_tac [DECIDE “j + n + k = (j + k) + n”]
    \\ simp [eval_to_Tick, eval_to_def]
    \\ gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      ‘∃j. ($= +++ LIST_REL v_rel) (result_map (eval_to k) xs)
                                   (result_map (eval_to (j + k)) ys)’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’ \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map (eval_to k) xs’
          \\ Cases_on ‘result_map (eval_to (j + k)) ys’ \\ gs [v_rel_def])
      \\ gvs [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ qexists_tac ‘j’
        \\ rw [] \\ gs [SF SFY_ss]
        \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ Cases_on ‘eval_to (j + k) (EL n ys)’ \\ gs [])
      \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃j. ($= +++ v_rel) (eval_to k (EL n xs))
                               (eval_to (j + k) (EL n ys))’
        by rw []
      \\ last_x_assum kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        Cases_on
          ‘∃m. m < LENGTH ys ∧ eval_to k (EL m ys) = INL Type_error’ \\ gs []
        >- (
          ‘F’ suffices_by rw []
          \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
          \\ ‘eval_to k (EL m ys) ≠ INL Diverge’
            by gs []
          \\ ‘∀i. eval_to (i + k) (EL m ys) = eval_to k (EL m ys)’
            by (strip_tac \\ irule eval_to_mono \\ gs [])
          \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
        \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ qexists_tac ‘0’
        \\ rw [] \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ ‘eval_to k (EL n ys) ≠ INL Diverge’
          by gs []
        \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
      \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to k (EL n xs))
                               (eval_to (j + k) (EL n ys))’
        by (rpt (pop_assum mp_tac)
            \\ qid_spec_tac ‘ys’
            \\ qid_spec_tac ‘xs’
            \\ Induct \\ simp []
            \\ Cases_on ‘ys’ \\ simp []
            \\ qx_gen_tac ‘x’
            \\ rename1 ‘_ (EL _ (x::xs)) (EL _ (y::ys))’
            \\ rw []
            \\ last_x_assum drule
            \\ impl_tac
            >- (
              rw []
              \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs [SF SFY_ss])
            \\ disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ ‘0 < SUC (LENGTH ys)’ by gs []
            \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
            \\ gs []
            \\ qexists_tac ‘MAX j j1’
            \\ Cases \\ rw [arithmeticTheory.MAX_DEF]
            >- (
              ‘eval_to k x ≠ INL Diverge’
                by (strip_tac
                    \\ ‘0 < SUC (LENGTH ys)’ by gs []
                    \\ first_x_assum (drule_then assume_tac) \\ gs [])
              \\ ‘eval_to (j + k) y ≠ INL Diverge’
                by (strip_tac \\ Cases_on ‘eval_to k x’ \\ gs [])
              \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
              \\ gs [])
            \\ gs [arithmeticTheory.NOT_LESS]
            \\ rename1 ‘m < LENGTH ys’
            \\ ‘SUC m < SUC (LENGTH ys)’ by gs []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ ‘eval_to (j1 + k) (EL m ys) ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
            \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ rw [] \\ gs [SF SFY_ss, DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      >~ [‘MAP OUTR _’] >- (
        gvs [EVERY2_MAP, LIST_REL_EL_EQN] \\ rw []
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n xs)’
        \\ Cases_on ‘eval_to (j + k) (EL n ys)’ \\ gvs []
        \\ rename1 ‘err ≠ Type_error’ \\ Cases_on ‘err’ \\ gs [])
      \\ first_x_assum (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
    >- ((* IsEq *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (j + k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs []
      \\ rw [v_rel_def])
    >- ((* Proj *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (j + k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* AtomOp *)
      Cases_on ‘k = 0’ \\ gs []
      >- (
        qexists_tac ‘0’ \\ gs []
        \\ rw [result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS]
        \\ Cases_on ‘ys = []’ \\ gs []
        >- (
          CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
        \\ ‘xs ≠ []’ by (strip_tac \\ gs [])
        \\ first_x_assum (qspec_then ‘0’ assume_tac) \\ gs [])
      \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ qabbrev_tac ‘g = λj x. case eval_to (j + k - 1) x of
                                INL err => INL err
                              | INR (Atom x) => INR x
                              | _ => INL Type_error’ \\ gs []
      \\ ‘∃j. result_map f xs = result_map (g j) ys’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’ \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map (g j) ys’ \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
      \\ unabbrev_all_tac
      \\ simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ Cases_on ‘k’ \\ gs [arithmeticTheory.ADD1]
      \\ rename1 ‘eval_to k’
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃j. ($= +++ v_rel) (eval_to k (EL n xs))
                               (eval_to (j + k) (EL n ys))’
        by rw []
      \\ last_x_assum kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        rename1 ‘m < LENGTH ys’
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ qexists_tac ‘j’
        \\ rw [] \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to k (EL m xs)’
        \\ Cases_on ‘eval_to (j + k) (EL m ys)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ ‘∀n. n < LENGTH ys ⇒ eval_to k (EL n xs) = INL Diverge ∨
                              ∃x. eval_to k (EL n xs) = INR (Atom x)’
        by (rw [DISJ_EQ_IMP]
            \\ first_x_assum drule
            \\ rw [CaseEqs ["sum", "v"]]
            \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs []
            >~ [‘INL err’] >- (
              Cases_on ‘err’ \\ gs [])
            \\ rename1 ‘INR x’
            \\ Cases_on ‘x’ \\ gs [])
      \\ qpat_x_assum ‘∀n. _ ⇒ sum_CASE _ _ _ ≠ _’ kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        Cases_on
          ‘∃m. m < LENGTH ys ∧ eval_to k (EL m ys) = INL Type_error’ \\ gs []
        >- (
          ‘F’ suffices_by rw []
          \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
          \\ ‘eval_to k (EL m ys) ≠ INL Diverge’
            by gs []
          \\ ‘∀i. eval_to (i + k) (EL m ys) = eval_to k (EL m ys)’
            by (strip_tac \\ irule eval_to_mono \\ gs [])
          \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs []
          \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs [])
        \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        \\ rename1 ‘n < LENGTH ys’
        \\ rgs [Once (CaseEq "sum"), CaseEq "v"]
        \\ qexists_tac ‘0’
        \\ rw [] \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
        >- (
          rename1 ‘m < LENGTH ys’
          \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
          \\ ‘eval_to k (EL m ys) ≠ INL Diverge’
            by (strip_tac \\ gs [])
          \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
          \\ Cases_on ‘eval_to k (EL m ys)’
          \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs []
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac) \\ gs [v_rel_def])
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ ‘eval_to k (EL n ys) ≠ INL Diverge’
          by (strip_tac \\ gs [])
        \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
      \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃x. eval_to k (EL n xs) = INR (Atom x)’
        by (rw []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs [])
      \\ qpat_x_assum ‘∀n. n < _ ⇒ sum_CASE _ _ _ ≠ _’ kall_tac
      \\ qpat_x_assum ‘∀n. n < _ ⇒ _ ∨ _’ kall_tac
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to k (EL n xs))
                               (eval_to (j + k) (EL n ys))’
        by (rpt (pop_assum mp_tac)
            \\ qid_spec_tac ‘ys’
            \\ qid_spec_tac ‘xs’
            \\ Induct \\ simp []
            \\ Cases_on ‘ys’ \\ simp []
            \\ qx_gen_tac ‘x’
            \\ rename1 ‘_ (EL _ (x::xs)) (EL _ (y::ys))’
            \\ rw []
            \\ last_x_assum drule
            \\ impl_tac
            >- (
              rw []
              \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs [SF SFY_ss]
              \\ qexists_tac ‘j’ \\ gs [])
            \\ disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ ‘0 < SUC (LENGTH ys)’ by gs []
            \\ last_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
            \\ gs []
            \\ qexists_tac ‘MAX j j1’
            \\ Cases \\ rw [arithmeticTheory.MAX_DEF]
            >- (
              ‘eval_to k x ≠ INL Diverge’
                by (strip_tac
                    \\ ‘0 < SUC (LENGTH ys)’ by gs []
                    \\ first_x_assum (drule_then assume_tac) \\ gs [])
              \\ ‘eval_to (j + k) y ≠ INL Diverge’
                by (strip_tac \\ Cases_on ‘eval_to k x’ \\ gs [])
              \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
              \\ gs [])
            \\ gs [arithmeticTheory.NOT_LESS]
            \\ rename1 ‘m < LENGTH ys’
            \\ ‘SUC m < SUC (LENGTH ys)’ by gs []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ ‘eval_to (j1 + k) (EL m ys) ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
            \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ rw [] \\ gs [DECIDE “A ⇒ ¬(B < C) ⇔ B < C ⇒ ¬A”]
      >~ [‘MAP OUTR _’] >- (
        irule LIST_EQ \\ simp [EL_MAP]
        \\ qx_gen_tac ‘n’
        \\ strip_tac
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [v_rel_def])
      \\ rename1 ‘n < LENGTH ys’
      \\ rpt (first_x_assum (drule_all_then assume_tac))
      \\ Cases_on ‘eval_to k (EL n xs)’
      \\ Cases_on ‘eval_to (j + k) (EL n ys)’ \\ gs [v_rel_def]))
QED

Theorem exp_rel_eval:
  exp_rel x y ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘MAX k j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
    \\ ‘eval_to ( MAX k j) x = eval_to k x’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to (m + MAX k j) y = eval_to j y’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘j’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to \\ gs []
    \\ drule_then (qspec_then ‘m + j’ assume_tac) eval_to_mono \\ gs [])
  \\ rename1 ‘_ _ (eval_to k x)’
  \\ drule_all_then
    (qspec_then ‘k’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
  \\ Cases_on ‘eval_to (k + m) x’ \\ gvs []
QED

Theorem tick_apply_closure[local]:
  exp_rel x y ∧
  v_rel v2 w2 ∧
  (∀x y. ($= +++ v_rel) x y ⇒ next_rel v_rel exp_rel (f x) (g y)) ⇒
    next_rel v_rel exp_rel (apply_closure x v2 f) (apply_closure y w2 g)
Proof
  rw [apply_closure_def] >> simp[with_value_def] >>
  dxrule_then assume_tac exp_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[]
  >- (CASE_TAC >> gvs[]) >>
  rename1 `eval x = INR v1` >> rename1 `eval y = INR w1`
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [v_rel_def, dest_anyClosure_def]
  >- (
    first_x_assum irule
    \\ irule exp_rel_eval
    \\ irule exp_rel_subst \\ gs [])
  \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
  \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
    by (irule LIST_REL_OPTREL
        \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
  \\ gs [OPTREL_def]
  \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
  \\ rw [Once exp_rel_cases] \\ gs []
  \\ drule_then assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
  \\ gvs [EVERY_EL, EL_MAP]
  >~ [‘Tick y’] >- (
    first_x_assum (drule_then assume_tac)
    \\ gs [])
  \\ first_x_assum irule
  \\ irule exp_rel_eval
  \\ irule exp_rel_subst
  \\ simp [EVERY2_MAP, LAMBDA_PROD, v_rel_def, MAP_MAP_o, combinTheory.o_DEF,
           GSYM FST_THM]
  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EVERY_EL, EL_MAP, LIST_EQ_REWRITE]
QED

Theorem tick_rel_ok[local]:
  rel_ok T v_rel exp_rel
Proof
  rw[rel_ok_def, tick_apply_closure]
  \\ gs [v_rel_def] \\ rw [Once exp_rel_cases]
QED

Theorem tick_sim_ok[local]:
  sim_ok T v_rel exp_rel
Proof
  rw [sim_ok_def, exp_rel_eval, exp_rel_subst]
QED

Theorem tick_semantics:
  exp_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics \\ gs []
  \\ first_assum (irule_at Any)
  \\ qexists_tac ‘T’ \\ gs []
  \\ irule_at Any tick_rel_ok
  \\ irule_at Any tick_sim_ok
QED

val _ = export_theory ();
