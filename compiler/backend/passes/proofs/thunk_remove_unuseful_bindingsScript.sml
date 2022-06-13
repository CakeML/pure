(*
  Remove all unuseful bindings from an expression expressed in thunkLang
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory;

val _ = new_theory "thunk_remove_unuseful_bindings";

Definition ok_bind_def:
  ok_bind (Lam s e) = T ∧
  ok_bind (Delay e) = T ∧
  ok_bind _ = F
End

Definition no_op_def:
  no_op (Lam s e) = T ∧
  no_op (Delay e) = T ∧
  no_op (Value v) = T ∧
  no_op _ = F
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
[~remove_Letrec:]
  (∀f x y.
     EVERY ok_bind (MAP SND f) ∧
     exp_rel x y ∧
     EVERY (λv. v ∉ freevars x) (MAP FST f) ⇒
     exp_rel (Letrec f x) y) ∧
[~Let:]
  (∀opt x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
     exp_rel (Let opt x1 y1) (Let opt x2 y2)) ∧
(*[~Let_commutes:]
  (∀x1 x2 y1 y2 z1 z2 s1 s2.
     exp_rel x1 x2 ∧ exp_rel y1 y2 ∧ exp_rel z1 z2 ∧
     s1 ∉ freevars y1 ∧ s2 ∉ freevars x1 ∧ s1 ≠ s2 ⇒
     exp_rel (Let (SOME s1) (Tick x1) (Let (SOME s2) y1 z1)) (Let (SOME s2) (Tick y2) (Let (SOME s1) x2 z2))) ∧*)
[~remove_Let:]
  (∀s x y1 y2.
     exp_rel y1 y2 ∧
     s ∉ freevars y1 ∧
     no_op x ⇒
     exp_rel (Let (SOME s) x y1) y2) ∧
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
[~MkTick:]
  (∀x y. exp_rel x y ⇒ exp_rel (MkTick x) (MkTick y)) ∧
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
   “v_rel (Closure s x) v”,
   “v_rel (Recclosure f n) v”,
   “v_rel (Atom x) v”,
   “v_rel (Thunk x) v”,
   “v_rel (DoTick x) v”]
  |> map (SIMP_CONV (srw_ss()) [Once exp_rel_cases])
  |> LIST_CONJ

Theorem ok_bind_subst[simp]:
  ∀x. ok_bind x ⇒ ok_bind (subst ws x)
Proof
  Cases \\ rw [ok_bind_def] \\ gs [subst_def, ok_bind_def]
QED

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars y ⊆ freevars x
Proof
  completeInduct_on ‘exp_size x’ >> Cases >>
  gvs [exp_size_def, exp_rel_def, PULL_EXISTS, freevars_def, SUBSET_DEF, PULL_FORALL] >>
  rw [] >> gvs []
  >- (rename1 ‘LIST_REL _ xs ys’
      \\ last_x_assum $ irule_at Any
      \\ gvs [MEM_EL, EL_MAP, LIST_REL_EL_EQN, PULL_EXISTS]
      \\ rpt $ last_assum $ irule_at Any
      \\ assume_tac exp_size_lemma
      \\ gvs [EL_MAP, MEM_EL, PULL_EXISTS]
      \\ rename1 ‘n < _’
      \\ first_x_assum $ qspecl_then [‘xs’, ‘n’] assume_tac \\ gvs [])
  >- (disj1_tac \\ first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj2_tac \\ first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (gvs [freevars_def]
      >- (disj1_tac \\ last_x_assum irule \\ gvs []
          \\ rpt $ first_x_assum $ irule_at Any)
      \\ disj2_tac \\ last_x_assum $ irule_at Any
      \\ gvs [MEM_EL, LIST_REL_EL_EQN, EL_MAP]
      \\ last_x_assum $ irule_at Any
      \\ rpt $ first_assum $ irule_at Any
      \\ gvs [EL_MAP, SND_THM]
      \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
      \\ assume_tac exp_size_lemma
      \\ gvs [MEM_EL, PULL_EXISTS]
      \\ rename1 ‘n < _’
      \\ first_x_assum $ qspecl_then [‘FST (EL n l)’, ‘SND (EL n l)’, ‘l’, ‘n’] assume_tac \\ gvs [])
  >- gvs [freevars_def]
  >- (disj1_tac \\ last_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (rename1 ‘exp_rel y1 y2’ \\ last_x_assum $ qspecl_then [‘y1’, ‘y2’] assume_tac \\ gvs []
      \\ pop_assum $ dxrule_then assume_tac \\ strip_tac \\ gvs [EVERY_MEM])
  >- (rename1 ‘exp_rel x1 x2’ \\ rename1 ‘exp_rel y1 y2’
      \\ rename1 ‘Let opt _ _’ \\ Cases_on ‘opt’
      \\ last_assum $ qspecl_then [‘x1’, ‘x2’] assume_tac
      \\ last_x_assum $ qspecl_then [‘y1’, ‘y2’] assume_tac \\ gvs [freevars_def])
(*  >- (rename1 ‘exp_rel x1 x2’ \\ rename1 ‘exp_rel y1 y2’ \\ rename1 ‘exp_rel z1 z2’
      \\ last_assum $ qspecl_then [‘x1’, ‘x2’] assume_tac
      \\ last_assum $ qspecl_then [‘y1’, ‘y2’] assume_tac
      \\ last_x_assum $ qspecl_then [‘z1’, ‘z2’] assume_tac \\ gvs [freevars_def, exp_size_def]
      \\ rw [] \\ gvs [])*)
  >- (rename1 ‘exp_rel y1 y2’ \\ last_x_assum $ qspecl_then [‘y1’, ‘y2’] assume_tac \\ gvs [freevars_def]
      \\ rw [] \\ gvs [])
  >- (disj1_tac \\ disj1_tac \\ first_x_assum irule \\ gvs []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj1_tac \\ disj2_tac \\ first_x_assum irule \\ gvs []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (disj2_tac \\ first_x_assum irule \\ gvs []
      \\ rpt $ first_x_assum $ irule_at Any)
  >- (first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
  >- (first_x_assum irule \\ gvs [] \\ rpt $ first_x_assum $ irule_at Any)
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
    \\ rename1 ‘LIST_REL v_rel (MAP SND vs) (MAP SND ws)’
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
  >~ [‘exp_rel (subst _ (Letrec f x)) (subst _ (Letrec g y))’] >- (
    rw [subst_def]
    \\ irule exp_rel_Letrec
    \\ gvs [EVERY_MAP, EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
            GSYM FST_THM]
    \\ first_x_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER]
    \\ rename1 ‘MAP FST f = MAP FST g’
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
  >~[‘Letrec _ x’] >- (
    rw [subst_def] \\ irule exp_rel_remove_Letrec \\ rw []
    >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
        \\ rw [] \\ irule ok_bind_subst \\ first_x_assum $ dxrule_then irule)
    >- gvs [EVERY_MEM, MAP_MAP_o, combinTheory.o_DEF, GSYM FST_THM, freevars_subst, LAMBDA_PROD]
    \\ qspecl_then [‘ws’, ‘y’, ‘set (MAP FST f)’] mp_tac $ GSYM subst_remove \\ impl_tac
    >- (dxrule_then assume_tac exp_rel_freevars \\ gvs [DISJOINT_ALT, EVERY_MEM, SUBSET_DEF]
        \\ rw [] \\ strip_tac \\ metis_tac [])
    \\ rw []
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST f)’ \\ fs []
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ irule_at Any EVERY2_mono
    \\ first_assum $ irule_at Any
    \\ gvs [])
(*  >~[‘exp_rel (subst vs (Let (SOME s1) (Tick x1) (Let (SOME s2) y1 z1))) (subst ws (Let _ (Tick y2) (Let _ x2 z2)))’]
  >- (rw [subst_def, exp_rel_def, freevars_subst] \\ disj1_tac
      \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
      \\ qspecl_then [‘vs’, ‘x1’, ‘{s2}’] assume_tac $ GSYM subst_remove
      \\ qspecl_then [‘vs’, ‘y1’, ‘{s1}’] assume_tac subst_remove \\ gvs []
      \\ rw [] \\ first_x_assum $ irule_at Any
      >- (gvs [MAP_FST_FILTER, EVERY2_MAP, FILTER_FILTER, LAMBDA_PROD]
          \\ qabbrev_tac ‘P = λn. n ≠ s2’ \\ gs []
          \\ gs [EVERY2_MAP] \\ irule LIST_REL_FILTER
          \\ gvs [LIST_REL_EL_EQN])
      \\ ‘(λ(n,p : thunkLang$v). n ≠ s2 ∧ n ≠ s1) = (λ(n,p). n ≠ s1 ∧ n ≠ s2)’
        by (gvs [] \\ metis_tac [CONJ_COMM])
      \\ gvs [FILTER_FILTER, LAMBDA_PROD] \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
      \\ qabbrev_tac ‘P = λn. n ≠ s1 ∧ n ≠ s2’ \\ gs []
      \\ irule LIST_REL_FILTER \\ gvs []
      \\ irule LIST_REL_mono
      \\ first_x_assum $ irule_at Any \\ gvs [])*)
  >~ [‘exp_rel (subst _ (Let s x y)) (subst _ (Let _ _ _))’] >- (
    Cases_on ‘s’ \\ rw [subst_def]
    \\ irule exp_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER]
    \\ rename1 ‘_ ≠ s’
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ gs [EVERY2_MAP]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~[‘Let _ _ _’] >- (
    rw [subst_def] \\ irule exp_rel_remove_Let
    \\ conj_tac >- (rename1 ‘no_op (subst _ x)’ \\ Cases_on ‘x’ \\ gvs [subst_def, no_op_def])
    \\ gvs [freevars_subst]
    \\ rename1 ‘exp_rel (subst (FILTER _ vs) y1) _’ \\ rename1 ‘s ∉ _’
    \\ qspecl_then [‘vs’, ‘y1’, ‘{s}’] mp_tac subst_remove \\ gvs [])
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
  >~[‘MkTick x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_MkTick])
QED

Theorem subst_APPEND:
  ∀e l1 l2. subst (l1 ++ l2) e = subst l1 (subst l2 e)
Proof
  Induct using freevars_ind >> gvs [subst_def, FILTER_APPEND]
  >- (gvs [REVERSE_APPEND, ALOOKUP_APPEND] >>
      rw [] >> CASE_TAC >> gvs [subst_def])
  >- (rw [] >> irule LIST_EQ >>
      rw [EL_MAP] >>
      last_x_assum irule >> gvs [EL_MEM]) >>
  rw []
  >- (irule LIST_EQ >>
      rw [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, EL_MAP] >>
      pairarg_tac >> gvs [MEM_EL, PULL_EXISTS] >>
      last_x_assum irule >>
      first_x_assum $ irule_at Any >> gvs [])
  >- rw [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
QED

Theorem subst_notin_frees:
  ∀vs e. DISJOINT (set (MAP FST vs)) (freevars e) ⇒ subst vs e = e
Proof
  Induct >> gvs [subst_empty] >> Cases >>
  once_rewrite_tac [CONS_APPEND] >> rw [subst_APPEND] >>
  gvs [subst1_notin_frees]
QED

Theorem exp_rel_eval_to:
  ∀x y.
    exp_rel x y ⇒
      ∃j. ($= +++ v_rel) (eval_to (j + k) x) (eval_to k y)
Proof
  completeInduct_on ‘k’
  \\ Induct using freevars_ind \\ rpt gen_tac
  >~ [‘Var v’] >- (
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘Value v’] >- (
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >~ [‘App g y’] >- (
    gvs [Once exp_rel_def, eval_to_def, PULL_EXISTS] \\ rw []
    \\ rename1 ‘exp_rel y x’ \\ rename1 ‘exp_rel g f’
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
    \\ rename1 ‘v_rel w1 v1’
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
    >~ [‘eval_to _ _ = INL err’] >- (
      Cases_on ‘err’ \\ gs []
      \\ qexists_tac ‘j1 + j’
      \\ ‘eval_to (j1 + j + k) y = eval_to (j + k) y’
        by (irule eval_to_mono \\ gs [])
      \\ ‘eval_to (j1 + j + k) g = eval_to (j1 + k) g’
        by (irule eval_to_mono \\ gs []
            \\ strip_tac \\ gs [])
      \\ Cases_on ‘eval_to (j1 + k) g’ \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k) g’ \\ gs []
    \\ rename1 ‘v_rel w2 v2’
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
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
          \\ last_x_assum $ dxrule_then assume_tac
          \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gs [ok_bind_def]))
    \\ pairarg_tac \\ gvs []
    \\ ‘∃body' binds'. dest_anyClosure w2 = INR (s,body',binds')’
      by (Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
          >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
              \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                by (irule LIST_REL_OPTREL
                    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
              \\ gvs [OPTREL_def]
              \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
              \\ last_x_assum $ dxrule_then assume_tac
              \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
              \\ rw [Once exp_rel_cases] \\ gvs [CaseEqs ["option", "exp"], ok_bind_def]))
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’ \\ gs []
      \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_mono \\ gs []
      \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j1’ assume_tac) eval_to_mono \\ gs [])
    \\ ‘exp_rel (subst (binds' ++ [s,w1]) body') (subst (binds ++ [s,v1]) body)’
      by (Cases_on ‘v2’ \\ Cases_on ‘w2’
          \\ gvs [dest_anyClosure_def, v_rel_def, subst_APPEND]
          >- (irule exp_rel_subst \\ gvs [])
          >- (irule exp_rel_subst
              \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
              \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                by (irule LIST_REL_OPTREL
                    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
              \\ irule_at Any exp_rel_subst
              \\ gvs [OPTREL_def]
              \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
              \\ last_assum $ dxrule_then assume_tac
              \\ gvs [CaseEqs ["option", "exp"], v_rel_def, ok_bind_def]
              \\ gs [Once exp_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                     GSYM FST_THM, EVERY2_MAP, v_rel_def]
              \\ gvs [LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP, ELIM_UNCURRY, EVERY_MEM, MEM_MAP, PULL_EXISTS]))
    \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gs []
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
  >~ [‘Lam s x’] >- (
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def, v_rel_def])
  >~ [‘Let NONE x y’] >- (
    rw [exp_rel_def] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘exp_rel x x2’ \\ rename1 ‘exp_rel y y2’
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
    \\ last_assum $ dxrule_then $ qx_choose_then ‘j1’ assume_tac
    \\ last_x_assum $ dxrule_then $ qx_choose_then ‘j2’ assume_tac
    \\ rename1 ‘eval_to (jx + k - 1) x’
    \\ rename1 ‘eval_to (jy + k - 1) y’
    \\ Cases_on ‘eval_to (k - 1) x2’
    >- (qexists_tac ‘jx’ \\ Cases_on ‘eval_to (jx + k - 1) x’ \\ gs [])
    \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
    >- (qexists_tac ‘0’
        \\ Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘jx + k - 1’] assume_tac) eval_to_mono
        \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) y = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘jy + k - 1’] assume_tac) eval_to_mono \\ gs [])
    \\ Cases_on ‘eval_to (jx + k - 1) x’ \\ gs []
    \\ ‘eval_to (jy + jx + k - 1) x = eval_to (jx + k - 1) x’
        by (irule eval_to_mono \\ gs [])
    \\ ‘eval_to (jx + jy + k - 1) y = eval_to (jy + k - 1) y’
      by (irule eval_to_mono
          \\ Cases_on ‘eval_to (jy + k - 1) y’
          \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs [])
    \\ qexists_tac ‘jx + jy’ \\ gvs [])
  >~ [‘Let (SOME n) x y’] >- (
    rw [exp_rel_def] \\ gs []
    >~[‘no_op x’]
    >- (gvs [eval_to_def, subst1_notin_frees]
        \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
        \\ qexists_tac ‘j + 1’ \\ gvs []
        \\ Cases_on ‘x’ \\ gvs [no_op_def] \\ gvs [eval_to_def])
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘exp_rel x x2’ \\ rename1 ‘exp_rel y y2’
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
    \\ first_assum $ qspecl_then [‘x’, ‘x2’] mp_tac
    \\ impl_tac >- gvs []
    \\ disch_then $ qx_choose_then ‘j1’ assume_tac
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    >- (qexists_tac ‘j1’ \\ Cases_on ‘eval_to (j1 + k - 1) x’ \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k - 1) x’ \\ gs []
    \\ rename1 ‘v_rel v1 v2’
    \\ first_x_assum $ qspecl_then [‘subst1 n v1 y’, ‘subst1 n v2 y2’] mp_tac
    \\ impl_tac >- gvs [exp_rel_subst]
    \\ disch_then $ qx_choose_then ‘j2’ assume_tac
    \\ Cases_on ‘eval_to (k - 1) (subst1 n v2 y2) = INL Diverge’ \\ gs []
    >- (qexists_tac ‘0’
        \\ Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘j1 + k - 1’] assume_tac) eval_to_mono
        \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
        \\ Cases_on ‘eval_to (k - 1) (subst1 n v1 y) = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k - 1) x’ \\ gs []
    \\ ‘eval_to (j2 + j1 + k - 1) x = eval_to (j1 + k - 1) x’
        by (irule eval_to_mono \\ gs [])
    \\ ‘eval_to (j1 + j2 + k - 1) (subst1 n v1 y) = eval_to (j2 + k - 1) (subst1 n v1 y)’
      by (irule eval_to_mono
          \\ Cases_on ‘eval_to (j2 + k - 1) (subst1 n v1 y)’
          \\ Cases_on ‘eval_to (k - 1) (subst1 n v2 y2)’ \\ gs [])
    \\ qexists_tac ‘j1 + j2’ \\ gvs [])
  >~ [‘Letrec f x’] >- (
    rw [exp_rel_def] \\ gs []
    >- (simp [eval_to_def]
        \\ IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ >> gs [])
        \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
        \\ first_x_assum irule
        \\ simp [subst_funs_def, closed_subst, MAP_MAP_o, combinTheory.o_DEF,
                 LAMBDA_PROD, GSYM FST_THM]
        \\ irule exp_rel_subst
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
        \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
        \\ rename1 ‘MAP FST f = MAP FST g’
        \\ ‘∀i. i < LENGTH f ⇒ FST (EL i f) = FST (EL i g)’
          by (rw [] >>
              ‘i < LENGTH f’ by gs [] >>
              dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
              ‘i < LENGTH g’ by gs [] >>
              dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
              rw [])
        \\ gs [] \\ first_x_assum $ dxrule_then assume_tac \\ gvs [])
    >- (simp [eval_to_def]
        \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
        \\ qexists_tac ‘j + 1’
        \\ qspecl_then [‘MAP (λ(v,e). (v, Recclosure f v)) f’, ‘x’] assume_tac subst_notin_frees
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                EVERY_MEM, DISJOINT_ALT, subst_funs_def]))
  >~ [‘If x1 y1 z1’] >- (
    rw [exp_rel_def, eval_to_def] \\ gs [eval_to_def]
    \\ Cases_on ‘k = 0’
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’ \\ rename1 ‘exp_rel z1 z2’
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ last_x_assum kall_tac
    \\ rpt $ first_assum $ dxrule_then assume_tac
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
    \\ rename1 ‘eval_to (j2 + k - 1) z1’
    \\ rename1 ‘eval_to (j1 + k - 1) y1’
    \\ rename1 ‘eval_to (j  + k - 1) x1’
    \\ Cases_on ‘eval_to (k - 1) x2’
    \\ Cases_on ‘eval_to (j + k - 1) x1’ \\ gs []
    >~ [‘INL err’] >- (qexists_tac ‘j’ \\ simp [])
    \\ rename1 ‘v_rel v1 w1’
    \\ IF_CASES_TAC \\ gvs [v_rel_def]
    >- (
      Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (k - 1) x1 = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ gs [])
        \\ ‘∀i. eval_to (i + k - 1) x1 = eval_to (k - 1) x1’
          by (strip_tac \\ irule eval_to_mono \\ gs [])
        \\ qexists_tac ‘j1’ \\ gs []
        \\ Cases_on ‘v1’ \\ gs [v_rel_def])
      \\ ‘eval_to (j1 + k - 1) y1 ≠ INL Diverge’
        by (strip_tac \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs [])
      \\ ‘eval_to (j1 + j + k - 1) x1 = eval_to (j + k - 1) x1’
        by (irule eval_to_mono \\ gs [])
      \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono
      \\ qexists_tac ‘j1 + j’ \\ gs []
      \\ Cases_on ‘v1’ \\ gs [v_rel_def])
    \\ IF_CASES_TAC \\ gvs [v_rel_def]
    >- (
      Cases_on ‘eval_to (k - 1) z2 = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (k - 1) x1 = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ gs [])
        \\ ‘∀i. eval_to (i + k - 1) x1 = eval_to (k - 1) x1’
          by (strip_tac \\ irule eval_to_mono \\ gs [])
        \\ qexists_tac ‘j2’ \\ Cases_on ‘v1’ \\ gs [v_rel_def])
      \\ ‘eval_to (j2 + k - 1) z1 ≠ INL Diverge’
        by (strip_tac \\ Cases_on ‘eval_to (k - 1) z2’ \\ gs [])
      \\ ‘eval_to (j2 + j + k - 1) x1 = eval_to (j + k - 1) x1’
        by (irule eval_to_mono \\ gs [])
      \\ drule_then (qspec_then ‘j + j2 + k - 1’ assume_tac) eval_to_mono
      \\ qexists_tac ‘j2 + j’ \\ Cases_on ‘v1’ \\ gs [v_rel_def])
    \\ qexists_tac ‘j’ \\ gs []
    \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gs [v_rel_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs [])
  >~ [‘Force x’] >- (
    rw [exp_rel_def] \\ gs []
    \\ rename1 ‘exp_rel x y’
    \\ once_rewrite_tac [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
    \\ last_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
    \\ Cases_on ‘eval_to k y’ \\ Cases_on ‘eval_to (j + k) x’ \\ gs []
    >~[‘INL err’]
    >- (qexists_tac ‘j’ \\ gvs [])
    \\ rename1 ‘v_rel v w’
    \\ Cases_on ‘dest_Tick w’ \\ gs []
    >- (
      ‘dest_Tick v = NONE’
        by (Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs []
            \\ gs [Once v_rel_def])
      \\ gs []
      \\ Cases_on ‘v’ \\ gvs [dest_anyThunk_def, v_rel_def]
      >~[‘Recclosure _ _’]
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL exp_rel
              (ALOOKUP (REVERSE xs) s)
              (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
          \\ gs [OPTREL_def]
          >- (qexists_tac ‘j’ \\ gvs [])
          \\ rename1 ‘exp_rel x0 y0’
          \\ ‘MEM (s, x0) xs’ by (rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [])
          \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
          \\ first_assum $ dxrule_then assume_tac
          \\ Cases_on ‘x0’ \\ gvs [ok_bind_def, exp_rel_def]
          >~[‘subst_funs ys e2’]
          >- (rename1 ‘exp_rel e1 e2’
              \\ last_x_assum $ qspecl_then [‘subst_funs xs e1’, ‘subst_funs ys e2’] mp_tac
              \\ impl_tac
              >- (gvs [FORALL_PROD, subst_funs_def] \\ irule exp_rel_subst
                  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
                  \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
                  \\ rename1 ‘n < _’
                  \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gs []
                  \\ gvs [EL_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
                  \\ rw [] \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
              \\ disch_then $ qx_choose_then ‘j2’ assume_tac
              \\ Cases_on ‘eval_to (k - 1) (subst_funs ys e2) = INL Diverge’ \\ gs []
              >- (qexists_tac ‘0’
                  \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
                  \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
                  \\ Cases_on ‘eval_to (k - 1) (subst_funs xs e1) = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono \\ gs [])
              \\ qexists_tac ‘j + j2’
              \\ ‘eval_to (j + j2 + k) x = eval_to (j + k) x’ by (irule eval_to_mono \\ gvs [])
              \\ gvs []
              \\ ‘eval_to (j + (j2 + k) - 1) (subst_funs xs e1) = eval_to (j2 + k - 1) (subst_funs xs e1)’
                by (irule eval_to_mono
                    \\ Cases_on ‘eval_to (j2 + k - 1) (subst_funs xs e1)’
                    \\ Cases_on ‘eval_to (k - 1) (subst_funs ys e2)’ \\ gvs [])
              \\ gvs [])
          \\ qexists_tac ‘j’ \\ gvs [])
      >~[‘subst_funs [] y2’]
      >- (rename1 ‘exp_rel x2 y2’
          \\ last_x_assum $ qspecl_then [‘x2’, ‘y2’] assume_tac \\ gs [subst_funs_def, subst_empty]
          \\ rename1 ‘eval_to (j2 + k - 1) x2’
          \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
          >- (qexists_tac ‘0’
              \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
              \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
              \\ Cases_on ‘eval_to (k - 1) x2 = INL Diverge’ \\ gs []
              \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono \\ gs [])
            \\ qexists_tac ‘j + j2’
            \\ ‘eval_to (j + j2 + k) x = eval_to (j + k) x’ by (irule eval_to_mono \\ gvs [])
            \\ gvs []
            \\ ‘eval_to (j + (j2 + k) - 1) x2 = eval_to (j2 + k - 1) x2’
              by (irule eval_to_mono
                  \\ Cases_on ‘eval_to (j2 + k - 1) x2’
                  \\ Cases_on ‘eval_to (k - 1) y2’ \\ gvs [])
            \\ gvs [])
      \\ qexists_tac ‘j’ \\ gvs [])
    \\ Cases_on ‘v’ \\ gs [v_rel_def, exp_rel_def, PULL_EXISTS, dest_Tick_def]
    \\ rename1 ‘v_rel v2 w2’
    \\ last_x_assum $ qspecl_then [‘Force (Value v2)’, ‘Force (Value w2)’] assume_tac
    \\ gvs [exp_rel_def]
    \\ rename1 ‘v_rel v2 w2’ \\ rename1 ‘eval_to (j2 + k - 1) (Force _)’
    \\ Cases_on ‘eval_to (k - 1) (Force (Value w2)) = INL Diverge’ \\ gs []
    >- (qexists_tac ‘0’
        \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
        \\ Cases_on ‘eval_to (k - 1) (Force (Value v2)) = INL Diverge’ \\ gs []
        \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono \\ gs [])
    \\ qexists_tac ‘j + j2’
    \\ ‘eval_to (j + j2 + k) x = eval_to (j + k) x’ by (irule eval_to_mono \\ gvs [])
    \\ gs []
    \\ ‘eval_to (j + (j2 + k) - 1) (Force (Value v2)) = eval_to (j2 + k - 1) (Force (Value v2))’
      by (irule eval_to_mono
          \\ Cases_on ‘eval_to (j2 + k - 1) (Force (Value v2))’
          \\ Cases_on ‘eval_to (k - 1) (Force (Value w2))’ \\ gvs [])
    \\ gvs [])
  >~ [‘Delay x’] >- (
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def, v_rel_def])
  >~ [‘Box x’] >- (
    rw [exp_rel_def] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum $ drule_then $ qx_choose_then ‘j’ assume_tac
    \\ qexists_tac ‘j’
    \\ Cases_on ‘eval_to k y’ \\ Cases_on ‘eval_to (k + j) x’ \\ gs [v_rel_def])
  >~ [‘MkTick x’] >- (
    rw [exp_rel_def] \\ gs [eval_to_def]
    \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
    \\ qexists_tac ‘j’
    \\ rename1 ‘($= +++ v_rel) (eval_to (j + k) x) (eval_to _ y)’
    \\ Cases_on ‘eval_to (j + k) x’
    \\ Cases_on ‘eval_to k y’ \\ gvs [v_rel_def])
  >~ [‘Prim op xs’] >- (
    rw []
    \\ gvs [Once exp_rel_def, eval_to_def]
    \\ gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      last_x_assum kall_tac
      \\ ‘∃j. ($= +++ LIST_REL v_rel) (result_map (eval_to (j + k)) xs)
                                      (result_map (eval_to k) ys)’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’ \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map (eval_to k) ys’
          \\ Cases_on ‘result_map (eval_to (j + k)) xs’ \\ gs [v_rel_def])
      \\ gvs [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ qexists_tac ‘j’
        \\ rw [] \\ gs [SF SFY_ss]
        \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs [])
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃j. ($= +++ v_rel) (eval_to (j + k) (EL n xs))
                               (eval_to k (EL n ys))’
        by rw []
      \\ last_x_assum kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        Cases_on
          ‘∃m. m < LENGTH xs ∧ eval_to k (EL m xs) = INL Type_error’ \\ gs []
        >- (
          ‘F’ suffices_by rw []
          \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
          \\ ‘eval_to k (EL m xs) ≠ INL Diverge’
            by gs []
          \\ ‘∀i. eval_to (i + k) (EL m xs) = eval_to k (EL m xs)’
            by (strip_tac \\ irule eval_to_mono \\ gs [])
          \\ Cases_on ‘eval_to k (EL m ys)’ \\ gs [])
        \\ qexists_tac ‘0’
        \\ rw [] \\ gs []
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ Cases_on ‘eval_to k (EL n xs) = INL Diverge’ \\ gs []
        \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to (j + k) (EL n xs))
                               (eval_to k (EL n ys))’
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
              rpt $ strip_tac
              \\ rename1 ‘n < LENGTH ys’
              \\ ‘SUC n < SUC (LENGTH ys)’ by gs []
              \\ res_tac \\ fs [SF SFY_ss]
              \\ rpt $ first_x_assum $ qspecl_then [‘SUC n’] assume_tac
              \\ gs [])
            \\ disch_then (qx_choose_then ‘j1’ assume_tac)
            \\ ‘0 < SUC (LENGTH ys)’ by gs []
            \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
            \\ gs []
            \\ qexists_tac ‘MAX j j1’
            \\ Cases \\ rw [arithmeticTheory.MAX_DEF]
            >- (
              ‘eval_to k y ≠ INL Diverge’
                by (strip_tac
                    \\ rpt $ first_x_assum $ qspecl_then [‘0’] assume_tac
                    \\ gs [])
              \\ ‘eval_to (j + k) x ≠ INL Diverge’
                by (strip_tac \\ Cases_on ‘eval_to k y’ \\ gs [])
              \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
              \\ gs [])
            \\ gs [arithmeticTheory.NOT_LESS]
            \\ rename1 ‘m < LENGTH ys’
            \\ ‘SUC m < SUC (LENGTH ys)’ by gs []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ ‘eval_to (j1 + k) (EL m xs) ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to k (EL m ys)’
                  \\ first_x_assum $ qspecl_then [‘SUC m’] assume_tac
                  \\ gs [])
            \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ rw [] \\ gs [SF SFY_ss]
      >~ [‘MAP OUTR _’] >- (
        gvs [EVERY2_MAP, LIST_REL_EL_EQN] \\ rw []
        \\ first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n ys)’
        \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gvs []
        \\ rename1 ‘INL err’ \\ Cases_on ‘err’ \\ gs [])
      \\ first_x_assum (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
    >- ((* IsEq *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ first_x_assum $ qspecl_then [‘0’] assume_tac \\ gs []
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs []
      \\ rw [v_rel_def])
    >- ((* Proj *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ first_x_assum $ qspecl_then [‘0’] assume_tac \\ gvs []
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs []
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
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ qabbrev_tac ‘f = λj x. case eval_to (j + k - 1) x of
                                INL err => INL err
                              | INR (Atom x) => INR x
                              | _ => INL Type_error’ \\ gs []
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
      \\ last_x_assum kall_tac \\ gvs []
      \\ ‘∃j. result_map (f j) xs = result_map g ys’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’ \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map g ys’ \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
      \\ unabbrev_all_tac
      \\ simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ Cases_on ‘k’ \\ gs [arithmeticTheory.ADD1]
      \\ rename1 ‘eval_to k’
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃j. ($= +++ v_rel) (eval_to (j + k) (EL n xs))
                               (eval_to k (EL n ys))’
        by rw []
      \\ qpat_x_assum ‘∀x y. exp_rel _ _ ⇒ _’ kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        rename1 ‘m < LENGTH ys’
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ qexists_tac ‘j’
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ rw [] \\ gs []
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to k (EL m ys)’
        \\ Cases_on ‘eval_to (j + k) (EL m xs)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      \\ ‘∀n. n < LENGTH ys ⇒ eval_to k (EL n ys) = INL Diverge ∨
                              ∃x. eval_to k (EL n ys) = INR (Atom x)’
        by (rw [DISJ_EQ_IMP]
            \\ first_x_assum drule
            \\ rw [CaseEqs ["sum", "v"]]
            \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
            >~ [‘INL err’] >- (
              Cases_on ‘err’ \\ gs [])
            \\ rename1 ‘INR x’
            \\ Cases_on ‘x’ \\ gs [])
      \\ qpat_x_assum ‘∀n. _ ⇒ ¬( _ < _)’ kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        Cases_on
          ‘∃m. m < LENGTH ys ∧ eval_to k (EL m xs) = INL Type_error’ \\ gs []
        >- (
          ‘F’ suffices_by rw []
          \\ first_x_assum (drule_then (qx_choose_then ‘j1’ assume_tac))
          \\ ‘eval_to k (EL m xs) ≠ INL Diverge’
            by gs []
          \\ ‘∀i. eval_to (i + k) (EL m xs) = eval_to k (EL m xs)’
            by (strip_tac \\ irule eval_to_mono \\ gs [])
          \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs []
          \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs [])
        \\ rename1 ‘n < LENGTH ys’
        \\ rgs [Once (CaseEq "sum"), CaseEq "v"]
        \\ qexists_tac ‘0’
        \\ rw [] \\ gs []
        >- (
          rename1 ‘m < LENGTH ys’
          \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
          \\ ‘eval_to k (EL m xs) ≠ INL Diverge’
            by (strip_tac \\ gs [])
          \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
          \\ Cases_on ‘eval_to k (EL m xs)’
          \\ Cases_on ‘eval_to k (EL m ys)’ \\ gs []
          \\ first_x_assum (drule_then assume_tac) \\ gs []
          \\ rename1 ‘v_rel y _’ \\ Cases_on ‘y’ \\ gs [v_rel_def])
        >- (
          first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ ‘eval_to k (EL n xs) ≠ INL Diverge’
            by (strip_tac \\ gs [])
          \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
          \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
        >- (rename1 ‘eval_to _ _ = INR v3’ \\ Cases_on ‘v3’ \\ gvs [])
        >- (rpt $ first_x_assum $ qspecl_then [‘n’] assume_tac
            \\ rename1 ‘eval_to _ _ = INR v3’ \\ Cases_on ‘v3’ \\ gvs []))
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃x. eval_to k (EL n ys) = INR (Atom x)’
        by (rw []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs [])
      \\ qpat_x_assum ‘∀n. _ ⇒ ¬(n < _)’ kall_tac
      \\ qpat_x_assum ‘∀n. n < _ ⇒ _ ∨ _’ kall_tac
      \\ ‘∃j. ∀n. n < LENGTH ys ⇒
                ($= +++ v_rel) (eval_to (j + k) (EL n xs))
                               (eval_to k (EL n ys))’
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
              ‘eval_to k y ≠ INL Diverge’
                by (strip_tac
                    \\ ‘0 < SUC (LENGTH ys)’ by gs []
                    \\ first_x_assum (drule_then assume_tac) \\ gs [])
              \\ ‘eval_to (j + k) x ≠ INL Diverge’
                by (strip_tac \\ Cases_on ‘eval_to k y’ \\ gs [])
              \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
              \\ gs [])
            \\ gs [arithmeticTheory.NOT_LESS]
            \\ rename1 ‘m < LENGTH ys’
            \\ ‘SUC m < SUC (LENGTH ys)’ by gs []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs []
            \\ ‘eval_to (j1 + k) (EL m xs) ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to k (EL m ys)’ \\ gs [])
            \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ gs [])
      \\ qexists_tac ‘j’
      \\ rw [] \\ gs []
      >~ [‘MAP OUTR _’] >- (
        irule LIST_EQ \\ simp [EL_MAP]
        \\ qx_gen_tac ‘n’
        \\ strip_tac
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [v_rel_def])
      \\ rename1 ‘n < LENGTH ys’
      \\ rpt (first_x_assum (drule_all_then assume_tac))
      \\ Cases_on ‘eval_to k (EL n ys)’
      \\ Cases_on ‘eval_to (j + k) (EL n xs)’ \\ gs []
      \\ rename1 ‘v_rel v0 (Atom _)’ \\ Cases_on ‘v0’ \\ gs [v_rel_def]))
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
  \\ dxrule_then (qspec_then ‘m + k’ assume_tac) eval_to_mono \\ gvs []
QED

Theorem delay_lam_apply_force[local] =
  apply_force_rel
  |> Q.INST [‘Rv’|->‘v_rel’, ‘Re’|->‘exp_rel’,‘allow_error’|->‘T’]
  |> SIMP_RULE std_ss [exp_rel_eval, exp_rel_Force, exp_rel_Value];

Theorem delay_lam_apply_closure[local]:
  v_rel v1 w1 ∧
  v_rel v2 w2 ∧
  (∀x y. ($= +++ v_rel) x y ⇒ next_rel v_rel (f x) (g y)) ⇒
    next_rel v_rel (apply_closure v1 v2 f) (apply_closure w1 w2 g)
Proof
  rw [apply_closure_def]
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [v_rel_def, dest_anyClosure_def]
  >- (
    first_x_assum irule
    \\ irule exp_rel_eval
    \\ irule exp_rel_subst \\ gs [])
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ ‘ok_bind x0’ by (rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
                          \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
      \\ rw [Once exp_rel_cases] \\ gs [ok_bind_def]
      \\ drule_then assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
      \\ gvs [EVERY_EL, EL_MAP]
      \\ first_x_assum irule
      \\ irule exp_rel_eval
      \\ irule exp_rel_subst
      \\ simp [EVERY2_MAP, LAMBDA_PROD, v_rel_def, MAP_MAP_o, combinTheory.o_DEF,
               GSYM FST_THM]
      \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EVERY_EL, EL_MAP, LIST_EQ_REWRITE])
QED

Theorem delay_lam_rel_ok[local]:
  rel_ok T v_rel
Proof
  rw [rel_ok_def, v_rel_def, exp_rel_def]
  \\ rw [delay_lam_apply_force, delay_lam_apply_closure]
QED

Theorem delay_lam_sim_ok[local]:
  sim_ok T v_rel exp_rel
Proof
  rw [sim_ok_def, exp_rel_eval, exp_rel_subst]
QED

Theorem delay_lam_semantics:
  exp_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics \\ gs []
  \\ first_assum (irule_at Any)
  \\ qexists_tac ‘T’ \\ gs []
  \\ irule_at Any delay_lam_rel_ok
  \\ irule_at Any delay_lam_sim_ok
QED

val _ = export_theory ();
