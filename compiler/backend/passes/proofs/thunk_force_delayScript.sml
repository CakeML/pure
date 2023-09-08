(*
  Simplify occurences of `Force (Delay e)` to `e`
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory thunk_remove_unuseful_bindingsTheory;

val _ = new_theory "thunk_force_delay";

Inductive force_delay_rel:
[~Var:]
  (∀n. force_delay_rel (Var n) (Var n)) ∧
[~Prim:]
  (∀op xs ys.
     LIST_REL force_delay_rel xs ys ⇒
       force_delay_rel (Prim op xs) (Prim op ys)) ∧
[~Monad:]
  (∀mop xs ys.
     LIST_REL force_delay_rel xs ys ⇒
       force_delay_rel (Monad mop xs) (Monad mop ys)) ∧
[~App:]
  (∀f g x y.
     force_delay_rel f g ∧
     force_delay_rel x y ⇒
       force_delay_rel (App f x) (App g y)) ∧
[~Lam:]
  (∀s x y.
     force_delay_rel x y ⇒
       force_delay_rel (Lam s x) (Lam s y)) ∧
[~Letrec:]
  (∀f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL force_delay_rel (MAP SND f) (MAP SND g) ∧
     force_delay_rel x y ⇒
     force_delay_rel (Letrec f x) (Letrec g y)) ∧
[~Let:]
  (∀opt x1 y1 x2 y2.
     force_delay_rel x1 x2 ∧
     force_delay_rel y1 y2 ⇒
     force_delay_rel (Let opt x1 y1) (Let opt x2 y2)) ∧
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     force_delay_rel x1 x2 ∧
     force_delay_rel y1 y2 ∧
     force_delay_rel z1 z2 ⇒
       force_delay_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[~Delay:]
  (∀x y.
     force_delay_rel x y ⇒
       force_delay_rel (Delay x) (Delay y)) ∧
[~Force:]
  (∀x y.
     force_delay_rel x y ⇒
     force_delay_rel (Force x) (Force y)) ∧
[~simp:]
   (∀x y.
     force_delay_rel x y ⇒
     force_delay_rel (Force (Delay x)) y) ∧
[~MkTick:]
  (∀x y. force_delay_rel x y ⇒ force_delay_rel (MkTick x) (MkTick y))
End

Theorem force_delay_rel_def =
  [“force_delay_rel (Var v) x”,
   “force_delay_rel (Value v) x”,
   “force_delay_rel (Prim op xs) x”,
   “force_delay_rel (Monad mop xs) x”,
   “force_delay_rel (App f x) y”,
   “force_delay_rel (Lam s x) y”,
   “force_delay_rel (Letrec f x) y”,
   “force_delay_rel (Let s x y) z”,
   “force_delay_rel (If x y z) w”,
   “force_delay_rel (Delay x) y”,
   “force_delay_rel (MkTick x) y”,
   “force_delay_rel (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once force_delay_rel_cases])
  |> LIST_CONJ;


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
[~Force:]
  (∀x y.
     exp_rel x y ⇒
     exp_rel (Force x) (Force y)) ∧
[~simp:]
   (∀x y.
     exp_rel x y ⇒
     exp_rel (Force (Delay x)) (Tick y)) ∧
[~MkTick:]
  (∀x y. exp_rel x y ⇒ exp_rel (MkTick x) (MkTick y)) ∧
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
[v_rel_Thunk:]
  (∀x y.
     exp_rel x y ⇒
     v_rel (Thunk x) (Thunk y)) ∧
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
  |> LIST_CONJ

Theorem ok_bind_subst[simp]: (* TODO : move *)
  ∀x. ok_bind x ⇒ ok_bind (subst ws x)
Proof
  Cases \\ rw [ok_bind_def] \\ gs [subst_def, ok_bind_def]
QED

Theorem exp_rel_freevars:
    ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
    completeInduct_on ‘exp_size x’ >> Cases >>
    gs [exp_size_def, exp_rel_def, PULL_EXISTS, freevars_def] >>
    rw [] >> gs []
    >- (AP_TERM_TAC >> AP_TERM_TAC >>
        irule LIST_EQ >> gs [LIST_REL_EL_EQN, EL_MAP] >>
        gen_tac >> strip_tac >> last_x_assum irule >>
        first_x_assum $ irule_at $ Pos last >> simp [] >>
        rename1 ‘EL x l’ >>
        ‘exp_size (EL x l) ≤ exp3_size l’ suffices_by gvs [] >>
        assume_tac exp_size_lemma >> fs [] >>
        first_x_assum irule >> gs [EL_MEM])
    >- (AP_TERM_TAC >> AP_TERM_TAC >>
        irule LIST_EQ >> gs [LIST_REL_EL_EQN, EL_MAP] >>
        gen_tac >> strip_tac >> last_x_assum irule >>
        first_x_assum $ irule_at $ Pos last >> simp [] >>
        rename1 ‘EL x l’ >>
        ‘exp_size (EL x l) ≤ exp3_size l’ suffices_by gvs [] >>
        assume_tac exp_size_lemma >> fs [] >>
        first_x_assum irule >> gs [EL_MEM])
    >- (MK_COMB_TAC >- (AP_TERM_TAC >> gs []) >> gs [])
    >- (AP_THM_TAC >> AP_TERM_TAC >> gs [])
    >- (AP_THM_TAC >> AP_TERM_TAC >>
        MK_COMB_TAC >- (AP_TERM_TAC >> gs []) >>
        AP_TERM_TAC >> AP_TERM_TAC >>
        irule LIST_EQ >> gs [LIST_REL_EL_EQN, EL_MAP] >>
        gen_tac >> strip_tac >>
        first_x_assum $ drule_then assume_tac >>
        pairarg_tac >> simp [] >>
        pairarg_tac >> gs [] >>
        last_x_assum irule >>
        first_x_assum $ irule_at $ Pos last >> simp [] >>
        rename [‘exp1_size l’, ‘EL i l’] >>
        ‘exp_size (SND (EL i l)) ≤ exp1_size l’ suffices_by gvs [] >>
        qpat_x_assum ‘LENGTH _ = LENGTH _’ $ assume_tac >>
        dxrule_then assume_tac EQ_SYM >>
        assume_tac exp_size_lemma >> gs [MEM_EL, PULL_EXISTS] >>
        first_x_assum $ drule_then assume_tac >> gs [])
    >~[‘Let opt _ _’]
    >- (Cases_on ‘opt’ >> gs [freevars_def]
        >- (MK_COMB_TAC >- (AP_TERM_TAC >> gs []) >> gs [])
        >- (MK_COMB_TAC
            >- (AP_TERM_TAC >> gs [])
            >- (AP_THM_TAC >> AP_TERM_TAC >> gs [])))
    >- (MK_COMB_TAC
        >- (AP_TERM_TAC >> MK_COMB_TAC >- (AP_TERM_TAC >> gs []) >> gs [])
        >- gs [])
    >- gs [freevars_def]
    >- gs [freevars_def, exp_size_def]
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
  >~ [‘Monad mop xs’] >- (
    rw [subst_def]
    \\ irule exp_rel_Monad
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
  >~ [‘Letrec f x’] >- (
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
   >~[‘Force (Delay _)’] >- (
    rw [subst_def]
    \\ ‘FILTER (λ(n,v). T) ws = ws’ suffices_by gs [exp_rel_simp]
    \\ rpt $ pop_assum kall_tac
    \\ Induct_on ‘ws’ \\ simp [FORALL_PROD])
  >~ [‘Delay x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Delay])
  >~ [‘Force x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Force])
  >~[‘MkTick x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_MkTick])
QED

Theorem exp_rel_eval_to[local]:
  ∀x y.
    exp_rel x y ⇒
      ($= +++ v_rel) (eval_to k x) (eval_to k y)
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
    \\ first_x_assum $ drule_then assume_tac \\ gs []
    \\ Cases_on ‘eval_to k x’ \\ gs []
    \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘v_rel w1 v1’
    \\ first_x_assum $ drule_then assume_tac \\ gs []
    \\ Cases_on ‘eval_to k f’
    \\ Cases_on ‘eval_to k g’ \\ gs []
    \\ rename1 ‘v_rel w2 v2’
    \\ Cases_on ‘dest_anyClosure v2’ \\ gs []
    >- (
      Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
      \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
      \\ gvs [OPTREL_def]
      \\ rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
      \\ last_x_assum $ dxrule_then assume_tac
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs [ok_bind_def])
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
    \\ last_x_assum $ qspec_then ‘k - 1’ irule \\ gs []
    \\ irule exp_rel_subst
    \\ Cases_on ‘w2’
    \\ gvs [dest_anyClosure_def, v_rel_def, subst_APPEND]
    \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
    \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
      by (irule LIST_REL_OPTREL
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
    \\ gvs [OPTREL_def]
    \\ rename1 ‘exp_rel x' y'’ \\ Cases_on ‘x'’ \\ gvs [exp_rel_def]
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ gs [LIST_REL_EL_EQN, EL_MAP]
    \\ gen_tac \\ strip_tac
    \\ pairarg_tac \\ fs []
    \\ pairarg_tac \\ fs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
    \\ rename1 ‘n < _’
    \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by simp []
    \\ gs [EL_MAP])
  >~ [‘Lam s x’] >- (
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def, v_rel_def])
  >~ [‘Let NONE x y’] >- (
    rw [exp_rel_def] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ rename1 ‘exp_rel x x2’ \\ rename1 ‘exp_rel y y2’
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
    \\ last_assum $ dxrule_then assume_tac
    \\ last_x_assum $ dxrule_then assume_tac
    \\ Cases_on ‘eval_to (k - 1) x2’
    \\ Cases_on ‘eval_to (k - 1) x’ \\ gs [])
  >~ [‘Let (SOME n) x y’] >- (
    rw [exp_rel_def] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ rename1 ‘exp_rel x x2’ \\ rename1 ‘exp_rel y y2’
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
    \\ last_x_assum assume_tac
    \\ last_assum $ dxrule_then assume_tac
    \\ Cases_on ‘eval_to (k - 1) x2’
    \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
    \\ last_x_assum irule
    \\ irule exp_rel_subst \\ gs [])
  >~ [‘Letrec f x’] >- (
    rw [exp_rel_def] \\ gs []
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
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
  >~ [‘If x1 y1 z1’] >- (
    rw [exp_rel_def, eval_to_def] \\ gs [eval_to_def]
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’ \\ rename1 ‘exp_rel z1 z2’
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ last_x_assum kall_tac
    \\ rpt $ first_assum $ dxrule_then assume_tac
    \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gvs []
    \\ Cases_on ‘eval_to (k - 1) x2’
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
    \\ rename1 ‘v_rel v1 w1’
    \\ IF_CASES_TAC \\ gvs [v_rel_def]
    \\ IF_CASES_TAC \\ gvs [v_rel_def]
    \\ IF_CASES_TAC \\ gs []
    >- (Cases_on ‘v1’ \\ gs [v_rel_def])
    \\ IF_CASES_TAC \\ gvs []
    >- (Cases_on ‘v1’ \\ gs [v_rel_def]))
  >~ [‘Force x’] >- (
    rw [exp_rel_def] \\ gs []
    >~[‘Force (Delay x)’] >- (
        once_rewrite_tac [eval_to_def]
        \\ IF_CASES_TAC \\ simp []
        \\ simp [Once eval_to_def, dest_anyThunk_def]
        \\ simp [subst_funs_def, subst_empty])
    \\ rename1 ‘exp_rel x y’
    \\ once_rewrite_tac [eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
    \\ last_x_assum $ dxrule_then assume_tac
    \\ Cases_on ‘eval_to k y’ \\ Cases_on ‘eval_to k x’ \\ gs []
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
          \\ rename1 ‘exp_rel x0 y0’
          \\ ‘MEM (s, x0) xs’ by (rpt $ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [])
          \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
          \\ first_assum $ dxrule_then assume_tac
          \\ Cases_on ‘x0’ \\ gvs [ok_bind_def, exp_rel_def]
          >~[‘subst_funs ys e2’]
          >- (last_x_assum irule \\ simp [subst_funs_def]
              \\ irule exp_rel_subst \\ simp []
              \\ gs [FORALL_PROD]
              \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
              \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
              \\ gs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
              \\ rw []
              >- (
                 rename [‘n < _’, ‘MAP FST xs = MAP FST ys’]
                 \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gs []
                 \\ gvs [EL_MAP])
              \\ last_x_assum $ drule_then irule))
      \\ gs [subst_funs_def, subst_empty])
    \\ Cases_on ‘v’ \\ gs [v_rel_def, exp_rel_def, PULL_EXISTS, dest_Tick_def])
  >~ [‘Delay x’] >- (
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def, v_rel_def])
  >~ [‘MkTick x’] >- (
    rw [exp_rel_def] \\ gs []
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum $ drule_then assume_tac
    \\ Cases_on ‘eval_to k y’ \\ Cases_on ‘eval_to k x’ \\ gs [v_rel_def])
  >~ [‘Prim op xs’] >- (
    rw []
    \\ gvs [Once exp_rel_def, eval_to_def]
    \\ gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      last_x_assum kall_tac
      \\ ‘($= +++ LIST_REL v_rel) (result_map (eval_to k) xs)
                                      (result_map (eval_to k) ys)’
        suffices_by (
          strip_tac \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map (eval_to k) ys’
          \\ Cases_on ‘result_map (eval_to k) xs’ \\ gs [v_rel_def])
      \\ gvs [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum (drule_all_then assume_tac)
        \\ first_x_assum $ drule_all_then assume_tac
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gvs []
        \\ rw [] \\ gs [SF SFY_ss])
      \\ ‘∀n. n < LENGTH ys ⇒
            ($= +++ v_rel) (eval_to k (EL n xs))
                               (eval_to k (EL n ys))’
        by rw []
      \\ last_x_assum kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        >- (
          first_x_assum $ drule_then assume_tac
          \\ last_x_assum $ drule_then assume_tac
          \\ rename1 ‘eval_to _ (EL m ys) = INL Type_error’
          \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs [])
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
        \\ IF_CASES_TAC \\ gvs [])
      \\ rw [] \\ gs [SF SFY_ss]
      >- (
        first_x_assum $ drule_then assume_tac \\ gs []
        \\ rename1 ‘n < _’
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      >- (
        first_x_assum $ drule_then assume_tac \\ gs []
        \\ rename1 ‘n < _’
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
      >- (
        gvs [EVERY2_MAP, LIST_REL_EL_EQN] \\ rw []
        \\ first_x_assum (drule_all_then assume_tac)
        \\ Cases_on ‘eval_to k (EL n ys)’
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gvs []
        \\ rename1 ‘INL err’ \\ Cases_on ‘err’ \\ gs []))
    >- ((* IsEq *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs []
      \\ rw [v_rel_def])
    >- ((* Proj *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘exp_rel x y’
      \\ IF_CASES_TAC \\ gs []
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs [])
    >- ((* AtomOp *)
      Cases_on ‘k = 0’ \\ gs []
      >- (
        rw [result_map_def, MEM_MAP, MEM_EL, PULL_EXISTS]
        \\ Cases_on ‘ys = []’ \\ gs []
        >- (
          CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
        \\ ‘xs ≠ []’ by (strip_tac \\ gs [])
        \\ first_x_assum (qspec_then ‘0’ assume_tac) \\ gs [])
      \\ qmatch_goalsub_abbrev_tac ‘result_map f ys’
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
      \\ last_x_assum kall_tac \\ gvs []
      \\ ‘result_map f xs = result_map f ys’
        suffices_by (
          strip_tac \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map f ys’ \\ gs []
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_rel_def])
      \\ unabbrev_all_tac
      \\ simp [result_map_def, MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss]
      \\ Cases_on ‘k’ \\ gs [arithmeticTheory.ADD1]
      \\ rename1 ‘eval_to k’
      \\ ‘∀n. n < LENGTH ys ⇒
            ($= +++ v_rel) (eval_to k (EL n xs))
                               (eval_to k (EL n ys))’
        by rw []
      \\ qpat_x_assum ‘∀x y. exp_rel _ _ ⇒ _’ kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        rename1 ‘m < LENGTH ys’
        \\ first_x_assum $ drule_all_then assume_tac
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ rw [] \\ gs []
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to k (EL m ys)’
        \\ Cases_on ‘eval_to k (EL m xs)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
      \\ ‘∀n. n < LENGTH ys ⇒ eval_to k (EL n ys) = INL Diverge ∨
                              ∃x. eval_to k (EL n ys) = INR (Atom x)’
        by (rw [DISJ_EQ_IMP]
            \\ first_x_assum drule
            \\ first_x_assum $ qspec_then ‘n’ assume_tac
            \\ rw [CaseEqs ["sum", "v"]]
            \\ Cases_on ‘eval_to k (EL n xs)’
            \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs []
            >~ [‘INL err’] >- (
              Cases_on ‘err’ \\ gs [])
            \\ rename1 ‘v_rel x _’
            \\ Cases_on ‘x’ \\ gs [v_rel_def])
      \\ qpat_x_assum ‘∀n. _ ⇒ ¬( _ < _)’ kall_tac
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        >- (
          first_x_assum $ drule_then assume_tac \\ gs [])
        \\ rename1 ‘n < LENGTH ys’
        \\ first_assum $ irule_at Any
        \\ last_x_assum $ drule_then assume_tac
        \\ last_x_assum $ drule_then assume_tac
        \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs []
        >- (
          Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
        \\ rename1 ‘INR y’ \\ Cases_on ‘y’ \\ gs [])
      \\ IF_CASES_TAC \\ gs []
      >- (
        first_x_assum $ drule_then assume_tac \\ gs [])
      \\ strip_tac
      >- (gen_tac \\ strip_tac \\ strip_tac
          \\ rpt $ last_x_assum $ drule_then assume_tac \\ gs []
          \\ rename1 ‘n < _’
          \\ last_x_assum $ qspec_then ‘n’ mp_tac \\ simp []
          \\ CASE_TAC \\ gs [])
      \\ AP_TERM_TAC \\ irule LIST_EQ \\ gs [EL_MAP]
      \\ gen_tac \\ strip_tac \\ rename1 ‘n < _’
      \\ rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gs []
      \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs []
      \\ CASE_TAC \\ gs [v_rel_def]))
  >~ [‘Monad mop xs’] >- (
    rw [Once exp_rel_cases] \\ gs []
    \\ simp [eval_to_def, v_rel_def])
QED

Theorem exp_rel_eval:
  exp_rel x y ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ simp [eval_def]
  \\ dxrule_then assume_tac exp_rel_eval_to \\ simp []
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ rw [] \\ gs []
  \\ rename1 ‘_ (eval_to k x) (eval_to j y)’
  \\ first_x_assum (qspec_then ‘MAX k j’ assume_tac)
  \\ ‘eval_to (MAX k j) x = eval_to k x’
    by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
  \\ ‘eval_to (MAX k j) y = eval_to j y’
    by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
  \\ gs []
QED

Theorem exp_rel_apply_closure[local]:
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

Theorem exp_rel_rel_ok[local]:
  rel_ok T v_rel exp_rel
Proof
  rw [rel_ok_def, v_rel_def, exp_rel_def]
  \\ rw [exp_rel_apply_closure]
QED

Theorem exp_rel_sim_ok[local]:
  sim_ok T v_rel exp_rel
Proof
  rw [sim_ok_def, exp_rel_eval, exp_rel_subst]
QED

Theorem exp_rel_semantics[local]:
  exp_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics \\ gs []
  \\ first_assum (irule_at Any)
  \\ qexists_tac ‘T’ \\ gs []
  \\ irule_at Any exp_rel_rel_ok
  \\ irule_at Any exp_rel_sim_ok
QED

Theorem force_delay_rel_comp:
  ∀ x z. force_delay_rel x z ⇒ ∃y. exp_rel x y ∧ clean_rel y z
Proof
  ho_match_mp_tac force_delay_rel_ind \\ rw []
  \\ gs [exp_rel_def, clean_rel_def, PULL_EXISTS]
  >- (
    first_x_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘xs’ \\ rw [PULL_EXISTS]
    \\ last_x_assum $ drule_then assume_tac \\ gs []
    \\ rpt $ last_x_assum $ irule_at Any)
  >- (
    first_x_assum mp_tac
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘xs’ \\ rw [PULL_EXISTS]
    \\ last_x_assum $ drule_then assume_tac \\ gs []
    \\ rpt $ last_x_assum $ irule_at Any)
  >- rpt $ last_x_assum $ irule_at Any
  >- rpt $ last_x_assum $ irule_at Any
  >- (
    first_x_assum $ irule_at Any \\ simp []
    \\ rename1 ‘MAP FST f = MAP FST g’
    \\ ‘∃h. MAP FST f = MAP FST h ∧ EVERY ok_bind (MAP SND h) ∧
            LIST_REL exp_rel (MAP SND f) (MAP SND h) ∧
            LIST_REL clean_rel (MAP SND h) (MAP SND g)’
      by (
        pop_assum kall_tac \\ last_x_assum kall_tac
        \\ rpt $ first_x_assum $ mp_tac
        \\ qabbrev_tac ‘g' = MAP SND g’ \\ pop_assum kall_tac
        \\ qid_spec_tac ‘g'’ \\ Induct_on ‘f’ \\ gs [PULL_EXISTS, FORALL_PROD, PULL_FORALL]
        \\ rw []
        \\ last_x_assum $ dxrule_all_then assume_tac \\ gs []
        \\ Q.REFINE_EXISTS_TAC ‘(_, _) :: _’ \\ simp []
        \\ rpt $ first_assum $ irule_at Any \\ simp []
        \\ rename1 ‘exp_rel x y’ \\ Cases_on ‘x’ \\ gs [exp_rel_def, ok_bind_def])
    \\ qexists_tac ‘h’ \\ simp []
    \\ rw []
    >- (metis_tac [])
    >- (disj1_tac \\ metis_tac []))
  >- metis_tac []
  >- metis_tac []
  >- metis_tac []
  >- (
    Q.REFINE_EXISTS_TAC ‘Force _’ \\ gs [clean_rel_def]
    \\ metis_tac [])
  >- (
    Q.REFINE_EXISTS_TAC ‘Tick _’ \\ gs [clean_rel_def]
    \\ first_x_assum $ irule_at Any \\ gs [])
  >- metis_tac []
QED

Theorem force_delay_semantics:
  force_delay_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ dxrule_then assume_tac force_delay_rel_comp \\ gs []
  \\ drule_then assume_tac exp_rel_freevars
  \\ dxrule_then assume_tac exp_rel_semantics
  \\ dxrule_then assume_tac clean_rel_semantics
  \\ gs [closed_def]
QED

val _ = export_theory ();
