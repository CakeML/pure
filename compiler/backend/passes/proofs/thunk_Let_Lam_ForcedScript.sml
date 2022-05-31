(*
 Relation to rewrite function definitions to remove Delay
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory;

val _ = new_theory "thunk_Let_Lam_Forced";

Definition ok_bind_def:
  ok_bind (Lam s e) = T ∧
  ok_bind (Delay e) = T ∧
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
[~Let_Lams_Force_Var:]
  (∀v1 v2 vL1 vL2 s s2 x1 x2 y1 y2.
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧
     ALL_DISTINCT (vL1 ++ s::vL2) ∧
     ¬MEM v2 (vL1 ++ s::vL2) ∧ ¬MEM s2 (vL1 ++ s::vL2) ∧
     v2 ≠ v1 ∧ v2 ≠ s2 ∧ s ≠ s2 ∧
     s ∉ freevars x1 ∧
     exp_rel x1 x2 ∧ exp_rel y1 y2 ⇒
     exp_rel (Let (SOME v1)
              (Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) x1))
              y1)
             (Let (SOME v2)
              (Lams (vL1 ++ s2::vL2) x2)
              (Let (SOME v1)
                  (Lams (vL1 ++ s::vL2) (Apps (Var v2) (MAP Var vL1 ++ Tick (Force (Var s))::MAP Var vL2))) y2))) ∧
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
[v_rel_Closure_Force_TL:]
  (∀eL1 eL2 vL1 vL2 vL3 s s2 x y.
     ALL_DISTINCT (s2::vL1 ++ vL2 ++ s::vL3) ∧
     LENGTH vL1 = LENGTH eL1 ∧
     LIST_REL v_rel eL1 eL2 ∧
     s ∉ freevars x ∧
     exp_rel x y ⇒
     v_rel (Closure (HD (SNOC s vL2))
            (Lams (TL (vL2++s::vL3)) (subst (ZIP (vL1, eL1)) (Let (SOME s2) (Force (Var s)) x))))
           (Closure (HD (SNOC s vL2)) (Lams (TL (vL2 ++ s::vL3))
                                       (Apps (Value (Closure (HD (vL1++vL2++s2::vL3))
                                                              (Lams (TL (vL1++vL2++s2::vL3)) y)))
                                        (MAP Value eL2 ++ MAP Var vL2 ++ (Tick (Force (Var s)))::MAP Var vL3))))) ∧
[v_rel_Closure_Force_HD:]
  (∀eL1 eL1' eL2 eL2' e e' vL1 vL2 vL3 s s2 x y.
     ALL_DISTINCT (s2::vL1 ++ vL2 ++ s::vL3) ∧
     LENGTH vL1 = LENGTH eL1 ∧ LENGTH vL2 = LENGTH eL2 ∧
     LIST_REL v_rel eL1 eL1' ∧ LIST_REL v_rel eL2 eL2' ∧ v_rel e e' ∧
     vL3 ≠ [] ∧
     s ∉ freevars x ∧
     exp_rel x y ⇒
     v_rel (Closure (HD vL3)
            (Lams (TL vL3) (subst (ZIP (vL1 ++ vL2, eL1 ++ eL2)) (Let (SOME s2) (Force (Value e)) x))))
           (Closure (HD vL3) (Lams (TL vL3)
                                       (Apps (Value (Closure (HD (vL1++s2::vL2++vL3))
                                                              (Lams (TL (vL1++s2::vL2++vL3)) y)))
                                        (MAP Value eL1' ++ (Tick (Force (Value e')))::MAP Value eL2'
                                         ++ MAP Var vL3))))) ∧
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

Theorem freevars_Lams:
  ∀l e. freevars (Lams l e) = freevars e DIFF (set l)
Proof
  Induct >> gvs [freevars_def, DIFF_INTER_COMPL] >>
  gvs [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem subst_Lams:
  ∀l e b. subst b (Lams l e) = Lams l (subst (FILTER (λ(v,e). ¬MEM v l) b) e)
Proof
  Induct >> gvs [subst_def, GSYM LAMBDA_PROD, FILTER_T, FILTER_FILTER] >>
  gvs [LAMBDA_PROD, CONJ_COMM]
QED

Theorem subst_Apps:
  ∀l e b. subst b (Apps e l) = Apps (subst b e) (MAP (subst b) l)
Proof
  Induct >> gvs [subst_def]
QED

Theorem freevars_Apps:
  ∀l e. freevars (Apps e l) = freevars e ∪ BIGUNION (set (MAP freevars l))
Proof
  Induct >> gvs [freevars_def, UNION_ASSOC]
QED

Theorem boundvars_Lams:
  ∀l e. boundvars (Lams l e) = boundvars e ∪ (set l)
Proof
  Induct >> gvs [boundvars_def] >>
  once_rewrite_tac [INSERT_SING_UNION] >>
  rw [SET_EQ_SUBSET, SUBSET_DEF]
QED

Theorem boundvars_Apps:
  ∀l e. boundvars (Apps e l) = boundvars e ∪ BIGUNION (set (MAP boundvars l))
Proof
  Induct >> gvs [boundvars_def, UNION_ASSOC]
QED

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
  ‘(∀x y. exp_rel x y ⇒ freevars x = freevars y) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw [] >>
  ho_match_mp_tac exp_rel_strongind >>
  gvs [exp_rel_def, PULL_EXISTS, freevars_def] >> rw []
  >- (AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      gvs [LIST_REL_EL_EQN, MEM_EL, EL_MAP, PULL_EXISTS])
  >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
      AP_TERM_TAC >> irule LIST_EQ >>
      gvs [MEM_EL, PULL_EXISTS, EL_MAP, LIST_REL_EL_EQN] >>
      rw [] >>
      last_x_assum $ dxrule_then assume_tac >>
      pairarg_tac >> gs [] >> pairarg_tac >> gvs [])
  >~[‘Let opt _ _’]
  >- (Cases_on ‘opt’ >> gvs [freevars_def])
  >- (gvs [freevars_Lams, freevars_def, freevars_Apps] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF]
      >- (gvs [] >> disj1_tac >>
          strip_tac >> first_x_assum irule >>
          gvs [MEM_LUPDATE, EL_MEM])
      >- (gvs [MAP_SNOC, MEM_SNOC, freevars_def] >>
          gvs [MEM_EL, EL_MAP, freevars_def])
      >- gvs [MEM_MAP, freevars_def]
      >- gvs [])
QED

Theorem exp_rel_boundvars:
  ∀x y. exp_rel x y ⇒ boundvars x ⊆ boundvars y
Proof
  ‘(∀x y. exp_rel x y ⇒ boundvars x ⊆ boundvars y) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw [] >>
  ho_match_mp_tac exp_rel_strongind >>
  gvs [exp_rel_def, PULL_EXISTS, boundvars_def] >> rw []
  >- (gvs [SUBSET_DEF, IN_BIGUNION, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >>
      rw [] >> first_assum $ irule_at Any >>
      gvs [EL_MAP] >>
      metis_tac [])
  >~[‘Force (Var _)’]
  >- (gvs [boundvars_Lams, boundvars_Apps, boundvars_def, SUBSET_DEF] >>
      rw [] >> gvs [MEM_SNOC, MAP_SNOC])
  >~[‘Let opt _ _’]
  >- (Cases_on ‘opt’ >> gvs [boundvars_def, SUBSET_DEF] >>
      rw [] >> gvs [])
  >- gvs [SUBSET_DEF]
  >- gvs [SUBSET_DEF]
  >- gvs [SUBSET_DEF]
  >- gvs [SUBSET_DEF]
  >- (gvs [SUBSET_DEF, IN_BIGUNION, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >>
      rw [] >> disj1_tac >> disj2_tac >>
      first_assum $ irule_at Any >>
      gvs [EL_MAP] >>
      pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
      first_x_assum $ dxrule_then assume_tac >>
      gvs []) >>
  gvs [SUBSET_DEF]
QED

Theorem LIST_FILTERED:
  ∀l1 l2 R f. MAP FST l1 = MAP FST l2 ∧ LIST_REL R (MAP SND l1) (MAP SND l2)
              ⇒ MAP FST (FILTER (λ(n, v). f n) l1) = MAP FST (FILTER (λ(n,v). f n) l2)
                ∧ LIST_REL R (MAP SND (FILTER (λ(n, v). f n) l1)) (MAP SND (FILTER (λ(n,v). f n) l2))
Proof
  Induct >> gvs [] >>
  PairCases >> Cases >> gvs [] >>
  rename1 ‘FST pair’ >> PairCases_on ‘pair’ >> rw [] >>
  last_x_assum $ dxrule_then $ dxrule_then assume_tac >>
  gvs []
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
    \\ ‘∀x f. ok_bind x ⇒ ok_bind (subst f x)’
      by (Cases \\ gs [ok_bind_def, subst_def]) (*ho_match_mp_tac subst_ind
          \\ rw [subst_def])*)
    \\ gvs [EVERY_EL, ELIM_UNCURRY]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ first_assum irule
    \\ gvs [MAP_FST_FILTER, LAMBDA_PROD]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~[‘Force (Var _)’]
  >- (gvs [subst_def, subst_Lams, subst_Apps, MAP_SNOC, GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
      gvs [EL_MEM, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      rename1 ‘Lams (vL1 ++ s::vL2) _’ >>
      ‘∀w. MAP (λx. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) w) (Var x)) vL1 = MAP Var vL1’
        by (gen_tac >> irule LIST_EQ >>
            gvs [EL_MAP, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
      ‘∀w. MAP (λx. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) w) (Var x)) vL2 = MAP Var vL2’
        by (gen_tac >> irule LIST_EQ >>
            gvs [EL_MAP, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
      rw [] >>
      irule exp_rel_Let_Lams_Force_Var >>
      gvs [boundvars_subst, freevars_subst, FILTER_FILTER, LAMBDA_PROD, PULL_EXISTS] >>
      conj_tac
      >- (rename1 ‘exp_rel _ (subst (FILTER _ ws) y)’ >>
          qspecl_then [‘FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s2 ∧ ¬MEM v vL2) ws’, ‘y’, ‘{s}’] assume_tac
                      $ GSYM subst_remove >>
          rpt $ dxrule_then assume_tac exp_rel_freevars >>
          gvs [FILTER_FILTER, LAMBDA_PROD] >>
          ‘∀p. (p ≠ s2 ∧ ¬MEM p vL1 ∧ p ≠ s ∧ ¬MEM p vL2) = (p ≠ s ∧ ¬MEM p vL1 ∧ p ≠ s2 ∧ ¬MEM p vL2)’
            by metis_tac [] >>
          gvs [] >>
          first_x_assum irule >>
          gvs [MAP_FST_FILTER, EVERY2_MAP] >>
          qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λv. v ≠ s ∧ ¬MEM v vL1 ∧ v ≠ s2 ∧ ¬MEM v vL2’] assume_tac
                      $ GEN_ALL LIST_REL_FILTER >>
          gvs [] >>
          pop_assum irule >>
          gvs [LIST_REL_EL_EQN])
      >- (rename1 ‘exp_rel _ (subst (FILTER _ ws) y2)’ >>
          qspecl_then [‘FILTER (λ(v,e). v ≠ v1) ws’, ‘y2’, ‘{v2}’] assume_tac subst_remove >>
          rpt $ dxrule_then assume_tac exp_rel_freevars >>
          gvs [FILTER_FILTER, LAMBDA_PROD, CONJ_COMM] >>
          first_x_assum irule >>
          gvs [MAP_FST_FILTER, EVERY2_MAP] >>
          qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λv. v ≠ v1’] assume_tac
                      $ GEN_ALL LIST_REL_FILTER >>
          gvs [] >>
          first_x_assum irule >>
          gvs [LIST_REL_EL_EQN]))
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
  >~[‘MkTick x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_MkTick])
QED

Theorem eval_to_Lams:
  ∀(l : string list) k e. l ≠ [] ⇒ eval_to k (Lams l e) = INR (Closure (HD l) (Lams (TL l) e))
Proof
  Cases >> gvs [eval_to_def]
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

Theorem eval_to_Apps_Lams_not_0:
  ∀vL eL e k. vL ≠ [] ∧ LENGTH vL = LENGTH eL ∧ k ≠ 0 ⇒
              eval_to k (Apps (Value (Closure (HD vL) (Lams (TL vL) e)))
                                       (MAP Value eL))
              = eval_to (k - 1) (subst (ZIP (vL, eL)) e)
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  qspecl_then [‘eL’] assume_tac SNOC_CASES >> gvs [ADD1] >>
  rename1 ‘SNOC v vL’ >> Cases_on ‘vL’ >> gvs []
  >- gvs [eval_to_def, dest_anyClosure_def] >>
  gvs [FOLDR_SNOC, FOLDL_APPEND, eval_to_def] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  first_x_assum $ qspecl_then [‘eL’, ‘Lam v e’, ‘k’] assume_tac >>
  gvs [subst_def, eval_to_def, dest_anyClosure_def] >>
  AP_TERM_TAC >>
  irule EQ_TRANS >> irule_at Any subst_commutes >>
  conj_tac >- rw [MAP_FST_FILTER, MAP_ZIP, MEM_FILTER] >>
  qspecl_then [‘ZIP (h::vL, eL)’, ‘subst1 v x' e’, ‘{v}’] mp_tac subst_remove >> impl_tac
  >- gvs [freevars_subst] >>
  rw [GSYM subst_APPEND] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  first_x_assum kall_tac >> first_x_assum kall_tac >>
  once_rewrite_tac [CONS_APPEND] >>
  once_rewrite_tac [APPEND_SNOC] >>
  once_rewrite_tac [SNOC_APPEND] >>
  qspecl_then [‘[h]++vL’, ‘eL’, ‘[v]’, ‘[x']’] assume_tac ZIP_APPEND >>
  gvs [ZIP]
QED

Theorem eval_to_Apps_Lams_0:
  ∀vL eL e k. vL ≠ [] ∧ LENGTH vL = LENGTH eL ⇒
              eval_to 0 (Apps (Value (Closure (HD vL) (Lams (TL vL) e)))
                                       (MAP Value eL))
              = INL Diverge
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  qspecl_then [‘eL’] assume_tac SNOC_CASES >> gvs [ADD1] >>
  rename1 ‘SNOC v vL’ >> Cases_on ‘vL’ >> gvs []
  >- (gvs [eval_to_def, dest_anyClosure_def]) >>
  gvs [FOLDR_SNOC, FOLDL_APPEND, eval_to_def]
QED

Theorem eval_to_Apps_APPEND1:
  ∀lst k v f eL. eval_to k lst = INR v ⇒ eval_to k (Apps f (eL ++ [lst])) = eval_to k (Apps f (eL ++ [Value v]))
Proof
  rw [FOLDL_APPEND, eval_to_def]
QED

Theorem eval_to_Apps_INL:
  ∀eL2 mid k f eL1 e. eval_to k mid = INL e ⇒ eval_to k (Apps f (eL1 ++ mid::MAP Value eL2)) = INL e
Proof
  Induct using SNOC_INDUCT \\ gvs [FOLDL_SNOC, MAP_SNOC]
  >- (gvs [FOLDL_APPEND]
      \\ once_rewrite_tac [eval_to_def]
      \\ gvs [])
  \\ once_rewrite_tac [GSYM SNOC]
  \\ once_rewrite_tac [APPEND_SNOC]
  \\ once_rewrite_tac [FOLDL_SNOC]
  \\ once_rewrite_tac [eval_to_def]
  \\ rw []
  \\ first_x_assum $ dxrule_then assume_tac
  \\ gvs [eval_to_def]
QED

Theorem eval_to_Apps_INR:
  ∀eL2 mid k f eL1 v. eval_to k mid = INR v ⇒
                      eval_to k (Apps f (eL1 ++ mid::MAP Value eL2)) =
                      eval_to k (Apps f (eL1 ++ Value v::MAP Value eL2))
Proof
  Induct using SNOC_INDUCT \\ gvs [FOLDL_SNOC, MAP_SNOC]
  >- (gvs [FOLDL_APPEND]
      \\ once_rewrite_tac [eval_to_def] \\ rw []
      \\ once_rewrite_tac [eval_to_def] \\ gvs [])
  \\ once_rewrite_tac [GSYM SNOC]
  \\ once_rewrite_tac [APPEND_SNOC]
  \\ once_rewrite_tac [FOLDL_SNOC]
  \\ once_rewrite_tac [eval_to_def]
  \\ rw []
  \\ first_x_assum $ dxrule_then assume_tac
  \\ gvs []
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ⇒
      ∃j. ($= +++ v_rel) (eval_to k x) (eval_to (j + k) y)
Proof
 ho_match_mp_tac eval_to_ind \\ rw []
  >~ [‘Var m’] >- (
    gvs [Once exp_rel_def]
    \\ qexists_tac ‘0’
    \\ simp [eval_to_def])
  >~ [‘Value v’] >- (
    gvs [Once exp_rel_def]
    \\ qexists_tac ‘0’
    \\ simp [eval_to_def])
  >~ [‘Lam s x’] >- (
    gvs [Once exp_rel_def]
    \\ qexists_tac ‘0’
    \\ gvs [eval_to_def, v_rel_Closure])
  >~ [‘App f x’] >- (
    gvs [Once exp_rel_def, eval_to_def]
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
    \\ Cases_on ‘∃vname e. v2 = Closure vname e’

    >- (gvs [v_rel_def, dest_anyClosure_def]
        >- (IF_CASES_TAC \\ gvs []
            >- (qexists_tac ‘0’ \\ gvs []
                \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
                \\ gvs [])
            \\ rename1 ‘eval_to (k - 1) (subst1 s v1 body)’
            \\ rename1 ‘v_rel v1 w1’ \\ rename1 ‘exp_rel body body'’
            \\ last_x_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘body’, ‘subst1 s w1 body'’] mp_tac
            \\ impl_tac
            >- (gvs [] \\ irule exp_rel_subst \\ gvs [])
            \\ disch_then $ qx_choose_then ‘j2’ assume_tac
            \\ Cases_on ‘eval_to (k - 1) (subst1 s v1 body) = INL Diverge’
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k y’ \\ gvs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g’ \\ gvs []
                \\ Cases_on ‘eval_to (k - 1) (subst1 s w1 body') = INL Diverge’ \\ gs []
                \\ drule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                \\ gvs [])
            \\ qexists_tac ‘j + j1 + j2’
            \\ first_x_assum $ qspecl_then [‘j + j2’] assume_tac
            \\ first_x_assum $ qspecl_then [‘j1 + j2’] assume_tac
            \\ gvs []
            \\ Cases_on ‘eval_to (j2 + k - 1) (subst1 s w1 body') = INL Diverge’ \\ gs []
            >- (Cases_on ‘eval_to (k - 1) (subst1 s v1 body)’ \\ gvs [])
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + k - 1’] assume_tac) eval_to_mono
            \\ gvs [])
        >- (IF_CASES_TAC \\ gvs []
            >- (qexists_tac ‘0’ \\ gvs []
                \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
                \\ gvs [])
            \\ Cases_on ‘vL2’ \\ gvs []
            >- (gvs [subst_Lams, ALL_DISTINCT_APPEND]
                \\ rename1 ‘subst1 s v1 (subst _ (Let _ _ x2))’
                \\ Cases_on ‘vL3 = []’ \\ gvs [eval_to_Lams]
                >- (last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Letrec [] (Force (Value v1))’,
                                                    ‘Letrec [] (Force (Value w1))’] mp_tac
                    \\ impl_tac
                    >- (gvs [subst1_def] \\ irule exp_rel_Letrec
                        \\ gvs [exp_rel_def])
                    \\ disch_then $ qx_choose_then ‘j2’ assume_tac
                    \\ gvs [subst_def]
                    \\ CASE_TAC >~[‘ALOOKUP _ _ = SOME _’]
                    >- (dxrule_then assume_tac ALOOKUP_MEM \\ gvs []
                        \\ gvs [MEM_EL, EL_ZIP])
                    \\ gvs [subst1_def, subst1_notin_frees, freevars_subst]
                    \\ once_rewrite_tac [eval_to_def]
                    \\ IF_CASES_TAC \\ gvs []
                    >- (qexists_tac ‘0’ \\ gvs []
                        \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                        \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
                        \\ Cases_on ‘eval_to k y’ \\ gvs []
                        \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                        \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
                        \\ Cases_on ‘eval_to k g’ \\ gvs [subst_Apps, subst1_def, FOLDL_APPEND]
                        \\ once_rewrite_tac [eval_to_def]
                        \\ once_rewrite_tac [eval_to_def]
                        \\ gvs [])
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value v1)) = INL Diverge’
                    >- (qexists_tac ‘0’ \\ gvs []
                        \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                        \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
                        \\ Cases_on ‘eval_to k y’ \\ gvs []
                        \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                        \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
                        \\ Cases_on ‘eval_to k g’ \\ gvs [subst_Apps, subst1_def, FOLDL_APPEND]
                        \\ ‘∀e. eval_to (k - 1) (Tick e) = eval_to (k - 2) e’
                          by (gen_tac \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def])
                        \\ ‘∀e. eval_to (j2 + k - 1) (Tick e) = eval_to (j2 + k - 2) e’
                          by (gen_tac \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def])
                        \\ gvs []
                        \\ once_rewrite_tac [eval_to_def]
                        \\ gvs []
                        \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gs []
                        \\ dxrule_then (qspecl_then [‘j2 + k - 2’] assume_tac) eval_to_mono
                        \\ gvs []
                        \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs [])
                    \\ ‘∀k e. k > 1 ⇒ eval_to (k - 1) (Tick e) = eval_to (k - 2) e’
                      by (rw [] \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def])
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value v1))’
                    >~[‘INL _’]
                    >- (qexists_tac ‘j + j1 + j2’
                        \\ last_x_assum $ qspecl_then [‘j1 + j2’] assume_tac
                        \\ last_x_assum $ qspecl_then [‘j + j2’] assume_tac
                        \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, FOLDL_APPEND]
                        \\ gvs [SF ETA_ss]
                        \\ once_rewrite_tac [eval_to_def]
                        \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
                        \\ dxrule_then (qspecl_then [‘j + j1 + j2 + k - 2’] assume_tac) eval_to_mono
                        \\ gvs []
                        \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs [])
                    \\ gvs []
                    \\ rename1 ‘eval_to (k - 2) (Force (Value v1)) = INR v2’
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
                    \\ ‘∀j3. eval_to (j + j1 + j2 + j3 + k - 2) (Force (Value w1))
                             = eval_to (j2 + k - 2) (Force (Value w1))’
                      by (gen_tac \\ irule eval_to_mono \\ gvs [])
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs []
                    \\ rename1 ‘v_rel v2 w2’ \\ rename1 ‘exp_rel x2 y2’
                    \\ ‘subst1 s2 v2 (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1, eL1))) x2) =
                        subst (ZIP (vL1, eL1)) (subst1 s2 v2 x2)’
                      by (irule EQ_TRANS \\ irule_at Any subst_commutes
                          \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP]
                          \\ AP_THM_TAC \\ AP_TERM_TAC
                          \\ gvs [FILTER_EQ_ID, EVERY_EL, MEM_EL, EL_ZIP]
                          \\ rw [] \\ rename1 ‘n < _’
                          \\ rpt $ first_x_assum $ qspecl_then [‘n’] assume_tac \\ gvs [])
                    \\ gvs []
                    \\ last_x_assum $ qspecl_then [‘ZIP (vL1, eL1)’, ‘s2’, ‘v2’, ‘Tick x2’,
                                                   ‘subst (ZIP(vL1, eL2) ++ [(s2, w2)]) (Tick y2)’] mp_tac
                    \\ impl_tac
                    >- (gvs [subst_APPEND]
                        \\ irule exp_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                        \\ irule exp_rel_subst \\ gvs [exp_rel_def])
                    \\ disch_then $ qx_choose_then ‘j3’ assume_tac
                    \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1, eL1)) (subst1 s2 v2 x2)) = INL Diverge’
                    >- (qexists_tac ‘0’
                        \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                        \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
                        \\ Cases_on ‘eval_to k y’ \\ gs []
                        \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                        \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
                        \\ Cases_on ‘eval_to k g’ \\ gs []
                        \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
                        \\ Cases_on ‘eval_to (k - 1) (Tick (Force (Value w1))) = INL Diverge’
                        >- (gvs [FOLDL_APPEND] \\ once_rewrite_tac [eval_to_def]
                            \\ gvs [])
                        \\ qspecl_then [‘Tick (Force (Value w1))’, ‘k - 1’] assume_tac eval_to_Apps_APPEND1
                        \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                        \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs []
                        \\ qspecl_then [‘vL1 ++ [s2]’, ‘eL2 ++ [w2]’, ‘y2’, ‘k - 1’]
                                       assume_tac eval_to_Apps_Lams_not_0
                        \\ gvs [LIST_REL_EL_EQN]
                        \\ gvs [subst_APPEND, subst_def, GSYM LAMBDA_PROD, FILTER_T, GSYM ZIP_APPEND]
                        \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1, eL2)) (subst1 s2 w2 y2)) = INL Diverge’
                        \\ gs []
                        \\ dxrule_then (qspecl_then [‘j3 + k - 2’] assume_tac) eval_to_mono
                        \\ gvs [])
                    \\ qexists_tac ‘j + j1 + j2 + j3’
                    \\ last_x_assum $ qspecl_then [‘j1 + j2 + j3’] assume_tac
                    \\ last_x_assum $ qspecl_then [‘j + j2 + j3’] assume_tac
                    \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
                    \\ gvs [SF ETA_ss]
                    \\ qspecl_then [‘Tick (Force (Value w1))’, ‘j + j1 + j2 + j3 + k - 1’]
                                   assume_tac eval_to_Apps_APPEND1
                    \\ gvs []
                    \\ rename1 ‘eval_to _ (Apps (Value (Closure (HD (vL1 ++ [s2])) (Lams _ y2)))
                                                 (MAP Value eL2 ++ [Value w2]))’
                    \\ qspecl_then [‘vL1 ++ [s2]’, ‘eL2 ++ [w2]’, ‘y2’, ‘j + j1 + j2 + j3 + k - 1’]
                                   assume_tac eval_to_Apps_Lams_not_0
                    \\ gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, subst_APPEND, subst_def]
                    \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
                    \\ ‘eval_to (j + j1 + j2 + j3 + k - 2) (subst (ZIP (vL1, eL2)) (subst1 s2 w2 y2))
                        = eval_to (j3 + k - 2) (subst (ZIP (vL1, eL2)) (subst1 s2 w2 y2))’
                      by (irule eval_to_mono \\ gvs []
                          \\ strip_tac \\ gvs []
                          \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1, eL1)) (subst1 s2 v2 x2))’ \\ gvs [])
                    \\ gvs [])
                \\ qexists_tac ‘j + j1’ \\ gvs []
                \\ last_x_assum $ qspecl_then [‘j1’] assume_tac \\ gvs []
                \\ gvs [subst_Lams, subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                        SF ETA_ss, eval_to_Lams]
                \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                \\ irule_at (Pos hd) EQ_REFL
                \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                \\ first_assum $ irule_at Any
                \\ first_assum $ irule_at Any
                \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ first_x_assum $ irule_at Any
                \\ gvs []
                \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                \\ first_x_assum $ irule_at Any
                \\ gvs []
                \\ first_x_assum $ irule_at $ Pos last
                \\ qexists_tac ‘[]’ \\ gvs []
                \\ irule_at (Pos hd) EQ_REFL
                \\ gvs []
                \\ qexists_tac ‘s’ \\ gvs [ALL_DISTINCT_APPEND]
                \\ first_x_assum $ irule_at $ Pos last
                \\ first_x_assum $ irule_at $ Pos last
                \\ gvs [] \\ conj_tac
                >- (irule LIST_EQ \\ rw [EL_MAP]
                    \\ strip_tac \\ gvs [EL_MEM])
                \\ irule EQ_TRANS \\ irule_at Any subst_commutes
                \\ gvs [subst1_def, subst1_notin_frees, MAP_ZIP]
                \\ strip_tac \\ first_x_assum $ drule_then assume_tac \\ gvs [])
            \\ qexists_tac ‘j + j1’ \\ gvs []
            \\ last_x_assum $ qspecl_then [‘j1’] assume_tac \\ gvs []
            \\ gvs [subst_Lams, subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                    SF ETA_ss, eval_to_Lams, ALL_DISTINCT_APPEND]
            \\ rename1 ‘HD (vL2 ++ s::vL3)’
            \\ ‘HD (vL2 ++ s::vL3) = HD (SNOC s vL2)’ by (Cases_on ‘vL2’ \\ gvs []) \\ rw []
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
            \\ irule_at (Pos hd) EQ_REFL
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_assum $ irule_at Any
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
            \\ first_x_assum $ irule_at Any
            \\ gvs []
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_x_assum $ irule_at Any
            \\ gvs []
            \\ irule_at (Pos hd) EQ_REFL
            \\ gvs [ALL_DISTINCT_APPEND]
            \\ first_x_assum $ irule_at $ Pos last \\ gvs []
            \\ qexists_tac ‘eL2 ++ [w1]’ \\ qexists_tac ‘eL1 ++ [v1]’
            \\ rw [] \\ gvs []
            >- (irule LIST_EQ
                \\ rw [EL_APPEND_EQN, EL_MAP] \\ gvs [EL_MEM]
                \\ strip_tac \\ gvs [EL_MEM]
                \\ rename1 ‘n < _’
                \\ first_x_assum $ qspecl_then [‘EL (n - (LENGTH vL2 + 1)) vL3’] assume_tac \\ gvs [EL_MEM])
            \\ irule EQ_TRANS \\ irule_at Any subst_commutes
            \\ gvs [MAP_ZIP]
            \\ conj_tac >- (strip_tac \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
            \\ gvs [GSYM subst_APPEND]
            \\ qspecl_then [‘vL1’, ‘eL1’, ‘[h]’, ‘[v1]’] assume_tac ZIP_APPEND
            \\ gvs [])
        \\ IF_CASES_TAC
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ Cases_on ‘vL3’
        \\ gvs [subst_Lams, ALL_DISTINCT_APPEND]
        \\ rename1 ‘Lams vL3 (subst1 v3 _ _)’
        \\ Cases_on ‘vL3 = []’ \\ gvs []

        >- (rename1 ‘Tick (Force (Value w2))::MAP _ _’ \\ rename1 ‘v_rel v2 w2’
            \\ last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Letrec [] (Force (Value v2))’,
                                         ‘Letrec [] (Force (Value w2))’] mp_tac
            \\ impl_tac
            >- (gvs [subst1_def] \\ irule exp_rel_Letrec
                \\ gvs [exp_rel_def])
            \\ disch_then $ qx_choose_then ‘j2’ assume_tac
            \\ gvs [subst_def]
            \\ once_rewrite_tac [eval_to_def]
            \\ IF_CASES_TAC \\ gvs []
            >- (qexists_tac ‘0’ \\ gvs []
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k y’ \\ gvs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g’ \\ gvs [subst_Apps, subst1_def]
                \\ gvs [MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss, subst1_def]
                \\ ‘k = 1’ by (Cases_on ‘k’ \\ gvs []) \\ gvs []
                \\ ‘eval_to 0 (Tick (Force (Value w2))) = INL Diverge’ by gvs [eval_to_def]
                \\ dxrule_then (qspecl_then [‘eL2' ++ [w1]’] assume_tac) eval_to_Apps_INL
                \\ gvs [MAP_APPEND, FOLDL_APPEND])
            \\ Cases_on ‘eval_to (k - 2) (Force (Value v2)) = INL Diverge’
            >- (qexists_tac ‘0’ \\ gvs []
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k y’ \\ gvs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g’ \\ gvs [subst_Apps, subst1_def]
                \\ ‘∀e. eval_to (k - 1) (Tick e) = eval_to (k - 2) e’
                  by (gen_tac \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def])
                \\ ‘∀e. eval_to (j2 + k - 1) (Tick e) = eval_to (j2 + k - 2) e’
                  by (gen_tac \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def])
                \\ gvs [MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss, subst1_def]
                \\ ‘eval_to (k - 1) (Tick (Force (Value w2))) = INL Diverge’
                  by (Cases_on ‘eval_to (k - 2) (Force (Value w2)) = INL Diverge’ \\ gvs []
                      \\ drule_then (qspecl_then [‘j2 + k - 2’] assume_tac) eval_to_mono
                      \\ Cases_on ‘eval_to (k - 2) (Force (Value w2))’ \\ gvs [])
                \\ dxrule_then (qspecl_then [‘eL2' ++ [w1]’] assume_tac) eval_to_Apps_INL
                \\ gvs [FOLDL_APPEND, MAP_APPEND])
            \\ ‘∀k e. k > 1 ⇒ eval_to (k - 1) (Tick e) = eval_to (k - 2) e’
              by (rw [] \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def])
            \\ Cases_on ‘eval_to (k - 2) (Force (Value v2))’
            >~[‘INL err’]
            >- (qexists_tac ‘j + j1 + j2’
                \\ last_x_assum $ qspecl_then [‘j1 + j2’] assume_tac
                \\ last_x_assum $ qspecl_then [‘j + j2’] assume_tac
                \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
                \\ gvs [SF ETA_ss]
                \\ ‘eval_to (j + j1 + j2 + k - 1) (Tick (Force (Value w2))) = INL err’
                  by (Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2)) = INL Diverge’ \\ gvs []
                      \\ drule_then (qspecl_then [‘j + j1 + j2 + k - 2’] assume_tac) eval_to_mono
                      \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2))’ \\ gvs [])
                \\ dxrule_then (qspecl_then [‘eL2' ++ [w1]’] assume_tac) eval_to_Apps_INL
                \\ gvs [MAP_APPEND, FOLDL_APPEND])
            \\ gvs []
            \\ rename1 ‘eval_to (k - 2) (Force (Value v2)) = INR v2'’
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2)) = INL Diverge’ \\ gvs []
            \\ ‘∀j3. eval_to (j + j1 + j2 + j3 + k - 2) (Force (Value w2))
                     = eval_to (j2 + k - 2) (Force (Value w2))’
              by (gen_tac \\ irule eval_to_mono \\ gvs [])
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2))’ \\ gvs []
            \\ rename1 ‘v_rel v2' w2'’ \\ rename1 ‘exp_rel x2 y2’
            \\ ‘subst1 s2 v2' (subst1 v3 v1 (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) x2)) =
                subst (ZIP (vL1 ++ vL2, eL1 ++ eL2)) (subst1 v3 v1 (subst1 s2 v2' x2))’
              by (gvs [subst1_commutes]
                  \\ ‘∀e. subst1 v3 v1 (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) e) =
                          subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) (subst1 v3 v1 e)’
                    by (gen_tac \\ irule subst_commutes \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP]
                        \\ conj_tac \\ strip_tac \\ first_x_assum $ qspecl_then [‘v3’] assume_tac \\ gvs [])
                  \\ ‘∀e. subst1 s2 v2' (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) e) =
                          subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) (subst1 s2 v2' e)’
                    by (gen_tac \\ irule subst_commutes \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP])
                  \\ gvs []
                  \\ AP_THM_TAC \\ AP_TERM_TAC
                  \\ gvs [FILTER_EQ_ID, EVERY_EL, MEM_EL, EL_ZIP, EL_APPEND_EQN]
                  \\ rw [] \\ rename1 ‘n < _’
                  \\ strip_tac \\ gvs []
                  \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                  \\ gvs [])
            \\ gvs []
            \\ last_x_assum $ qspecl_then [‘ZIP (vL1 ++ vL2, eL1 ++ eL2) ++ [(v3, v1)]’, ‘s2’, ‘v2'’, ‘Tick x2’,
                       ‘subst (ZIP(vL1 ++ vL2, eL1' ++ eL2') ++ [(v3, w1)] ++ [(s2, w2')]) (Tick y2)’] mp_tac
            \\ impl_tac
            >- (gvs [subst_APPEND, LIST_REL_EL_EQN]
                \\ irule exp_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                \\ rw [EL_APPEND_EQN] \\ gvs []
                \\ irule exp_rel_subst \\ gvs [exp_rel_def]
                \\ irule exp_rel_subst \\ gvs [exp_rel_def])
            \\ disch_then $ qx_choose_then ‘j3’ assume_tac
            \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1 ++ vL2, eL1 ++ eL2))
                                          (subst1 v3 v1 (subst1 s2 v2' x2))) = INL Diverge’
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k y’ \\ gs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g’ \\ gs []
                \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
                \\ Cases_on ‘eval_to (k - 1) (Tick (Force (Value w2))) = INL Diverge’
                >- (dxrule_then (qspecl_then [‘eL2' ++ [w1]’] assume_tac) eval_to_Apps_INL
                    \\ gvs [MAP_APPEND, FOLDL_APPEND])
                \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                \\ qspecl_then [‘eL2' ++ [w1]’, ‘Tick (Force (Value w2))’, ‘k - 1’] assume_tac eval_to_Apps_INR
                \\ gvs [FOLDL_APPEND]
                \\ qspecl_then [‘vL1 ++ s2::vL2 ++ [v3]’, ‘eL1' ++ w2'::eL2' ++ [w1]’, ‘y2’, ‘k - 1’]
                               assume_tac eval_to_Apps_Lams_not_0
                \\ Cases_on ‘eval_to (k - 2) (Force (Value w2))’
                \\ gvs [LIST_REL_EL_EQN, FOLDL_APPEND, subst_def, GSYM ZIP_APPEND, subst_APPEND]
                \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1, eL1')) (subst1 s2 w2' (subst (ZIP (vL2, eL2'))
                                              (subst1 v3 w1 y2)))) = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspecl_then [‘j3 + k - 2’] assume_tac) eval_to_mono \\ gvs []
                \\ ‘∀e. subst1 s2 w2' (subst (ZIP (vL2, eL2')) e) = subst (ZIP (vL2, eL2')) (subst1 s2 w2' e)’
                  by (gen_tac \\ irule subst_commutes \\ gvs [MAP_ZIP])
                \\ gvs [subst1_commutes])
            \\ qexists_tac ‘j + j1 + j2 + j3’
            \\ last_x_assum $ qspecl_then [‘j1 + j2 + j3’] assume_tac
            \\ last_x_assum $ qspecl_then [‘j + j2 + j3’] assume_tac
            \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
            \\ gvs [SF ETA_ss]
            \\ qspecl_then [‘eL2' ++ [w1]’, ‘Tick (Force (Value w2))’, ‘j + j1 + j2 + j3 + k - 1’]
                           assume_tac eval_to_Apps_INR
            \\ ‘eval_to (j2 + k - 2) (Force (Value w2)) ≠ INL Diverge’ by gvs []
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + j3 + k - 2’] assume_tac) eval_to_mono
            \\ gvs [FOLDL_APPEND]
            \\ qspecl_then [‘vL1 ++ s2::vL2 ++ [v3]’, ‘eL1' ++ w2'::eL2' ++ [w1]’, ‘y2’, ‘j + j1 + j2 + j3 + k - 1’]
                           assume_tac eval_to_Apps_Lams_not_0
            \\ gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, subst_APPEND, subst_def, FOLDL_APPEND]
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND, GSYM LAMBDA_PROD, FILTER_T]
            \\ ‘eval_to (j3 + k - 2) (subst (ZIP (vL1, eL1')) (subst (ZIP (vL2, eL2'))
                                                               (subst1 v3 w1 (subst1 s2 w2' y2)))) ≠ INL Diverge’
              by (strip_tac
                  \\ Cases_on ‘eval_to (k − 2) (subst (ZIP (vL1,eL1))
                                                (subst (ZIP (vL2,eL2)) (subst1 v3 v1 (subst1 s2 v2' x2))))’
                  \\ gvs [])
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + j3 + k - 2’] assume_tac) eval_to_mono \\ gvs []
            \\ ‘∀e. subst1 s2 w2' (subst (ZIP (vL2, eL2')) e) = subst (ZIP (vL2, eL2')) (subst1 s2 w2' e)’
              by (gen_tac \\ irule subst_commutes \\ gvs [MAP_ZIP])
            \\ gvs [subst1_commutes])
        \\ gvs [eval_to_Lams]
        \\ qexists_tac ‘j + j1’ \\ gvs []
        \\ last_x_assum $ qspecl_then [‘j1’] assume_tac
        \\ gvs [subst1_def, subst_Lams, subst_Apps, eval_to_Lams]
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, subst1_def, SF ETA_ss]
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
        \\ first_x_assum $ irule_at Any
        \\ gvs []
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_x_assum $ irule_at Any
        \\ gvs []
        \\ first_x_assum $ irule_at $ Pos last
        \\ Q.REFINE_EXISTS_TAC ‘l1 ++ [variable]’
        \\ gvs [] \\ irule_at (Pos hd) EQ_REFL
        \\ gvs [ALL_DISTINCT_APPEND]
        \\ first_assum $ irule_at $ Pos last \\ gvs []
        \\ first_assum $ irule_at $ Pos last \\ gvs []
        \\ qexists_tac ‘eL2' ++ [w1]’ \\ gvs []
        \\ qexists_tac ‘eL2 ++ [v1]’ \\ gvs []
        \\ qexists_tac ‘eL1'’ \\ qexists_tac ‘eL1’ \\ gvs []
        \\ rw [] \\ gvs []
        >- (irule LIST_EQ \\ rw [EL_MAP]
            \\ strip_tac \\ gvs [EL_MEM])
        >- (irule EQ_TRANS \\ irule_at Any subst_commutes
            \\ gvs [MAP_ZIP]
            \\ conj_tac
            >- (rw[] \\ strip_tac \\ first_x_assum $ qspecl_then [‘v3’] assume_tac \\ gvs [])
            \\ gvs [GSYM subst_APPEND]
            \\ qspecl_then [‘vL1 ++ vL2’, ‘eL1 ++ eL2’, ‘[v3]’, ‘[v1]’] assume_tac ZIP_APPEND
            \\ gvs [])
        \\ strip_tac
        \\ first_x_assum $ qspecl_then [‘v3’] assume_tac
        \\ gvs [])
    \\ ‘∃body' binds'. dest_anyClosure w2 = INR (s,body',binds')’
      by (Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
          >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
                \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                  by (irule LIST_REL_OPTREL
                      \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
                \\ gvs [OPTREL_def]
                \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
                \\ rw [Once exp_rel_cases] \\ gvs [CaseEqs ["option", "exp"]]
                \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
                \\ gvs [EVERY_EL, EL_MAP]
                \\ first_x_assum (drule_then assume_tac)
                \\ gs [ok_bind_def]))
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’ \\ gs []
      \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_mono \\ gs []
      \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j1’ assume_tac) eval_to_mono \\ gs [])
    \\ ‘exp_rel (subst (binds ++ [s,v1]) body) (subst (binds' ++ [s,w1]) body')’
      by (Cases_on ‘v2’ \\ Cases_on ‘w2’
          \\ gvs [dest_anyClosure_def, v_rel_def]
          >- (irule exp_rel_subst
              \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
              \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                by (irule LIST_REL_OPTREL
                    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
              \\ gvs [OPTREL_def]
              \\ gvs [CaseEqs ["option", "exp"], v_rel_def]
              \\ gs [Once exp_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                     GSYM FST_THM, EVERY2_MAP, v_rel_def]
              \\ gvs [LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP, ELIM_UNCURRY]))
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
    gvs [Once exp_rel_def, eval_to_def]
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
    gvs [Once exp_rel_def, eval_to_def]
    >~[‘Lams _ _’]
    >- (IF_CASES_TAC \\ gs []
        >- (
         qexists_tac ‘0’
         \\ gs [])
        \\ gvs [eval_to_Lams, subst1_def]
        \\ drule_then assume_tac exp_rel_freevars
        \\ gvs [subst1_notin_frees, subst_Lams, subst_Apps, subst1_def]
        \\ gvs [eval_to_def, eval_to_Lams]
        \\ Q.REFINE_EXISTS_TAC ‘(SUC j)’
        \\ gvs [arithmeticTheory.ADD1]
        \\ last_x_assum $ irule
        \\ irule exp_rel_subst
        \\ gvs [MAP_SNOC, subst_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
        \\ rename1 ‘HD (vL1 ++ s::vL2)’
        \\ ‘HD (vL1 ++ s::vL2) = HD (SNOC s vL1)’ by (Cases_on ‘vL1’ >> gvs [])
        \\ rw [] \\ simp [v_rel_def] \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ ‘∀e1 e2 l1 l2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_x_assum $ irule_at Any
        \\ gvs []
        \\ ‘∀e1 e2 l1 l2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
        \\ first_x_assum $ irule_at Any
        \\ gvs []
        \\ irule_at (Pos $ el 4) EQ_REFL
        \\ ‘∀e1 e2 l1 l2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ rename1 ‘Let (SOME s2) _ x1’ \\ qexists_tac ‘x1’
        \\ qexists_tac ‘[]’ \\ qexists_tac ‘s2’
        \\ qexists_tac ‘[]’ \\ gvs []
        \\ irule LIST_EQ \\ rw [EL_MAP, EL_APPEND_EQN] \\ gvs [EL_MEM]
        \\ strip_tac \\ gvs [EL_MEM])
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
    gvs [Once exp_rel_def, eval_to_def]
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
    gvs [Once exp_rel_def, eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘exp_rel x y’
    \\ last_x_assum irule
    \\ gvs [subst_funs_def]
    \\ irule exp_rel_subst
    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
    \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
    \\ rename1 ‘n < LENGTH g’
    \\ ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gs [] \\ gvs [EL_MAP]
    \\ irule v_rel_Recclosure
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
 >~ [‘Delay x’] >- (
    gvs [Once exp_rel_def, eval_to_def, v_rel_def])
  >~ [‘Box x’] >- (
    gvs [Once exp_rel_def, eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
    \\ qexists_tac ‘j’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
    \\ simp [v_rel_def])
  >~ [‘Force x’] >- (
    rgs [Once exp_rel_def]
    \\ once_rewrite_tac [eval_to_def] \\ simp []
    \\ pop_assum kall_tac
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
    \\ rename1 ‘exp_rel x y’ \\ gvs []
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
        by (Cases_on ‘v1’ \\ Cases_on ‘w1’
            \\ gvs [v_rel_def]
            \\ gvs [dest_anyThunk_def, v_rel_def]
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
    gvs [Once exp_rel_def, eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
    \\ qexists_tac ‘j’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
    \\ simp [v_rel_def])
  >~ [‘Prim op xs’] >- (
    gvs [Once exp_rel_def, eval_to_def]
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
        \\ Cases_on ‘eval_to (j + k) (EL n ys)’ \\ gs [])
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
        \\ qexists_tac ‘0’
        \\ rw [] \\ gs []
        \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
        \\ Cases_on ‘eval_to k (EL n ys) = INL Diverge’ \\ gs []
        \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
        \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
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
              ‘eval_to k x ≠ INL Diverge’
                by (strip_tac
                    \\ rpt $ first_x_assum $ qspecl_then [‘0’] assume_tac
                    \\ gs [])
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
              by (strip_tac \\ Cases_on ‘eval_to k (EL m xs)’
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
        \\ Cases_on ‘eval_to k (EL n xs)’
        \\ Cases_on ‘eval_to (j + k) (EL n ys)’ \\ gvs []
        \\ rename1 ‘INL err’ \\ Cases_on ‘err’ \\ gs [])
      \\ first_x_assum (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to k (EL n xs)’ \\ gs [])
    >- ((* IsEq *)
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ first_x_assum $ qspecl_then [‘0’] assume_tac \\ gs []
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
      IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ first_x_assum $ qspecl_then [‘0’] assume_tac \\ gvs []
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
        \\ rw [] \\ gs []
        \\ rpt (first_x_assum (qspec_then ‘m’ assume_tac)) \\ gs []
        \\ Cases_on ‘eval_to k (EL m xs)’
        \\ Cases_on ‘eval_to (j + k) (EL m ys)’ \\ gs []
        \\ rename1 ‘v_rel v w’
        \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [v_rel_def])
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
      \\ qpat_x_assum ‘∀n. _ ⇒ ¬( _ < _)’ kall_tac
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
        \\ rename1 ‘n < LENGTH ys’
        \\ rgs [Once (CaseEq "sum"), CaseEq "v"]
        \\ qexists_tac ‘0’
        \\ rw [] \\ gs []
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
        >- (
          first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
          \\ first_x_assum (drule_then assume_tac)
          \\ first_x_assum (drule_then assume_tac)
          \\ ‘eval_to k (EL n ys) ≠ INL Diverge’
            by (strip_tac \\ gs [])
          \\ drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono \\ gs []
          \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [])
        >- (rename1 ‘eval_to _ _ = INR v3’ \\ Cases_on ‘v3’ \\ gvs [])
        >- (rpt $ first_x_assum $ qspecl_then [‘n’] assume_tac
            \\ rename1 ‘eval_to _ _ = INR v3’ \\ Cases_on ‘v3’ \\ gvs []))
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃x. eval_to k (EL n xs) = INR (Atom x)’
        by (rw []
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac) \\ gs [])
      \\ qpat_x_assum ‘∀n. _ ⇒ ¬(n < _)’ kall_tac
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

Theorem eval_Lams:
  ∀l e. l ≠ [] ⇒ eval (Lams l e) = INR (Closure (HD l) (Lams (TL l) e))
Proof
  Cases >> gvs [eval_def, eval_to_Lams] >>
  DEEP_INTRO_TAC some_intro >> rw []
QED

Theorem delay_lam_apply_force[local] =
  apply_force_rel
  |> Q.INST [‘Rv’|->‘v_rel’, ‘Re’|->‘exp_rel’,‘allow_error’|->‘T’]
  |> SIMP_RULE std_ss [exp_rel_eval, exp_rel_Force, exp_rel_Value];

Theorem eval_App_Values:
  eval (App (Value (Closure s e)) (Value v)) = eval (subst1 s v e)
Proof
  Cases_on ‘∀k. eval_to k (subst1 s v e) = INL Diverge’ >> gvs []
  >- (gvs [eval_def, eval_to_def] >> gvs [dest_anyClosure_def]) >>
  irule EQ_TRANS >> irule_at Any eval_to_equals_eval >>
  first_assum $ irule_at Any >>
  irule EQ_TRANS >> irule_at (Pos hd) $ GSYM eval_to_equals_eval >>
  gvs [eval_to_def, dest_anyClosure_def] >>
  Q.REFINE_EXISTS_TAC ‘SUC num’ >>
  gvs [ADD1] >>
  irule_at Any EQ_REFL >>
  gvs []
QED

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
  >- (first_x_assum irule
      \\ rename1 ‘Let (SOME s2) (Force (Var s)) x’
      \\ rename1 ‘exp_rel x y’ \\ rename1 ‘v_rel v w’
      \\ rename1 ‘LIST_REL v_rel eL1 eL2’ \\ rename1 ‘ALL_DISTINCT (vL1 ++ vL2 ++ s::vL3)’
      \\ qspecl_then [‘eL1’, ‘eL2’, ‘vL1’, ‘vL2’, ‘vL3’, ‘s’, ‘s2’, ‘x’, ‘y’] assume_tac v_rel_Closure_Force_TL
      \\ gvs [] \\ dxrule_then assume_tac exp_rel_Value
      \\ dxrule_then (qspecl_then [‘Value v’, ‘Value w’] assume_tac) exp_rel_App
      \\ ‘exp_rel (Value v) (Value w)’ by gvs [exp_rel_Value] \\ gvs []
      \\ pop_assum kall_tac
      \\ dxrule_then assume_tac exp_rel_eval
      \\ gvs [eval_App_Values, SNOC_APPEND])
  >- (first_x_assum irule
      \\ rename1 ‘subst1 (HD vL3) v2 (Lams _ (subst (ZIP (vL1 ++ vL2, eL1 ++ eL2))
                                              (Let (SOME s2) (Force (Value v1)) x)))’
      \\ rename1 ‘LIST_REL v_rel eL1 eL1'’ \\ rename1 ‘LIST_REL v_rel eL2 eL2'’
      \\ rename1 ‘exp_rel x y’ \\ rename1 ‘v_rel v2 w2’ \\ rename1 ‘v_rel v1 w1’
      \\ rename1 ‘ALL_DISTINCT (vL1 ++ vL2 ++ s::vL3)’
      \\ qspecl_then [‘eL1’, ‘eL1'’, ‘eL2’, ‘eL2'’, ‘v1’, ‘w1’, ‘vL1’, ‘vL2’, ‘vL3’, ‘s’, ‘s2’, ‘x’, ‘y’]
                     assume_tac v_rel_Closure_Force_HD
      \\ gvs [] \\ dxrule_then assume_tac exp_rel_Value
      \\ dxrule_then (qspecl_then [‘Value v2’, ‘Value w2’] assume_tac) exp_rel_App
      \\ ‘exp_rel (Value v2) (Value w2)’ by gvs [exp_rel_Value] \\ gvs []
      \\ pop_assum kall_tac
      \\ dxrule_then assume_tac exp_rel_eval
      \\ gvs [eval_App_Values])
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs []
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
