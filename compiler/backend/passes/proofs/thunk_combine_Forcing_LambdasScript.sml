(*
 Relation to rewrite function definitions to remove Delay
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory;

val _ = new_theory "thunk_combine_Forcing_Lambdas";

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
[~Let_Lams_combine1:]
  (∀v1 v2 vL1 vL2 vL3 bL1 bL2 bL3 x1 x2 y1 y2 i.
     LENGTH vL1 = LENGTH bL2 ∧ LENGTH vL1 = LENGTH vL2 ∧ LENGTH vL1 = LENGTH bL3 ∧
     ¬MEM v1 vL1 ∧ ALL_DISTINCT vL1 ∧ vL1 ≠ [] ∧ ALL_DISTINCT (vL3 ++ vL2) ∧
     (∀i. i < LENGTH vL1 ⇒ (EL i vL1 = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL3 bL2 ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL3, vL1))) ∧

     i < LENGTH vL1 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL1) ∧
     v1 ∉ freevars x1 ∧ EVERY (λv. v ∉ freevars x1) (vL1 ++ vL2 ++ vL3) ∧

     exp_rel x1 x2 ∧ exp_rel y1 y2 ∧ v1 ≠ v2 ⇒
     exp_rel (Let (SOME v1) (Lams (vL3 ++ vL2) (Apps x1 (MAP Var vL3 ++
                                                         MAP2 (λb e. if b then Force e else e) bL1 (MAP Var vL2))))
              (Let (SOME v2) (Lams vL1 (Apps (Var v1) (MAP Var vL3 ++
                                                      MAP2 (λb e. if b then Force e else e) bL2 (MAP Var vL1)))) y1))
             (Let (SOME v1) (Lams (vL3 ++ vL2) (Apps x2 (MAP Var vL3 ++
                                                         MAP2 (λb e. if b then Force e else e) bL1 (MAP Var vL2))))
              (Let (SOME v2) (Lams vL1 (Tick (Apps x2
                                              (MAP Var vL3 ++
                                               MAP2 (λb e. if b then Force e else e) bL1
                                                (MAP2 (λb e. if b then Force e else e) bL2 (MAP Var vL1)))))) y2))) ∧
[~Let_Lams_combine2:]
  (∀v1 v2 vL1 vL2 vL3 bL1 bL2 bL3 x1 x2 y1 y2 i.
     LENGTH vL1 = LENGTH bL2 ∧ LENGTH vL1 = LENGTH vL2 ∧ LENGTH vL1 = LENGTH bL3 ∧
     ¬MEM v1 vL1 ∧ ALL_DISTINCT vL1 ∧ vL1 ≠ [] ∧ ALL_DISTINCT (vL3 ++ vL2) ∧
     (∀i. i < LENGTH vL1 ⇒ (EL i vL1 = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL3 bL2 ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL3, vL1))) ∧

     i < LENGTH vL1 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL1) ∧
     v1 ∉ freevars x1 ∧ EVERY (λv. v ∉ freevars x1) (vL1 ++ vL2 ++ vL3) ∧

     exp_rel x1 x2 ∧ exp_rel y1 y2 ∧ v1 ≠ v2 ⇒
     exp_rel (Let (SOME v1) (Lams (vL3 ++ vL2) (Apps x1 (Var (EL i vL2)::MAP Var vL3 ++
                                                         MAP2 (λb e. if b then Force e else e) bL1 (MAP Var vL2))))
              (Let (SOME v2) (Lams vL1 (Apps (Var v1)(MAP Var vL3 ++
                                                      MAP2 (λb e. if b then Force e else e) bL2 (MAP Var vL1)))) y1))
             (Let (SOME v1) (Lams (vL3 ++ vL2) (Apps x2 (Var (EL i vL2)::
                                                         MAP Var vL3 ++
                                                         MAP2 (λb e. if b then Force e else e) bL1 (MAP Var vL2))))
              (Let (SOME v2) (Lams vL1 (Tick (Apps x2
                                              (Var (EL i vL1)::
                                               MAP Var vL3 ++
                                               MAP2 (λb e. if b then Force e else e) bL1
                                                (MAP2 (λb e. if b then Force e else e) bL2 (MAP Var vL1)))))) y2))) ∧
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
[v_rel_Closure_combine1:]
  (∀vL1a vL1b vL2 vL3a vL3b eL1a eL1 eL2a eL2 bL1 bL2 bL3a bL3b x y i.
     LENGTH (vL1a ++ vL1b) = LENGTH vL2 ∧
     LENGTH vL1a = LENGTH eL1 ∧ vL1b ≠ [] ∧ LENGTH (vL1a ++ vL1b)  = LENGTH bL2 ∧
     ALL_DISTINCT (vL1a ++ vL1b) ∧ ALL_DISTINCT (vL3a ++ vL3b ++ vL2) ∧
     LENGTH bL3a = LENGTH vL1a ∧ LENGTH bL3b = LENGTH vL1b ∧
     LENGTH eL1a = LENGTH vL3a ∧
     (∀i. i < LENGTH vL2 ⇒ (EL i (vL1a ++ vL1b) = EL i vL2 ⇔ ¬EL i bL2)) ∧
     eL1a = MAP SND (FILTER FST (ZIP (bL3a, eL1))) ∧
     eL2a = MAP SND (FILTER FST (ZIP (bL3a, eL2))) ∧
     vL3a = MAP SND (FILTER FST (ZIP (bL3a, vL1a))) ∧
     vL3b = MAP SND (FILTER FST (ZIP (bL3b, vL1b))) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) (bL3a ++ bL3b) bL2 ∧

     LIST_REL v_rel eL1 eL2 ∧
     i < LENGTH bL2 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH bL2) ∧
     EVERY (λv. v ∉ freevars x) (vL1a ++ vL1b ++ vL2 ++ vL3a ++ vL3b) ∧
     exp_rel x y ⇒
     v_rel (Closure (HD vL1b)
            (Lams (TL vL1b) (Apps (Value (
                                   Closure (HD (vL3a ++ vL3b ++ vL2))
                                   (Lams (TL (vL3a ++ vL3b ++ vL2))
                                    (Apps x (MAP Var vL3a ++ MAP Var vL3b ++
                                             MAP2 (λb e. if b then Force e else e)
                                                  bL1 (MAP Var vL2))))))
                             (MAP Value eL1a ++ MAP Var vL3b ++
                                  MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL1 ++ MAP Var vL1b)))))
           (Closure (HD vL1b)
            (Lams (TL vL1b)(Tick(Apps y
                                 (MAP Value eL2a ++ MAP Var vL3b ++
                                  MAP2 (λb e. if b then Force e else e) bL1
                                       (MAP2 (λb e. if b then Force e else e) bL2
                                        (MAP Value eL2 ++ MAP Var vL1b)))))))) ∧
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
      rw [SET_EQ_SUBSET, SUBSET_DEF] \\ gvs []
      >- (gvs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gvs [MEM_EL, EL_ZIP])
      >- (gvs [MEM_EL, EL_MAP, EL_MAP2]
          \\ rename1 ‘n < _’ \\ Cases_on ‘EL n bL2’
          \\ gvs [freevars_def])
      >- (disj1_tac \\ conj_tac \\ strip_tac
          \\ gvs [EVERY_MEM, MEM_MAP, MEM_FILTER]
          \\ gvs [MEM_EL, EL_ZIP])
      >- (gvs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gvs [MEM_EL, EL_ZIP])
      >- (gvs [MEM_EL, EL_MAP, EL_MAP2, PULL_EXISTS, SF CONJ_ss, LIST_REL_EL_EQN,
               freevars_def]
          \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac
          \\ IF_CASES_TAC >- (strip_tac \\ gvs [freevars_def])
          \\ IF_CASES_TAC \\ strip_tac \\ gvs [freevars_def]))
  >- (gvs [freevars_Lams, freevars_def, freevars_Apps] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] \\ gvs []
      >- (gvs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gvs [MEM_EL, EL_ZIP])
      >- (gvs [MEM_EL, EL_MAP, EL_MAP2]
          \\ rename1 ‘n < _’ \\ Cases_on ‘EL n bL2’
          \\ gvs [freevars_def])
      >- (disj1_tac \\ conj_tac \\ strip_tac
          \\ gvs [EVERY_MEM, MEM_MAP, MEM_FILTER]
          \\ gvs [MEM_EL, EL_ZIP])
      >- (gvs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gvs [MEM_EL, EL_ZIP])
      >- (gvs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gvs [MEM_EL, EL_ZIP])
      >- (gvs [MEM_EL, EL_MAP, EL_MAP2, PULL_EXISTS, SF CONJ_ss, LIST_REL_EL_EQN,
               freevars_def]
          \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac
          \\ IF_CASES_TAC >- (strip_tac \\ gvs [freevars_def])
          \\ IF_CASES_TAC \\ strip_tac \\ gvs [freevars_def]))
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
      by (Cases \\ gs [ok_bind_def, subst_def])
    \\ gvs [EVERY_EL, ELIM_UNCURRY]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ first_assum irule
    \\ gvs [MAP_FST_FILTER, LAMBDA_PROD]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~[‘Apps (App _ _) _’]
  >- (gvs [subst_def, subst_Lams, subst_Apps, GSYM LAMBDA_PROD, FILTER_T,
           GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
      \\ gvs [exp_rel_def] \\ disj2_tac \\ disj2_tac
      \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ irule_at (Pos $ el 2) EQ_REFL
      \\ rpt (‘∀l1 l2 e1 (e2 : exp list). l1 = l2 ∧ e1 = e2 ⇒ e1 ++ l1 = e2 ++ l2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gvs [SF CONJ_ss]
      \\ qexists_tac ‘bL3’ \\ qexists_tac ‘bL2’ \\ rw []
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ dxrule_then assume_tac EL_MEM
          \\ gvs [MEM_FILTER] \\ gvs [MEM_EL, EL_ZIP])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ gvs [MEM_MAP]
          \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ gvs [EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ dxrule_then assume_tac EL_MEM
          \\ gvs [MEM_FILTER] \\ gvs [MEM_EL, EL_ZIP])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ gvs [MEM_MAP]
          \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ gvs [EL_MEM])
      >- (gvs [FILTER_FILTER, LAMBDA_PROD]
          \\ rename1 ‘subst (FILTER (λ(p1, p2). ¬MEM p1 vL1 ∧ p1 ≠ v1) ws) y = subst (FILTER _ ws) _’
          \\ qspecl_then [‘ws’, ‘y’, ‘set vL1 ∪ {v1}’] mp_tac subst_remove \\ impl_tac \\ gvs []
          >- (qspecl_then [‘x’, ‘y’] assume_tac exp_rel_freevars
              \\ gvs [DISJOINT_ALT, EVERY_MEM])
          \\ disch_then kall_tac
          \\ qspecl_then [‘ws’, ‘y’, ‘set (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∪ set vL2’] mp_tac
                         $ GSYM subst_remove
          \\ impl_tac \\ gvs []
          \\ qspecl_then [‘x’, ‘y’] assume_tac exp_rel_freevars
          \\ gvs [DISJOINT_ALT, EVERY_MEM])
      >- gvs [freevars_subst]
      >- gvs [EVERY_MEM, freevars_subst]
      >- gvs [EVERY_MEM, freevars_subst]
      >- gvs [EVERY_MEM, freevars_subst]
      >- (first_x_assum irule \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
          \\ qabbrev_tac ‘P = λv. ¬MEM v (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∧ ¬MEM v vL2’ \\ gvs []
          \\ irule LIST_REL_FILTER \\ gs []
          \\ irule LIST_REL_mono
          \\ first_x_assum $ irule_at $ Pos last
          \\ gvs [])
      >- (first_x_assum irule \\ gvs [MAP_FST_FILTER, EVERY2_MAP, FILTER_FILTER, LAMBDA_PROD]
          \\ qabbrev_tac ‘P = λv. v ≠ v2 ∧ v ≠ v1’ \\ gvs []
          \\ irule LIST_REL_FILTER \\ gs []
          \\ irule LIST_REL_mono
          \\ first_x_assum $ irule_at $ Pos last
          \\ gvs []))
  >~[‘Let _ _ (Let _ _ _)’]
  >- (gvs [subst_def, subst_Lams, subst_Apps, GSYM LAMBDA_PROD, FILTER_T,
           GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
      \\ gvs [exp_rel_def] \\ disj2_tac \\ disj1_tac
      \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ qpat_assum ‘_ < LENGTH _’ $ irule_at Any
      \\ qpat_assum ‘LIST_REL (λb3 b2. b3 ⇒ b2) _ _’ $ irule_at Any
      \\ gvs [EVERY_MEM, freevars_subst]
      \\ rpt (‘∀l1 l2 e1 (e2 : exp list). l1 = l2 ∧ e1 = e2 ⇒ e1 ++ l1 = e2 ++ l2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ rw []
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ dxrule_then assume_tac EL_MEM
          \\ gvs [MEM_FILTER] \\ gvs [MEM_EL, EL_ZIP])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ gvs [MEM_MAP]
          \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ gvs [EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ dxrule_then assume_tac EL_MEM
          \\ gvs [MEM_FILTER] \\ gvs [MEM_EL, EL_ZIP])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ gvs [MEM_MAP]
          \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ gvs [EL_MEM])
      >- (gvs [FILTER_FILTER, LAMBDA_PROD]
          \\ rename1 ‘subst (FILTER (λ(p1, p2). ¬MEM p1 vL1 ∧ p1 ≠ v1) ws) y = subst (FILTER _ ws) _’
          \\ qspecl_then [‘ws’, ‘y’, ‘set vL1 ∪ {v1}’] mp_tac subst_remove \\ impl_tac \\ gvs []
          >- (qspecl_then [‘x’, ‘y’] assume_tac exp_rel_freevars
              \\ gvs [DISJOINT_ALT, EVERY_MEM])
          \\ disch_then kall_tac
          \\ qspecl_then [‘ws’, ‘y’, ‘set (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∪ set vL2’] mp_tac
                         $ GSYM subst_remove
          \\ impl_tac \\ gvs []
          \\ qspecl_then [‘x’, ‘y’] assume_tac exp_rel_freevars
          \\ gvs [DISJOINT_ALT, EVERY_MEM])
      >- (first_x_assum irule \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
          \\ qabbrev_tac ‘P = λv. ¬MEM v (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∧ ¬MEM v vL2’ \\ gvs []
          \\ irule LIST_REL_FILTER \\ gs []
          \\ irule LIST_REL_mono
          \\ first_x_assum $ irule_at $ Pos last
          \\ gvs [])
      >- (first_x_assum irule \\ gvs [MAP_FST_FILTER, EVERY2_MAP, FILTER_FILTER, LAMBDA_PROD]
          \\ qabbrev_tac ‘P = λv. v ≠ v2 ∧ v ≠ v1’ \\ gvs []
          \\ irule LIST_REL_FILTER \\ gs []
          \\ irule LIST_REL_mono
          \\ first_x_assum $ irule_at $ Pos last
          \\ gvs [FORALL_PROD]))
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

Theorem eval_to_Apps_Recclosure_Lams_not_0:
  ∀vL eL e k list v. vL ≠ [] ∧ LENGTH vL = LENGTH eL ∧ k ≠ 0 ∧
                     ALOOKUP (REVERSE list) v = SOME (Lams vL e) ⇒
                     eval_to k (Apps (Value (Recclosure list v))
                                (MAP Value eL))
                     = eval_to (k - 1) (subst (ZIP (vL, eL) ++ (FILTER (λ(v,e). ¬MEM v vL)
                                                                (MAP (λ(v,e).(v, Recclosure list v)) list))) e)
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  qspecl_then [‘eL’] assume_tac SNOC_CASES >> gvs [ADD1] >>
  rename1 ‘SNOC s vL’ >> Cases_on ‘vL’ >> gvs []
  >- (gvs [eval_to_def, dest_anyClosure_def] >>
      once_rewrite_tac [CONS_APPEND] >> gvs [subst_APPEND] >>
      ‘∀l e1 e2. subst l (subst1 s e1 e2) = subst1 s e1 (subst (FILTER (λ(v,e). v ≠ s) l) e2)’
        by (rw [] >> irule EQ_TRANS >> irule_at (Pos last) subst_commutes >>
            gvs [MAP_FST_FILTER, MEM_FILTER] >>
            qspecl_then [‘l’, ‘subst1 s e1 e2’, ‘{s}’] assume_tac subst_remove >>
            gvs [freevars_subst]) >>
      gvs []) >>
  gvs [FOLDR_SNOC, FOLDL_APPEND, eval_to_def] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  first_x_assum $ qspecl_then [‘eL’, ‘Lam s e’, ‘k’, ‘list’, ‘v’] assume_tac >>
  gvs [subst_def, eval_to_def, dest_anyClosure_def] >>
  once_rewrite_tac [SNOC_APPEND] >>
  AP_TERM_TAC >>
  rename1 ‘ZIP (h::(vL1 ++ [s]), eL ++ [x])’ >>
  qspecl_then [‘h::vL1’, ‘eL’, ‘[s]’, ‘[x]’] assume_tac $ GSYM ZIP_APPEND >>
  gvs [subst_APPEND] >>
  irule EQ_TRANS >> irule_at (Pos hd) subst_commutes >>
  gvs [MAP_FST_FILTER, MEM_FILTER, FILTER_APPEND, subst_APPEND] >>
  ‘∀expr. subst (ZIP (h::vL1, eL)) (subst1 s x expr) =
       subst (FILTER (λ(n,x). n ≠ s) (ZIP (h::vL1, eL))) (subst1 s x expr)’
    by (gen_tac >> qspecl_then [‘ZIP (h::vL1, eL)’, ‘subst1 s x expr’, ‘{s}’] assume_tac subst_remove >>
        gvs [freevars_subst]) >>
  gvs [] >> AP_TERM_TAC >>
  gvs [FILTER_FILTER, LAMBDA_PROD] >>
  irule subst_commutes >>
  gvs [MAP_FST_FILTER, MEM_FILTER]
QED

Theorem eval_to_Apps_Lams_0:
  ∀vL eL e. vL ≠ [] ∧ LENGTH vL = LENGTH eL ⇒
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

Theorem dest_anyClosure_INL:
  ∀v e. dest_anyClosure v = INL e ⇒ e = Type_error
Proof
  Cases \\ gvs [dest_anyClosure_def]
  \\ CASE_TAC \\ gvs []
  \\ CASE_TAC \\ gvs []
QED

Theorem exp_rel_Lams:
  ∀vL x y. exp_rel x y ⇒ exp_rel (Lams vL x) (Lams vL y)
Proof
  Induct \\ gvs [exp_rel_def]
QED

Theorem exp_rel_Apps:
  ∀eL1 eL2 x y. LIST_REL exp_rel eL1 eL2 ∧ exp_rel x y ⇒ exp_rel (Apps x eL1) (Apps y eL2)
Proof
  Induct \\ gvs [exp_rel_def]
  \\ gen_tac \\ Cases \\ gvs []
  \\ rw [] \\ last_x_assum irule
  \\ gvs [exp_rel_def]
QED

Theorem LESS_EQ_CASES:
  ∀(l: num) i. i ≤ l ⇒ i < l ∨ i = l
Proof
  Induct \\ gvs []
QED

Theorem eval_to_Apps_arg_Div:
  ∀eL i k e. eval_to k (Apps e eL) ≠ INL Type_error ∧ i < LENGTH eL ∧ eval_to k (EL i eL) = INL Diverge
             ⇒ eval_to k (Apps e eL) = INL Diverge
Proof
  Induct using SNOC_INDUCT \\ gvs []
  \\ rw [] \\ gvs [GSYM LESS_EQ_IFF_LESS_SUC, FOLDL_SNOC]
  \\ rename1 ‘SNOC x eL’
  \\ dxrule_then assume_tac LESS_EQ_CASES \\ gvs [EL_SNOC, EL_LENGTH_SNOC, eval_to_def]
  \\ Cases_on ‘eval_to k x’ \\ gvs []
  >~[‘INL err’] >- (Cases_on ‘err’ \\ gvs [])
  \\ Cases_on ‘eval_to k (Apps e eL) = INL Type_error’ \\ gs []
  \\ last_x_assum $ dxrule_then $ drule_then $ drule_then assume_tac
  \\ gvs []
QED

Theorem eval_to_Apps_arg_Div_exp_rel:
  ∀eL eL2 i k e e2.
    eval_to k (Apps e eL) ≠ INL Type_error ∧ i < LENGTH eL ∧ eval_to k (EL i eL) = INL Diverge ∧
    LENGTH eL = LENGTH eL2 ∧
    (∀j. i ≤ j ∧ j < LENGTH eL ∧ eval_to k (EL j eL) ≠ INL Type_error ⇒
         ∃j2. ($= +++ v_rel) (eval_to k (EL j eL)) (eval_to (k + j2) (EL j eL2)))
    ⇒ eval_to k (Apps e2 eL2) = INL Diverge
Proof
  Induct using SNOC_INDUCT \\ gvs []
  \\ rw [] \\ gvs [GSYM LESS_EQ_IFF_LESS_SUC, FOLDL_SNOC]
  \\ rename1 ‘SNOC x eL’
  \\ qspec_then ‘eL2’ assume_tac SNOC_CASES \\ gvs [FOLDL_APPEND]
  \\ rename1 ‘eL2 ++ [x2]’ \\ gvs [SNOC_APPEND]
  \\ dxrule_then assume_tac LESS_EQ_CASES \\ gvs [EL_SNOC, EL_LENGTH_SNOC, eval_to_def, EL_APPEND_EQN]
  \\ Cases_on ‘eval_to k x2 = INL Diverge’ \\ gs []
  \\ dxrule_then assume_tac eval_to_mono \\ gvs [GSYM ADD1]
  >- (‘∃j. ($= +++ v_rel) (eval_to k x) (eval_to (k + j) x2)’
        by (last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
            \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gvs [])
      \\ Cases_on ‘eval_to k x’
      >~[‘eval_to k x = INL err’]
      >- (Cases_on ‘err’ \\ gvs []
          \\ Cases_on ‘eval_to k x2’ \\ gs [])
      \\ Cases_on ‘eval_to k x2’ \\ gvs []
      \\ Cases_on ‘eval_to k (Apps e eL) = INL Type_error’ \\ gs [PULL_EXISTS]
      \\ last_x_assum $ drule_then $ drule_then $ drule_then $ qspecl_then [‘eL2’, ‘e2’] mp_tac
      \\ impl_tac \\ gvs []
      \\ rw []
      \\ last_x_assum $ drule_then assume_tac \\ gvs []
      \\ first_x_assum $ irule_at Any)
  \\ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac \\ gvs []
  \\ Cases_on ‘eval_to k x2’ \\ gvs []
QED

Theorem eval_to_Apps_arg_Div_exp_rel2:
  ∀eL eL2 i k e2.
    i < LENGTH eL ∧ eval_to k (EL i eL) = INL Diverge ∧
    LENGTH eL = LENGTH eL2 ∧
    (∀j. j < LENGTH eL ⇒ eval_to k (EL j eL) ≠ INL Type_error) ∧
    (∀j. i ≤ j ∧ j < LENGTH eL ∧ eval_to k (EL j eL) ≠ INL Type_error ⇒
         ∃j2. ($= +++ v_rel) (eval_to k (EL j eL)) (eval_to (k + j2) (EL j eL2)))
    ⇒ eval_to k (Apps e2 eL2) = INL Diverge
Proof
  Induct using SNOC_INDUCT \\ gvs []
  \\ rw [] \\ gvs [GSYM LESS_EQ_IFF_LESS_SUC, FOLDL_SNOC]
  \\ rename1 ‘SNOC x eL’
  \\ qspec_then ‘eL2’ assume_tac SNOC_CASES \\ gvs [FOLDL_APPEND]
  \\ rename1 ‘eL2 ++ [x2]’ \\ gvs [SNOC_APPEND]
  \\ dxrule_then assume_tac LESS_EQ_CASES \\ gvs [EL_SNOC, EL_LENGTH_SNOC, eval_to_def, EL_APPEND_EQN]
  \\ Cases_on ‘eval_to k x2 = INL Diverge’ \\ gs []
  \\ dxrule_then assume_tac eval_to_mono \\ gvs [GSYM ADD1]
  >- (‘∃j. ($= +++ v_rel) (eval_to k x) (eval_to (k + j) x2)’
        by (rpt $ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
            \\ gvs [] \\ first_x_assum $ irule_at Any)
      \\ Cases_on ‘eval_to k x’
      >~[‘eval_to k x = INL err’]
      >- (last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
          \\ Cases_on ‘err’ \\ gvs []
          \\ Cases_on ‘eval_to k x2’ \\ gs [])
      \\ Cases_on ‘eval_to k x2’ \\ gvs []
      \\ last_x_assum $ drule_then $ drule_then $ qspecl_then [‘eL2’, ‘e2’] mp_tac
      \\ impl_tac \\ gvs []
      \\ rw []
      >- (rename1 ‘j < _’ \\ last_x_assum $ qspec_then ‘j’ assume_tac \\ gvs [])
      \\ last_x_assum $ drule_then assume_tac \\ gvs []
      \\ first_x_assum $ irule_at Any)
  \\ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
  \\ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac \\ gvs []
  \\ Cases_on ‘eval_to k x2’ \\ gs []
QED

(*Theorem eval_to_Apps_INR_exp_rel:
  ∀eL eL2 vL1 k e e2.
    LENGTH eL = LENGTH eL2 ∧ LIST_REL (λe v. eval_to k e = INR v) eL vL1 ∧
    (∀j. j < LENGTH eL ∧ eval_to k (EL j eL) ≠ INL Type_error ⇒
         ∃j2. ($= +++ v_rel) (eval_to k (EL j eL)) (eval_to (k + j2) (EL j eL2)))
    ⇒ ∃vL2. LIST_REL v_rel vL1 vL2 ∧ eval_to k (Apps e2 eL2) = eval_to k (Apps e2 (MAP Value vL2))
Proof
  Induct using SNOC_INDUCT \\ gvs []
  \\ rw [] \\ gvs [GSYM LESS_EQ_IFF_LESS_SUC, FOLDL_SNOC]
  \\ rename1 ‘SNOC x eL’
  \\ qspec_then ‘eL2’ assume_tac SNOC_CASES \\ gvs [FOLDL_APPEND]
  \\ rename1 ‘eL2 ++ [x2]’ \\ gvs [SNOC_APPEND]
  \\ Q.REFINE_EXISTS_TAC ‘vL2 ++ [lst2]’
  \\ qspec_then ‘vL1’ assume_tac SNOC_CASES \\ gvs [MAP_APPEND, FOLDL_APPEND, GSYM ADD1]
  \\ rename1 ‘LIST_REL _ eL vL1’
  \\ last_x_assum $ qspecl_then [‘eL2’, ‘vL1’, ‘k’, ‘e2’] mp_tac \\ gs []
  \\ impl_tac
  >- (gen_tac \\ rename1 ‘j < _ ∧ _ ⇒ _’ \\ rw []
      \\ first_x_assum $ qspec_then ‘j’ assume_tac \\ gvs [EL_APPEND_EQN]
      \\ first_x_assum $ irule_at Any)
  \\ rw [] \\ first_x_assum $ irule_at Any
  \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac \\ gvs [EL_APPEND_EQN]
  \\ cheat
QED*)

Theorem eval_to_Apps_no_INL:
  ∀eL e k. eval_to k (Apps e eL) ≠ INL Type_error ∧ (∀i. i < LENGTH eL ⇒ eval_to k (EL i eL) ≠ INL Diverge)
           ⇒ ∃vL. LIST_REL (λe v. eval_to k e = INR v) eL vL ∧
                  eval_to k (Apps e eL) = eval_to k (Apps e (MAP Value vL))
Proof
  Induct using SNOC_INDUCT \\ gvs [] \\ rw []
  \\ Q.REFINE_EXISTS_TAC ‘SNOC lst vL’ \\ gvs [FOLDL_SNOC, eval_to_def]
  \\ rename1 ‘SNOC x eL’
  \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gvs []
  \\ ‘eval_to k x ≠ INL Diverge’ by (first_x_assum $ qspec_then ‘LENGTH eL’ assume_tac \\ gvs [EL_LENGTH_SNOC])
  \\ Cases_on ‘eval_to k x’ \\ gvs []
  >~[‘value ≠ Type_error’] >- (Cases_on ‘value’ \\ gvs [])
  \\ Cases_on ‘eval_to k (Apps e eL) = INL Type_error’ \\ gvs []
  \\ last_x_assum $ dxrule_then mp_tac \\ impl_tac
  >- (rw [] \\ rename1 ‘i < _’ \\ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_SNOC])
  \\ disch_then $ qx_choose_then ‘vL’ assume_tac
  \\ rename1 ‘eval_to k x = INR v’ \\ qexists_tac ‘v’ \\ qexists_tac ‘vL’
  \\ gvs [MAP_SNOC, FOLDL_SNOC, eval_to_def, GSYM LESS_EQ_IFF_LESS_SUC] \\ rw []
  \\ gvs [LIST_REL_SNOC]
QED

Theorem eval_to_Apps_0:
  ∀bL1 bL2 vL e. LENGTH vL = LENGTH bL1 ∧ LENGTH bL1 = LENGTH bL2 ∧
                 (∃i. i < LENGTH bL1 ∧ EL i bL1) ⇒
                 eval_to 0 (Apps e
                            (MAP2 (λb e. if b then Tick (Force e) else e) bL1
                             (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value vL))))
                 = INL Diverge
Proof
  Induct using SNOC_INDUCT \\ gvs []
  \\ gen_tac \\ gen_tac \\ gen_tac
  \\ qspec_then ‘vL’ assume_tac SNOC_CASES
  \\ qspec_then ‘bL2’ assume_tac SNOC_CASES
  \\ rw [] \\ gvs [SNOC_APPEND, MAP_APPEND, MAP2_APPEND, GSYM ADD1, EL_APPEND_EQN, GSYM LESS_EQ_IFF_LESS_SUC]
  \\ dxrule_then assume_tac LESS_EQ_CASES \\ gvs []
  >- (IF_CASES_TAC \\ gvs [FOLDL_APPEND]
      >- (once_rewrite_tac [eval_to_def] \\ gvs []
          \\ once_rewrite_tac [eval_to_def] \\ gvs [])
      \\ IF_CASES_TAC
      >- (once_rewrite_tac [eval_to_def] \\ gvs []
          \\ once_rewrite_tac [eval_to_def] \\ gvs [])
      \\ gvs [PULL_EXISTS]
      \\ rename1 ‘Apps e (MAP2 _ bL1 (MAP2 _ bL2 (MAP Value vL)))’ \\ rename1 ‘i < _’
      \\ last_x_assum $ qspecl_then [‘bL2’, ‘vL’, ‘e’, ‘i’] assume_tac
      \\ gvs [eval_to_def])
  \\ gvs [FOLDL_APPEND]
  \\ once_rewrite_tac [eval_to_def] \\ gvs []
  \\ once_rewrite_tac [eval_to_def] \\ gvs []
QED

Theorem eval_to_Value:
  ∀k v. eval_to k (Value v) = INR v
Proof
  simp [eval_to_def]
QED

Theorem eval_to_Tick:
  ∀k e. k ≠ 0 ⇒ eval_to k (Tick e) = eval_to (k - 1) e
Proof
  rw [eval_to_def, subst_funs_def, subst_empty]
QED

Theorem eval_to_Apps_Div_or_INR:
  ∀eL vL1 e k. LENGTH eL = LENGTH vL1 ∧
             (∀i. i < LENGTH eL ⇒ eval_to k (EL i eL) = INL Diverge ∨
                                  ($= +++ v_rel) (INR (EL i vL1)) (eval_to k (EL i eL))) ⇒
             eval_to k (Apps e eL) = INL Diverge ∨
             (∃vL2. LIST_REL v_rel vL1 vL2 ∧ eval_to k (Apps e eL) = eval_to k (Apps e (MAP Value vL2)))
Proof
  Induct using SNOC_INDUCT \\ gvs [FOLDL_SNOC]
  \\ gen_tac \\ gen_tac \\ qspec_then ‘vL1’ assume_tac SNOC_CASES
  \\ gvs [GSYM ADD1, FOLDL_APPEND]
  \\ rw []
  \\ once_rewrite_tac [eval_to_def] \\ gvs []
  \\ first_assum $ qspec_then ‘LENGTH eL’ assume_tac \\ gvs [EL_LENGTH_SNOC, EL_APPEND_EQN]
  \\ Cases_on ‘eval_to k x’ \\ gvs []
  \\ rename1 ‘LIST_REL _ (vL1 ++ [v1])’
  \\ last_x_assum $ qspecl_then [‘vL1’, ‘e’, ‘k’] mp_tac \\ gvs []
  \\ impl_tac
  >- (rw [] \\ rename1 ‘i < _’ \\ last_x_assum $ qspec_then ‘i’ assume_tac
      \\ gvs [EL_SNOC])
  \\ rw [] \\ gvs [] \\ disj2_tac
  \\ rename1 ‘Apps _ (MAP Value vL2)’ \\ rename1 ‘eval_to _ _ = INR w1’
  \\ qexists_tac ‘vL2 ++ [w1]’ \\ gvs [FOLDL_APPEND, eval_to_def]
QED

Theorem eval_to_INR_List:
  ∀eL vL1 k. LIST_REL (λv e. ∃j. ($= +++ v_rel) (INR v) (eval_to (j + k) e)) vL1 eL ⇒
             ∃vL2 j.
               LIST_REL v_rel vL1 vL2 ∧ LIST_REL (λe v. ∀j2. eval_to (j2 + j + k) e = INR v) eL vL2
Proof
  Induct \\ gvs [] \\ gen_tac \\ Cases \\ gvs [PULL_EXISTS]
  \\ rw []
  \\ last_x_assum $ dxrule_then assume_tac
  \\ rename1 ‘eval_to (j + k) h’
  \\ Cases_on ‘eval_to (j + k) h’ \\ gs []
  \\ last_x_assum $ irule_at Any
  \\ last_x_assum $ irule_at Any
  \\ rename1 ‘eval_to (j1 + (_ + k)) _’
  \\ qexists_tac ‘j + j1’
  \\ qspecl_then [‘j + k’, ‘h’] assume_tac eval_to_mono \\ gvs []
  \\ gvs [LIST_REL_EL_EQN] \\ rw []
  \\ last_x_assum $ drule_then $ qspec_then ‘j + j2’ assume_tac \\ gvs []
QED

Theorem eval_to_Apps_LIST_INR:
  ∀eL vL e k. LIST_REL (λe v. ∀j. eval_to (j + k) e = INR v) eL vL
              ⇒ ∀j. k ≤ j ⇒ eval_to j (Apps e eL) = eval_to j (Apps e (MAP Value vL))
Proof
  Induct using SNOC_INDUCT \\ gvs [LIST_REL_SNOC, PULL_EXISTS, FOLDL_APPEND, FOLDL_SNOC]
  \\ rw [] \\ last_x_assum $ drule_all_then assume_tac
  \\ gvs [eval_to_def]
  \\ first_x_assum $ qspec_then ‘j - k’ assume_tac
  \\ gvs []
QED

Theorem exp_rel_eval_to:
  ∀x y.
    eval_to k x ≠ INL Type_error ∧
    exp_rel x y ⇒
      ∃j. ($= +++ v_rel) (eval_to k x) (eval_to (j + k) y)
Proof
  completeInduct_on ‘k’ \\ completeInduct_on ‘exp_size x’
  \\ Cases \\ gvs [PULL_FORALL, exp_size_def] \\ rw []
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
  >~ [‘Delay x’] >- (
    gvs [Once exp_rel_def, eval_to_def, v_rel_def])
  >~ [‘Box x’] >- (
    gvs [Once exp_rel_def, eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum $ qspecl_then [‘x’, ‘y’] mp_tac \\ gs []
    \\ impl_tac >- (strip_tac \\ gvs [])
    \\ disch_then $ qx_choose_then ‘j’ assume_tac
    \\ qexists_tac ‘j’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
    \\ simp [v_rel_def])
  >~ [‘App f x’] >- (
    gvs [Once exp_rel_def, eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gvs []
    \\ first_assum $ qspec_then ‘x’ mp_tac \\ impl_tac >- gs []
    \\ disch_then $ drule_then $ drule_then $ qx_choose_then ‘j’ assume_tac \\ gs []
    \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k) y’ \\ gs [])
    \\ Cases_on ‘eval_to k x’ \\ gs []
    >~ [‘($= +++ v_rel) (INL err) _’] >- (Cases_on ‘err’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
    \\ rename1 ‘v_rel v1 w1’
    \\ Cases_on ‘eval_to k f = INL Type_error’ \\ gvs []
    \\ first_x_assum $ qspec_then ‘f’ assume_tac \\ gs []
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
    >~ [‘($= +++ v_rel) (INL err) _’] >- (Cases_on ‘err’ \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k) g’ \\ gs []
    \\ rename1 ‘v_rel v2 w2’
    \\ ‘∀i. eval_to (i + j + k) y = eval_to (j + k) y’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ ‘∀i. eval_to (i + j1 + k) g = eval_to (j1 + k) g’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘dest_anyClosure v2’ \\ gs []
    >- (dxrule_then assume_tac dest_anyClosure_INL \\ gvs [])
    \\ pairarg_tac \\ gvs []
    \\ Cases_on ‘v2’ \\ gvs [v_rel_def, dest_anyClosure_def]
    >~[‘Closure _ _’]
    >- (IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ rename1 ‘eval_to (k - 1) (subst1 s v1 body)’
        \\ rename1 ‘v_rel v1 w1’ \\ rename1 ‘exp_rel body body'’
        \\ last_x_assum $ qspecl_then [‘k - 1’, ‘subst1 s v1 body’, ‘subst1 s w1 body'’] mp_tac
        \\ gvs [] \\ impl_tac
        >- (irule exp_rel_subst \\ gvs [])
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

    (* combine closure1 *)
    >- (IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ Cases_on ‘vL1b’ \\ gs []
        \\ Cases_on ‘bL3b’ \\ gs []
        \\ rename1  ‘LIST_REL _ (bL3a ++ b::bL3b) bL2’
        \\ rename1 ‘eval_to _ (subst1 h v1 (Lams vL1b _))’ \\ Cases_on ‘vL1b = []’ \\ gvs []
        >- (gvs [subst_Apps, subst1_def]
            \\ ‘MAP (subst [(h,v1)])
                (MAP Value (MAP SND (FILTER FST (ZIP (bL3a,eL1)))))
                = MAP Value (MAP SND (FILTER FST (ZIP (bL3a,eL1))))’
              by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2, subst1_def])
            \\ gs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst [(h,v1)])
                (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL1 ++ [Var h]))
                = MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL1 ++ [Value v1])’
              by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2, subst1_def]
                  \\ rw [subst_def, EL_APPEND_EQN, EL_MAP]
                  \\ Cases_on ‘LENGTH vL2’ \\ gvs [NOT_LESS, GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                  \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gs [subst1_def])
            \\ gs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst [(h,v1)]) (MAP Var (MAP SND (if b then [(T,h)] else [])))
                = if b then [Value v1] else []’
              by (IF_CASES_TAC \\ gvs [subst_def])
            \\ gs [] \\ pop_assum kall_tac
            \\ Cases_on ‘∃i. i < SUC (LENGTH eL1) ∧ eval_to (k - 1) (EL i (MAP2 (λb e. if b then Force e else e)
                                                                     bL2 (MAP Value eL1 ++ [Value v1])))
                                                    = INL Diverge’ \\ gvs []
            >- (rename1 ‘eval_to _ (EL i2 _) = INL Diverge’
                \\ gvs [FOLDL_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ (Apps expr1 argL1)) _’
                \\ qspecl_then [‘argL1’, ‘i2’, ‘k - 1’, ‘expr1’] mp_tac eval_to_Apps_arg_Div \\ gvs []
                \\ impl_tac >- gvs [Abbr ‘argL1’] \\ rw []
                \\ qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono \\ gs []
                \\ rename1 ‘hd ∉ freevars x2’ \\ rename1 ‘exp_rel x2 y2’
                \\ qspecl_then [‘x2’, ‘y2’] assume_tac exp_rel_freevars
                \\ Cases_on ‘k = 1’
                \\ gvs [subst_Apps, subst1_notin_frees, freevars_def, subst1_def, eval_to_Tick]
                >- simp [eval_to_def]
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps expr2 argL2))’
                \\ qspecl_then [‘argL1’, ‘argL2’, ‘i2’, ‘k - 2’, ‘expr1’, ‘expr2’]
                               mp_tac eval_to_Apps_arg_Div_exp_rel
                \\ impl_tac \\ gvs []
                \\ conj_tac
                >- (Cases_on ‘eval_to (k - 2) (Apps expr1 argL1) = INL Diverge’ \\ gs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
                \\ unabbrev_all_tac \\ gvs [LIST_REL_EL_EQN, EL_MAP2, EL_MAP]
                \\ conj_tac
                >- (‘∀e. eval_to (k - 1) e = INL Diverge ⇒ eval_to (k - 2) e = INL Diverge’
                      suffices_by gvs []
                    \\ rw []
                    \\ Cases_on ‘eval_to (k - 2) e = INL Diverge’ \\ gs []
                    \\ drule_then assume_tac eval_to_mono \\ gvs [])
                \\ gen_tac \\ strip_tac
                \\ last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gs []
                \\ first_x_assum $ dxrule_then assume_tac
                \\ Cases_on ‘EL i2 bL2’ \\ gs []
                >~[‘¬EL i2 bL2’]
                >- (qpat_x_assum ‘eval_to _ (EL _ _) = INL Diverge’ mp_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP]
                    \\ IF_CASES_TAC \\ gvs [eval_to_def, NOT_LESS, GSYM ADD1]
                    \\ Cases_on ‘LENGTH bL2’ \\ gvs []
                    \\ ‘i2 = LENGTH eL2’ by (irule LESS_EQUAL_ANTISYM \\ gvs [])
                    \\ gvs [eval_to_def])
                \\ qpat_x_assum ‘∀j. _ ⇒ ¬EL _ _’ $ qspec_then ‘i2’ assume_tac \\ gvs [NOT_LESS_EQUAL]
                \\ gvs [EL_MAP2, EL_MAP]
                \\ first_x_assum irule
                \\ IF_CASES_TAC \\ gvs [EL_APPEND_EQN, EL_MAP, subst1_def]
                \\ IF_CASES_TAC \\ gvs [exp_rel_def, subst1_def]
                \\ Cases_on ‘LENGTH vL2’ \\ gvs []
                \\ gvs [NOT_LESS, GSYM LESS_EQ_IFF_LESS_SUC, GSYM ADD1]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                \\ gvs [subst1_def, exp_rel_def])
            \\ gvs [FOLDL_APPEND]
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ (Apps expr1 argL1)) _’
            \\ qspecl_then [‘argL1’, ‘expr1’, ‘k - 1’] mp_tac eval_to_Apps_no_INL
            \\ gvs [] \\ impl_tac
            >- (rw [] \\ strip_tac \\ first_x_assum $ dxrule_then assume_tac \\ gvs [Abbr ‘argL1’])
            \\ disch_then $ qx_choose_then ‘valL1’ assume_tac \\ gvs [Abbr ‘expr1’]
            \\ pop_assum kall_tac
            \\ ‘LENGTH vL2 = LENGTH valL1’ by gvs [Abbr ‘argL1’, LIST_REL_EL_EQN]
            \\ Cases_on ‘k - 1 = 0’ \\ gvs []
            >- (dxrule_then assume_tac LESS_EQ_CASES \\ gvs []
                \\ qspecl_then [‘(MAP SND (FILTER FST (ZIP (bL3a,vL1a))) ++
                                  MAP SND (if b then [(T,h)] else []) ++ vL2)’,
                                ‘MAP SND (FILTER FST (ZIP (bL3a,eL1)))
                                 ++ (if b then [v1] else []) ++ valL1’] assume_tac eval_to_Apps_Lams_0
                \\ gvs [FOLDL_APPEND]
                \\ ‘MAP Value (if b then [v1] else []) = if b then [Value v1] else []’ by (IF_CASES_TAC \\ gs [])
                \\ gvs []
                \\ Cases_on ‘vL2 = []’ \\ gs []
                \\ Cases_on ‘b’ \\ gvs []
                \\ qexists_tac ‘0’
                \\ Cases_on ‘eval_to 1 y = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono \\ gs []
                \\ Cases_on ‘eval_to 1 g = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono \\ gs []
                \\ gvs [subst1_def, eval_to_def])
            \\ ‘∀(v : thunkLang$v). MAP Value (if b then [v] else []) = if b then [Value v] else []’ by rw []
            \\ ‘∀(h : string). LENGTH (if b then [(T, h)] else []) = if b then 1 else 0’ by rw []
            \\ ‘∀(v : thunkLang$v). LENGTH (if b then [v] else []) = if b then 1 else 0’ by rw []
            \\ Cases_on ‘vL2 = []’ \\ gvs []
            \\ qspecl_then [‘MAP SND (FILTER FST (ZIP (bL3a,vL1a))) ++
                             MAP SND (if b then [(T,h)] else []) ++ vL2’,
                            ‘MAP SND (FILTER FST (ZIP (bL3a, eL1))) ++
                             (if b then [v1] else []) ++ valL1’] assume_tac eval_to_Apps_Lams_not_0
            \\ gvs [FOLDL_APPEND]
            \\ pop_assum kall_tac
            \\ rename1 ‘subst _ (Apps (Apps (Apps x2 _) _) _)’
            \\ qmatch_goalsub_abbrev_tac ‘eval_to _ (subst list (Apps (Apps (Apps _ _) _) _))’
            \\ qspecl_then [‘list’, ‘x2’] mp_tac subst_notin_frees
            \\ gvs [MAP_ZIP, DISJOINT_ALT] \\ impl_tac
            >- (gvs [Abbr ‘list’, MAP_ZIP] \\ rw [] \\ gvs [EVERY_MEM])
            \\ strip_tac \\ gvs [subst_Apps] \\ pop_assum kall_tac
            \\ ‘MAP (subst list) (MAP Var (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))))
                = MAP Value (MAP SND (FILTER FST (ZIP (bL3a, eL1))))’
              by (gvs [Abbr ‘list’, GSYM ZIP_APPEND]
                  \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def, REVERSE_APPEND, ALOOKUP_APPEND]
                  \\ gen_tac \\ strip_tac \\ rename1 ‘n < LENGTH (FILTER _ _)’
                  \\ drule_then assume_tac EL_MEM \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP]
                  \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘SND (EL n (FILTER FST (ZIP (bL3a, vL1a))))’]
                                 mp_tac $ iffRL ALOOKUP_NONE
                  \\ impl_tac \\ gvs []
                  >- (gvs [ALL_DISTINCT_APPEND, MAP_REVERSE, MAP_ZIP]
                      \\ first_x_assum irule
                      \\ disj1_tac \\ gvs [MEM_MAP, MEM_FILTER]
                      \\ gvs [MEM_EL, EL_ZIP, SF CONJ_ss, PULL_EXISTS]
                      \\ irule_at (Pos hd) EQ_REFL \\ gvs [])
                  \\ disch_then kall_tac
                  \\ qspecl_then [‘REVERSE (ZIP (MAP SND (if b then [(T,h)] else []),
                                                          if b then [v1] else []))’,
                                  ‘SND (EL n (FILTER FST (ZIP (bL3a, vL1a))))’]
                                 mp_tac $ iffRL ALOOKUP_NONE
                  \\ impl_tac \\ gvs []
                  >- (IF_CASES_TAC \\ gvs []
                      \\ strip_tac \\ gvs [ALL_DISTINCT_APPEND, MEM_MAP, MEM_FILTER, EL_MEM])
                  \\ disch_then kall_tac
                  \\ ‘ALL_DISTINCT (MAP FST (ZIP (MAP SND (FILTER FST (ZIP (bL3a,vL1a))),
                                                  MAP SND (FILTER FST (ZIP (bL3a,eL1))))))’
                    by gvs [MAP_ZIP, ALL_DISTINCT_APPEND]
                  \\ gvs [alookup_distinct_reverse]
                  \\ qspecl_then [‘ZIP (MAP SND (FILTER FST (ZIP (bL3a,vL1a))),
                                        MAP SND (FILTER FST (ZIP (bL3a,eL1))))’,
                                  ‘n’] mp_tac ALOOKUP_ALL_DISTINCT_EL
                  \\ gvs [EL_ZIP, EL_MAP])
            \\ gvs [] \\ pop_assum kall_tac
           \\ ‘MAP (subst list) (MAP2 (λb e. if b then Force e else e)
                                 (GENLIST (λn. n = i) (LENGTH valL1)) (MAP Var vL2))
                = MAP2 (λb e. if b then Force e else e)
                       (GENLIST (λn. n = i) (LENGTH valL1)) (MAP Value valL1)’
              by (gvs [Abbr ‘list’, GSYM ZIP_APPEND]
                  \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                  \\ gen_tac \\ strip_tac \\ rename1 ‘n < LENGTH _’
                  \\ qspecl_then [‘ZIP (vL2, valL1)’] assume_tac $ GEN_ALL alookup_distinct_reverse
                  \\ qspecl_then [‘ZIP (vL2, valL1)’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
                  \\ Cases_on ‘n = i’ \\ gvs [subst_def, REVERSE_APPEND, ALOOKUP_APPEND]
                  \\ gvs [MAP_ZIP, ALL_DISTINCT_APPEND, EL_ZIP])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst list) (MAP Var (MAP SND (if b then [(T, h)] else [])))
                = if b then [Value v1] else []’
               by (gvs [Abbr ‘list’, GSYM ZIP_APPEND]
                   \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def, REVERSE_APPEND, ALOOKUP_APPEND]
                   \\ IF_CASES_TAC \\ gvs []
                   \\ Cases \\ gvs []
                   \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘h’] assume_tac ALOOKUP_NONE
                   \\ gvs [MAP_REVERSE, MAP_ZIP, ALL_DISTINCT_APPEND])
            \\ gvs [] \\ pop_assum kall_tac
            \\ Cases_on ‘eval_to (k - 2) (Force (Value (EL i valL1))) = INL Diverge’ \\ gvs []
            >- (dxrule_then (qspec_then ‘i’ assume_tac) eval_to_Apps_arg_Div
                \\ gvs [EL_MAP2, EL_MAP]
                \\ qexists_tac ‘0’
                \\ rename1 ‘exp_rel x2 y2’ \\ qspecl_then [‘x2’, ‘y2’] assume_tac exp_rel_freevars
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono
                \\ gvs [subst_Apps, subst1_def, subst1_notin_frees, eval_to_Tick]
                \\ ‘MAP (subst [(h,w1)])
                    (MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                     (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Var h]))) =
                    MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                         (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’
                  by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                      \\ rw [subst1_def, EL_APPEND_EQN, EL_MAP]
                      \\ gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
                \\ gvs [] \\ pop_assum kall_tac
                \\ qmatch_goalsub_abbrev_tac ‘_ (INL Diverge) (eval_to _ (Apps expr2 _))’
                \\ qspecl_then [‘MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                                  (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL1 ++ [Value v1]))’,
                              ‘MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                                  (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’,
                                ‘i’, ‘k - 2’, ‘expr2’] mp_tac eval_to_Apps_arg_Div_exp_rel2
                \\ impl_tac \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN]
                \\ ‘LENGTH valL1 = SUC (LENGTH eL1)’ by gvs []
                \\ ‘EL i (eL1 ++ [v1]) = EL i valL1’
                  by (qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                      \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’]
                      \\ pop_assum $ qspec_then ‘i’ assume_tac
                      \\ gvs [EL_MAP2, EL_APPEND_EQN, EL_MAP]
                      \\ IF_CASES_TAC \\ gvs [eval_to_Value, NOT_LESS, GSYM LESS_EQ_IFF_LESS_SUC]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ gvs [eval_to_Value])
                \\ rw []
                >- gvs [EL_APPEND_EQN]
                >- (‘LENGTH valL1 = SUC (LENGTH eL1)’ by gvs []
                    \\ gvs [GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ gvs [EL_APPEND_EQN])
                >- gvs [GSYM ADD1, LIST_REL_EL_EQN]
                >- gvs [EL_APPEND_EQN]
                >- (‘LENGTH valL1 = SUC (LENGTH eL1)’ by gvs []
                    \\ gvs [GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ gvs [ EL_APPEND_EQN])
                >- (qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’] \\ rename1 ‘Force (Value (EL j _))’
                    \\ pop_assum $ qspec_then ‘j’ assume_tac
                    \\ gvs [EL_MAP2, EL_APPEND_EQN, EL_MAP]
                    \\ rename1 ‘eval_to _ expr’ \\ strip_tac
                    \\ qspecl_then [‘k - 2’, ‘expr’, ‘k - 1’] assume_tac eval_to_mono \\ gvs [])
                >- (qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_MAP2, EL_APPEND_EQN, EL_MAP]
                    \\ rename1 ‘eval_to _ expr’
                    \\ Cases_on ‘eval_to (k - 2) expr = INL Diverge’ \\ gs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gs [])
                >- gvs [eval_to_Value]
                >- (gvs [GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ gvs [eval_to_Value])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN]
                    \\ pop_assum $ qspec_then ‘i’ assume_tac
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, exp_rel_def]
                    \\ rpt $ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, exp_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN]
                    \\ pop_assum $ qspec_then ‘j’ assume_tac
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, exp_rel_def]
                    \\ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, exp_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN, eval_to_Value, exp_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, exp_rel_def, eval_to_Value]))
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ (Apps expr1 argL2)) _’
            \\ qspecl_then [‘argL2’, ‘expr1’, ‘k - 2’] mp_tac eval_to_Apps_no_INL
            \\ gvs [] \\ impl_tac
            >- (gvs [Abbr ‘argL2’, EL_MAP2, EL_MAP] \\ rw [eval_to_Value])
            \\ disch_then $ qx_choose_then ‘valL2’ assume_tac \\ gvs []
            \\ Cases_on ‘eval_to (k - 2) (Apps expr1 (MAP Value valL2)) = INL Diverge’ \\ gvs []
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono \\ gvs [] \\ pop_assum kall_tac
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono \\ gvs [] \\ pop_assum kall_tac
                \\ rename1 ‘exp_rel x2 y2’ \\ qspecl_then [‘x2’, ‘y2’] assume_tac exp_rel_freevars
                \\ gvs [subst_Apps, subst1_notin_frees, subst1_def, eval_to_Tick]
                \\ ‘MAP (subst [(h,w1)])
                    (MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                     (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Var h]))) =
                    MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                         (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’
                  by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                      \\ rw [subst1_def, EL_APPEND_EQN, EL_MAP]
                      \\ gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
                \\ gvs [] \\ pop_assum kall_tac
                \\ qmatch_goalsub_abbrev_tac ‘Apps _ argL1'’
                \\ ‘∀i. i < LENGTH argL1' ⇒ eval_to (k - 2) (EL i argL1') = INL Diverge
                                            ∨ ($= +++ v_rel) (INR (EL i valL2)) (eval_to (k - 2) (EL i argL1'))’
                  by (rw [] \\ rename1 ‘i2 < _’
                      \\ Cases_on ‘eval_to (k - 2) (EL i2 argL1') = INL Diverge’ \\ gvs []
                      \\ gvs [Abbr ‘argL1'’, EL_MAP2, EL_MAP, EL_APPEND_EQN] \\ rw []
                      >- (last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value (EL i eL1))’,
                                                      ‘Force (Value (EL i eL2))’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘i’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [exp_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [exp_rel_def])
                      >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                      ‘Force (Value (EL i2 eL2))’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [exp_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [exp_rel_def])
                      >- (gvs [eval_to_Value, LIST_REL_EL_EQN, Abbr ‘argL1’, Abbr ‘argL2’]
                          \\ rpt $ last_x_assum $ qspec_then ‘i2’ assume_tac
                          \\ gvs [EL_MAP2, EL_APPEND_EQN, EL_MAP, eval_to_Value])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ gvs [eval_to_Value, LIST_REL_EL_EQN, Abbr ‘argL1’, Abbr ‘argL2’]
                          \\ rpt $ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                          \\ gvs [EL_MAP2, EL_APPEND_EQN, EL_MAP, eval_to_Value]))
                \\ qmatch_goalsub_abbrev_tac ‘_ (INL Diverge) (eval_to _ (Apps expr2 _))’
                \\ qspecl_then [‘argL1'’, ‘valL2’, ‘expr2’, ‘k  - 2’] mp_tac eval_to_Apps_Div_or_INR \\ gvs []
                \\ impl_tac >- gvs [Abbr ‘argL1'’, LIST_REL_EL_EQN, Abbr ‘argL2’]
                \\ rw [] \\ gvs []
                \\ rename1 ‘_ (INL Diverge) (eval_to _ (Apps _ (MAP Value valL2')))’
                \\ Cases_on ‘eval_to (k - 2) (Apps expr2 (MAP Value valL2')) = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono
                \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Apps expr1 (MAP Value valL2)’,
                                               ‘Apps expr2 (MAP Value valL2')’] mp_tac
                \\ gvs [] \\ impl_tac \\ gvs []
                \\ irule exp_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP, exp_rel_def]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’]
                \\ irule exp_rel_Apps
                \\ conj_tac
                >- (irule exp_rel_Apps \\ gvs [EVERY2_MAP, subst1_def, exp_rel_def]
                    \\ qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λx.x’]
                                   assume_tac $ GEN_ALL LIST_REL_FILTER
                    \\ gs [GSYM FST_THM] \\ pop_assum irule \\ gvs [MAP_ZIP]
                    \\ irule LIST_REL_mono
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                    \\ gvs [LIST_REL_EL_EQN, EL_ZIP])
                \\ IF_CASES_TAC \\ gvs [subst1_def, exp_rel_def])

            \\ Q.REFINE_EXISTS_TAC ‘j + j1 + j2’ \\ gvs []
            \\ ‘eval_to (j + k) y ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ ‘eval_to (j1 + k) g ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ rename1 ‘exp_rel x2 y2’ \\ qspecl_then [‘x2’, ‘y2’] assume_tac exp_rel_freevars
            \\ gvs [subst_Apps, subst1_notin_frees, subst1_def, eval_to_Tick]
            \\ ‘MAP (subst [(h,w1)])
                (MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                 (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Var h]))) =
                MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                     (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’
              by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                  \\ rw [subst1_def, EL_APPEND_EQN, EL_MAP]
                  \\ gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                  \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps _ argL1'))’
            \\ ‘∀i. i < LENGTH argL1' ⇒ ∃j. ($= +++ v_rel) (INR (EL i valL2)) (eval_to (j + k - 2) (EL i argL1'))’
              by (rw [] \\ rename1 ‘i2 < _’
                  \\ gvs [Abbr ‘argL1'’, EL_MAP2, EL_MAP, EL_APPEND_EQN] \\ rw []
                  >- (last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value (EL i eL1))’,
                                                  ‘Force (Value (EL i eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ first_x_assum irule \\ rw [exp_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ first_x_assum irule \\ rw [exp_rel_def])
                  >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                  ‘Force (Value (EL i2 eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gvs []
                      \\ first_x_assum irule \\ rw [exp_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gs []
                      \\ first_x_assum irule \\ rw [exp_rel_def])
                  >- (gvs [eval_to_Value, LIST_REL_EL_EQN, Abbr ‘argL1’, Abbr ‘argL2’]
                      \\ rpt $ last_x_assum $ qspec_then ‘i2’ assume_tac
                      \\ gvs [EL_MAP2, EL_APPEND_EQN, EL_MAP, eval_to_Value])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ gvs [eval_to_Value, LIST_REL_EL_EQN, Abbr ‘argL1’, Abbr ‘argL2’]
                      \\ rpt $ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                      \\ gvs [EL_MAP2, EL_APPEND_EQN, EL_MAP, eval_to_Value]))
            \\ qspecl_then [‘argL1'’, ‘valL2’, ‘k  - 2’] mp_tac eval_to_INR_List \\ impl_tac
            >- (gvs [LIST_REL_EL_EQN] \\ conj_asm1_tac \\ gvs []
                \\ gvs [Abbr ‘argL1'’, Abbr ‘argL2’])
            \\ pop_assum kall_tac
            \\ disch_then $ qx_choose_then ‘vL2’ $ qx_choose_then ‘j2’ assume_tac
            \\ Q.REFINE_EXISTS_TAC ‘j2 + j3’
            \\ qspecl_then [‘argL1'’, ‘vL2’, ‘y2’, ‘j2 + k - 2’] mp_tac eval_to_Apps_LIST_INR
            \\ impl_tac \\ gvs []
            >- (gvs [LIST_REL_EL_EQN] \\ rw []
                \\ rename1 ‘j + _ - 2’
                \\ first_x_assum $ dxrule_then $ qspec_then ‘j’ assume_tac \\ gvs [])
            \\ disch_then kall_tac
            \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Apps x2 (MAP Value valL2)’, ‘Apps y2 (MAP Value vL2)’] mp_tac
            \\ gvs [] \\ impl_tac
            >- (irule exp_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                \\ rw [exp_rel_def] \\ gvs [])
            \\ disch_then $ qx_choose_then ‘j3’ assume_tac \\ qexists_tac ‘j3’
            \\ Cases_on ‘eval_to (j3 + k − 2) (Apps y2 (MAP Value vL2)) = INL Diverge’ \\ gs []
            >- (Cases_on ‘eval_to (k - 2) (Apps x2 (MAP Value valL2))’ \\ gvs [])
            \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
        \\ qexists_tac ‘j + j1’
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
        \\ gvs [subst_Lams, subst_Apps, eval_to_Lams, subst_def]
        \\ gvs [v_rel_def] \\ disj2_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs [ALL_DISTINCT_APPEND]
        \\ irule_at (Pos last) exp_rel_subst
        \\ gvs [EXISTS_PROD, PULL_EXISTS, subst1_notin_frees]
        \\ first_assum $ irule_at $ Pos hd \\ first_assum $ irule_at $ Pos hd
        \\ Q.REFINE_EXISTS_TAC ‘l1 ++ l2’ \\ gvs [subst1_notin_frees]
        \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs [] \\ pop_assum $ irule_at Any
        \\ irule_at (Pos hd) EQ_REFL
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs [] \\ pop_assum $ irule_at Any
        \\ qexists_tac ‘i’ \\ gvs []
        \\ qexists_tac ‘eL2 ++ [w1]’ \\ qexists_tac ‘eL1 ++ [v1]’
        \\ qexists_tac ‘bL2’
        \\ gvs [] \\ rw [] \\ gvs []
        >- (gvs [MAP2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN]
            \\ irule LIST_EQ \\ rw [EL_MAP, EL_ZIP, EL_MAP2, subst1_def, EL_APPEND_EQN]
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (rw [] \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (rw [] \\ gvs [EL_MEM]))
        >- (gvs [MAP2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN]
            \\ irule LIST_EQ \\ rw [EL_MAP, EL_ZIP, EL_MAP2, subst1_def]
            \\ (rw [EL_APPEND_EQN, subst1_def, EL_MAP]
                >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ gvs [subst1_def])
                \\ IF_CASES_TAC \\ gvs [EL_MEM]))
        >- gvs [ALL_DISTINCT_APPEND])

    >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
        \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
        \\ gvs [OPTREL_def]
        \\ rename1 ‘exp_rel x0 _’ \\ Cases_on ‘x0’ \\ gvs [exp_rel_def]
        \\ IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ rename1 ‘subst (_ ++ [(s2, v1)]) _’
        \\ rename1 ‘exp_rel body body2’
        \\ last_x_assum $ qspecl_then [‘k - 1’, ‘subst (MAP (λ(g,x). (g, Recclosure xs g)) xs ++ [(s2, v1)]) body’,
                                       ‘subst (MAP (λ(g,x).(g, Recclosure ys g)) ys ++ [(s2, w1)]) body2’] mp_tac
        \\ gs [] \\ impl_tac
        >- (gs [] \\ irule exp_rel_subst \\ gvs []
            \\ gvs [LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
            \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
            \\ rename1 ‘n < _’ \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
            \\ irule v_rel_Recclosure \\ gvs [LIST_REL_EL_EQN, EL_MAP])
        \\ disch_then $ qx_choose_then ‘j2’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x). (g, Recclosure xs g)) xs ++ [(s2,v1)]) body) = INL Diverge’
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k y’
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k g’ \\ gvs []
            \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x). (g, Recclosure ys g)) ys ++ [(s2,w1)]) body2)
                         = INL Diverge’ \\ gvs []
            \\ dxrule_then (qspec_then ‘j2 + k - 1’ assume_tac) eval_to_mono
            \\ gvs [])
        \\ qexists_tac ‘j + j1 + j2’
        \\ first_x_assum $ qspec_then ‘j + j2’ assume_tac
        \\ first_x_assum $ qspec_then ‘j1 + j2’ assume_tac
        \\ gvs []
        \\ ‘eval_to (j2 + k - 1) (subst (MAP (λ(g,x). (g, Recclosure ys g)) ys ++ [(s2,w1)]) body2)
                     ≠ INL Diverge’
          by (strip_tac
              \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs ++ [(s2,v1)]) body)’
              \\ gvs [])
        \\ dxrule_then (qspec_then ‘j + j1 + j2 + k - 1’ assume_tac) eval_to_mono
        \\ gvs []))
  >~ [‘Let opt x1 y1’] >- (
    Cases_on ‘opt’ >~[‘Seq x1 y1’]
    >- (gvs [exp_rel_def, eval_to_def]
        \\ IF_CASES_TAC \\ gs [] >- (qexists_tac ‘0’ \\ gs [])
        \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gvs []
        \\ last_x_assum kall_tac
        \\ last_assum $ qspec_then ‘x1’ assume_tac
        \\ last_x_assum $ qspec_then ‘y1’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) x1 = INL Type_error’ \\ gs []
        \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
        >- (qexists_tac ‘j’ \\ Cases_on ‘eval_to (j + k - 1) x2’ \\ gvs [])
        \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j1’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) y1 = INL Diverge’ \\ gvs []
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to (k - 1) x2 = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j + k - 1’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to (k - 1) x2’ \\ gvs []
            \\ Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono
            \\ gvs [])
        \\ Cases_on ‘eval_to (j + k - 1) x2’ \\ gvs []
        \\ qexists_tac ‘j + j1’
        \\ ‘eval_to (j + k - 1) x2 ≠ INL Diverge’ by gvs []
        \\ dxrule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono \\ gvs []
        \\ ‘eval_to (j1 + k - 1) y2 ≠ INL Diverge’ by (strip_tac \\ Cases_on ‘eval_to (k - 1) y1’ \\ gvs [])
        \\ dxrule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono \\ gvs [])
    \\ gvs [Once exp_rel_def, eval_to_def]
    >~[‘Lams _ _’]
    >- (IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs [])
        \\ gvs [eval_to_Lams, subst1_def, subst_Lams, subst_Apps, eval_to_def]
        \\ IF_CASES_TAC \\ gs [] >- (qexists_tac ‘0’ \\ gvs [])
        \\ last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gs []
        \\ last_x_assum irule \\ gvs []
        \\ irule exp_rel_subst \\ gvs []
        \\ irule_at Any exp_rel_subst \\ gvs []
        \\ conj_tac
        >- (irule v_rel_Closure \\ irule exp_rel_Lams
            \\ irule exp_rel_Apps \\ gvs []
            \\ rpt $ pop_assum kall_tac
            \\ rw [LIST_REL_EL_EQN, EL_MAP2, EL_MAP]
            \\ IF_CASES_TAC \\ gvs [exp_rel_def])
        \\ gvs [v_rel_def] \\ disj2_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ ‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs [] \\ pop_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs [] \\ pop_assum $ irule_at Any
        \\ qexists_tac ‘[]’ \\ gvs []
        \\ irule_at (Pos hd) EQ_REFL
        \\ first_x_assum $ irule_at Any
        \\ rw []
        >- (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2] \\ rw []
            \\ gvs [subst_def] \\ IF_CASES_TAC \\ gvs [EL_MEM])
        >- (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2] \\ rw []
            \\ gvs [subst_def] \\ IF_CASES_TAC \\ gvs [EL_MEM])
        >- (rename1 ‘exp_rel x1 (subst1 _ _ x2)’
            \\ qspecl_then [‘x1’, ‘x2’] assume_tac exp_rel_freevars
            \\ gvs [subst1_notin_frees]))
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ gs [])
    \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ last_x_assum kall_tac \\ gs []
    \\ Cases_on ‘eval_to (k - 1) x1 = INL Type_error’ \\ gs []
    \\ first_assum (dxrule_then $ drule_then $ qx_choose_then ‘j’ assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
    >~ [‘($= +++ v_rel) (INL _) _’] >- (
      Cases_on ‘eval_to (j + k - 1) x2’ \\ gs []
      \\ qexists_tac ‘j’ \\ simp [])
    \\ Cases_on ‘eval_to (j + k - 1) x2’ \\ gs []
    \\ rename1 ‘v_rel v1 w1’ \\ rename1 ‘subst1 m _ _’
    \\ ‘exp_rel (subst1 m v1 y1) (subst1 m w1 y2)’
      by (irule exp_rel_subst \\ gs [])
    \\ last_x_assum (drule_then $ drule_then $ qx_choose_then ‘j1’ assume_tac)
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
    \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ last_x_assum kall_tac \\ gs []
    \\ Cases_on ‘eval_to (k - 1) x1 = INL Type_error’ \\ gs []
    \\ first_assum (dxrule_then $ drule_then $ qx_choose_then ‘j’ assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ gs []
    >~ [‘($= +++ v_rel) (INL err) _’] >- (
      Cases_on ‘eval_to (j + k - 1) x2’ \\ gs []
      \\ qexists_tac ‘j’
      \\ simp [])
    \\ Cases_on ‘eval_to (j + k - 1) x2’ \\ gs []
    \\ rename1 ‘v_rel v1 w1’
    \\ IF_CASES_TAC \\ gvs [v_rel_def]
    >- (first_x_assum $ dxrule_then $ dxrule_then $ qx_choose_then ‘j1’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) y1 = INL Diverge’ \\ gs []
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
    >- (first_x_assum $ dxrule_then $ dxrule_then $ qx_choose_then ‘j2’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) z1 = INL Diverge’ \\ gs []
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
        \\ qexists_tac ‘j2 + j’ \\ gs []))
  >~ [‘Letrec f x’] >- (
    gvs [Once exp_rel_def, eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘exp_rel x y’
    \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ last_x_assum kall_tac
    \\ gvs []
    \\ pop_assum irule
    \\ gvs [subst_funs_def]
    \\ irule exp_rel_subst
    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
    \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
    \\ rename1 ‘n < LENGTH g’
    \\ ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gs [] \\ gvs [EL_MAP]
    \\ irule v_rel_Recclosure
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >~ [‘Force x’] >- (
    qpat_x_assum ‘_ ≠ INL Type_error’ mp_tac \\ rgs [Once exp_rel_def]
    \\ once_rewrite_tac [eval_to_def] \\ simp []
    \\ pop_assum kall_tac
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ simp [])
    \\ rw []
    \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gs []
    \\ first_x_assum $ qspec_then ‘x’ assume_tac \\ gs []
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
        >- (‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
            \\ gvs [OPTREL_def]
            \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gs []
            \\ Cases_on ‘x0’ \\ gvs []))
      \\ pairarg_tac \\ gvs []
      \\ Cases_on ‘∃xs n. v1 = Recclosure xs n’ \\ gvs [v_rel_def]
      >- (gvs [dest_anyThunk_def, v_rel_def]
          \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
          \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gvs []
          \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ rename1 ‘subst_funs xs x2’ \\ rename1 ‘exp_rel x2 y2’
          \\ last_x_assum $ qspecl_then [‘k - 1’, ‘subst_funs xs x2’, ‘subst_funs ys y2’] mp_tac
          \\ gs [] \\ impl_tac
          >- (gvs [subst_funs_def] \\ irule exp_rel_subst
              \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
              \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
              \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ irule v_rel_Recclosure \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          \\ disch_then $ qx_choose_then ‘j1’ assume_tac
          \\ Cases_on ‘eval_to (k - 1) (subst_funs xs x2) = INL Diverge’ \\ gvs []
          >- (qexists_tac ‘0’
              \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
              \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
              \\ Cases_on ‘eval_to k y’ \\ gvs []
              \\ Cases_on ‘eval_to (k - 1) (subst_funs ys y2) = INL Diverge’ \\ gvs []
              \\ dxrule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono \\ gvs [])
          \\ qexists_tac ‘j + j1’
          \\ ‘eval_to (j + k) y ≠ INL Diverge’ by gvs []
          \\ dxrule_then (qspec_then ‘j + j1 + k’ assume_tac) eval_to_mono \\ gvs []
          \\ ‘eval_to (j1 + k - 1) (subst_funs ys y2) ≠ INL Diverge’
            by (strip_tac \\ Cases_on ‘eval_to (k - 1) (subst_funs xs x2)’ \\ gvs [])
          \\ dxrule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono \\ gvs [])
      \\ ‘∃wx' binds'. dest_anyThunk w1 = INR (wx', binds') ∧
                       (v_rel +++ exp_rel) wx wx' ∧
                       MAP FST binds = MAP FST binds' ∧
                       EVERY ok_bind (MAP SND binds) ∧
                       EVERY ok_bind (MAP SND binds') ∧
                       LIST_REL exp_rel (MAP SND binds) (MAP SND binds')’
        by (Cases_on ‘v1’ \\ Cases_on ‘w1’
            \\ gvs [v_rel_def]
            \\ gvs [dest_anyThunk_def, v_rel_def])
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
      \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gs []
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
    \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gs []
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
    \\ first_x_assum $ qspec_then ‘x’ assume_tac
    \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gs []
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
      \\ ‘∀n. n < LENGTH ys ⇒
            ∃j. ($= +++ v_rel) (eval_to k (EL n xs))
                               (eval_to (j + k) (EL n ys))’
        by (rw [] \\ last_x_assum kall_tac \\ last_x_assum irule
            \\ gvs []
            \\ conj_tac >- (strip_tac \\ gvs [])
            \\ assume_tac exp_size_lemma \\ gvs [MEM_EL, PULL_EXISTS]
            \\ first_x_assum $ qspec_then ‘xs’ assume_tac \\ gvs []
            \\ pop_assum $ dxrule_then assume_tac \\ gvs [])
      \\ last_x_assum kall_tac
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
      \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ last_x_assum kall_tac \\ gs []
      \\ Cases_on ‘eval_to (k - 1) x = INL Type_error’ \\ gs []
      \\ first_x_assum (drule_then $ drule_then $ qx_choose_then ‘j’ assume_tac)
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
      \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ last_x_assum kall_tac \\ gs []
      \\ Cases_on ‘eval_to (k - 1) x = INL Type_error’ \\ gs []
      \\ first_x_assum (drule_then $ drule_then $ qx_choose_then ‘j’ assume_tac)
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
        by (rw [] \\ last_x_assum irule
            \\ gvs [result_map_def]
            \\ last_x_assum kall_tac \\ last_x_assum mp_tac \\ IF_CASES_TAC \\ gs []
            \\ disch_then kall_tac \\ strip_tac
            \\ rename1 ‘n < _’
            \\ gvs [MEM_EL] \\ first_x_assum $ qspec_then ‘n’ assume_tac
            \\ gvs [EL_MAP])
      \\ last_x_assum kall_tac
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
      \\ qpat_x_assum ‘_ ≠ INL Type_error’ kall_tac
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
  exp_rel x y ∧ eval x ≠ INL Type_error ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ ‘eval_to (MAX k j) x ≠ INL Type_error’
      by (strip_tac \\ qpat_x_assum ‘eval _ ≠ _’ mp_tac \\ simp [eval_def]
          \\ DEEP_INTRO_TAC some_intro \\ rw []
          >- (rename1 ‘eval_to x2 x = INL Type_error’
              \\ ‘eval_to (MAX x2 (MAX k j)) x = eval_to (MAX k j) x’
                by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
              \\ ‘eval_to (MAX x2 (MAX k j)) x = eval_to x2 x’
                by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
              \\ gvs [])
          \\ first_x_assum $ irule_at Any)
    \\ drule_all_then (qx_choose_then ‘m’ assume_tac) exp_rel_eval_to
    \\ ‘eval_to ( MAX k j) x = eval_to k x’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to (m + MAX k j) y = eval_to j y’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ ‘eval_to j x ≠ INL Type_error’ by gvs []
    \\ drule_all_then (qx_choose_then ‘m’ assume_tac) exp_rel_eval_to \\ gs []
    \\ drule_then (qspec_then ‘m + j’ assume_tac) eval_to_mono \\ gs [])
  \\ rename1 ‘_ _ (eval_to k x)’
  \\ ‘eval_to k x ≠ INL Type_error’
    by (strip_tac \\ qpat_x_assum ‘eval _ ≠ _’ mp_tac \\ simp [eval_def]
        \\ DEEP_INTRO_TAC some_intro \\ rw []
        >- (rename1 ‘eval_to x2 x = INL Type_error’
            \\ ‘eval_to (MAX x2 k) x = eval_to k x’
              by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
            \\ ‘eval_to (MAX x2 k) x = eval_to x2 x’
              by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
            \\ gvs [])
        \\ first_x_assum $ irule_at Any)
  \\ drule_all_then (qx_choose_then ‘m’ assume_tac) exp_rel_eval_to
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
  |> Q.INST [‘Rv’|->‘v_rel’, ‘Re’|->‘exp_rel’,‘allow_error’|->‘F’]
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

Theorem v_rel_eval_subst:
  v_rel (Closure s e) (Closure s f) ∧ v_rel v w ∧ eval (subst1 s v e) ≠ INL Type_error ⇒
  ($= +++ v_rel) (eval (subst1 s v e)) (eval (subst1 s w f))
Proof
  gvs [GSYM eval_App_Values]
  \\ rw [] \\ irule exp_rel_eval
  \\ gvs [exp_rel_def]
QED

Theorem delay_lam_apply_closure[local]:
  v_rel v1 w1 ∧
  v_rel v2 w2 ∧
  apply_closure v1 v2 f ≠ Err ∧
  f (INL Type_error) = Err ∧
  (∀x y. ($= +++ v_rel) x y ∧ f x ≠ Err ⇒ next_rel v_rel (f x) (g y)) ⇒
    next_rel v_rel (apply_closure v1 v2 f) (apply_closure w1 w2 g)
Proof
  rw [apply_closure_def]
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [v_rel_def, dest_anyClosure_def]
  >- (
    first_x_assum irule \\ fs []
    \\ irule exp_rel_eval
    \\ conj_tac
    >- (strip_tac \\ gvs [])
    \\ irule exp_rel_subst \\ gs [])
  >- (first_x_assum irule \\ fs []
      \\ irule v_rel_eval_subst \\ fs []
      \\ conj_tac >- (strip_tac \\ gvs [])
      \\ gvs [v_rel_def] \\ disj2_tac
      \\ rpt $ irule_at Any EQ_REFL \\ gvs [])
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs []
      \\ drule_then assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
      \\ gvs [EVERY_EL, EL_MAP]
      \\ first_x_assum irule \\ fs []
      \\ irule exp_rel_eval
      \\ conj_tac >- (strip_tac \\ gvs [])
      \\ irule exp_rel_subst
      \\ simp [EVERY2_MAP, LAMBDA_PROD, v_rel_def, MAP_MAP_o, combinTheory.o_DEF,
               GSYM FST_THM]
      \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EVERY_EL, EL_MAP, LIST_EQ_REWRITE])
QED

Theorem delay_lam_rel_ok[local]:
  rel_ok F v_rel
Proof
  rw [rel_ok_def, v_rel_def, exp_rel_def]
  \\ rw [delay_lam_apply_force, delay_lam_apply_closure]
QED

Theorem delay_lam_sim_ok[local]:
  sim_ok F v_rel exp_rel
Proof
  rw [sim_ok_def, exp_rel_eval, exp_rel_subst]
QED

Theorem delay_lam_semantics:
  exp_rel x y ∧
  safe_itree (semantics x Done []) ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics \\ gs []
  \\ first_assum (irule_at Any)
  \\ qexists_tac ‘F’ \\ gs []
  \\ irule_at Any delay_lam_rel_ok
  \\ irule_at Any delay_lam_sim_ok
QED

val _ = export_theory ();
