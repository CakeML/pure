(*
 Relation to rewrite function definitions to remove Delay
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory;

val _ = new_theory "thunk_combine_Forcing_Lambdas";

Inductive combine_rel:
[~Var:]
  (∀n. combine_rel (Var n) (Var n)) ∧
[~Value:]
  (∀v w.
     v_rel v w ⇒
       combine_rel (Value v) (Value w)) ∧
[~Prim:]
  (∀op xs ys.
     LIST_REL combine_rel xs ys ⇒
       combine_rel (Prim op xs) (Prim op ys)) ∧
[~Monad:]
  (∀mop xs ys.
     LIST_REL combine_rel xs ys ⇒
       combine_rel (Monad mop xs) (Monad mop ys)) ∧
[~App:]
  (∀f g x y.
     combine_rel f g ∧
     combine_rel x y ⇒
       combine_rel (App f x) (App g y)) ∧
[~Lam:]
  (∀s x y.
     combine_rel x y ⇒
       combine_rel (Lam s x) (Lam s y)) ∧
[~Letrec:]
  (∀f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL combine_rel (MAP SND f) (MAP SND g) ∧
     combine_rel x y ⇒
     combine_rel (Letrec f x) (Letrec g y)) ∧
[~Letrec_Lams_combine1:]
  (∀f g y1 y2 v1 v2 x1 x2 vL1 vL2 vL3 bL1 bL2 bL3 i.
     MAP FST f = MAP FST g ∧
     ¬MEM v1 (MAP FST f) ∧ ¬MEM v2 (MAP FST f) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL combine_rel (MAP SND f) (MAP SND g) ∧
     combine_rel y1 y2 ∧ combine_rel x1 x2 ∧

     LENGTH vL1 = LENGTH bL2 ∧ LENGTH vL1 = LENGTH vL2 ∧ LENGTH vL1 = LENGTH bL3 ∧
     ¬MEM v1 vL1 ∧ ALL_DISTINCT vL1 ∧ vL1 ≠ [] ∧ ALL_DISTINCT (vL3 ++ vL2) ∧
     (∀i. i < LENGTH vL1 ⇒ (EL i vL1 = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL3 bL2 ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL3, vL1))) ∧

     i < LENGTH vL1 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL1) ∧
     EVERY (λv. v ∉ freevars x1) (vL1 ++ vL2 ++ vL3) ⇒
     combine_rel (Letrec (SNOC (v1, Lams (vL3++vL2) (Apps x1
                                                 (MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e)
                                                       bL1 (MAP Var vL2))))
                      (SNOC (v2, Lams vL1 (Apps (Var v1)
                                           (MAP Var vL3 ++
                                            (MAP2 (λb e. if b then Force e else e)
                                             bL2 (MAP Var vL1)))))
                       f)) y1)
             (Letrec (SNOC (v1, Lams (vL3++vL2) (Apps x2
                                                 (MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e)
                                                       bL1 (MAP Var vL2))))
                      (SNOC (v2, Lams vL1 (Tick (Apps x2
                                                 (MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP2 (λb e. if b then Force e else e)
                                                        bL2 (MAP Var vL1))))))
                       g)) y2)) ∧
[~Letrec_Lams_combine2:]
  (∀f g y1 y2 v1 v2 x1 x2 vL1 vL2 vL3 bL1 bL2 bL3 i.
     MAP FST f = MAP FST g ∧
     ¬MEM v1 (MAP FST f) ∧ ¬MEM v2 (MAP FST f) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL combine_rel (MAP SND f) (MAP SND g) ∧
     combine_rel y1 y2 ∧ combine_rel x1 x2 ∧

     LENGTH vL1 = LENGTH bL2 ∧ LENGTH vL1 = LENGTH vL2 ∧ LENGTH vL1 = LENGTH bL3 ∧
     ¬MEM v1 vL1 ∧ ALL_DISTINCT vL1 ∧ vL1 ≠ [] ∧ ALL_DISTINCT (vL3 ++ vL2) ∧
     (∀i. i < LENGTH vL1 ⇒ (EL i vL1 = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL3 bL2 ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL3, vL1))) ∧

     i < LENGTH vL1 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL1) ∧
     EVERY (λv. v ∉ freevars x1) (vL1 ++ vL2 ++ vL3) ⇒
     combine_rel (Letrec (SNOC (v1, Lams (vL3++vL2) (Apps x1
                                                 (Var (EL i vL2)::MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e)
                                                       bL1 (MAP Var vL2))))
                      (SNOC (v2, Lams vL1 (Apps (Var v1)
                                           (MAP Var vL3 ++
                                            (MAP2 (λb e. if b then Force e else e)
                                             bL2 (MAP Var vL1)))))
                       f)) y1)
             (Letrec (SNOC (v1, Lams (vL3++vL2) (Apps x2
                                                 (Var (EL i vL2)::MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e)
                                                       bL1 (MAP Var vL2))))
                      (SNOC (v2, Lams vL1 (Tick (Apps x2
                                                 (Var (EL i vL1)::MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP2 (λb e. if b then Force e else e)
                                                        bL2 (MAP Var vL1))))))
                       g)) y2)) ∧
[~Let:]
  (∀opt x1 y1 x2 y2.
     combine_rel x1 x2 ∧
     combine_rel y1 y2 ⇒
     combine_rel (Let opt x1 y1) (Let opt x2 y2)) ∧
[~Let_Lams_combine1:]
  (∀v1 v2 vL1 vL2 vL3 bL1 bL2 bL3 x1 x2 y1 y2 i.
     LENGTH vL1 = LENGTH bL2 ∧ LENGTH vL1 = LENGTH vL2 ∧ LENGTH vL1 = LENGTH bL3 ∧
     ¬MEM v1 vL1 ∧ ALL_DISTINCT vL1 ∧ vL1 ≠ [] ∧ ALL_DISTINCT (vL3 ++ vL2) ∧
     (∀i. i < LENGTH vL1 ⇒ (EL i vL1 = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL3 bL2 ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL3, vL1))) ∧

     i < LENGTH vL1 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL1) ∧
     v1 ∉ freevars x1 ∧ EVERY (λv. v ∉ freevars x1) (vL1 ++ vL2 ++ vL3) ∧

     combine_rel x1 x2 ∧ combine_rel y1 y2 ∧ v1 ≠ v2 ⇒
     combine_rel (Let (SOME v1) (Lams (vL3 ++ vL2) (Apps x1 (MAP Var vL3 ++
                                                         MAP2 (λb e. if b then Force e else e)
                                                                  bL1 (MAP Var vL2))))
              (Let (SOME v2) (Lams vL1 (Apps (Var v1) (MAP Var vL3 ++
                                                       MAP2 (λb e. if b then Force e else e)
                                                                bL2 (MAP Var vL1)))) y1))
             (Let (SOME v1) (Lams (vL3 ++ vL2) (Apps x2 (MAP Var vL3 ++
                                                         MAP2 (λb e. if b then Force e else e)
                                                                  bL1 (MAP Var vL2))))
              (Let (SOME v2) (Lams vL1 (Tick (Apps x2
                                              (MAP Var vL3 ++
                                               MAP2 (λb e. if b then Force e else e) bL1
                                                    (MAP2 (λb e. if b then Force e else e)
                                                          bL2 (MAP Var vL1)))))) y2))) ∧
[~Let_Lams_combine2:]
  (∀v1 v2 vL1 vL2 vL3 bL1 bL2 bL3 x1 x2 y1 y2 i.
     LENGTH vL1 = LENGTH bL2 ∧ LENGTH vL1 = LENGTH vL2 ∧ LENGTH vL1 = LENGTH bL3 ∧
     ¬MEM v1 vL1 ∧ ALL_DISTINCT vL1 ∧ vL1 ≠ [] ∧ ALL_DISTINCT (vL3 ++ vL2) ∧
     (∀i. i < LENGTH vL1 ⇒ (EL i vL1 = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL3 bL2 ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL3, vL1))) ∧

     i < LENGTH vL1 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL1) ∧
     v1 ∉ freevars x1 ∧ EVERY (λv. v ∉ freevars x1) (vL1 ++ vL2 ++ vL3) ∧

     combine_rel x1 x2 ∧ combine_rel y1 y2 ∧ v1 ≠ v2 ⇒
     combine_rel (Let (SOME v1) (Lams (vL3 ++ vL2) (Apps x1 (Var (EL i vL2)::MAP Var vL3 ++
                                                         MAP2 (λb e. if b then Force e else e)
                                                              bL1 (MAP Var vL2))))
              (Let (SOME v2) (Lams vL1 (Apps (Var v1)(MAP Var vL3 ++
                                                      MAP2 (λb e. if b then Force e else e)
                                                           bL2 (MAP Var vL1)))) y1))
             (Let (SOME v1) (Lams (vL3 ++ vL2) (Apps x2 (Var (EL i vL2)::
                                                         MAP Var vL3 ++
                                                         MAP2 (λb e. if b then Force e else e)
                                                              bL1 (MAP Var vL2))))
              (Let (SOME v2) (Lams vL1 (Tick (Apps x2
                                              (Var (EL i vL1)::
                                               MAP Var vL3 ++
                                               MAP2 (λb e. if b then Force e else e) bL1
                                                    (MAP2 (λb e. if b then Force e else e)
                                                     bL2 (MAP Var vL1)))))) y2))) ∧
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     combine_rel x1 x2 ∧
     combine_rel y1 y2 ∧
     combine_rel z1 z2 ⇒
       combine_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[~Delay:]
  (∀x y.
     combine_rel x y ⇒
       combine_rel (Delay x) (Delay y)) ∧
[~Force:]
  (∀x y.
     combine_rel x y ⇒
     combine_rel (Force x) (Force y)) ∧
[~MkTick:]
  (∀x y. combine_rel x y ⇒ combine_rel (MkTick x) (MkTick y)) ∧
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Monadic:]
  (∀s vs ws.
     LIST_REL combine_rel vs ws ⇒
       v_rel (Monadic s vs) (Monadic s ws)) ∧
[v_rel_Closure:]
  (∀s x y.
     combine_rel x y ⇒
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
     combine_rel x y ⇒
     v_rel (Closure (HD vL1b)
            (Lams (TL vL1b) (Apps (Value (
                                   Closure (HD (vL3a ++ vL3b ++ vL2))
                                   (Lams (TL (vL3a ++ vL3b ++ vL2))
                                    (Apps x (MAP Var vL3a ++ MAP Var vL3b ++
                                             MAP2 (λb e. if b then Force e else e)
                                                  bL1 (MAP Var vL2))))))
                             (MAP Value eL1a ++ MAP Var vL3b ++
                              MAP2 (λb e. if b then Force e else e) bL2
                                   (MAP Value eL1 ++ MAP Var vL1b)))))
           (Closure (HD vL1b)
            (Lams (TL vL1b)(Tick(Apps y
                                 (MAP Value eL2a ++ MAP Var vL3b ++
                                  MAP2 (λb e. if b then Force e else e) bL1
                                       (MAP2 (λb e. if b then Force e else e) bL2
                                        (MAP Value eL2 ++ MAP Var vL1b)))))))) ∧
[v_rel_Closure_combine2:]
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
     combine_rel x y ⇒
     v_rel (Closure (HD vL1b)
            (Lams (TL vL1b) (Apps (Value (
                                   Closure (HD (vL3a ++ vL3b ++ vL2))
                                   (Lams (TL (vL3a ++ vL3b ++ vL2))
                                    (Apps x (Var (EL i vL2)::
                                             MAP Var vL3a ++ MAP Var vL3b ++
                                             MAP2 (λb e. if b then Force e else e)
                                                  bL1 (MAP Var vL2))))))
                             (MAP Value eL1a ++ MAP Var vL3b ++
                              MAP2 (λb e. if b then Force e else e) bL2
                                   (MAP Value eL1 ++ MAP Var vL1b)))))
           (Closure (HD vL1b)
            (Lams (TL vL1b) (Tick (Apps y
                                   (EL i (MAP Value eL2 ++ MAP Var vL1b)::
                                    MAP Value eL2a ++ MAP Var vL3b ++
                                    MAP2 (λb e. if b then Force e else e) bL1
                                         (MAP2 (λb e. if b then Force e else e) bL2
                                          (MAP Value eL2 ++ MAP Var vL1b)))))))) ∧
[v_rel_Closure_combine1_Rec:]
  (∀f g v1 v2 x1 x2 vL1a vL1b vL2 vL3a vL3b bL1 bL2 bL3a bL3b i list eL1 eL1a eL2a eL2.
     MAP FST f = MAP FST g ∧
     ¬MEM v1 (MAP FST f) ∧ ¬MEM v2 (MAP FST f) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL combine_rel (MAP SND f) (MAP SND g) ∧
     combine_rel x1 x2 ∧

     LENGTH (vL1a ++ vL1b) = LENGTH bL2 ∧ LENGTH bL2 = LENGTH vL2 ∧
     LENGTH vL1a = LENGTH bL3a ∧ LENGTH vL1b = LENGTH bL3b ∧
     LENGTH eL1a = LENGTH vL3a ∧ LENGTH vL1a = LENGTH eL1 ∧
     ¬MEM v1 (vL1a ++ vL1b) ∧ ALL_DISTINCT (vL1a ++ vL1b) ∧ vL1b ≠ [] ∧
     ALL_DISTINCT (vL3a ++ vL3b ++ vL2) ∧
     (∀i. i < LENGTH vL2 ⇒ (EL i (vL1a ++ vL1b) = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) (bL3a ++ bL3b) bL2 ∧
     LIST_REL v_rel eL1 eL2 ∧
     eL1a = MAP SND (FILTER FST (ZIP (bL3a, eL1))) ∧
     eL2a = MAP SND (FILTER FST (ZIP (bL3a, eL2))) ∧
     vL3a = MAP SND (FILTER FST (ZIP (bL3a, vL1a))) ∧
     vL3b = MAP SND (FILTER FST (ZIP (bL3b, vL1b))) ∧
     list = SNOC (v1, Lams (vL3a ++ vL3b ++vL2) (Apps x2
                                                 (MAP Var vL3a ++ MAP Var vL3b ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP Var vL2))))
                 (SNOC (v2, Lams (vL1a ++ vL1b) (Tick (Apps x2
                                                   (MAP Var vL3a ++ MAP Var vL3b ++
                                                    MAP2 (λb e. if b then Force e else e) bL1
                                                         (MAP2 (λb e. if b then Force e else e)
                                                          bL2
                                                          (MAP Var (vL1a ++ vL1b))))))) g) ∧

     i < LENGTH vL2 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL2) ∧
     EVERY (λv. v ∉ freevars x1) (vL1a ++ vL1b ++ vL2 ++ vL3a ++ vL3b) ⇒
     v_rel (Closure (HD vL1b)
            (Lams (TL vL1b) (Apps (Value (Recclosure (SNOC (v1, Lams (vL3a ++ vL3b ++vL2)
                                                                     (Apps x1
                                                 (MAP Var vL3a ++ MAP Var vL3b ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP Var vL2))))
                                            (SNOC (v2, Lams (vL1a ++ vL1b) (Apps (Var v1)
                                                   (MAP Var vL3a ++ MAP Var vL3b ++
                                                    (MAP2 (λb e. if b then Force e else e) bL2
                                                     (MAP Var (vL1a ++ vL1b))))))
                                             f)) v1))
                               (MAP Value eL1a ++ MAP Var vL3b ++
                                MAP2 (λb e. if b then Force e else e) bL2
                                     (MAP Value eL1 ++ MAP Var vL1b)))))
           (Closure (HD vL1b)
            (Lams (TL vL1b) (Tick (Apps (subst (FILTER (λ(n,x). ¬MEM n (vL1a ++ vL1b))
                                                (MAP (λ(n,x). (n, Recclosure list n)) list)) x2)
                                   (MAP Value eL2a ++ MAP Var vL3b ++
                                    MAP2 (λb e. if b then Force e else e) bL1
                                         (MAP2 (λb e. if b then Force e else e) bL2
                                          (MAP Value eL2 ++ MAP Var vL1b)))))))) ∧
[v_rel_Closure_combine2_Rec:]
  (∀f g v1 v2 x1 x2 vL1a vL1b vL2 vL3a vL3b bL1 bL2 bL3a bL3b i list eL1 eL1a eL2a eL2.
     MAP FST f = MAP FST g ∧
     ¬MEM v1 (MAP FST f) ∧ ¬MEM v2 (MAP FST f) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL combine_rel (MAP SND f) (MAP SND g) ∧
     combine_rel x1 x2 ∧

     LENGTH (vL1a ++ vL1b) = LENGTH bL2 ∧ LENGTH bL2 = LENGTH vL2 ∧
     LENGTH vL1a = LENGTH bL3a ∧ LENGTH vL1b = LENGTH bL3b ∧
     LENGTH eL1a = LENGTH vL3a ∧ LENGTH vL1a = LENGTH eL1 ∧
     ¬MEM v1 (vL1a ++ vL1b) ∧ ALL_DISTINCT (vL1a ++ vL1b) ∧ vL1b ≠ [] ∧
     ALL_DISTINCT (vL3a ++ vL3b ++ vL2) ∧
     (∀i. i < LENGTH vL2 ⇒ (EL i (vL1a ++ vL1b) = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) (bL3a ++ bL3b) bL2 ∧
     LIST_REL v_rel eL1 eL2 ∧
     eL1a = MAP SND (FILTER FST (ZIP (bL3a, eL1))) ∧
     eL2a = MAP SND (FILTER FST (ZIP (bL3a, eL2))) ∧
     vL3a = MAP SND (FILTER FST (ZIP (bL3a, vL1a))) ∧
     vL3b = MAP SND (FILTER FST (ZIP (bL3b, vL1b))) ∧
     list = SNOC (v1, Lams (vL3a ++ vL3b ++vL2) (Apps x2
                                                 (EL i (MAP Var vL2)::
                                                  MAP Var vL3a ++ MAP Var vL3b ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP Var vL2))))
                 (SNOC (v2, Lams (vL1a ++ vL1b) (Tick (Apps x2
                                                   (EL i (MAP Var (vL1a ++ vL1b))::
                                                    MAP Var vL3a ++ MAP Var vL3b ++
                                                    MAP2 (λb e. if b then Force e else e) bL1
                                                         (MAP2 (λb e. if b then Force e else e)
                                                          bL2
                                                          (MAP Var (vL1a ++ vL1b))))))) g) ∧

     i < LENGTH vL2 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL2) ∧
     EVERY (λv. v ∉ freevars x1) (vL1a ++ vL1b ++ vL2 ++ vL3a ++ vL3b) ⇒
     v_rel (Closure (HD vL1b)
            (Lams (TL vL1b) (Apps (Value (Recclosure (SNOC (v1, Lams (vL3a ++ vL3b ++vL2)
                                                                     (Apps x1
                                                 (EL i (MAP Var vL2)::
                                                  MAP Var vL3a ++ MAP Var vL3b ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP Var vL2))))
                                            (SNOC (v2, Lams (vL1a ++ vL1b) (Apps (Var v1)
                                                   (MAP Var vL3a ++ MAP Var vL3b ++
                                                    (MAP2 (λb e. if b then Force e else e) bL2
                                                     (MAP Var (vL1a ++ vL1b))))))
                                             f)) v1))
                             (MAP Value eL1a ++ MAP Var vL3b ++
                              MAP2 (λb e. if b then Force e else e) bL2
                                   (MAP Value eL1 ++ MAP Var vL1b)))))
           (Closure (HD vL1b)
            (Lams (TL vL1b) (Tick (Apps (subst (FILTER (λ(n,x). ¬MEM n (vL1a ++ vL1b))
                                                (MAP (λ(n,x). (n, Recclosure list n)) list)) x2)
                                   (EL i (MAP Value eL2 ++ MAP Var vL1b)::
                                    MAP Value eL2a ++ MAP Var vL3b ++
                                    MAP2 (λb e. if b then Force e else e) bL1
                                         (MAP2 (λb e. if b then Force e else e) bL2
                                          (MAP Value eL2 ++ MAP Var vL1b)))))))) ∧
[v_rel_Recclosure:]
  (∀f g n.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL combine_rel (MAP SND f) (MAP SND g) ⇒
     v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Recclosure_combine1:]
  (∀f g n v1 v2 x1 x2 vL1 vL2 vL3 bL1 bL2 bL3 i.
     MAP FST f = MAP FST g ∧
     ¬MEM v1 (MAP FST f) ∧ ¬MEM v2 (MAP FST f) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL combine_rel (MAP SND f) (MAP SND g) ∧
     combine_rel x1 x2 ∧

     LENGTH vL1 = LENGTH bL2 ∧ LENGTH vL1 = LENGTH vL2 ∧ LENGTH vL1 = LENGTH bL3 ∧
     ¬MEM v1 vL1 ∧ ALL_DISTINCT vL1 ∧ vL1 ≠ [] ∧ ALL_DISTINCT (vL3 ++ vL2) ∧
     (∀i. i < LENGTH vL1 ⇒ (EL i vL1 = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL3 bL2 ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL3, vL1))) ∧

     i < LENGTH vL1 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL1) ∧
     EVERY (λv. v ∉ freevars x1) (vL1 ++ vL2 ++ vL3) ⇒
     v_rel (Recclosure (SNOC (v1, Lams (vL3++vL2) (Apps x1
                                                 (MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP Var vL2))))
                      (SNOC (v2, Lams vL1 (Apps (Var v1)
                                           (MAP Var vL3 ++
                                            (MAP2 (λb e. if b then Force e else e) bL2
                                             (MAP Var vL1)))))
                       f)) n)
             (Recclosure (SNOC (v1, Lams (vL3++vL2) (Apps x2
                                                 (MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP Var vL2))))
                      (SNOC (v2, Lams vL1 (Tick (Apps x2
                                                 (MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP2 (λb e. if b then Force e else e) bL2
                                                        (MAP Var vL1))))))
                       g)) n)) ∧
[v_rel_Recclosure_combine2:]
  (∀f g n v1 v2 x1 x2 vL1 vL2 vL3 bL1 bL2 bL3 i.
     MAP FST f = MAP FST g ∧
     ¬MEM v1 (MAP FST f) ∧ ¬MEM v2 (MAP FST f) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL combine_rel (MAP SND f) (MAP SND g) ∧
     combine_rel x1 x2 ∧

     LENGTH vL1 = LENGTH bL2 ∧ LENGTH vL1 = LENGTH vL2 ∧ LENGTH vL1 = LENGTH bL3 ∧
     ¬MEM v1 vL1 ∧ ALL_DISTINCT vL1 ∧ vL1 ≠ [] ∧ ALL_DISTINCT (vL3 ++ vL2) ∧
     (∀i. i < LENGTH vL1 ⇒ (EL i vL1 = EL i vL2 ⇔ ¬EL i bL2)) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL3 bL2 ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL3, vL1))) ∧

     i < LENGTH vL1 ∧ (∀j. j ≤ i ⇒ ¬EL j bL2) ∧ bL1 = GENLIST (λn. n = i) (LENGTH vL1) ∧
     EVERY (λv. v ∉ freevars x1) (vL1 ++ vL2 ++ vL3) ⇒
     v_rel (Recclosure (SNOC (v1, Lams (vL3++vL2) (Apps x1
                                                 (Var (EL i vL2)::MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP Var vL2))))
                      (SNOC (v2, Lams vL1 (Apps (Var v1)
                                           (MAP Var vL3 ++
                                            (MAP2 (λb e. if b then Force e else e) bL2
                                             (MAP Var vL1)))))
                       f)) n)
             (Recclosure (SNOC (v1, Lams (vL3++vL2) (Apps x2
                                                 (Var (EL i vL2)::MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP Var vL2))))
                      (SNOC (v2, Lams vL1 (Tick (Apps x2
                                                 (Var (EL i vL1)::MAP Var vL3 ++
                                                  MAP2 (λb e. if b then Force e else e) bL1
                                                       (MAP2 (λb e. if b then Force e else e) bL2
                                                        (MAP Var vL1))))))
                       g)) n)) ∧
[v_rel_Thunk:]
  (∀x y.
     combine_rel x y ⇒
     v_rel (Thunk x) (Thunk y)) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x)) ∧
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
     v_rel (DoTick v) (DoTick w))
End

Theorem combine_rel_def =
  [“combine_rel (Var v) x”,
   “combine_rel (Value v) x”,
   “combine_rel (Prim op xs) x”,
   “combine_rel (Monad mop xs) x”,
   “combine_rel (App f x) y”,
   “combine_rel (Lam s x) y”,
   “combine_rel (Letrec f x) y”,
   “combine_rel (Let s x y) z”,
   “combine_rel (If x y z) w”,
   “combine_rel (Delay x) y”,
   “combine_rel (MkTick x) y”,
   “combine_rel (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once combine_rel_cases])
  |> LIST_CONJ;

Theorem v_rel_def =
  [“v_rel (Constructor s vs) v”,
   “v_rel (Monadic s vs) v”,
   “v_rel (Closure s x) v”,
   “v_rel (Recclosure f n) v”,
   “v_rel (Atom x) v”,
   “v_rel (Thunk x) v”,
   “v_rel (DoTick x) v”]
  |> map (SIMP_CONV (srw_ss()) [Once combine_rel_cases])
  |> LIST_CONJ

Triviality less_1_lemma[simp]:
  n < 1 ⇔ n = 0:num
Proof
  fs []
QED

Theorem combine_rel_Lams:
  ∀l x y. combine_rel x y ⇒ combine_rel (Lams l x) (Lams l y)
Proof
  Induct >> gvs [combine_rel_def]
QED

Theorem combine_rel_freevars:
  ∀x y. combine_rel x y ⇒ freevars x = freevars y
Proof
  ‘(∀x y. combine_rel x y ⇒ freevars x = freevars y) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw [] >>
  ho_match_mp_tac combine_rel_strongind >>
  gs [combine_rel_def, PULL_EXISTS, freevars_def] >> rw []
  >- (AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      gs [LIST_REL_EL_EQN, MEM_EL, EL_MAP, PULL_EXISTS])
  >- (AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      gs [LIST_REL_EL_EQN, MEM_EL, EL_MAP, PULL_EXISTS])
  >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
      AP_TERM_TAC >> irule LIST_EQ >>
      gs [MEM_EL, PULL_EXISTS, EL_MAP, LIST_REL_EL_EQN] >>
      rw [] >>
      last_x_assum $ dxrule_then assume_tac >>
      pairarg_tac >> gs [] >> pairarg_tac >> gs [])
  >- (gs [freevars_Lams, freevars_def, freevars_Apps] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] >> gs [MAP_SNOC]
      >- (gs [freevars_Lams, freevars_Apps, freevars_def]
          >- (disj2_tac
              \\ ‘∀A B. A ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
              \\ gs [])
          >- gs [MEM_MAP, freevars_def]
          >- (gs [MEM_EL, EL_MAP, EL_MAP2]
              \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac \\ IF_CASES_TAC \\ gs [freevars_def]
              \\ strip_tac \\ gs []))
      >- (gs [freevars_Lams, freevars_Apps, freevars_def]
          >- (gs [MEM_MAP, MEM_FILTER, freevars_def]
              \\ gs [MEM_EL, EL_ZIP])
          >- (gs [MEM_EL, EL_MAP, EL_MAP2]
              \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac \\ IF_CASES_TAC \\ gs [freevars_def]
              \\ strip_tac \\ gs []))
      >- (disj2_tac
          \\ ‘∀A B. B ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
          \\ ‘∀A B. B ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
          \\ gs [MEM_EL, LIST_REL_EL_EQN, EL_MAP, PULL_EXISTS]
          \\ first_assum $ irule_at Any \\ gs [EL_MAP]
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [])
      >- (gs [freevars_Lams, freevars_Apps, freevars_def]
          >- (disj2_tac
              \\ ‘∀A B. A ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
              \\ gs [])
          >- gs [MEM_MAP, freevars_def]
          >- (gs [MEM_EL, EL_MAP, EL_MAP2]
              \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac \\ IF_CASES_TAC \\ gs [freevars_def]
              \\ strip_tac \\ gs []))
      >- (gs [freevars_Lams, freevars_Apps, freevars_def]
          >- (disj2_tac
              \\ ‘∀A B. A ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
              \\ gs [EVERY_MEM]
              \\ conj_tac \\ strip_tac
              \\ first_x_assum $ dxrule_then assume_tac \\ gs [])
          >- (gs [MEM_MAP, MEM_FILTER, freevars_def]
              \\ gs [MEM_EL, EL_ZIP])
          >- (gs [MEM_EL, EL_MAP, EL_MAP2]
              \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac \\ IF_CASES_TAC \\ gs [freevars_def]
              >- (strip_tac \\ gs [])
              \\ IF_CASES_TAC \\ gs [freevars_def]
              \\ strip_tac \\ gs []))
      >- (disj2_tac
          \\ ‘∀A B. B ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
          \\ ‘∀A B. B ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
          \\ gs [MEM_EL, LIST_REL_EL_EQN, EL_MAP, PULL_EXISTS]
          \\ first_assum $ irule_at Any \\ gs [EL_MAP]
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []))
  >- (gs [freevars_Lams, freevars_def, freevars_Apps] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] >> gs [MAP_SNOC]
      >- (gs [freevars_Lams, freevars_Apps, freevars_def]
          >- (disj2_tac
              \\ ‘∀A B. A ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
              \\ gs [])
          >- gs [EL_MEM]
          >- gs [MEM_MAP, freevars_def]
          >- (gs [MEM_EL, EL_MAP, EL_MAP2]
              \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac \\ IF_CASES_TAC \\ gs [freevars_def]
              \\ strip_tac \\ gs []))
      >- (gs [freevars_Lams, freevars_Apps, freevars_def]
          >- (gs [MEM_MAP, MEM_FILTER, freevars_def]
              \\ gs [MEM_EL, EL_ZIP])
          >- (gs [MEM_EL, EL_MAP, EL_MAP2]
              \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac \\ IF_CASES_TAC \\ gs [freevars_def]
              \\ strip_tac \\ gs []))
      >- (disj2_tac
          \\ ‘∀A B. B ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
          \\ ‘∀A B. B ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
          \\ gs [MEM_EL, LIST_REL_EL_EQN, EL_MAP, PULL_EXISTS]
          \\ first_assum $ irule_at Any \\ gs [EL_MAP]
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [])
      >- (gs [freevars_Lams, freevars_Apps, freevars_def]
          >- (disj2_tac
              \\ ‘∀A B. A ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
              \\ gs [])
          >- gs [EL_MEM]
          >- gs [MEM_MAP, freevars_def]
          >- (gs [MEM_EL, EL_MAP, EL_MAP2]
              \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac \\ IF_CASES_TAC \\ gs [freevars_def]
              \\ strip_tac \\ gs []))
      >- (gs [freevars_Lams, freevars_Apps, freevars_def]
          >- (disj2_tac
              \\ ‘∀A B. A ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
              \\ gs [EVERY_MEM]
              \\ conj_tac \\ strip_tac
              \\ first_x_assum $ dxrule_then assume_tac \\ gs [])
          >- gs [EL_MEM]
          >- (gs [MEM_MAP, MEM_FILTER, freevars_def]
              \\ gs [MEM_EL, EL_ZIP])
          >- (gs [MEM_EL, EL_MAP, EL_MAP2]
              \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac \\ IF_CASES_TAC \\ gs [freevars_def]
              >- (strip_tac \\ gs [])
              \\ IF_CASES_TAC \\ gs [freevars_def]
              \\ strip_tac \\ gs []))
      >- (disj2_tac
          \\ ‘∀A B. B ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
          \\ ‘∀A B. B ⇒ A ∨ B’ by gs [] \\ pop_assum $ irule_at Any
          \\ gs [MEM_EL, LIST_REL_EL_EQN, EL_MAP, PULL_EXISTS]
          \\ first_assum $ irule_at Any \\ gs [EL_MAP]
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []))
  >~[‘Let opt _ _’]
  >- (Cases_on ‘opt’ >> gs [freevars_def])
  >- (gs [freevars_Lams, freevars_def, freevars_Apps] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] \\ gs []
      >- (gs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gs [MEM_EL, EL_ZIP])
      >- (gs [MEM_EL, EL_MAP, EL_MAP2]
          \\ rename1 ‘n < _’ \\ Cases_on ‘EL n bL2’
          \\ gs [freevars_def])
      >- (disj1_tac \\ conj_tac \\ strip_tac
          \\ gs [EVERY_MEM, MEM_MAP, MEM_FILTER]
          \\ gs [MEM_EL, EL_ZIP])
      >- (gs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gs [MEM_EL, EL_ZIP])
      >- (gs [MEM_EL, EL_MAP, EL_MAP2, PULL_EXISTS, SF CONJ_ss, LIST_REL_EL_EQN,
               freevars_def]
          \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac
          \\ IF_CASES_TAC >- (strip_tac \\ gs [freevars_def])
          \\ IF_CASES_TAC \\ strip_tac \\ gs [freevars_def]))
  >- (gs [freevars_Lams, freevars_def, freevars_Apps] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] \\ gs []
      >- (gs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gs [MEM_EL, EL_ZIP])
      >- (gs [MEM_EL, EL_MAP, EL_MAP2]
          \\ rename1 ‘n < _’ \\ Cases_on ‘EL n bL2’
          \\ gs [freevars_def])
      >- (disj1_tac \\ conj_tac \\ strip_tac
          \\ gs [EVERY_MEM, MEM_MAP, MEM_FILTER]
          \\ gs [MEM_EL, EL_ZIP])
      >- (gs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gs [MEM_EL, EL_ZIP])
      >- (gs [MEM_MAP, MEM_FILTER, freevars_def]
          \\ gs [MEM_EL, EL_ZIP])
      >- (gs [MEM_EL, EL_MAP, EL_MAP2, PULL_EXISTS, SF CONJ_ss, LIST_REL_EL_EQN,
               freevars_def]
          \\ qpat_x_assum ‘_ ∈ freevars _’ mp_tac
          \\ IF_CASES_TAC >- (strip_tac \\ gs [freevars_def])
          \\ IF_CASES_TAC \\ strip_tac \\ gs [freevars_def]))
QED

Theorem LIST_REL_EQ_IMP_EQ:
  ∀xs ys. LIST_REL (λx y. boundvars x = boundvars y) xs ys ⇒
          MAP boundvars xs = MAP boundvars ys
Proof
  Induct >> gs [PULL_EXISTS]
QED

Theorem combine_rel_boundvars:
  ∀x y. combine_rel x y ⇒ boundvars x = boundvars y
Proof
  ‘(∀x y. combine_rel x y ⇒ boundvars x = boundvars y) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw [] >>
  ho_match_mp_tac combine_rel_strongind >>
  simp [boundvars_def] >> rw []
  >- (gs [LIST_REL_CONJ, SF ETA_ss] >>
      dxrule_then assume_tac LIST_REL_EQ_IMP_EQ >> gs [])
  >- (gs [LIST_REL_CONJ, SF ETA_ss] >>
      dxrule_then assume_tac LIST_REL_EQ_IMP_EQ >> gs [])
  >- (gs [LIST_REL_CONJ, SF ETA_ss] >>
      dxrule_then assume_tac LIST_REL_EQ_IMP_EQ >>
      gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, SF ETA_ss])
  >- (gs [LIST_REL_CONJ, SF ETA_ss] >>
      dxrule_then assume_tac LIST_REL_EQ_IMP_EQ >>
      gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, SF ETA_ss, MAP_SNOC, LIST_TO_SET_SNOC,
          boundvars_Lams, boundvars_def, boundvars_Apps] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] >> gs []
      >- (rename1 ‘MEM s (MAP boundvars (MAP2 _ bL2 (MAP Var vL1)))’ >>
          rename1 ‘x'' ∈ s’ >>
          ‘MEM x'' vL1’ suffices_by gs [] >>
          gs [MEM_EL, EL_MAP, EL_MAP2] >>
          first_assum $ irule_at Any >>
          pop_assum mp_tac >>
          IF_CASES_TAC >> gs [boundvars_def])
      >- (rename1 ‘MEM s (MAP boundvars (MAP2 _ (GENLIST _ _) (MAP2 _ bL2 (MAP Var vL1))))’ >>
          rename1 ‘x'' ∈ s’ >>
          ‘MEM x'' vL1’ suffices_by gs [] >>
          gs [MEM_EL, EL_MAP, EL_MAP2] >>
          first_assum $ irule_at Any >>
          pop_assum mp_tac >>
          IF_CASES_TAC >> gs [boundvars_def] >>
          IF_CASES_TAC >> gs [boundvars_def]))
  >- (gs [LIST_REL_CONJ, SF ETA_ss] >>
      dxrule_then assume_tac LIST_REL_EQ_IMP_EQ >>
      gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, SF ETA_ss, MAP_SNOC, LIST_TO_SET_SNOC,
          boundvars_Lams, boundvars_def, boundvars_Apps] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] >> gs []
      >- (rename1 ‘MEM s (MAP boundvars (MAP2 _ bL2 (MAP Var vL1)))’ >>
          rename1 ‘x'' ∈ s’ >>
          ‘MEM x'' vL1’ suffices_by gs [] >>
          gs [MEM_EL, EL_MAP, EL_MAP2] >>
          first_assum $ irule_at Any >>
          pop_assum mp_tac >>
          IF_CASES_TAC >> gs [boundvars_def])
      >- (rename1 ‘MEM s (MAP boundvars (MAP2 _ (GENLIST _ _) (MAP2 _ bL2 (MAP Var vL1))))’ >>
          rename1 ‘x'' ∈ s’ >>
          ‘MEM x'' vL1’ suffices_by gs [] >>
          gs [MEM_EL, EL_MAP, EL_MAP2] >>
          first_assum $ irule_at Any >>
          pop_assum mp_tac >>
          IF_CASES_TAC >> gs [boundvars_def] >>
          IF_CASES_TAC >> gs [boundvars_def]))
  >- (rename1 ‘Let opt _ _’ >>
      Cases_on ‘opt’ >> gs [boundvars_def])
  >- (rw [boundvars_Apps, boundvars_Lams, boundvars_def, SET_EQ_SUBSET, SUBSET_DEF] >>
      gs []
      >- (disj1_tac >> disj1_tac >>
          disj1_tac >> disj2_tac >> disj1_tac >>
          first_x_assum $ irule_at Any >> simp [])
      >- (disj1_tac >> disj2_tac >>
          disj1_tac >> disj1_tac >> disj2_tac >>
          gs [MEM_EL, LIST_REL_EL_EQN] >>
          first_assum $ irule_at Any >> gs[EL_MAP, EL_MAP2] >>
          pop_assum mp_tac >>
          IF_CASES_TAC >> gs [boundvars_def])
      >- (disj1_tac >> disj2_tac >>
          disj1_tac >> disj1_tac >> disj2_tac >>
          gs [MEM_MAP, MEM_FILTER, MEM_EL] >>
          first_assum $ irule_at Any >> gs[EL_ZIP, boundvars_def])
      >- (disj1_tac >> disj2_tac >>
          disj1_tac >> disj1_tac >> disj2_tac >>
          gs [MEM_EL, LIST_REL_EL_EQN] >>
          first_assum $ irule_at Any >> gs[EL_MAP, EL_MAP2] >>
          pop_assum mp_tac >>
          IF_CASES_TAC >> gs [boundvars_def] >>
          IF_CASES_TAC >> gs [boundvars_def]))
  >- (rw [boundvars_Apps, boundvars_Lams, boundvars_def, SET_EQ_SUBSET, SUBSET_DEF] >>
      gs []
      >- (disj1_tac >> disj1_tac >>
          disj1_tac >> disj2_tac >> disj1_tac >>
          first_x_assum $ irule_at Any >> simp [])
      >- (disj1_tac >> disj2_tac >>
          disj1_tac >> disj1_tac >> disj2_tac >>
          gs [MEM_EL, LIST_REL_EL_EQN] >>
          first_assum $ irule_at Any >> gs[EL_MAP, EL_MAP2] >>
          pop_assum mp_tac >>
          IF_CASES_TAC >> gs [boundvars_def])
      >- (disj1_tac >> disj2_tac >>
          disj1_tac >> disj1_tac >> disj2_tac >>
          gs [MEM_MAP, MEM_FILTER, MEM_EL] >>
          first_assum $ irule_at Any >> gs[EL_ZIP, boundvars_def])
      >- (disj1_tac >> disj2_tac >>
          disj1_tac >> disj1_tac >> disj2_tac >>
          gs [MEM_EL, LIST_REL_EL_EQN] >>
          first_assum $ irule_at Any >> gs[EL_MAP, EL_MAP2] >>
          pop_assum mp_tac >>
          IF_CASES_TAC >> gs [boundvars_def] >>
          IF_CASES_TAC >> gs [boundvars_def]))
QED

Theorem LIST_FILTERED:
  ∀l1 l2 R f. MAP FST l1 = MAP FST l2 ∧ LIST_REL R (MAP SND l1) (MAP SND l2)
              ⇒ MAP FST (FILTER (λ(n, v). f n) l1) = MAP FST (FILTER (λ(n,v). f n) l2)
                ∧ LIST_REL R (MAP SND (FILTER (λ(n, v). f n) l1)) (MAP SND (FILTER (λ(n,v). f n) l2))
Proof
  Induct >> gs [] >>
  PairCases >> Cases >> gs [] >>
  rename1 ‘FST pair’ >> PairCases_on ‘pair’ >> rw [] >>
  last_x_assum $ dxrule_then $ dxrule_then assume_tac >>
  gs []
QED

Theorem ok_bind_subst[simp]:
  ∀x. ok_bind x ⇒ ok_bind (subst ws x)
Proof
  Cases \\ rw [ok_bind_def] \\ gs [subst_def, ok_bind_def]
QED

Theorem combine_rel_subst:
  ∀vs x ws y.
    MAP FST vs = MAP FST ws ∧
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    combine_rel x y ⇒
      combine_rel (subst vs x) (subst ws y)
Proof
  ‘(∀x y.
     combine_rel x y ⇒
     ∀vs ws.
       MAP FST vs = MAP FST ws ∧
       LIST_REL v_rel (MAP SND vs) (MAP SND ws) ⇒
         combine_rel (subst vs x) (subst ws y)) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw []
  \\ ho_match_mp_tac combine_rel_strongind \\ rw []
  >~ [‘Var v’] >- (
    rw [subst_def]
    \\ rename1 ‘LIST_REL v_rel (MAP SND vs) (MAP SND ws)’
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_OPTREL
          \\ gs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
    \\ gs [OPTREL_def, combine_rel_Var, combine_rel_Value])
  >~ [‘Value v’] >- (
    rw [subst_def]
    \\ gs [combine_rel_Value])
  >~ [‘Prim op xs’] >- (
    rw [subst_def]
    \\ irule combine_rel_Prim
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [‘Monad op xs’] >- (
    rw [subst_def]
    \\ irule combine_rel_Monad
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [‘App f x’] >- (
    rw [subst_def]
    \\ gs [combine_rel_App])
  >~ [‘Lam s x’] >- (
    rw [subst_def]
    \\ irule combine_rel_Lam
    \\ first_x_assum irule
    \\ gs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER
    \\ gs [LIST_REL_EL_EQN])
  >~ [‘SNOC _ (SNOC _ _)’] >- (
    rw [subst_def, MAP_SNOC, subst_Lams, subst_Apps, GSYM LAMBDA_PROD, FILTER_T]
    \\ gs [combine_rel_def] \\ disj2_tac \\ disj1_tac
    \\ rpt (‘∀e1 e2 l1 l2. e1 = e2 ∧ l1 = l2 ⇒ Lams l1 e1 = Lams l2 e2’ by gs []
            \\ pop_assum $ irule_at Any)
    \\ gs []
    \\ rpt (‘∀e1 e2 l1 l2. e1 = e2 ∧ l1 = l2 ⇒ Apps e1 l1 = Apps e2 l2’ by gs []
            \\ pop_assum $ irule_at Any)
    \\ gs []
    \\ gs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
    \\ qpat_x_assum ‘LIST_REL (λb3 b2. b3 ⇒ b2) _ _’ $ irule_at Any
    \\ qpat_assum ‘ALL_DISTINCT (_ ++ _)’ $ irule_at Any \\ gs []
    \\ qpat_assum ‘_ < LENGTH _’ $ irule_at Any \\ gs [EVERY_MEM, freevars_subst]
    \\ rw [] \\ gs []
    >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gs []
        \\ pop_assum irule
        \\ conj_tac \\ irule LIST_EQ
        \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
        \\ drule_then assume_tac EL_MEM \\ gs [MEM_FILTER] \\ gs [MEM_EL, EL_ZIP])
    >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gs []
        \\ pop_assum irule
        \\ conj_tac \\ irule LIST_EQ
        \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
        \\ gs [MEM_MAP] \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
        \\ gs [EL_MEM])
    >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gs []
        \\ pop_assum irule
        \\ conj_tac \\ irule LIST_EQ
        \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
        \\ gs [MEM_MAP] \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
        \\ gs [EL_MEM])
    >- (rename1 ‘subst _ y2 = _’ \\ rename1 ‘combine_rel x2 y2’
        \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
        \\ qspecl_then [‘FILTER (λ(n,v). n ≠ v1 ∧ n ≠ v2 ∧ ¬MEM n (MAP FST g)) ws’, ‘y2’]
                       assume_tac subst_remove
        \\ first_assum $ qspec_then ‘set vL1’ assume_tac
        \\ first_x_assum $ qspec_then ‘set (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∪ set vL2’
                         assume_tac
        \\ gs [DISJOINT_ALT])
    >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gs []
        \\ pop_assum irule
        \\ conj_tac \\ irule LIST_EQ
        \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
        \\ drule_then assume_tac EL_MEM \\ gs [MEM_FILTER] \\ gs [MEM_EL, EL_ZIP])
    >- gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    >- gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    >- gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    >- (gs [MEM_MAP, PULL_EXISTS]
        \\ last_x_assum $ dxrule_then assume_tac
        \\ pairarg_tac \\ gs [ok_bind_subst])
    >- (gs [MEM_MAP, PULL_EXISTS]
        \\ last_x_assum $ dxrule_then assume_tac
        \\ pairarg_tac \\ gs [ok_bind_subst])
    >- (‘LENGTH f = LENGTH g’ by gs [LIST_REL_EL_EQN]
        \\ rw [LIST_REL_EL_EQN, EL_MAP]
        \\ gs [Once LIST_REL_EL_EQN, EL_MAP]
        \\ last_x_assum $ drule_then assume_tac
        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
        \\ first_x_assum irule
        \\ gs [MAP_FST_FILTER, EVERY2_MAP]
        \\ qabbrev_tac ‘P = λn. n ≠ v1 ∧ n ≠ v2 ∧ ¬MEM n (MAP FST g)’ \\ gs []
        \\ irule LIST_REL_FILTER \\ gs []
        \\ irule LIST_REL_mono
        \\ first_x_assum $ irule_at Any \\ gs [])
    >- (first_x_assum irule
        \\ gs [MAP_FST_FILTER, EVERY2_MAP]
        \\ qabbrev_tac ‘P = λn. n ≠ v1 ∧ n ≠ v2 ∧ ¬MEM n (MAP FST g)’ \\ gs []
        \\ irule LIST_REL_FILTER \\ gs []
        \\ irule LIST_REL_mono
        \\ first_x_assum $ irule_at Any \\ gs [])
    >- (first_x_assum irule
        \\ gs [MAP_FST_FILTER, EVERY2_MAP, FILTER_FILTER, LAMBDA_PROD, GSYM CONJ_ASSOC]
        \\ qabbrev_tac ‘P = λn. ¬MEM n (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∧ ¬ MEM n vL2 ∧
                                n ≠ v1 ∧ n ≠ v2 ∧ ¬MEM n (MAP FST g)’ \\ gs []
        \\ irule LIST_REL_FILTER \\ gs []
        \\ irule LIST_REL_mono
        \\ first_x_assum $ irule_at Any \\ gs []))
  >~ [‘SNOC _ (SNOC _ _)’] >- (
    rw [subst_def, MAP_SNOC, subst_Lams, subst_Apps, GSYM LAMBDA_PROD, FILTER_T]
    \\ gs [combine_rel_def] \\ disj2_tac \\ disj2_tac
    \\ rpt (‘∀e1 e2 l1 l2. e1 = e2 ∧ l1 = l2 ⇒ Lams l1 e1 = Lams l2 e2’ by gs []
            \\ pop_assum $ irule_at Any)
    \\ gs []
    \\ rpt (‘∀e1 e2 l1 l2. e1 = e2 ∧ l1 = l2 ⇒ Apps e1 l1 = Apps e2 l2’ by gs []
            \\ pop_assum $ irule_at Any)
    \\ gs []
    \\ gs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
    \\ qpat_x_assum ‘LIST_REL (λb3 b2. b3 ⇒ b2) _ _’ $ irule_at Any
    \\ qpat_assum ‘ALL_DISTINCT (_ ++ _)’ $ irule_at Any \\ gs []
    \\ qpat_assum ‘_ < LENGTH _’ $ irule_at Any \\ gs [EVERY_MEM, freevars_subst]
    \\ rw [] \\ gs [EL_MEM]
    >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gs []
        \\ pop_assum irule
        \\ conj_tac \\ irule LIST_EQ
        \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
        \\ drule_then assume_tac EL_MEM \\ gs [MEM_FILTER] \\ gs [MEM_EL, EL_ZIP])
    >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gs []
        \\ pop_assum irule
        \\ conj_tac \\ irule LIST_EQ
        \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
        \\ gs [MEM_MAP] \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
        \\ gs [EL_MEM])
    >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gs []
        \\ pop_assum irule
        \\ conj_tac \\ irule LIST_EQ
        \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
        \\ gs [MEM_MAP] \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
        \\ gs [EL_MEM])
    >- (rename1 ‘subst _ y2 = _’ \\ rename1 ‘combine_rel x2 y2’
        \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
        \\ qspecl_then [‘FILTER (λ(n,v). n ≠ v1 ∧ n ≠ v2 ∧ ¬MEM n (MAP FST g)) ws’, ‘y2’]
                       assume_tac subst_remove
        \\ first_assum $ qspec_then ‘set vL1’ assume_tac
        \\ first_x_assum $ qspec_then ‘set (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∪ set vL2’
                         assume_tac
        \\ gs [DISJOINT_ALT])
    >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gs []
        \\ pop_assum irule
        \\ conj_tac \\ irule LIST_EQ
        \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
        \\ drule_then assume_tac EL_MEM \\ gs [MEM_FILTER] \\ gs [MEM_EL, EL_ZIP])
    >- gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    >- gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    >- gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    >- (gs [MEM_MAP, PULL_EXISTS]
        \\ last_x_assum $ dxrule_then assume_tac
        \\ pairarg_tac \\ gs [ok_bind_subst])
    >- (gs [MEM_MAP, PULL_EXISTS]
        \\ last_x_assum $ dxrule_then assume_tac
        \\ pairarg_tac \\ gs [ok_bind_subst])
    >- (‘LENGTH f = LENGTH g’ by gs [LIST_REL_EL_EQN]
        \\ rw [LIST_REL_EL_EQN, EL_MAP]
        \\ gs [Once LIST_REL_EL_EQN, EL_MAP]
        \\ last_x_assum $ drule_then assume_tac
        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
        \\ first_x_assum irule
        \\ gs [MAP_FST_FILTER, EVERY2_MAP]
        \\ qabbrev_tac ‘P = λn. n ≠ v1 ∧ n ≠ v2 ∧ ¬MEM n (MAP FST g)’ \\ gs []
        \\ irule LIST_REL_FILTER \\ gs []
        \\ irule LIST_REL_mono
        \\ first_x_assum $ irule_at Any \\ gs [])
    >- (first_x_assum irule
        \\ gs [MAP_FST_FILTER, EVERY2_MAP]
        \\ qabbrev_tac ‘P = λn. n ≠ v1 ∧ n ≠ v2 ∧ ¬MEM n (MAP FST g)’ \\ gs []
        \\ irule LIST_REL_FILTER \\ gs []
        \\ irule LIST_REL_mono
        \\ first_x_assum $ irule_at Any \\ gs [])
    >- (first_x_assum irule
        \\ gs [MAP_FST_FILTER, EVERY2_MAP, FILTER_FILTER, LAMBDA_PROD, GSYM CONJ_ASSOC]
        \\ qabbrev_tac ‘P = λn. ¬MEM n (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∧ ¬ MEM n vL2 ∧
                                n ≠ v1 ∧ n ≠ v2 ∧ ¬MEM n (MAP FST g)’ \\ gs []
        \\ irule LIST_REL_FILTER \\ gs []
        \\ irule LIST_REL_mono
        \\ first_x_assum $ irule_at Any \\ gs []))
  >~ [‘Letrec f x’] >- (
    rw [subst_def]
    \\ irule combine_rel_Letrec
    \\ gs [EVERY_MAP, EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
            GSYM FST_THM]
    \\ first_x_assum (irule_at Any)
    \\ gs [MAP_FST_FILTER]
    \\ rename1 ‘MAP FST f = MAP FST g’
    \\ qabbrev_tac ‘P = λn. ¬MEM n (MAP FST g)’ \\ gs []
    \\ irule_at Any LIST_REL_FILTER
    \\ ‘∀x f. ok_bind x ⇒ ok_bind (subst f x)’
      by (Cases \\ gs [ok_bind_def, subst_def])
    \\ gs [EVERY_EL, ELIM_UNCURRY]
    \\ irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule LIST_REL_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ first_assum irule
    \\ gs [MAP_FST_FILTER, LAMBDA_PROD]
    \\ irule LIST_REL_FILTER
    \\ gs [LIST_REL_EL_EQN])
  >~[‘Apps (App _ _) _’]
  >- (gs [subst_def, subst_Lams, subst_Apps, GSYM LAMBDA_PROD, FILTER_T,
           GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
      \\ gs [combine_rel_def] \\ disj2_tac \\ disj2_tac
      \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gs []
      \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gs []
      \\ irule_at (Pos $ el 2) EQ_REFL
      \\ rpt (‘∀l1 l2 e1 (e2 : exp list). l1 = l2 ∧ e1 = e2 ⇒ e1 ++ l1 = e2 ++ l2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gs [SF CONJ_ss]
      \\ qexists_tac ‘bL3’ \\ qexists_tac ‘bL2’ \\ rw []
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ dxrule_then assume_tac EL_MEM
          \\ gs [MEM_FILTER] \\ gs [MEM_EL, EL_ZIP])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ gs [MEM_MAP]
          \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ gs [EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ dxrule_then assume_tac EL_MEM
          \\ gs [MEM_FILTER] \\ gs [MEM_EL, EL_ZIP])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ gs [MEM_MAP]
          \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ gs [EL_MEM])
      >- (gs [FILTER_FILTER, LAMBDA_PROD]
          \\ rename1 ‘subst (FILTER (λ(p1, p2). ¬MEM p1 vL1 ∧ p1 ≠ v1) ws) y = subst (FILTER _ ws) _’
          \\ qspecl_then [‘ws’, ‘y’, ‘set vL1 ∪ {v1}’] mp_tac subst_remove \\ impl_tac \\ gs []
          >- (qspecl_then [‘x’, ‘y’] assume_tac combine_rel_freevars
              \\ gs [DISJOINT_ALT, EVERY_MEM])
          \\ disch_then kall_tac
          \\ qspecl_then [‘ws’, ‘y’, ‘set (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∪ set vL2’] mp_tac
                         $ GSYM subst_remove
          \\ impl_tac \\ gs []
          \\ qspecl_then [‘x’, ‘y’] assume_tac combine_rel_freevars
          \\ gs [DISJOINT_ALT, EVERY_MEM])
      >- gs [freevars_subst]
      >- gs [EVERY_MEM, freevars_subst]
      >- gs [EVERY_MEM, freevars_subst]
      >- gs [EVERY_MEM, freevars_subst]
      >- (first_x_assum irule \\ gs [MAP_FST_FILTER, EVERY2_MAP]
          \\ qabbrev_tac ‘P = λv. ¬MEM v (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∧ ¬MEM v vL2’ \\ gs []
          \\ irule LIST_REL_FILTER \\ gs []
          \\ irule LIST_REL_mono
          \\ first_x_assum $ irule_at $ Pos last
          \\ gs [])
      >- (first_x_assum irule \\ gs [MAP_FST_FILTER, EVERY2_MAP, FILTER_FILTER, LAMBDA_PROD]
          \\ qabbrev_tac ‘P = λv. v ≠ v2 ∧ v ≠ v1’ \\ gs []
          \\ irule LIST_REL_FILTER \\ gs []
          \\ irule LIST_REL_mono
          \\ first_x_assum $ irule_at $ Pos last
          \\ gs []))
  >~[‘Let _ _ (Let _ _ _)’]
  >- (gs [subst_def, subst_Lams, subst_Apps, GSYM LAMBDA_PROD, FILTER_T,
           GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
      \\ gs [combine_rel_def] \\ disj2_tac \\ disj1_tac
      \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gs []
      \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ gs []
      \\ qpat_assum ‘_ < LENGTH _’ $ irule_at Any
      \\ qpat_assum ‘LIST_REL (λb3 b2. b3 ⇒ b2) _ _’ $ irule_at Any
      \\ gs [EVERY_MEM, freevars_subst]
      \\ rpt (‘∀l1 l2 e1 (e2 : exp list). l1 = l2 ∧ e1 = e2 ⇒ e1 ++ l1 = e2 ++ l2’ by gs []
              \\ pop_assum $ irule_at Any)
      \\ rw []
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ dxrule_then assume_tac EL_MEM
          \\ gs [MEM_FILTER] \\ gs [MEM_EL, EL_ZIP])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ gs [MEM_MAP]
          \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ gs [EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ dxrule_then assume_tac EL_MEM
          \\ gs [MEM_FILTER] \\ gs [MEM_EL, EL_ZIP])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
      >- (irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
          \\ gs [MEM_MAP]
          \\ first_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
          \\ gs [EL_MEM])
      >- (gs [FILTER_FILTER, LAMBDA_PROD]
          \\ rename1 ‘subst (FILTER (λ(p1, p2). ¬MEM p1 vL1 ∧ p1 ≠ v1) ws) y = subst (FILTER _ ws) _’
          \\ qspecl_then [‘ws’, ‘y’, ‘set vL1 ∪ {v1}’] mp_tac subst_remove \\ impl_tac \\ gs []
          >- (qspecl_then [‘x’, ‘y’] assume_tac combine_rel_freevars
              \\ gs [DISJOINT_ALT, EVERY_MEM])
          \\ disch_then kall_tac
          \\ qspecl_then [‘ws’, ‘y’, ‘set (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∪ set vL2’] mp_tac
                         $ GSYM subst_remove
          \\ impl_tac \\ gs []
          \\ qspecl_then [‘x’, ‘y’] assume_tac combine_rel_freevars
          \\ gs [DISJOINT_ALT, EVERY_MEM])
      >- (first_x_assum irule \\ gs [MAP_FST_FILTER, EVERY2_MAP]
          \\ qabbrev_tac ‘P = λv. ¬MEM v (MAP SND (FILTER FST (ZIP (bL3, vL1)))) ∧ ¬MEM v vL2’ \\ gs []
          \\ irule LIST_REL_FILTER \\ gs []
          \\ irule LIST_REL_mono
          \\ first_x_assum $ irule_at $ Pos last
          \\ gs [])
      >- (first_x_assum irule \\ gs [MAP_FST_FILTER, EVERY2_MAP, FILTER_FILTER, LAMBDA_PROD]
          \\ qabbrev_tac ‘P = λv. v ≠ v2 ∧ v ≠ v1’ \\ gs []
          \\ irule LIST_REL_FILTER \\ gs []
          \\ irule LIST_REL_mono
          \\ first_x_assum $ irule_at $ Pos last
          \\ gs [FORALL_PROD]))
  >~ [‘Let s x y’] >- (
    Cases_on ‘s’ \\ rw [subst_def]
    \\ irule combine_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ gs [MAP_FST_FILTER]
    \\ rename1 ‘_ ≠ s’
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ gs [EVERY2_MAP]
    \\ irule LIST_REL_FILTER
    \\ gs [LIST_REL_EL_EQN])
  >~ [‘If x y z’] >- (
    rw [subst_def]
    \\ gs [combine_rel_If])
  >~ [‘Delay x’] >- (
    rw [subst_def]
    \\ gs [combine_rel_Delay])
  >~ [‘Force x’] >- (
    rw [subst_def]
    \\ gs [combine_rel_Force])
  >~[‘MkTick x’] >- (
    rw [subst_def]
    \\ gs [combine_rel_MkTick])
QED

Theorem eval_to_Apps_Lams_not_0:
  ∀vL eL e k. vL ≠ [] ∧ LENGTH vL = LENGTH eL ∧ k ≠ 0 ⇒
              eval_to k (Apps (Value (Closure (HD vL) (Lams (TL vL) e)))
                                       (MAP Value eL))
              = eval_to (k - 1) (subst (ZIP (vL, eL)) e)
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  qspecl_then [‘eL’] assume_tac SNOC_CASES >> gs [ADD1] >>
  rename1 ‘SNOC v vL’ >> Cases_on ‘vL’ >> gs []
  >- gs [eval_to_def, dest_anyClosure_def] >>
  gvs [FOLDR_SNOC, FOLDL_APPEND, eval_to_def] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  first_x_assum $ qspecl_then [‘eL’, ‘Lam v e’, ‘k’] assume_tac >>
  gvs [subst_def, eval_to_def, dest_anyClosure_def] >>
  AP_TERM_TAC >>
  irule EQ_TRANS >> irule_at Any subst_commutes >>
  conj_tac >- rw [MAP_FST_FILTER, MAP_ZIP, MEM_FILTER] >>
  qspecl_then [‘ZIP (h::vL, eL)’, ‘subst1 v x' e’, ‘{v}’] mp_tac subst_remove >> impl_tac
  >- gs [freevars_subst] >>
  rw [GSYM subst_APPEND] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  first_x_assum kall_tac >> first_x_assum kall_tac >>
  once_rewrite_tac [CONS_APPEND] >>
  once_rewrite_tac [APPEND_SNOC] >>
  once_rewrite_tac [SNOC_APPEND] >>
  qspecl_then [‘[h]++vL’, ‘eL’, ‘[v]’, ‘[x']’] assume_tac ZIP_APPEND >>
  gs [ZIP]
QED

Theorem eval_to_Apps_not_Val_Lams_not_0:
  ∀vL eL e k. vL ≠ [] ∧ LENGTH vL = LENGTH eL ∧ k ≠ 0 ⇒
              eval_to k (Apps (Lams vL e)
                         (MAP Value eL))
              = eval_to (k - 1) (subst (ZIP (vL, eL)) e)
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  qspecl_then [‘eL’] assume_tac SNOC_CASES >> gs [ADD1] >>
  rename1 ‘SNOC v vL’ >> Cases_on ‘vL’ >> gs []
  >- gs [eval_to_def, dest_anyClosure_def] >>
  gvs [FOLDR_SNOC, FOLDL_APPEND, eval_to_def] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  gs [subst_def, eval_to_def, dest_anyClosure_def] >>
  AP_TERM_TAC >>
  irule EQ_TRANS >> irule_at (Pos hd) subst_commutes >>
  gs [MEM_FILTER, MAP_FST_FILTER] >>
  qspecl_then [‘ZIP (h::vL, eL)’, ‘subst1 v x' e’, ‘{v}’] assume_tac subst_remove >>
  gs [freevars_subst] >>
  gs [GSYM subst_APPEND] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  Cases_on ‘eL’ >> gs [SNOC_APPEND, GSYM ZIP_APPEND]
QED

Theorem eval_to_Apps_Recclosure_Lams_not_0:
  ∀eL k list v s e.  ALOOKUP (REVERSE list) v = SOME (Lam s e) ∧ eL ≠ [] ⇒
                   eval_to k (Apps (Value (Recclosure list v)) eL)
                   = eval_to k (Apps (Tick (subst_funs list (Lam s e))) eL)
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  last_x_assum $ drule_then $ qspec_then ‘k’ assume_tac >>
  Cases_on ‘eL = []’ >> gs [FOLDL_SNOC, eval_to_def] >>
  rename1 ‘eval_to k x’ >>
  Cases_on ‘eval_to k x’ >>
  gs [subst_funs_def, subst_empty, subst_def, eval_to_def, dest_anyClosure_def] >>
  IF_CASES_TAC >> gs [] >>
  AP_TERM_TAC >> irule EQ_TRANS >> irule_at (Pos last) subst_commutes >>
  gs [MAP_FST_FILTER, MEM_FILTER, subst_APPEND] >>
  irule EQ_TRANS >> irule_at (Pos hd) $ GSYM subst_remove >>
  Q.REFINE_EXISTS_TAC ‘{_}’ >> gs [] >> irule_at Any EQ_REFL >>
  gvs [freevars_subst]
QED

Theorem eval_to_Apps_Lams_0:
  ∀vL eL e. vL ≠ [] ∧ LENGTH vL = LENGTH eL ⇒
              eval_to 0 (Apps (Value (Closure (HD vL) (Lams (TL vL) e)))
                                       (MAP Value eL))
              = INL Diverge
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  rename1 ‘SUC (LENGTH vL) = LENGTH eL’ >>
  qspecl_then [‘eL’] assume_tac SNOC_CASES >> gs [ADD1] >>
  rename1 ‘SNOC v vL’ >> Cases_on ‘vL’ >> gs []
  >- (gs [eval_to_def, dest_anyClosure_def]) >>
  gs [FOLDR_SNOC, FOLDL_APPEND, eval_to_def]
QED

Theorem eval_to_Apps_Rec_0:
  ∀eL f n s e. eL ≠ [] ∧ ALOOKUP (REVERSE f) n = SOME (Lam s e) ⇒
              eval_to 0 (Apps (Value (Recclosure f n))
                                       (MAP Value eL))
              = INL Diverge
Proof
  Induct using SNOC_INDUCT >> rw [] >>
  gs [MAP_SNOC, FOLDL_SNOC] >>
  Cases_on ‘eL = []’ >> gs [eval_to_def, dest_anyClosure_def]
QED

Theorem dest_anyClosure_INL:
  ∀v e. dest_anyClosure v = INL e ⇒ e = Type_error
Proof
  Cases \\ gs [dest_anyClosure_def]
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
QED

Theorem combine_rel_Apps:
  ∀eL1 eL2 x y. LIST_REL combine_rel eL1 eL2 ∧ combine_rel x y ⇒ combine_rel (Apps x eL1) (Apps y eL2)
Proof
  Induct \\ gs [combine_rel_def]
  \\ gen_tac \\ Cases \\ gs []
  \\ rw [] \\ last_x_assum irule
  \\ gs [combine_rel_def]
QED

Theorem LESS_EQ_CASES:
  ∀(l: num) i. i ≤ l ⇒ i < l ∨ i = l
Proof
  Induct \\ gs []
QED

Theorem eval_to_Apps_arg_Div:
  ∀eL i k e. eval_to k (Apps e eL) ≠ INL Type_error ∧ i < LENGTH eL ∧ eval_to k (EL i eL) = INL Diverge
             ⇒ eval_to k (Apps e eL) = INL Diverge
Proof
  Induct using SNOC_INDUCT \\ gs []
  \\ rw [] \\ gs [GSYM LESS_EQ_IFF_LESS_SUC, FOLDL_SNOC]
  \\ rename1 ‘SNOC x eL’
  \\ dxrule_then assume_tac LESS_EQ_CASES \\ gs [EL_SNOC, EL_LENGTH_SNOC, eval_to_def]
  \\ Cases_on ‘eval_to k x’ \\ gs []
  >~[‘INL err’] >- (Cases_on ‘err’ \\ gs [])
  \\ Cases_on ‘eval_to k (Apps e eL) = INL Type_error’ \\ gs []
  \\ last_x_assum $ dxrule_then $ drule_then $ drule_then assume_tac
  \\ gs []
QED

Theorem eval_to_Apps_arg_Div_combine_rel:
  ∀eL eL2 i k e e2.
    eval_to k (Apps e eL) ≠ INL Type_error ∧ i < LENGTH eL ∧ eval_to k (EL i eL) = INL Diverge ∧
    LENGTH eL = LENGTH eL2 ∧
    (∀j. i ≤ j ∧ j < LENGTH eL ∧ eval_to k (EL j eL) ≠ INL Type_error ⇒
         ∃j2. ($= +++ v_rel) (eval_to k (EL j eL)) (eval_to (k + j2) (EL j eL2)))
    ⇒ eval_to k (Apps e2 eL2) = INL Diverge
Proof
  Induct using SNOC_INDUCT \\ gs []
  \\ rw [] \\ gs [GSYM LESS_EQ_IFF_LESS_SUC, FOLDL_SNOC]
  \\ rename1 ‘SNOC x eL’
  \\ qspec_then ‘eL2’ assume_tac SNOC_CASES \\ gvs [FOLDL_APPEND]
  \\ rename1 ‘eL2 ++ [x2]’ \\ gs [SNOC_APPEND]
  \\ dxrule_then assume_tac LESS_EQ_CASES \\ gs [EL_SNOC, EL_LENGTH_SNOC, eval_to_def, EL_APPEND_EQN]
  \\ Cases_on ‘eval_to k x2 = INL Diverge’ \\ gs []
  \\ dxrule_then assume_tac eval_to_mono \\ gs [GSYM ADD1]
  >- (‘∃j. ($= +++ v_rel) (eval_to k x) (eval_to (k + j) x2)’
        by (last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
            \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gs [])
      \\ Cases_on ‘eval_to k x’
      >~[‘eval_to k x = INL err’]
      >- (Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to k x2’ \\ gs [])
      \\ Cases_on ‘eval_to k x2’ \\ gs []
      \\ Cases_on ‘eval_to k (Apps e eL) = INL Type_error’ \\ gs [PULL_EXISTS]
      \\ last_x_assum $ drule_then $ drule_then $ drule_then $ qspecl_then [‘eL2’, ‘e2’] mp_tac
      \\ impl_tac \\ gs []
      \\ rw []
      \\ last_x_assum $ drule_then assume_tac \\ gs []
      \\ first_x_assum $ irule_at Any)
  \\ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac \\ gs []
  \\ Cases_on ‘eval_to k x2’ \\ gs []
QED

Theorem eval_to_Apps_arg_Div_combine_rel2:
  ∀eL eL2 i k e2.
    i < LENGTH eL ∧ eval_to k (EL i eL) = INL Diverge ∧
    LENGTH eL = LENGTH eL2 ∧
    (∀j. j < LENGTH eL ⇒ eval_to k (EL j eL) ≠ INL Type_error) ∧
    (∀j. i ≤ j ∧ j < LENGTH eL ∧ eval_to k (EL j eL) ≠ INL Type_error ⇒
         ∃j2. ($= +++ v_rel) (eval_to k (EL j eL)) (eval_to (k + j2) (EL j eL2)))
    ⇒ eval_to k (Apps e2 eL2) = INL Diverge
Proof
  Induct using SNOC_INDUCT \\ gs []
  \\ rw [] \\ gs [GSYM LESS_EQ_IFF_LESS_SUC, FOLDL_SNOC]
  \\ rename1 ‘SNOC x eL’
  \\ qspec_then ‘eL2’ assume_tac SNOC_CASES \\ gvs [FOLDL_APPEND]
  \\ rename1 ‘eL2 ++ [x2]’ \\ gs [SNOC_APPEND]
  \\ dxrule_then assume_tac LESS_EQ_CASES \\ gs [EL_SNOC, EL_LENGTH_SNOC, eval_to_def, EL_APPEND_EQN]
  \\ Cases_on ‘eval_to k x2 = INL Diverge’ \\ gs []
  \\ dxrule_then assume_tac eval_to_mono \\ gs [GSYM ADD1]
  >- (‘∃j. ($= +++ v_rel) (eval_to k x) (eval_to (k + j) x2)’
        by (rpt $ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
            \\ gs [] \\ first_x_assum $ irule_at Any)
      \\ Cases_on ‘eval_to k x’
      >~[‘eval_to k x = INL err’]
      >- (last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
          \\ Cases_on ‘err’ \\ gs []
          \\ Cases_on ‘eval_to k x2’ \\ gs [])
      \\ Cases_on ‘eval_to k x2’ \\ gs []
      \\ last_x_assum $ drule_then $ drule_then $ qspecl_then [‘eL2’, ‘e2’] mp_tac
      \\ impl_tac \\ gs []
      \\ rw []
      >- (rename1 ‘j < _’ \\ last_x_assum $ qspec_then ‘j’ assume_tac \\ gs [])
      \\ last_x_assum $ drule_then assume_tac \\ gs []
      \\ first_x_assum $ irule_at Any)
  \\ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
  \\ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac \\ gs []
  \\ Cases_on ‘eval_to k x2’ \\ gs []
QED

Theorem eval_to_Apps_no_INL:
  ∀eL e k. eval_to k (Apps e eL) ≠ INL Type_error ∧ (∀i. i < LENGTH eL ⇒ eval_to k (EL i eL) ≠ INL Diverge)
           ⇒ ∃vL. LIST_REL (λe v. eval_to k e = INR v) eL vL ∧
                  eval_to k (Apps e eL) = eval_to k (Apps e (MAP Value vL))
Proof
  Induct using SNOC_INDUCT \\ gs [] \\ rw []
  \\ Q.REFINE_EXISTS_TAC ‘SNOC lst vL’ \\ gs [FOLDL_SNOC, eval_to_def]
  \\ rename1 ‘SNOC x eL’
  \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gs []
  \\ ‘eval_to k x ≠ INL Diverge’ by (first_x_assum $ qspec_then ‘LENGTH eL’ assume_tac \\ gs [EL_LENGTH_SNOC])
  \\ Cases_on ‘eval_to k x’ \\ gs []
  >~[‘value ≠ Type_error’] >- (Cases_on ‘value’ \\ gs [])
  \\ Cases_on ‘eval_to k (Apps e eL) = INL Type_error’ \\ gs []
  \\ last_x_assum $ dxrule_then mp_tac \\ impl_tac
  >- (rw [] \\ rename1 ‘i < _’ \\ last_x_assum $ qspec_then ‘i’ assume_tac \\ gs [EL_SNOC])
  \\ disch_then $ qx_choose_then ‘vL’ assume_tac
  \\ rename1 ‘eval_to k x = INR v’ \\ qexists_tac ‘v’ \\ qexists_tac ‘vL’
  \\ gs [MAP_SNOC, FOLDL_SNOC, eval_to_def, GSYM LESS_EQ_IFF_LESS_SUC] \\ rw []
  \\ gs [LIST_REL_SNOC]
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
  Induct using SNOC_INDUCT \\ gs [FOLDL_SNOC]
  \\ gen_tac \\ gen_tac \\ qspec_then ‘vL1’ assume_tac SNOC_CASES
  \\ gs [GSYM ADD1, FOLDL_APPEND]
  \\ rw []
  \\ once_rewrite_tac [eval_to_def] \\ gs []
  \\ first_assum $ qspec_then ‘LENGTH eL’ assume_tac \\ gs [EL_LENGTH_SNOC, EL_APPEND_EQN]
  \\ Cases_on ‘eval_to k x’ \\ gs []
  \\ rename1 ‘LIST_REL _ (vL1 ++ [v1])’
  \\ last_x_assum $ qspecl_then [‘vL1’, ‘e’, ‘k’] mp_tac \\ gs []
  \\ impl_tac
  >- (rw [] \\ rename1 ‘i < _’ \\ last_x_assum $ qspec_then ‘i’ assume_tac
      \\ gs [EL_SNOC])
  \\ rw [] \\ gs [] \\ disj2_tac
  \\ rename1 ‘Apps _ (MAP Value vL2)’ \\ rename1 ‘eval_to _ _ = INR w1’
  \\ qexists_tac ‘vL2 ++ [w1]’ \\ gs [FOLDL_APPEND, eval_to_def]
QED

Theorem eval_to_INR_List:
  ∀eL vL1 k. LIST_REL (λv e. ∃j. ($= +++ v_rel) (INR v) (eval_to (j + k) e)) vL1 eL ⇒
             ∃vL2 j.
               LIST_REL v_rel vL1 vL2 ∧ LIST_REL (λe v. ∀j2. eval_to (j2 + j + k) e = INR v) eL vL2
Proof
  Induct \\ gs [] \\ gen_tac \\ Cases \\ gs [PULL_EXISTS]
  \\ rw []
  \\ last_x_assum $ dxrule_then assume_tac
  \\ rename1 ‘eval_to (j + k) h’
  \\ Cases_on ‘eval_to (j + k) h’ \\ gs []
  \\ last_x_assum $ irule_at Any
  \\ last_x_assum $ irule_at Any
  \\ rename1 ‘eval_to (j1 + (_ + k)) _’
  \\ qexists_tac ‘j + j1’
  \\ qspecl_then [‘j + k’, ‘h’] assume_tac eval_to_mono \\ gs []
  \\ gs [LIST_REL_EL_EQN] \\ rw []
  \\ last_x_assum $ drule_then $ qspec_then ‘j + j2’ assume_tac \\ gs []
QED

Theorem eval_to_Apps_LIST_INR:
  ∀eL vL e k. LIST_REL (λe v. ∀j. eval_to (j + k) e = INR v) eL vL
              ⇒ ∀j. k ≤ j ⇒ eval_to j (Apps e eL) = eval_to j (Apps e (MAP Value vL))
Proof
  Induct using SNOC_INDUCT \\ gs [LIST_REL_SNOC, PULL_EXISTS, FOLDL_APPEND, FOLDL_SNOC]
  \\ rw [] \\ last_x_assum $ drule_all_then assume_tac
  \\ gs [eval_to_def]
  \\ first_x_assum $ qspec_then ‘j - k’ assume_tac
  \\ gs []
QED

Theorem eval_to_Apps_Tick_Lam:
  ∀eL s e k. eval_to k (Apps (Tick (Lam s e)) (MAP Value eL))
             = if k = 0 then INL Diverge
               else eval_to k (Apps (Lam s e) (MAP Value eL))
Proof
  Induct using SNOC_INDUCT \\ gs [MAP_SNOC, FOLDL_SNOC]
  \\ gs [eval_to_def] \\ rw []
  \\ gs [subst_funs_def, subst_empty]
  \\ gs [eval_to_def]
QED

Theorem MEM_SND:
  ∀l v. MEM v l ⇒ MEM (SND v) (MAP SND l)
Proof
  Induct \\ gs [FORALL_PROD]
  \\ rw []
  \\ last_x_assum $ dxrule_then assume_tac \\ gs []
QED

fun print_tac str g = (print (str ^ "\n"); ALL_TAC g);

Theorem combine_rel_eval_to:
  ∀x y.
    eval_to k x ≠ INL Type_error ∧
    combine_rel x y ⇒
      ∃j. ($= +++ v_rel) (eval_to k x) (eval_to (j + k) y)
Proof
  cheat (*
  completeInduct_on ‘k’ \\ completeInduct_on ‘exp_size x’
  \\ Cases \\ gvs [PULL_FORALL, exp_size_def] \\ rw []
  >~ [‘Var m’] >- (
    gvs [Once combine_rel_def]
    \\ qexists_tac ‘0’
    \\ simp [eval_to_def])
  >~ [‘Value v’] >- (
    gvs [Once combine_rel_def]
    \\ qexists_tac ‘0’
    \\ simp [eval_to_def])
  >~ [‘Lam s x’] >- (
    gvs [Once combine_rel_def]
    \\ qexists_tac ‘0’
    \\ gvs [eval_to_def, v_rel_Closure])
  >~ [‘Delay x’] >- (
    gvs [Once combine_rel_def, eval_to_def, v_rel_def])
  >~ [`Monad mop xs`]
  >- (
    gvs[Once combine_rel_def, eval_to_def] >> rw[Once v_rel_def, SF SFY_ss]
    )
  >~ [‘App f x’]

>- (

    gvs [Once combine_rel_def, eval_to_def]
    \\ rename1 ‘combine_rel x y’
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
        \\ rename1 ‘v_rel v1 w1’ \\ rename1 ‘combine_rel body body'’
        \\ last_x_assum $ qspecl_then [‘k - 1’, ‘subst1 s v1 body’, ‘subst1 s w1 body'’] mp_tac
        \\ gvs [] \\ impl_tac
        >- (irule combine_rel_subst \\ gvs [])
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
    >- (print_tac "Closure 1/4"
        \\ IF_CASES_TAC \\ gvs []
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
                \\ rename1 ‘hd ∉ freevars x2’ \\ rename1 ‘combine_rel x2 y2’
                \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
                \\ Cases_on ‘k = 1’
                \\ gvs [subst_Apps, subst1_notin_frees, freevars_def, subst1_def, eval_to_Tick]
                >- simp [eval_to_def]
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps expr2 argL2))’
                \\ qspecl_then [‘argL1’, ‘argL2’, ‘i2’, ‘k - 2’, ‘expr1’, ‘expr2’]
                               mp_tac eval_to_Apps_arg_Div_combine_rel
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
                \\ IF_CASES_TAC \\ gvs [combine_rel_def, subst1_def]
                \\ Cases_on ‘LENGTH vL2’ \\ gvs []
                \\ gvs [NOT_LESS, GSYM LESS_EQ_IFF_LESS_SUC, GSYM ADD1]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                \\ gvs [subst1_def, combine_rel_def])
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
                (* \\ Cases \\ gvs [] *)
                   \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘h’] assume_tac ALOOKUP_NONE
                   \\ gvs [MAP_REVERSE, MAP_ZIP, ALL_DISTINCT_APPEND])
            \\ gvs [] \\ pop_assum kall_tac
            \\ Cases_on ‘eval_to (k - 2) (Force (Value (EL i valL1))) = INL Diverge’ \\ gvs []
            >- (dxrule_then (qspec_then ‘i’ assume_tac) eval_to_Apps_arg_Div
                \\ gvs [EL_MAP2, EL_MAP]
                \\ qexists_tac ‘0’
                \\ rename1 ‘combine_rel x2 y2’ \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
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
                                ‘i’, ‘k - 2’, ‘expr2’] mp_tac eval_to_Apps_arg_Div_combine_rel2
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
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def]
                    \\ rpt $ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN]
                    \\ pop_assum $ qspec_then ‘j’ assume_tac
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def]
                    \\ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN, eval_to_Value, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def, eval_to_Value]))
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
                \\ rename1 ‘combine_rel x2 y2’ \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
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
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                      ‘Force (Value (EL i2 eL2))’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
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
                \\ irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP, combine_rel_def]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’]
                \\ irule combine_rel_Apps
                \\ conj_tac
                >- (irule combine_rel_Apps \\ gvs [EVERY2_MAP, subst1_def, combine_rel_def]
                    \\ qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λx.x’]
                                   assume_tac $ GEN_ALL LIST_REL_FILTER
                    \\ gs [GSYM FST_THM] \\ pop_assum irule \\ gvs [MAP_ZIP]
                    \\ irule LIST_REL_mono
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                    \\ gvs [LIST_REL_EL_EQN, EL_ZIP])
                \\ IF_CASES_TAC \\ gvs [subst1_def, combine_rel_def])
            \\ Q.REFINE_EXISTS_TAC ‘j + j1 + j2’ \\ gvs []
            \\ ‘eval_to (j + k) y ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ ‘eval_to (j1 + k) g ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ rename1 ‘combine_rel x2 y2’ \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
            \\ gvs [subst_Apps, subst1_notin_frees, subst1_def, eval_to_Tick]
            \\ ‘MAP (subst [(h,w1)])
                (MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                 (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Var h])))
                = MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                       (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’
              by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                  \\ rw [subst1_def, EL_APPEND_EQN, EL_MAP]
                  \\ gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                  \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘∀l. MAP (subst [(h,w1)]) (MAP Value l) = MAP Value l’
              by (gen_tac \\ irule LIST_EQ \\ rw [subst_def, EL_MAP])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst [(h,w1)]) (MAP Var (MAP SND (if b then [(T, h)] else [])))
                = MAP Value (if b then [w1] else [])’
                by (IF_CASES_TAC \\ gvs [subst_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps expr2 argL1'))’
            \\ ‘∀i. i < LENGTH argL1' ⇒ ∃j. ($= +++ v_rel) (INR (EL i valL2)) (eval_to (j + k - 2) (EL i argL1'))’
              by (rw [] \\ rename1 ‘i2 < _’
                  \\ gvs [Abbr ‘argL1'’, EL_MAP2, EL_MAP, EL_APPEND_EQN] \\ rw []
                  >- (last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value (EL i eL1))’,
                                                  ‘Force (Value (EL i eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                  ‘Force (Value (EL i2 eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gvs []
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gs []
                      \\ first_x_assum irule \\ rw [combine_rel_def])
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
            \\ disch_then $ qx_choose_then ‘valL2'’ $ qx_choose_then ‘j2’ assume_tac
            \\ Q.REFINE_EXISTS_TAC ‘j2 + j3’
            \\ qspecl_then [‘argL1'’, ‘valL2'’, ‘expr2’, ‘j2 + k - 2’] mp_tac eval_to_Apps_LIST_INR
            \\ impl_tac \\ gvs []
            >- (gvs [LIST_REL_EL_EQN] \\ rw []
                \\ rename1 ‘j + _ - 2’
                \\ first_x_assum $ dxrule_then $ qspec_then ‘j’ assume_tac \\ gvs [])
            \\ disch_then kall_tac
            \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Apps expr1 (MAP Value valL2)’,
                                           ‘Apps expr2 (MAP Value valL2')’] mp_tac
            \\ gvs [] \\ impl_tac
            >- (irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP, combine_rel_def]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’] \\ irule combine_rel_Apps
                \\ irule_at Any combine_rel_Apps \\ gs []
                \\ conj_tac
                >- (gvs [EVERY2_MAP, combine_rel_def]
                    \\ qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λx.x’]
                                   assume_tac $ GEN_ALL LIST_REL_FILTER
                    \\ gvs [GSYM FST_THM] \\ pop_assum irule
                    \\ gvs [MAP_ZIP]
                    \\ irule LIST_REL_mono
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_ZIP])
                \\ IF_CASES_TAC \\ gvs [combine_rel_def])
            \\ disch_then $ qx_choose_then ‘j3’ assume_tac \\ qexists_tac ‘j3’
            \\ Cases_on ‘eval_to (j3 + k − 2) (Apps expr2 (MAP Value valL2')) = INL Diverge’ \\ gs []
            >- (Cases_on ‘eval_to (k - 2) (Apps expr1 (MAP Value valL2))’ \\ gvs [])
            \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
        \\ qexists_tac ‘j + j1’
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
        \\ gvs [subst_Lams, subst_Apps, eval_to_Lams, subst_def]
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs [ALL_DISTINCT_APPEND]
        \\ irule_at (Pos last) combine_rel_subst
        \\ gvs [EXISTS_PROD, PULL_EXISTS, subst1_notin_frees]
        \\ first_assum $ irule_at $ Pos hd \\ first_assum $ irule_at $ Pos hd
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ qexists_tac ‘vL2’
        \\ qexists_tac ‘vL1a ++ [h]’ \\ gvs []
        \\ qexists_tac ‘i’
        \\ qexists_tac ‘eL2 ++ [w1]’ \\ qexists_tac ‘eL1 ++ [v1]’ \\ gvs []
        \\ qexists_tac ‘bL3b’ \\ qexists_tac ‘bL3a ++ [b]’ \\ qexists_tac ‘bL2’ \\ gvs []
        \\ gvs [ALL_DISTINCT_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
        \\ gvs [EVERY_MEM, freevars_subst] \\ rw [] \\ gvs []
        >- gvs [subst1_notin_frees]
        >- (rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                 \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN]
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                 \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN]
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
            \\ rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN] \\ gvs []
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_APPEND]
            \\ rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN] \\ gvs []
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (qpat_x_assum ‘ALL_DISTINCT vL1b’ mp_tac
            \\ ‘LENGTH vL1b = LENGTH bL3b’ by gvs []
            \\ pop_assum mp_tac
            \\ rpt $ pop_assum kall_tac
            \\ qid_spec_tac ‘bL3b’
            \\ Induct_on ‘vL1b’ \\ gvs []
            \\ gen_tac \\ Cases \\ gvs []
            \\ rw [] \\ gvs [MEM_MAP, MEM_FILTER, FORALL_PROD]
            \\ strip_tac \\ first_x_assum irule
            \\ gvs [MEM_EL, EL_ZIP]
            \\ irule_at Any EQ_REFL \\ gvs [])
        >- (qpat_x_assum ‘LIST_REL (λb3 b2. b3 ⇒ b2) _ _’ mp_tac
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (gvs [MEM_MAP, MEM_FILTER]
            \\ rename1 ‘MEM y2 (ZIP (bL3b, vL1b))’
            \\ ‘MEM (SND y2) vL1b’ suffices_by gvs []
            \\ gvs [MEM_EL, EL_ZIP]
            \\ irule_at Any EQ_REFL \\ gvs []))

    (* combine closure2 *)
    >- (print_tac "Closure 2/4"
        \\ IF_CASES_TAC \\ gvs []
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
                \\ rename1 ‘hd ∉ freevars x2’ \\ rename1 ‘combine_rel x2 y2’
                \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
                \\ Cases_on ‘k = 1’
                \\ gvs [subst_Apps, subst1_notin_frees, freevars_def, subst1_def, eval_to_Tick]
                >- simp [eval_to_def]
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps expr2 argL2))’
                \\ qspecl_then [‘argL1’, ‘argL2’, ‘i2’, ‘k - 2’, ‘expr1’, ‘expr2’]
                               mp_tac eval_to_Apps_arg_Div_combine_rel
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
                \\ IF_CASES_TAC \\ gvs [combine_rel_def, subst1_def]
                \\ Cases_on ‘LENGTH vL2’ \\ gvs []
                \\ gvs [NOT_LESS, GSYM LESS_EQ_IFF_LESS_SUC, GSYM ADD1]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                \\ gvs [subst1_def, combine_rel_def])
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
            \\ rename1 ‘subst _ (Apps (Apps (Apps (App x2 _) _) _) _)’
            \\ qmatch_goalsub_abbrev_tac ‘eval_to _ (subst list (Apps (Apps (Apps _ _) _) _))’
            \\ qspecl_then [‘list’, ‘x2’] mp_tac subst_notin_frees
            \\ gvs [MAP_ZIP, DISJOINT_ALT] \\ impl_tac
            >- (gvs [Abbr ‘list’, MAP_ZIP] \\ rw [] \\ gvs [EVERY_MEM])
            \\ strip_tac \\ gvs [subst_Apps, subst_App] \\ pop_assum kall_tac
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
                (* \\ Cases \\ gvs [] *)
                   \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘h’] assume_tac ALOOKUP_NONE
                   \\ gvs [MAP_REVERSE, MAP_ZIP, ALL_DISTINCT_APPEND])
            \\ gvs [] \\ pop_assum kall_tac
            \\ Cases_on ‘eval_to (k - 2) (Force (Value (EL i valL1))) = INL Diverge’ \\ gvs []
            >- (dxrule_then (qspec_then ‘i’ assume_tac) eval_to_Apps_arg_Div
                \\ gvs [EL_MAP2, EL_MAP]
                \\ qexists_tac ‘0’
                \\ rename1 ‘combine_rel x2 y2’ \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
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
                                ‘i’, ‘k - 2’, ‘expr2’] mp_tac eval_to_Apps_arg_Div_combine_rel2
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
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def]
                    \\ rpt $ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN]
                    \\ pop_assum $ qspec_then ‘j’ assume_tac
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def]
                    \\ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN, eval_to_Value, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def, eval_to_Value]))
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
                \\ rename1 ‘combine_rel x2 y2’ \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
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
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                      ‘Force (Value (EL i2 eL2))’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
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
                \\ irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP, combine_rel_def]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’]
                \\ irule combine_rel_Apps
                \\ conj_tac
                >- (irule combine_rel_Apps \\ gvs [EVERY2_MAP, subst1_def, combine_rel_def]
                    \\ conj_tac
                    >- (gvs [subst_def, Abbr ‘list’, GSYM ZIP_APPEND, REVERSE_APPEND, ALOOKUP_APPEND]
                        \\ qspecl_then [‘ZIP (vL2, valL1)’, ‘i’] assume_tac ALOOKUP_ALL_DISTINCT_EL
                        \\ qspecl_then [‘ZIP (vL2, valL1)’, ‘EL i vL2’] assume_tac alookup_distinct_reverse
                        \\ gvs [MAP_ZIP, ALL_DISTINCT_APPEND, EL_ZIP, subst1_def]
                        \\ rpt $ first_x_assum $ qspec_then ‘i’ assume_tac
                        \\ gvs [Abbr ‘argL1’, eval_to_Value, EL_MAP2, EL_APPEND_EQN]
                        \\ rw [EL_MAP, subst1_def] \\ gvs [EL_MAP, combine_rel_def, eval_to_Value]
                        \\ gvs [NOT_LESS] \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM
                        \\ gvs [subst1_def, eval_to_Value])
                    \\ qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λx.x’]
                                   assume_tac $ GEN_ALL LIST_REL_FILTER
                    \\ gs [GSYM FST_THM] \\ pop_assum irule \\ gvs [MAP_ZIP]
                    \\ irule LIST_REL_mono
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                    \\ gvs [LIST_REL_EL_EQN, EL_ZIP])
                \\ IF_CASES_TAC \\ gvs [subst1_def, combine_rel_def])
            \\ Q.REFINE_EXISTS_TAC ‘j + j1 + j2’ \\ gvs []
            \\ ‘eval_to (j + k) y ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ ‘eval_to (j1 + k) g ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ rename1 ‘combine_rel x2 y2’ \\ qspecl_then [‘x2’, ‘y2’] assume_tac combine_rel_freevars
            \\ gvs [subst_Apps, subst1_notin_frees, subst1_def, eval_to_Tick]
            \\ ‘MAP (subst [(h,w1)])
                (MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                 (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Var h])))
                = MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                       (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’
              by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                  \\ rw [subst1_def, EL_APPEND_EQN, EL_MAP]
                  \\ gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                  \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘∀l. MAP (subst [(h,w1)]) (MAP Value l) = MAP Value l’
              by (gen_tac \\ irule LIST_EQ \\ rw [subst_def, EL_MAP])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst [(h,w1)]) (MAP Var (MAP SND (if b then [(T, h)] else [])))
                = MAP Value (if b then [w1] else [])’
                by (IF_CASES_TAC \\ gvs [subst_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps expr2 argL1'))’
            \\ ‘∀i. i < LENGTH argL1' ⇒ ∃j. ($= +++ v_rel) (INR (EL i valL2)) (eval_to (j + k - 2) (EL i argL1'))’
              by (rw [] \\ rename1 ‘i2 < _’
                  \\ gvs [Abbr ‘argL1'’, EL_MAP2, EL_MAP, EL_APPEND_EQN] \\ rw []
                  >- (last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value (EL i eL1))’,
                                                  ‘Force (Value (EL i eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                  ‘Force (Value (EL i2 eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gvs []
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gs []
                      \\ first_x_assum irule \\ rw [combine_rel_def])
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
            \\ disch_then $ qx_choose_then ‘valL2'’ $ qx_choose_then ‘j2’ assume_tac
            \\ Q.REFINE_EXISTS_TAC ‘j2 + j3’
            \\ qspecl_then [‘argL1'’, ‘valL2'’, ‘expr2’, ‘j2 + k - 2’] mp_tac eval_to_Apps_LIST_INR
            \\ impl_tac \\ gvs []
            >- (gvs [LIST_REL_EL_EQN] \\ rw []
                \\ rename1 ‘j + _ - 2’
                \\ first_x_assum $ dxrule_then $ qspec_then ‘j’ assume_tac \\ gvs [])
            \\ disch_then kall_tac
            \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Apps expr1 (MAP Value valL2)’,
                                           ‘Apps expr2 (MAP Value valL2')’] mp_tac
            \\ gvs [] \\ impl_tac
            >- (irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP, combine_rel_def]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’]
                \\ irule combine_rel_Apps
                \\ conj_tac
                >- (irule combine_rel_Apps \\ gvs [EVERY2_MAP, subst1_def, combine_rel_def]
                    \\ conj_tac
                    >- (gvs [subst_def, Abbr ‘list’, GSYM ZIP_APPEND, REVERSE_APPEND, ALOOKUP_APPEND]
                        \\ qspecl_then [‘ZIP (vL2, valL1)’, ‘i’] assume_tac ALOOKUP_ALL_DISTINCT_EL
                        \\ qspecl_then [‘ZIP (vL2, valL1)’, ‘EL i vL2’] assume_tac alookup_distinct_reverse
                        \\ gvs [MAP_ZIP, ALL_DISTINCT_APPEND, EL_ZIP, subst1_def]
                        \\ rpt $ first_x_assum $ qspec_then ‘i’ assume_tac
                        \\ gvs [Abbr ‘argL1’, eval_to_Value, EL_MAP2, EL_APPEND_EQN]
                        \\ rw [EL_MAP, subst1_def] \\ gvs [EL_MAP, combine_rel_def, eval_to_Value]
                        \\ gvs [NOT_LESS] \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM
                        \\ gvs [subst1_def, eval_to_Value])
                    \\ qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λx.x’]
                                   assume_tac $ GEN_ALL LIST_REL_FILTER
                    \\ gs [GSYM FST_THM] \\ pop_assum irule \\ gvs [MAP_ZIP]
                    \\ irule LIST_REL_mono
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                    \\ gvs [LIST_REL_EL_EQN, EL_ZIP])
                \\ IF_CASES_TAC \\ gvs [subst1_def, combine_rel_def])
            \\ disch_then $ qx_choose_then ‘j3’ assume_tac \\ qexists_tac ‘j3’
            \\ Cases_on ‘eval_to (j3 + k − 2) (Apps expr2 (MAP Value valL2')) = INL Diverge’ \\ gs []
            >- (Cases_on ‘eval_to (k - 2) (Apps expr1 (MAP Value valL2))’ \\ gvs [])
            \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
        \\ qexists_tac ‘j + j1’
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
        \\ gvs [subst_Lams, subst_Apps, eval_to_Lams, subst_def]
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs [ALL_DISTINCT_APPEND]
        \\ irule_at (Pos last) combine_rel_subst
        \\ gvs [EXISTS_PROD, PULL_EXISTS, subst1_notin_frees]
        \\ first_assum $ irule_at $ Pos hd \\ first_assum $ irule_at $ Pos hd
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs [] \\ pop_assum $ irule_at Any)
        \\ qexists_tac ‘vL2’
        \\ qexists_tac ‘vL1a ++ [h]’ \\ gvs []
        \\ qexists_tac ‘i’
        \\ qexists_tac ‘eL2 ++ [w1]’ \\ qexists_tac ‘eL1 ++ [v1]’ \\ gvs []
        \\ qexists_tac ‘bL3b’ \\ qexists_tac ‘bL3a ++ [b]’ \\ qexists_tac ‘bL2’ \\ gvs []
        \\ gvs [ALL_DISTINCT_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
        \\ gvs [EVERY_MEM, freevars_subst] \\ rw [] \\ gvs []
        >- gvs [subst1_notin_frees]
        >- (rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                 \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN]
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                 \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN]
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
            \\ rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN] \\ gvs []
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_APPEND]
            \\ rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN] \\ gvs []
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (once_rewrite_tac [CONS_APPEND] \\ gvs []
            \\ rw [EL_APPEND_EQN, EL_MAP, subst1_def]
            >- (gvs [NOT_LESS, GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            \\ gvs [LIST_REL_EL_EQN, EL_MAP, subst1_def]
            \\ IF_CASES_TAC \\ gvs [EL_MEM])
        >- (qpat_x_assum ‘ALL_DISTINCT vL1b’ mp_tac
            \\ ‘LENGTH vL1b = LENGTH bL3b’ by gvs []
            \\ pop_assum mp_tac
            \\ rpt $ pop_assum kall_tac
            \\ qid_spec_tac ‘bL3b’
            \\ Induct_on ‘vL1b’ \\ gvs []
            \\ gen_tac \\ Cases \\ gvs []
            \\ rw [] \\ gvs [MEM_MAP, MEM_FILTER, FORALL_PROD]
            \\ strip_tac \\ first_x_assum irule
            \\ gvs [MEM_EL, EL_ZIP]
            \\ irule_at Any EQ_REFL \\ gvs [])
        >- (qpat_x_assum ‘LIST_REL (λb3 b2. b3 ⇒ b2) _ _’ mp_tac
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (gvs [MEM_MAP, MEM_FILTER]
            \\ rename1 ‘MEM y2 (ZIP (bL3b, vL1b))’
            \\ ‘MEM (SND y2) vL1b’ suffices_by gvs []
            \\ gvs [MEM_EL, EL_ZIP]
            \\ irule_at Any EQ_REFL \\ gvs []))

    (* combine closure1 rec *)
    >- (print_tac "Closure 3/4"
        \\ IF_CASES_TAC \\ gvs []
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
            \\ Cases_on ‘∃i. i < SUC (LENGTH eL1) ∧
                             eval_to (k - 1) (EL i (MAP2 (λb e. if b then Force e else e)
                                                    bL2 (MAP Value eL1 ++ [Value v1])))
                                                    = INL Diverge’ \\ gvs []
            >- (rename1 ‘eval_to _ (EL i2 _) = INL Diverge’
                \\ gvs [FOLDL_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ (Apps expr1 argL1)) _’
                \\ qspecl_then [‘argL1’, ‘i2’, ‘k - 1’, ‘expr1’] mp_tac eval_to_Apps_arg_Div
                \\ gvs []
                \\ impl_tac >- gvs [Abbr ‘argL1’] \\ rw []
                \\ qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono \\ gs []
                \\ pop_assum kall_tac \\ pop_assum kall_tac
                \\ Cases_on ‘k = 1’
                \\ gvs [subst_Apps, subst1_notin_frees, freevars_def, subst1_def, eval_to_Tick]
                >- simp [eval_to_def]
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps expr2 argL2))’
                \\ qspecl_then [‘argL1’, ‘argL2’, ‘i2’, ‘k - 2’, ‘expr1’, ‘expr2’]
                               mp_tac eval_to_Apps_arg_Div_combine_rel
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
                \\ qpat_x_assum ‘∀j. _ ⇒ ¬EL _ _’ $ qspec_then ‘i2’ assume_tac
                \\ gvs [NOT_LESS_EQUAL]
                \\ gvs [EL_MAP2, EL_MAP]
                \\ first_x_assum irule
                \\ IF_CASES_TAC \\ gvs [EL_APPEND_EQN, EL_MAP, subst1_def]
                \\ IF_CASES_TAC \\ gvs [combine_rel_def, subst1_def]
                \\ Cases_on ‘LENGTH vL2’ \\ gvs []
                \\ gvs [NOT_LESS, GSYM LESS_EQ_IFF_LESS_SUC, GSYM ADD1]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                \\ gvs [subst1_def, combine_rel_def])
            \\ gvs [FOLDL_APPEND]
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ (Apps expr1 argL1)) _’
            \\ qspecl_then [‘argL1’, ‘expr1’, ‘k - 1’] mp_tac eval_to_Apps_no_INL
            \\ gvs [] \\ impl_tac
            >- (rw [] \\ strip_tac \\ first_x_assum $ dxrule_then assume_tac \\ gvs [Abbr ‘argL1’])
            \\ disch_then $ qx_choose_then ‘valL1’ assume_tac \\ gvs [Abbr ‘expr1’]
            \\ pop_assum kall_tac
            \\ ‘LENGTH vL2 = LENGTH valL1’ by gvs [Abbr ‘argL1’, LIST_REL_EL_EQN]
            \\ Cases_on ‘k = 1’ \\ gvs []
            >- (qmatch_goalsub_abbrev_tac ‘Apps (Apps (Apps (Value (Recclosure list _)) _) _) _’
                \\ qspecl_then [‘MAP SND (FILTER FST (ZIP (bL3a,eL1))) ++
                                  (if b then [v1] else []) ++ valL1’,
                                ‘list’, ‘v1'’] mp_tac eval_to_Apps_Rec_0
                \\ Cases_on ‘vL2 = []’ \\ gvs []
                \\ gvs [Abbr ‘list’, REVERSE_SNOC, Lams_split]
                \\ impl_tac
                >- (rw [] \\ gvs [Abbr ‘argL1’, LIST_REL_EL_EQN])
                \\ gvs [FOLDL_APPEND]
                \\ ‘MAP Value (if b then [v1] else []) = if b then [Value v1] else []’ by (IF_CASES_TAC \\ gs [])
                \\ gvs []
                \\ disch_then kall_tac
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
            \\ qmatch_goalsub_abbrev_tac ‘Apps (Apps (Apps (Value (Recclosure list _)) _) _) _’
            \\ qspecl_then [‘MAP Value (MAP SND (FILTER FST (ZIP (bL3a, eL1)))) ++
                             (if b then [Value v1] else []) ++ MAP Value valL1’,
                            ‘k - 1’, ‘list’, ‘v1'’] mp_tac eval_to_Apps_Recclosure_Lams_not_0
            \\ gvs [Abbr ‘list’, REVERSE_SNOC, Lams_split]
            \\ impl_tac
            >- (rw [] \\ gvs [Abbr ‘argL1’, LIST_REL_EL_EQN])
            \\ strip_tac \\ gvs [FOLDL_APPEND]
            \\ pop_assum kall_tac
            \\ gvs [subst_funs_def, subst_def]
            \\ qmatch_goalsub_abbrev_tac ‘Tick (Lam _ expr1)’
            \\ qspecl_then [‘MAP SND (FILTER FST (ZIP (bL3a,eL1))) ++
                             (if b then [v1] else []) ++ valL1’,
                            ‘HD (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))
                                 ++ MAP SND (if b then [(T, h)] else []) ++ vL2)’,
                            ‘expr1’, ‘k - 1’] assume_tac eval_to_Apps_Tick_Lam
            \\ gvs [FOLDL_APPEND]
            \\ gvs [Abbr ‘expr1’, subst_Lams, GSYM Lams_split]
            \\ qmatch_goalsub_abbrev_tac ‘Apps (Apps (Apps (Lams _ expr1) _) _) _’
            \\ qspecl_then [‘MAP SND (FILTER FST (ZIP (bL3a,vL1a))) ++
                             MAP SND (if b then [(T,h)] else []) ++ vL2’,
                            ‘MAP SND (FILTER FST (ZIP (bL3a, eL1))) ++
                             (if b then [v1] else []) ++ valL1’,
                            ‘expr1’, ‘k - 1’] assume_tac eval_to_Apps_not_Val_Lams_not_0
            \\ gvs [FOLDL_APPEND] \\ pop_assum kall_tac
            \\ gvs [Abbr ‘expr1’, subst_Apps]
            \\ qmatch_goalsub_abbrev_tac ‘eval_to _ (Apps (Apps (Apps (subst list1a (subst list1b _)) _) _) _)’
            \\ qspecl_then [‘list1a’, ‘subst list1b x1’] mp_tac subst_notin_frees
            \\ gvs [MAP_ZIP, DISJOINT_ALT] \\ impl_tac
            >- (gvs [Abbr ‘list1a’, MAP_ZIP] \\ rw [] \\ gvs [EVERY_MEM, freevars_subst])
            \\ strip_tac \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst list1a) (MAP (subst list1b) (MAP Var (MAP SND (FILTER FST (ZIP (bL3a, vL1a))))))
                = MAP Value (MAP SND (FILTER FST (ZIP (bL3a, eL1))))’
              by (gvs [Abbr ‘list1a’, Abbr ‘list1b’, GSYM ZIP_APPEND]
                  \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def, REVERSE_APPEND, ALOOKUP_APPEND]
                  \\ gen_tac \\ strip_tac \\ rename1 ‘n < LENGTH (FILTER _ _)’
                  \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                  \\ Cases_on ‘FILTER FST (ZIP (bL3a, vL1a))’ \\ gvs []
                  \\ Cases_on ‘n’ \\ gvs []
                  >- (gvs [subst_def, REVERSE_APPEND, ALOOKUP_APPEND]
                      \\ rename1 ‘FILTER FST _ = hd::tl’
                      \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘SND hd’]
                                     mp_tac $ iffRL ALOOKUP_NONE
                      \\ impl_tac \\ gvs []
                      >- (strip_tac \\ gvs [MAP_REVERSE, MAP_ZIP]
                          \\ ‘MEM hd (FILTER FST (ZIP (bL3a, vL1a)))’ by gvs []
                          \\ gvs [MEM_FILTER])
                      \\ disch_then kall_tac
                      \\ Cases_on ‘HD (FILTER FST (ZIP (bL3a, eL1)))’
                      \\ Cases_on ‘FILTER FST (ZIP (bL3a, eL1))’ \\ gvs [ALOOKUP_APPEND]
                      \\ rename1 ‘ZIP (MAP SND tl1, MAP SND tl2)’
                      \\ qspecl_then [‘REVERSE (ZIP (MAP SND tl1, MAP SND tl2))’, ‘SND (hd)’]
                                     mp_tac $ iffRL ALOOKUP_NONE
                      \\ impl_tac \\ gvs []
                      >- (strip_tac \\ gvs [MAP_REVERSE, MAP_ZIP])
                      \\ disch_then kall_tac
                      \\ IF_CASES_TAC \\ gvs [])
                  >- (rpt $ qpat_x_assum ‘eval_to _ _ = _’ kall_tac
                      \\ rpt $ qpat_x_assum ‘∀i. eval_to _ _ = _’ kall_tac
                      \\ rename1 ‘n < LENGTH t’
                      \\ ‘MEM (SND (EL n t)) (MAP SND t)’
                        by (gvs [MEM_EL, SF CONJ_ss, EL_MAP]
                            \\ irule_at Any EQ_REFL \\ gvs [])
                      \\ gvs [subst_def, REVERSE_APPEND, ALOOKUP_APPEND]
                      \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘SND (EL n t)’]
                                     mp_tac $ iffRL ALOOKUP_NONE
                      \\ impl_tac \\ gvs []
                      >- (strip_tac \\ gvs [MAP_REVERSE, MAP_ZIP, ALL_DISTINCT_APPEND])
                      \\ disch_then kall_tac
                      \\ Cases_on ‘HD (FILTER FST (ZIP (bL3a, eL1)))’
                      \\ Cases_on ‘FILTER FST (ZIP (bL3a, eL1))’ \\ gvs [ALOOKUP_APPEND]
                      \\ rename1 ‘ZIP (MAP SND tl1, MAP SND tl2)’
                      \\ qspecl_then [‘ZIP (MAP SND tl1, MAP SND tl2)’] assume_tac alookup_distinct_reverse
                      \\ qspecl_then [‘ZIP (MAP SND tl1, MAP SND tl2)’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
                      \\ gvs [ALL_DISTINCT_APPEND, MAP_ZIP, EL_ZIP, EL_MAP]
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs [MEM_MAP]))
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst list1a) (MAP (subst list1b)
                                    (MAP2 (λb e. if b then Force e else e)
                                     (GENLIST (λn. n = i) (LENGTH valL1)) (MAP Var vL2)))
                = MAP2 (λb e. if b then Force e else e)
                       (GENLIST (λn. n = i) (LENGTH valL1)) (MAP Value valL1)’
              by (rpt $ qpat_x_assum ‘eval_to _ _ = _’ kall_tac
                  \\ rpt $ qpat_x_assum ‘∀i. eval_to _ _ = _’ kall_tac
                  \\ qpat_x_assum ‘eval_to _ _ ≠ _’ kall_tac
                  \\ gvs [Abbr ‘list1a’, Abbr ‘list1b’, GSYM ZIP_APPEND]
                  \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                  \\ gen_tac \\ strip_tac \\ rename1 ‘n < LENGTH _’
                  \\ qspecl_then [‘ZIP (vL2, valL1)’] assume_tac $ GEN_ALL alookup_distinct_reverse
                  \\ qspecl_then [‘ZIP (vL2, valL1)’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
                  \\ ‘MEM (EL n vL2) (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))
                                       ++ MAP SND (if b then [(T, h)] else []) ++ vL2)’
                    by gvs [EL_MEM]
                  \\ ‘∀l. MEM (EL n vL2) l ∧ l ≠ [] ⇒ MEM (EL n vL2) (TL l) ∨ EL n vL2 = HD l’
                    by (Cases \\ rw [] \\ gvs [])
                  \\ pop_assum $ dxrule_then assume_tac
                  \\ rename1 ‘subst (FILTER _ (FILTER _ abbrev_list))’
                  \\ Cases_on ‘n = i’
                  \\ gvs [subst_def, REVERSE_APPEND, ALOOKUP_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER,
                          ALL_DISTINCT_APPEND, EL_ZIP, MAP_ZIP])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst list1a) (MAP (subst list1b) (MAP Var (MAP SND (if b then [(T, h)] else []))))
                = if b then [Value v1] else []’
              by (IF_CASES_TAC \\ gvs []
                  \\ gvs [Abbr ‘list1a’, Abbr ‘list1b’, GSYM ZIP_APPEND, ALL_DISTINCT_APPEND]
                  \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                  \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘h’] assume_tac ALOOKUP_NONE
                  \\ gvs [MAP_ZIP, MAP_REVERSE]
                  \\ Cases_on ‘MAP SND (FILTER FST (ZIP (bL3a, vL1a)))’ \\ gvs [subst_APPEND, subst_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ Cases_on ‘eval_to (k - 2) (Force (Value (EL i valL1))) = INL Diverge’ \\ gvs []
            >- (dxrule_then (qspec_then ‘i’ assume_tac) eval_to_Apps_arg_Div
                \\ gvs [EL_MAP2, EL_MAP]
                \\ qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono
                \\ gvs [subst_Apps, subst1_def, subst1_notin_frees, eval_to_Tick]
                \\ qpat_x_assum ‘∀j. _ ⇒ eval_to _ g = _’ kall_tac
                \\ qpat_x_assum ‘∀j. _ ⇒ eval_to _ y = _’ kall_tac
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
                \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                \\ gvs [subst1_notin_frees, freevars_subst]
                \\ qmatch_goalsub_abbrev_tac ‘_ (INL Diverge) (eval_to _ (Apps expr2 _))’
                \\ qspecl_then [‘MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                                  (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL1 ++ [Value v1]))’,
                              ‘MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                                  (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’,
                                ‘i’, ‘k - 2’, ‘expr2’] mp_tac eval_to_Apps_arg_Div_combine_rel2
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
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def]
                    \\ rpt $ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN]
                    \\ pop_assum $ qspec_then ‘j’ assume_tac
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def]
                    \\ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN, eval_to_Value, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def, eval_to_Value]))
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
                \\ rename1 ‘combine_rel x1 x2’ \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                \\ gvs [subst_Apps, subst1_notin_frees, subst1_def, freevars_subst, eval_to_Tick]
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
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                      ‘Force (Value (EL i2 eL2))’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
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
                \\ irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP, combine_rel_def]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’]
                \\ irule combine_rel_Apps
                \\ conj_tac
                >- (irule combine_rel_Apps \\ gvs [EVERY2_MAP, subst1_def, combine_rel_def]
                    \\ qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λx.x’]
                                   assume_tac $ GEN_ALL LIST_REL_FILTER
                    \\ gs [GSYM FST_THM] \\ pop_assum $ irule_at Any \\ gvs [MAP_ZIP]
                    \\ irule_at Any LIST_REL_mono
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                    \\ gvs [LIST_REL_EL_EQN, EL_ZIP]
                    \\ rpt $ qpat_x_assum ‘eval_to _ _ = _’ kall_tac
                    \\ rpt $ qpat_x_assum ‘∀j. _ ⇒ eval_to _ _ = _’ kall_tac
                    \\ gvs [Abbr ‘list1b’, FILTER_FILTER, LAMBDA_PROD]
                    \\ qmatch_goalsub_abbrev_tac ‘combine_rel (subst (FILTER _ list1) _)
                                                  (subst (FILTER _ list2) _)’
                    \\ ‘∀l (v : string). l ≠ [] ⇒ (¬MEM v (TL l) ∧ v ≠ HD l) = ¬MEM v l’
                      by (Cases \\ gvs [CONJ_COMM])
                    \\ gvs [] \\ pop_assum kall_tac
                    \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                    \\ qspecl_then [‘list2’, ‘x2’, ‘set vL1a ∪ {h}’] assume_tac subst_remove
                    \\ gvs [DISJOINT_ALT, EVERY_MEM]
                    \\ pop_assum kall_tac
                    \\ qspecl_then [‘list1’, ‘x1’,
                                    ‘set (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))) ∪
                                     set (MAP SND (if b then [(T, h)] else [])) ∪
                                     set vL2’] assume_tac subst_remove
                    \\ gvs [DISJOINT_ALT]
                    \\ pop_assum kall_tac
                    \\ irule combine_rel_subst \\ gvs [Abbr ‘list1’, Abbr ‘list2’]
                    \\ conj_tac
                    >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                    \\ gvs [MAP_SNOC, LIST_REL_SNOC]
                    \\ rpt $ conj_tac
                    >- (gvs [LIST_REL_EL_EQN, EL_MAP]
                        \\ gen_tac \\ rename1 ‘n < _ ⇒ _’ \\ strip_tac
                        \\ rename1 ‘MAP FST xs = MAP FST ys’
                        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1a ++ [h]’
                        \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3a ++ [b]’
                        \\ qexists_tac ‘i’
                        \\ gvs [FOLDL_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_MEM])
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                    \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1a ++ [h]’
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3a ++ [b]’
                    \\ qexists_tac ‘i’
                    \\ gvs [FOLDL_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_MEM])
                \\ IF_CASES_TAC \\ gvs [subst1_def, combine_rel_def])
            \\ Q.REFINE_EXISTS_TAC ‘j + j1 + j2’ \\ gvs []
            \\ ‘eval_to (j + k) y ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ ‘eval_to (j1 + k) g ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ qpat_x_assum ‘eval_to _ f = _’ kall_tac
            \\ rename1 ‘combine_rel x1 x2’ \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
            \\ gvs [subst_Apps, subst1_notin_frees, subst1_def, eval_to_Tick]
            \\ ‘MAP (subst [(h,w1)])
                (MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                 (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Var h])))
                = MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                       (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’
              by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                  \\ rw [subst1_def, EL_APPEND_EQN, EL_MAP]
                  \\ gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                  \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘∀l. MAP (subst [(h,w1)]) (MAP Value l) = MAP Value l’
              by (gen_tac \\ irule LIST_EQ \\ rw [subst_def, EL_MAP])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst [(h,w1)]) (MAP Var (MAP SND (if b then [(T, h)] else [])))
                = MAP Value (if b then [w1] else [])’
                by (IF_CASES_TAC \\ gvs [subst_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps expr2 argL1'))’
            \\ ‘∀i. i < LENGTH argL1' ⇒
                    ∃j. ($= +++ v_rel) (INR (EL i valL2)) (eval_to (j + k - 2) (EL i argL1'))’
              by (rw [] \\ rename1 ‘i2 < _’
                  \\ gvs [Abbr ‘argL1'’, EL_MAP2, EL_MAP, EL_APPEND_EQN] \\ rw []
                  >- (last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value (EL i eL1))’,
                                                  ‘Force (Value (EL i eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                  ‘Force (Value (EL i2 eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gvs []
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gs []
                      \\ first_x_assum irule \\ rw [combine_rel_def])
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
            \\ disch_then $ qx_choose_then ‘valL2'’ $ qx_choose_then ‘j2’ assume_tac
            \\ Q.REFINE_EXISTS_TAC ‘j2 + j3’
            \\ qspecl_then [‘argL1'’, ‘valL2'’, ‘expr2’, ‘j2 + k - 2’] mp_tac eval_to_Apps_LIST_INR
            \\ impl_tac \\ gvs []
            >- (gvs [LIST_REL_EL_EQN] \\ rw []
                \\ rename1 ‘j + _ - 2’
                \\ first_x_assum $ dxrule_then $ qspec_then ‘j’ assume_tac \\ gvs [])
            \\ disch_then kall_tac
            \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Apps expr1 (MAP Value valL2)’,
                                           ‘Apps expr2 (MAP Value valL2')’] mp_tac
            \\ gvs [] \\ impl_tac
            >- (irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP, combine_rel_def]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’, subst1_notin_frees, freevars_subst]
                \\ irule combine_rel_Apps
                \\ conj_tac
                >- (irule combine_rel_Apps \\ gvs [EVERY2_MAP, subst1_def, combine_rel_def]
                    \\ qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λx.x’]
                                   assume_tac $ GEN_ALL LIST_REL_FILTER
                    \\ gs [GSYM FST_THM] \\ pop_assum $ irule_at Any \\ gvs [MAP_ZIP]
                    \\ irule_at Any LIST_REL_mono
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                    \\ gvs [LIST_REL_EL_EQN, EL_ZIP]
                    \\ rpt $ qpat_x_assum ‘eval_to _ _ = _’ kall_tac
                    \\ rpt $ qpat_x_assum ‘∀j. _ ⇒ eval_to _ _ = _’ kall_tac
                    \\ gvs [Abbr ‘list1b’, FILTER_FILTER, LAMBDA_PROD]
                    \\ qmatch_goalsub_abbrev_tac ‘combine_rel (subst (FILTER _ list1) _)
                                                  (subst (FILTER _ list2) _)’
                    \\ ‘∀l (v : string). l ≠ [] ⇒ (¬MEM v (TL l) ∧ v ≠ HD l) = ¬MEM v l’
                      by (Cases \\ gvs [CONJ_COMM])
                    \\ gvs [] \\ pop_assum kall_tac
                    \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                    \\ qspecl_then [‘list2’, ‘x2’, ‘set vL1a ∪ {h}’] assume_tac subst_remove
                    \\ gvs [DISJOINT_ALT, EVERY_MEM]
                    \\ pop_assum kall_tac
                    \\ qspecl_then [‘list1’, ‘x1’,
                                    ‘set (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))) ∪
                                     set (MAP SND (if b then [(T, h)] else [])) ∪
                                     set vL2’] assume_tac subst_remove
                    \\ gvs [DISJOINT_ALT]
                    \\ pop_assum kall_tac
                    \\ irule combine_rel_subst \\ gvs [Abbr ‘list1’, Abbr ‘list2’]
                    \\ conj_tac
                    >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                    \\ gvs [MAP_SNOC, LIST_REL_SNOC]
                    \\ rpt $ conj_tac
                    >- (gvs [LIST_REL_EL_EQN, EL_MAP]
                        \\ gen_tac \\ rename1 ‘n < _ ⇒ _’ \\ strip_tac
                        \\ rename1 ‘MAP FST xs = MAP FST ys’
                        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1a ++ [h]’
                        \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3a ++ [b]’
                        \\ qexists_tac ‘i’
                        \\ gvs [FOLDL_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_MEM])
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                    \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1a ++ [h]’
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3a ++ [b]’
                    \\ qexists_tac ‘i’
                    \\ gvs [FOLDL_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_MEM])
                \\ IF_CASES_TAC \\ gvs [subst1_def, combine_rel_def])
            \\ disch_then $ qx_choose_then ‘j3’ assume_tac \\ qexists_tac ‘j3’
            \\ Cases_on ‘eval_to (j3 + k − 2) (Apps expr2 (MAP Value valL2')) = INL Diverge’
            \\ gs []
            >- (Cases_on ‘eval_to (k - 2) (Apps expr1 (MAP Value valL2))’ \\ gvs [])
            \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
        \\ qexists_tac ‘j + j1’
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
        \\ gvs [subst_Lams, subst_Apps, eval_to_Lams, subst_def]
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs [ALL_DISTINCT_APPEND]
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ gvs [subst1_notin_frees, freevars_subst]
        \\ qpat_assum ‘combine_rel x1 x2’ $ irule_at Any
        \\ qexists_tac ‘vL2’ \\ qexists_tac ‘i’ \\ gvs []
        \\ rename1 ‘MAP FST xs = MAP FST ys’ \\ qexists_tac ‘ys’ \\ gvs []
        \\ qexists_tac ‘eL2 ++ [w1]’ \\ qexists_tac ‘eL1 ++ [v1]’ \\ gvs []
        \\ qexists_tac ‘bL3b’ \\ qexists_tac ‘bL3a ++ [b]’ \\ qexists_tac ‘bL2’ \\ gvs []
        \\ gvs [ALL_DISTINCT_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
        \\ gvs [EVERY_MEM, freevars_subst] \\ rw [] \\ gvs []
        >- (rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                 \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN]
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                 \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN]
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
            \\ rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN] \\ gvs []
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_APPEND]
            \\ rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN] \\ gvs []
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (irule EQ_TRANS \\ irule_at (Pos hd) subst1_notin_frees
            \\ gvs [GSYM CONJ_ASSOC, freevars_subst]
            \\ first_x_assum $ qspec_then ‘h’ assume_tac \\ gvs []
            \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars \\ gvs []
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (irule EQ_TRANS \\ irule_at (Pos hd) subst1_notin_frees
            \\ gvs [GSYM CONJ_ASSOC, freevars_subst]
            \\ first_x_assum $ qspec_then ‘h’ assume_tac \\ gvs []
            \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars \\ gvs []
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (qpat_x_assum ‘ALL_DISTINCT vL1b’ mp_tac
            \\ qpat_x_assum ‘LENGTH vL1b = LENGTH bL3b’ mp_tac
            \\ rpt $ pop_assum kall_tac
            \\ qid_spec_tac ‘bL3b’
            \\ Induct_on ‘vL1b’ \\ gvs []
            \\ gen_tac \\ Cases \\ gvs []
            \\ rw [] \\ gvs [MEM_MAP, MEM_FILTER, FORALL_PROD]
            \\ strip_tac \\ first_x_assum irule
            \\ gvs [MEM_EL, EL_ZIP]
            \\ irule_at Any EQ_REFL \\ gvs [])
        >- (qpat_x_assum ‘LIST_REL (λb3 b2. b3 ⇒ b2) _ _’ mp_tac
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (gvs [MEM_MAP, MEM_FILTER]
            \\ rename1 ‘MEM y2 (ZIP (bL3b, vL1b))’
            \\ ‘MEM (SND y2) vL1b’ suffices_by gvs []
            \\ gvs [MEM_EL, EL_ZIP]
            \\ irule_at Any EQ_REFL \\ gvs []))

    (* combine closure2 rec *)
    >- (print_tac "Closure 4/4"
        \\ IF_CASES_TAC \\ gvs []
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
            \\ Cases_on ‘∃i. i < SUC (LENGTH eL1) ∧
                             eval_to (k - 1) (EL i (MAP2 (λb e. if b then Force e else e)
                                                    bL2 (MAP Value eL1 ++ [Value v1])))
                                                    = INL Diverge’ \\ gvs []
            >- (rename1 ‘eval_to _ (EL i2 _) = INL Diverge’
                \\ gvs [FOLDL_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ (Apps expr1 argL1)) _’
                \\ qspecl_then [‘argL1’, ‘i2’, ‘k - 1’, ‘expr1’] mp_tac eval_to_Apps_arg_Div
                \\ gvs []
                \\ impl_tac >- gvs [Abbr ‘argL1’] \\ rw []
                \\ qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono \\ gs []
                \\ pop_assum kall_tac \\ pop_assum kall_tac
                \\ Cases_on ‘k = 1’
                \\ gvs [subst_Apps, subst1_notin_frees, freevars_def, subst1_def, eval_to_Tick]
                >- simp [eval_to_def]
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps expr2 argL2))’
                \\ qspecl_then [‘argL1’, ‘argL2’, ‘i2’, ‘k - 2’, ‘expr1’, ‘expr2’]
                               mp_tac eval_to_Apps_arg_Div_combine_rel
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
                \\ qpat_x_assum ‘∀j. _ ⇒ ¬EL _ _’ $ qspec_then ‘i2’ assume_tac
                \\ gvs [NOT_LESS_EQUAL]
                \\ gvs [EL_MAP2, EL_MAP]
                \\ first_x_assum irule
                \\ IF_CASES_TAC \\ gvs [EL_APPEND_EQN, EL_MAP, subst1_def]
                \\ IF_CASES_TAC \\ gvs [combine_rel_def, subst1_def]
                \\ Cases_on ‘LENGTH vL2’ \\ gvs []
                \\ gvs [NOT_LESS, GSYM LESS_EQ_IFF_LESS_SUC, GSYM ADD1]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                \\ gvs [subst1_def, combine_rel_def])
            \\ gvs [FOLDL_APPEND]
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ (Apps expr1 argL1)) _’
            \\ qspecl_then [‘argL1’, ‘expr1’, ‘k - 1’] mp_tac eval_to_Apps_no_INL
            \\ gvs [] \\ impl_tac
            >- (rw [] \\ strip_tac \\ first_x_assum $ dxrule_then assume_tac
                \\ gvs [Abbr ‘argL1’])
            \\ disch_then $ qx_choose_then ‘valL1’ assume_tac \\ gvs [Abbr ‘expr1’]
            \\ pop_assum kall_tac
            \\ ‘LENGTH vL2 = LENGTH valL1’ by gvs [Abbr ‘argL1’, LIST_REL_EL_EQN]
            \\ Cases_on ‘k = 1’ \\ gvs []
            >- (qmatch_goalsub_abbrev_tac ‘Apps (Apps (Apps (Value (Recclosure list _)) _) _) _’
                \\ qspecl_then [‘MAP SND (FILTER FST (ZIP (bL3a,eL1))) ++
                                  (if b then [v1] else []) ++ valL1’,
                                ‘list’, ‘v1'’] mp_tac eval_to_Apps_Rec_0
                \\ Cases_on ‘vL2 = []’ \\ gvs []
                \\ gvs [Abbr ‘list’, REVERSE_SNOC, Lams_split]
                \\ impl_tac
                >- (rw [] \\ gvs [Abbr ‘argL1’, LIST_REL_EL_EQN])
                \\ gvs [FOLDL_APPEND]
                \\ ‘MAP Value (if b then [v1] else []) = if b then [Value v1] else []’
                  by (IF_CASES_TAC \\ gs [])
                \\ gvs []
                \\ disch_then kall_tac
                \\ Cases_on ‘b’ \\ gvs []
                \\ qexists_tac ‘0’
                \\ Cases_on ‘eval_to 1 y = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono \\ gs []
                \\ Cases_on ‘eval_to 1 g = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono \\ gs []
                \\ gvs [subst1_def, eval_to_def])
            \\ ‘∀(v : thunkLang$v). MAP Value (if b then [v] else [])
                                    = if b then [Value v] else []’ by rw []
            \\ ‘∀(h : string). LENGTH (if b then [(T, h)] else []) = if b then 1 else 0’ by rw []
            \\ ‘∀(v : thunkLang$v). LENGTH (if b then [v] else []) = if b then 1 else 0’ by rw []
            \\ Cases_on ‘vL2 = []’ \\ gvs []
            \\ qmatch_goalsub_abbrev_tac ‘Apps (Apps (Apps (Value (Recclosure list _)) _) _) _’
            \\ qspecl_then [‘MAP Value (MAP SND (FILTER FST (ZIP (bL3a, eL1)))) ++
                             (if b then [Value v1] else []) ++ MAP Value valL1’,
                            ‘k - 1’, ‘list’, ‘v1'’] mp_tac eval_to_Apps_Recclosure_Lams_not_0
            \\ gvs [Abbr ‘list’, REVERSE_SNOC, Lams_split]
            \\ impl_tac
            >- (rw [] \\ gvs [Abbr ‘argL1’, LIST_REL_EL_EQN])
            \\ strip_tac \\ gvs [FOLDL_APPEND]
            \\ pop_assum kall_tac
            \\ gvs [subst_funs_def, subst_def]
            \\ qmatch_goalsub_abbrev_tac ‘Tick (Lam _ expr1)’
            \\ qspecl_then [‘MAP SND (FILTER FST (ZIP (bL3a,eL1))) ++
                             (if b then [v1] else []) ++ valL1’,
                            ‘HD (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))
                                 ++ MAP SND (if b then [(T, h)] else []) ++ vL2)’,
                            ‘expr1’, ‘k - 1’] assume_tac eval_to_Apps_Tick_Lam
            \\ gvs [FOLDL_APPEND]
            \\ gvs [Abbr ‘expr1’, subst_Lams, GSYM Lams_split]
            \\ qmatch_goalsub_abbrev_tac ‘Apps (Apps (Apps (Lams _ expr1) _) _) _’
            \\ qspecl_then [‘MAP SND (FILTER FST (ZIP (bL3a,vL1a))) ++
                             MAP SND (if b then [(T,h)] else []) ++ vL2’,
                            ‘MAP SND (FILTER FST (ZIP (bL3a, eL1))) ++
                             (if b then [v1] else []) ++ valL1’,
                            ‘expr1’, ‘k - 1’] assume_tac eval_to_Apps_not_Val_Lams_not_0
            \\ gvs [FOLDL_APPEND] \\ pop_assum kall_tac
            \\ gvs [Abbr ‘expr1’, subst_Apps]
            \\ qmatch_goalsub_abbrev_tac ‘eval_to _ (Apps(Apps(Apps(subst list1a
                                                                    (subst list1b _)) _) _) _)’
            \\ qspecl_then [‘list1a’, ‘subst list1b x1’] mp_tac subst_notin_frees
            \\ gvs [MAP_ZIP, DISJOINT_ALT] \\ impl_tac
            >- (gvs [Abbr ‘list1a’, MAP_ZIP] \\ rw [] \\ gvs [EVERY_MEM, freevars_subst])
            \\ strip_tac \\ gvs [subst_def] \\ pop_assum kall_tac
            \\ ‘MAP (subst list1a) (MAP (subst list1b)
                                    (MAP Var (MAP SND (FILTER FST (ZIP (bL3a, vL1a))))))
                = MAP Value (MAP SND (FILTER FST (ZIP (bL3a, eL1))))’
              by (gvs [Abbr ‘list1a’, Abbr ‘list1b’, GSYM ZIP_APPEND]
                  \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def, REVERSE_APPEND, ALOOKUP_APPEND]
                  \\ gen_tac \\ strip_tac \\ rename1 ‘n < LENGTH (FILTER _ _)’
                  \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                  \\ Cases_on ‘FILTER FST (ZIP (bL3a, vL1a))’ \\ gvs []
                  \\ Cases_on ‘n’ \\ gvs []
                  >- (gvs [subst_def, REVERSE_APPEND, ALOOKUP_APPEND]
                      \\ rename1 ‘FILTER FST _ = hd::tl’
                      \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘SND hd’]
                                     mp_tac $ iffRL ALOOKUP_NONE
                      \\ impl_tac \\ gvs []
                      >- (strip_tac \\ gvs [MAP_REVERSE, MAP_ZIP]
                          \\ ‘MEM hd (FILTER FST (ZIP (bL3a, vL1a)))’ by gvs []
                          \\ gvs [MEM_FILTER])
                      \\ disch_then kall_tac
                      \\ Cases_on ‘HD (FILTER FST (ZIP (bL3a, eL1)))’
                      \\ Cases_on ‘FILTER FST (ZIP (bL3a, eL1))’ \\ gvs [ALOOKUP_APPEND]
                      \\ rename1 ‘ZIP (MAP SND tl1, MAP SND tl2)’
                      \\ qspecl_then [‘REVERSE (ZIP (MAP SND tl1, MAP SND tl2))’, ‘SND (hd)’]
                                     mp_tac $ iffRL ALOOKUP_NONE
                      \\ impl_tac \\ gvs []
                      >- (strip_tac \\ gvs [MAP_REVERSE, MAP_ZIP])
                      \\ disch_then kall_tac
                      \\ IF_CASES_TAC \\ gvs [])
                  >- (rpt $ qpat_x_assum ‘eval_to _ _ = _’ kall_tac
                      \\ rpt $ qpat_x_assum ‘∀i. eval_to _ _ = _’ kall_tac
                      \\ rename1 ‘n < LENGTH t’
                      \\ ‘MEM (SND (EL n t)) (MAP SND t)’
                        by (gvs [MEM_EL, SF CONJ_ss, EL_MAP]
                            \\ irule_at Any EQ_REFL \\ gvs [])
                      \\ gvs [subst_def, REVERSE_APPEND, ALOOKUP_APPEND]
                      \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘SND (EL n t)’]
                                     mp_tac $ iffRL ALOOKUP_NONE
                      \\ impl_tac \\ gvs []
                      >- (strip_tac \\ gvs [MAP_REVERSE, MAP_ZIP, ALL_DISTINCT_APPEND])
                      \\ disch_then kall_tac
                      \\ Cases_on ‘HD (FILTER FST (ZIP (bL3a, eL1)))’
                      \\ Cases_on ‘FILTER FST (ZIP (bL3a, eL1))’ \\ gvs [ALOOKUP_APPEND]
                      \\ rename1 ‘ZIP (MAP SND tl1, MAP SND tl2)’
                      \\ qspecl_then [‘ZIP (MAP SND tl1, MAP SND tl2)’]
                                     assume_tac alookup_distinct_reverse
                      \\ qspecl_then [‘ZIP (MAP SND tl1, MAP SND tl2)’, ‘n’]
                                     assume_tac ALOOKUP_ALL_DISTINCT_EL
                      \\ gvs [ALL_DISTINCT_APPEND, MAP_ZIP, EL_ZIP, EL_MAP]
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs [MEM_MAP]))
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst list1a) (MAP (subst list1b)
                                    (MAP2 (λb e. if b then Force e else e)
                                     (GENLIST (λn. n = i) (LENGTH valL1)) (MAP Var vL2)))
                = MAP2 (λb e. if b then Force e else e)
                       (GENLIST (λn. n = i) (LENGTH valL1)) (MAP Value valL1)’
              by (rpt $ qpat_x_assum ‘eval_to _ _ = _’ kall_tac
                  \\ rpt $ qpat_x_assum ‘∀i. eval_to _ _ = _’ kall_tac
                  \\ qpat_x_assum ‘eval_to _ _ ≠ _’ kall_tac
                  \\ gvs [Abbr ‘list1a’, Abbr ‘list1b’, GSYM ZIP_APPEND]
                  \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                  \\ gen_tac \\ strip_tac \\ rename1 ‘n < LENGTH _’
                  \\ qspecl_then [‘ZIP (vL2, valL1)’] assume_tac
                                 $ GEN_ALL alookup_distinct_reverse
                  \\ qspecl_then [‘ZIP (vL2, valL1)’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
                  \\ ‘MEM (EL n vL2) (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))
                                       ++ MAP SND (if b then [(T, h)] else []) ++ vL2)’
                    by gvs [EL_MEM]
                  \\ ‘∀l. MEM (EL n vL2) l ∧ l ≠ [] ⇒ MEM (EL n vL2) (TL l) ∨ EL n vL2 = HD l’
                    by (Cases \\ rw [] \\ gvs [])
                  \\ pop_assum $ dxrule_then assume_tac
                  \\ rename1 ‘subst (FILTER _ (FILTER _ abbrev_list))’
                  \\ Cases_on ‘n = i’
                  \\ gvs [subst_def, REVERSE_APPEND, ALOOKUP_APPEND, GSYM FILTER_REVERSE,
                          ALOOKUP_FILTER, ALL_DISTINCT_APPEND, EL_ZIP, MAP_ZIP])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst list1a) (MAP (subst list1b)
                                    (MAP Var (MAP SND (if b then [(T, h)] else []))))
                = if b then [Value v1] else []’
              by (IF_CASES_TAC \\ gvs []
                  \\ gvs [Abbr ‘list1a’, Abbr ‘list1b’, GSYM ZIP_APPEND, ALL_DISTINCT_APPEND]
                  \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                  \\ qspecl_then [‘REVERSE (ZIP (vL2, valL1))’, ‘h’] assume_tac ALOOKUP_NONE
                  \\ gvs [MAP_ZIP, MAP_REVERSE]
                  \\ Cases_on ‘MAP SND (FILTER FST (ZIP (bL3a, vL1a)))’
                  \\ gvs [subst_APPEND, subst_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘subst list1a (subst list1b (EL i (MAP Var vL2))) = Value (EL i valL1)’
              by (rpt $ qpat_x_assum ‘eval_to _ _ = _’ kall_tac
                  \\ rpt $ qpat_x_assum ‘∀i. eval_to _ _ = _’ kall_tac
                  \\ qpat_x_assum ‘eval_to _ _ ≠ _’ kall_tac
                  \\ gvs [Abbr ‘list1a’, Abbr ‘list1b’, GSYM ZIP_APPEND]
                  \\ gvs [EL_MAP]
                  \\ qspecl_then [‘ZIP (vL2, valL1)’] assume_tac
                                 $ GEN_ALL alookup_distinct_reverse
                  \\ qspecl_then [‘ZIP (vL2, valL1)’, ‘i’] assume_tac ALOOKUP_ALL_DISTINCT_EL
                  \\ ‘MEM (EL i vL2) (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))
                                       ++ MAP SND (if b then [(T, h)] else []) ++ vL2)’
                    by gvs [EL_MEM]
                  \\ ‘∀l. MEM (EL i vL2) l ∧ l ≠ [] ⇒ MEM (EL i vL2) (TL l) ∨ EL i vL2 = HD l’
                    by (Cases \\ rw [] \\ gvs [])
                  \\ pop_assum $ dxrule_then assume_tac
                  \\ rename1 ‘subst (FILTER _ (FILTER _ abbrev_list))’
                  \\ gvs [subst_def, REVERSE_APPEND, ALOOKUP_APPEND, GSYM FILTER_REVERSE,
                          ALOOKUP_FILTER, ALL_DISTINCT_APPEND, EL_ZIP, MAP_ZIP])
            \\ gvs [] \\ pop_assum kall_tac
            \\ Cases_on ‘eval_to (k - 2) (Force (Value (EL i valL1))) = INL Diverge’ \\ gvs []
            >- (dxrule_then (qspec_then ‘i’ assume_tac) eval_to_Apps_arg_Div
                \\ gvs [EL_MAP2, EL_MAP]
                \\ qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                \\ dxrule_then assume_tac eval_to_mono
                \\ gvs [subst_Apps, subst1_def, subst1_notin_frees, eval_to_Tick]
                \\ qpat_x_assum ‘∀j. _ ⇒ eval_to _ g = _’ kall_tac
                \\ qpat_x_assum ‘∀j. _ ⇒ eval_to _ y = _’ kall_tac
                \\ ‘MAP (subst [(h,w1)])
                    (MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                     (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Var h]))) =
                    MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                         (MAP2 (λb e. if b then Force e else e)
                          bL2 (MAP Value eL2 ++ [Value w1]))’
                  by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                      \\ rw [subst1_def, EL_APPEND_EQN, EL_MAP]
                      \\ gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ gvs [subst1_def])
                \\ gvs [] \\ pop_assum kall_tac
                \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                \\ gvs [subst1_notin_frees, freevars_subst]
                \\ qmatch_goalsub_abbrev_tac ‘_ (INL Diverge) (eval_to _ (Apps expr2 _))’
                \\ qspecl_then [‘MAP2 (λb e. if b then Force e else e)
                                 (GENLIST (λn. n = i) (LENGTH valL1))
                                 (MAP2 (λb e. if b then Force e else e)
                                  bL2 (MAP Value eL1 ++ [Value v1]))’,
                                ‘MAP2 (λb e. if b then Force e else e)
                                 (GENLIST (λn. n = i) (LENGTH valL1))
                                 (MAP2 (λb e. if b then Force e else e)
                                  bL2 (MAP Value eL2 ++ [Value w1]))’,
                                ‘i’, ‘k - 2’, ‘expr2’] mp_tac eval_to_Apps_arg_Div_combine_rel2
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
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def]
                    \\ rpt $ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN]
                    \\ pop_assum $ qspec_then ‘j’ assume_tac
                    \\ gvs [Abbr ‘argL1’, EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def]
                    \\ last_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, Abbr ‘argL1’, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [EL_MAP2, EL_MAP, EL_APPEND_EQN, LIST_REL_EL_EQN,
                            eval_to_Value, combine_rel_def])
                >- (last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gvs []
                    \\ pop_assum irule
                    \\ qpat_x_assum ‘LIST_REL _ _ _’ assume_tac
                    \\ gvs [LIST_REL_EL_EQN, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                    \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                    \\ first_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                    \\ gvs [EL_APPEND_EQN, EL_MAP2, EL_MAP, combine_rel_def, eval_to_Value]))
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
                \\ rename1 ‘combine_rel x1 x2’ \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                \\ gvs [subst_Apps, subst1_notin_frees, subst1_def, freevars_subst, eval_to_Tick]
                \\ ‘MAP (subst [(h,w1)])
                    (MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                     (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Var h]))) =
                    MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                        (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’
                  by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                      \\ rw [subst1_def, EL_APPEND_EQN, EL_MAP]
                      \\ gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ gvs [subst1_def])
                \\ gvs [] \\ pop_assum kall_tac
                \\ qmatch_goalsub_abbrev_tac ‘Apps _ argL1'’
                \\ ‘∀i. i < LENGTH argL1' ⇒ eval_to (k - 2) (EL i argL1') = INL Diverge
                                            ∨ ($= +++ v_rel) (INR (EL i valL2))
                                                             (eval_to (k - 2) (EL i argL1'))’
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
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                      ‘Force (Value (EL i2 eL2))’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                         ‘Force (Value w1)’] assume_tac
                          \\ gvs [LIST_REL_EL_EQN]
                          \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                          \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                                  eval_to_Value, eval_to_Tick]
                          \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                          \\ first_x_assum irule \\ rw [combine_rel_def])
                      >- (gvs [eval_to_Value, LIST_REL_EL_EQN, Abbr ‘argL1’, Abbr ‘argL2’]
                          \\ rpt $ last_x_assum $ qspec_then ‘i2’ assume_tac
                          \\ gvs [EL_MAP2, EL_APPEND_EQN, EL_MAP, eval_to_Value])
                      >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                          \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                          \\ gvs [eval_to_Value, LIST_REL_EL_EQN, Abbr ‘argL1’, Abbr ‘argL2’]
                          \\ rpt $ last_x_assum $ qspec_then ‘LENGTH eL2’ assume_tac
                          \\ gvs [EL_MAP2, EL_APPEND_EQN, EL_MAP, eval_to_Value]))
                \\ qmatch_goalsub_abbrev_tac ‘_ (INL Diverge) (eval_to _ (Apps expr2 _))’
                \\ qspecl_then [‘argL1'’, ‘valL2’, ‘expr2’, ‘k  - 2’]
                               mp_tac eval_to_Apps_Div_or_INR \\ gvs []
                \\ impl_tac >- gvs [Abbr ‘argL1'’, LIST_REL_EL_EQN, Abbr ‘argL2’]
                \\ rw [] \\ gvs []
                \\ rename1 ‘_ (INL Diverge) (eval_to _ (Apps _ (MAP Value valL2')))’
                \\ Cases_on ‘eval_to (k - 2) (Apps expr2 (MAP Value valL2')) = INL Diverge’
                \\ gs []
                \\ dxrule_then assume_tac eval_to_mono
                \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Apps expr1 (MAP Value valL2)’,
                                               ‘Apps expr2 (MAP Value valL2')’] mp_tac
                \\ gvs [] \\ impl_tac \\ gvs []
                \\ irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP, combine_rel_def]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’]
                \\ irule combine_rel_Apps
                \\ conj_tac
                >- (irule combine_rel_Apps \\ gvs [EVERY2_MAP, subst1_def, combine_rel_def]
                    \\ qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λx.x’]
                                   assume_tac $ GEN_ALL LIST_REL_FILTER
                    \\ gs [GSYM FST_THM] \\ pop_assum $ irule_at Any \\ gvs [MAP_ZIP]
                    \\ irule_at Any LIST_REL_mono
                    \\ qexists_tac ‘EL i (eL2 ++ [w1])’
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                    \\ gvs [LIST_REL_EL_EQN, EL_ZIP]
                    \\ conj_tac
                    >~[‘subst1 _ _ _ = Value _’]
                    >- (gvs [EL_APPEND_EQN, EL_MAP] \\ IF_CASES_TAC \\ gvs [subst1_def]
                        >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac
                            \\ gvs [Abbr ‘argL1’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value])
                        \\ rpt $ first_x_assum $ qspec_then ‘i’ assume_tac
                        \\ gvs [Abbr ‘argL1’, EL_MAP2, EL_MAP, EL_APPEND_EQN, eval_to_Value]
                        \\ gvs [NOT_LESS]
                        \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM
                        \\ gvs [subst_def, eval_to_Value])
                    \\ rpt $ qpat_x_assum ‘eval_to _ _ = _’ kall_tac
                    \\ rpt $ qpat_x_assum ‘∀j. _ ⇒ eval_to _ _ = _’ kall_tac
                    \\ gvs [Abbr ‘list1b’, FILTER_FILTER, LAMBDA_PROD]
                    \\ qmatch_goalsub_abbrev_tac ‘combine_rel (subst (FILTER _ list1) _)
                                                  (subst (FILTER _ list2) _)’
                    \\ ‘∀l (v : string). l ≠ [] ⇒ (¬MEM v (TL l) ∧ v ≠ HD l) = ¬MEM v l’
                      by (Cases \\ gvs [CONJ_COMM])
                    \\ gvs [] \\ pop_assum kall_tac
                    \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                    \\ qspecl_then [‘list2’, ‘x2’, ‘set vL1a ∪ {h}’] assume_tac subst_remove
                    \\ gvs [DISJOINT_ALT, EVERY_MEM]
                    \\ pop_assum kall_tac
                    \\ qspecl_then [‘list1’, ‘x1’,
                                    ‘set (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))) ∪
                                     set (MAP SND (if b then [(T, h)] else [])) ∪
                                     set vL2’] assume_tac subst_remove
                    \\ gvs [DISJOINT_ALT]
                    \\ pop_assum kall_tac
                    \\ irule combine_rel_subst \\ gvs [Abbr ‘list1’, Abbr ‘list2’]
                    \\ conj_tac
                    >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                    \\ gvs [MAP_SNOC, LIST_REL_SNOC]
                    \\ rpt $ conj_tac
                    >- (gvs [LIST_REL_EL_EQN, EL_MAP]
                        \\ gen_tac \\ rename1 ‘n < _ ⇒ _’ \\ strip_tac
                        \\ rename1 ‘MAP FST xs = MAP FST ys’
                        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1a ++ [h]’
                        \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3a ++ [b]’
                        \\ qexists_tac ‘i’
                        \\ gvs [FOLDL_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_MEM]
                        \\ gvs [EL_APPEND_EQN, EL_MAP] \\ rw []
                        \\ gvs [NOT_LESS] \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [])
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                    \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1a ++ [h]’
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3a ++ [b]’
                    \\ qexists_tac ‘i’
                    \\ gvs [FOLDL_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_MEM]
                    \\ gvs [EL_APPEND_EQN, EL_MAP] \\ rw []
                    \\ gvs [NOT_LESS] \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [])
                \\ IF_CASES_TAC \\ gvs [subst1_def, combine_rel_def])
            \\ Q.REFINE_EXISTS_TAC ‘j + j1 + j2’ \\ gvs []
            \\ ‘eval_to (j + k) y ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ ‘eval_to (j1 + k) g ≠ INL Diverge’ by gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ pop_assum kall_tac
            \\ qpat_x_assum ‘eval_to _ f = _’ kall_tac
            \\ rename1 ‘combine_rel x1 x2’ \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
            \\ gvs [subst_Apps, subst1_notin_frees, subst1_def, eval_to_Tick]
            \\ ‘MAP (subst [(h,w1)])
                (MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                 (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Var h])))
                = MAP2 (λb e. if b then Force e else e) (GENLIST (λn. n = i) (LENGTH valL1))
                       (MAP2 (λb e. if b then Force e else e) bL2 (MAP Value eL2 ++ [Value w1]))’
              by (irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                  \\ rw [subst1_def, EL_APPEND_EQN, EL_MAP]
                  \\ gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                  \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘∀l. MAP (subst [(h,w1)]) (MAP Value l) = MAP Value l’
              by (gen_tac \\ irule LIST_EQ \\ rw [subst_def, EL_MAP])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘MAP (subst [(h,w1)]) (MAP Var (MAP SND (if b then [(T, h)] else [])))
                = MAP Value (if b then [w1] else [])’
                by (IF_CASES_TAC \\ gvs [subst_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ ‘subst1 h w1 (EL i (MAP Value eL2 ++ [Var h])) = EL i (MAP Value (eL2 ++ [w1]))’
              by (gvs [EL_APPEND_EQN, EL_MAP] \\ rw [subst_def]
                  \\ gvs [NOT_LESS, Abbr ‘argL1’, LIST_REL_EL_EQN]
                  \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            \\ gvs [] \\ pop_assum kall_tac
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ (Apps expr2 argL1'))’
            \\ ‘∀i. i < LENGTH argL1' ⇒
                    ∃j. ($= +++ v_rel) (INR (EL i valL2)) (eval_to (j + k - 2) (EL i argL1'))’
              by (rw [] \\ rename1 ‘i2 < _’
                  \\ gvs [Abbr ‘argL1'’, EL_MAP2, EL_MAP, EL_APPEND_EQN] \\ rw []
                  >- (last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value (EL i eL1))’,
                                                  ‘Force (Value (EL i eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                              eval_to_Value]
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                              eval_to_Value]
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value (EL i2 eL1))’,
                                                  ‘Force (Value (EL i2 eL2))’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘i2’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                              eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gvs []
                      \\ first_x_assum irule \\ rw [combine_rel_def])
                  >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                      \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM
                      \\ last_x_assum $ qspecl_then [‘k - 1’, ‘Force (Value v1)’,
                                                     ‘Force (Value w1)’] assume_tac
                      \\ gvs [LIST_REL_EL_EQN]
                      \\ rpt $ first_x_assum $ qspecl_then [‘LENGTH eL1’] assume_tac
                      \\ gvs [Abbr ‘argL1’, Abbr ‘argL2’, EL_MAP2, EL_MAP, EL_APPEND_EQN,
                              eval_to_Value]
                      \\ Q.REFINE_EXISTS_TAC ‘j + 1’ \\ gs []
                      \\ first_x_assum irule \\ rw [combine_rel_def])
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
            \\ disch_then $ qx_choose_then ‘valL2'’ $ qx_choose_then ‘j2’ assume_tac
            \\ Q.REFINE_EXISTS_TAC ‘j2 + j3’
            \\ qspecl_then [‘argL1'’, ‘valL2'’, ‘expr2’, ‘j2 + k - 2’]
                           mp_tac eval_to_Apps_LIST_INR
            \\ impl_tac \\ gvs []
            >- (gvs [LIST_REL_EL_EQN] \\ rw []
                \\ rename1 ‘j + _ - 2’
                \\ first_x_assum $ dxrule_then $ qspec_then ‘j’ assume_tac \\ gvs [])
            \\ disch_then kall_tac
            \\ last_x_assum $ qspecl_then [‘k - 2’, ‘Apps expr1 (MAP Value valL2)’,
                                           ‘Apps expr2 (MAP Value valL2')’] mp_tac
            \\ gvs [] \\ impl_tac
            >- (irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP, combine_rel_def]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’, subst1_notin_frees, freevars_subst]
                \\ irule combine_rel_Apps
                \\ conj_tac
                >- (irule combine_rel_Apps \\ gvs [EVERY2_MAP, subst1_def, combine_rel_def]
                    \\ qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λx.x’]
                                   assume_tac $ GEN_ALL LIST_REL_FILTER
                    \\ gs [GSYM FST_THM] \\ pop_assum $ irule_at Any \\ gvs [MAP_ZIP]
                    \\ irule_at Any LIST_REL_mono
                    \\ qexists_tac ‘EL i (eL2 ++ [w1])’
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                    \\ gvs [LIST_REL_EL_EQN, EL_ZIP]
                    \\ conj_tac
                    >~[‘EL _ _ = Value _ ∧ v_rel _ _’]
                    >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac
                        \\ gvs [EL_APPEND_EQN, EL_MAP, Abbr ‘argL1’]
                        \\ IF_CASES_TAC
                        \\ gvs [EL_MAP2, EL_MAP, eval_to_Value, EL_APPEND_EQN, NOT_LESS]
                        \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [eval_to_Value])
                    \\ rpt $ qpat_x_assum ‘eval_to _ _ = _’ kall_tac
                    \\ rpt $ qpat_x_assum ‘∀j. _ ⇒ eval_to _ _ = _’ kall_tac
                    \\ gvs [Abbr ‘list1b’, FILTER_FILTER, LAMBDA_PROD]
                    \\ qmatch_goalsub_abbrev_tac ‘combine_rel (subst (FILTER _ list1) _)
                                                  (subst (FILTER _ list2) _)’
                    \\ ‘∀l (v : string). l ≠ [] ⇒ (¬MEM v (TL l) ∧ v ≠ HD l) = ¬MEM v l’
                      by (Cases \\ gvs [CONJ_COMM])
                    \\ gvs [] \\ pop_assum kall_tac
                    \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                    \\ qspecl_then [‘list2’, ‘x2’, ‘set vL1a ∪ {h}’] assume_tac subst_remove
                    \\ gvs [DISJOINT_ALT, EVERY_MEM]
                    \\ pop_assum kall_tac
                    \\ qspecl_then [‘list1’, ‘x1’,
                                    ‘set (MAP SND (FILTER FST (ZIP (bL3a, vL1a)))) ∪
                                     set (MAP SND (if b then [(T, h)] else [])) ∪
                                     set vL2’] assume_tac subst_remove
                    \\ gvs [DISJOINT_ALT]
                    \\ pop_assum kall_tac
                    \\ irule combine_rel_subst \\ gvs [Abbr ‘list1’, Abbr ‘list2’]
                    \\ conj_tac
                    >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                    \\ gvs [MAP_SNOC, LIST_REL_SNOC]
                    \\ rpt $ conj_tac
                    >- (gvs [LIST_REL_EL_EQN, EL_MAP]
                        \\ gen_tac \\ rename1 ‘n < _ ⇒ _’ \\ strip_tac
                        \\ rename1 ‘MAP FST xs = MAP FST ys’
                        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1a ++ [h]’
                        \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3a ++ [b]’
                        \\ qexists_tac ‘i’
                        \\ gvs [FOLDL_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_MEM]
                        \\ gvs [EL_APPEND_EQN, EL_MAP] \\ rw [] \\ gvs [NOT_LESS]
                        \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [Abbr ‘argL1’])
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                    \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1a ++ [h]’
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3a ++ [b]’
                    \\ qexists_tac ‘i’
                    \\ gvs [FOLDL_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_MEM]
                    \\ gvs [EL_APPEND_EQN, EL_MAP] \\ rw [] \\ gvs [NOT_LESS]
                    \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [Abbr ‘argL1’])
                \\ IF_CASES_TAC \\ gvs [subst1_def, combine_rel_def])
            \\ disch_then $ qx_choose_then ‘j3’ assume_tac \\ qexists_tac ‘j3’
            \\ Cases_on ‘eval_to (j3 + k − 2) (Apps expr2 (MAP Value valL2')) = INL Diverge’
            \\ gs []
            >- (Cases_on ‘eval_to (k - 2) (Apps expr1 (MAP Value valL2))’ \\ gvs [])
            \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
        \\ qexists_tac ‘j + j1’
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
        \\ gvs [subst_Lams, subst_Apps, eval_to_Lams, subst_def]
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs [ALL_DISTINCT_APPEND]
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ gvs [subst1_notin_frees, freevars_subst]
        \\ qpat_assum ‘combine_rel x1 x2’ $ irule_at Any
        \\ qexists_tac ‘vL2’ \\ qexists_tac ‘i’ \\ gvs []
        \\ rename1 ‘MAP FST xs = MAP FST ys’ \\ qexists_tac ‘ys’ \\ gvs []
        \\ qexists_tac ‘eL2 ++ [w1]’ \\ qexists_tac ‘eL1 ++ [v1]’ \\ gvs []
        \\ qexists_tac ‘bL3b’ \\ qexists_tac ‘bL3a ++ [b]’ \\ qexists_tac ‘bL2’ \\ gvs []
        \\ gvs [ALL_DISTINCT_APPEND, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
        \\ gvs [EVERY_MEM, freevars_subst] \\ rw [] \\ gvs []
        >- (rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                 \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN]
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                 \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN]
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- gvs [NOT_LESS]
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_APPEND, MAP_APPEND]
            \\ rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ gvs [subst1_def]
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN] \\ gvs []
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_APPEND]
            \\ rpt (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst_def, EL_APPEND_EQN] \\ gvs []
            >- (strip_tac \\ gvs [MEM_MAP]
                \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER, MEM_EL, EL_ZIP])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (gvs [GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC, NOT_LESS]
                \\ dxrule_then (dxrule_then assume_tac) LESS_EQUAL_ANTISYM \\ gvs [subst1_def])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (irule EQ_TRANS \\ irule_at (Pos hd) subst1_notin_frees
            \\ gvs [GSYM CONJ_ASSOC, freevars_subst]
            \\ first_x_assum $ qspec_then ‘h’ assume_tac \\ gvs []
            \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars \\ gvs []
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (irule EQ_TRANS \\ irule_at (Pos hd) subst1_notin_frees
            \\ gvs [GSYM CONJ_ASSOC, freevars_subst]
            \\ first_x_assum $ qspec_then ‘h’ assume_tac \\ gvs []
            \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars \\ gvs []
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (gvs [EL_APPEND_EQN, EL_MAP]
            \\ IF_CASES_TAC
            \\ gvs [subst1_def, NOT_LESS, GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
            \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM
            \\ IF_CASES_TAC \\ gvs [NOT_LESS_EQUAL, subst1_def]
            \\ Cases_on ‘i’ \\ gvs [EL_MAP, subst1_def]
            \\ once_rewrite_tac [CONS_APPEND]
            \\ gvs [EL_APPEND_EQN, GSYM ADD1]
            \\ gvs [LIST_REL_EL_EQN, subst1_def, EL_MAP]
            \\ IF_CASES_TAC \\ gvs [EL_MEM])
        >- (qpat_x_assum ‘ALL_DISTINCT vL1b’ mp_tac
            \\ qpat_x_assum ‘LENGTH vL1b = LENGTH bL3b’ mp_tac
            \\ rpt $ pop_assum kall_tac
            \\ qid_spec_tac ‘bL3b’
            \\ Induct_on ‘vL1b’ \\ gvs []
            \\ gen_tac \\ Cases \\ gvs []
            \\ rw [] \\ gvs [MEM_MAP, MEM_FILTER, FORALL_PROD]
            \\ strip_tac \\ first_x_assum irule
            \\ gvs [MEM_EL, EL_ZIP]
            \\ irule_at Any EQ_REFL \\ gvs [])
        >- (qpat_x_assum ‘LIST_REL (λb3 b2. b3 ⇒ b2) _ _’ mp_tac
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (gvs [MEM_MAP, MEM_FILTER]
            \\ rename1 ‘MEM y2 (ZIP (bL3b, vL1b))’
            \\ ‘MEM (SND y2) vL1b’ suffices_by gvs []
            \\ gvs [MEM_EL, EL_ZIP]
            \\ irule_at Any EQ_REFL \\ gvs []))

    (* default recclosure *)
    >- (print_tac "Recclosure 1/3"
        \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
        \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
        \\ gvs [OPTREL_def]
        \\ rename1 ‘combine_rel x0 _’ \\ Cases_on ‘x0’ \\ gvs [combine_rel_def]
        \\ IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ rename1 ‘subst (_ ++ [(s2, v1)]) _’
        \\ rename1 ‘combine_rel body body2’
        \\ last_x_assum $ qspecl_then [‘k - 1’, ‘subst (MAP (λ(g,x). (g, Recclosure xs g)) xs
                                                        ++ [(s2, v1)]) body’,
                     ‘subst (MAP (λ(g,x).(g, Recclosure ys g)) ys ++ [(s2, w1)]) body2’] mp_tac
        \\ gs [] \\ impl_tac
        >- (gs [] \\ irule combine_rel_subst \\ gvs []
            \\ gvs [LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o, combinTheory.o_DEF,
                    LAMBDA_PROD, GSYM FST_THM]
            \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
            \\ rename1 ‘n < _’ \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
            \\ gvs [EL_MAP]
            \\ irule v_rel_Recclosure \\ gvs [LIST_REL_EL_EQN, EL_MAP])
        \\ disch_then $ qx_choose_then ‘j2’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x). (g, Recclosure xs g)) xs
                                             ++ [(s2,v1)]) body)
                     = INL Diverge’
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k y’
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k g’ \\ gvs []
            \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x). (g, Recclosure ys g)) ys
                                                 ++ [(s2,w1)]) body2)
                         = INL Diverge’ \\ gvs []
            \\ dxrule_then (qspec_then ‘j2 + k - 1’ assume_tac) eval_to_mono
            \\ gvs [])
        \\ qexists_tac ‘j + j1 + j2’
        \\ first_x_assum $ qspec_then ‘j + j2’ assume_tac
        \\ first_x_assum $ qspec_then ‘j1 + j2’ assume_tac
        \\ gvs []
        \\ ‘eval_to (j2 + k - 1) (subst (MAP (λ(g,x). (g, Recclosure ys g)) ys
                                         ++ [(s2,w1)]) body2)
                     ≠ INL Diverge’
          by (strip_tac
              \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs
                                                   ++ [(s2,v1)]) body)’
              \\ gvs [])
        \\ dxrule_then (qspec_then ‘j + j1 + j2 + k - 1’ assume_tac) eval_to_mono
        \\ gvs [])

    (* Recclosure with inlining 1 *)
    >- (print_tac "Recclosure 2/3"
        \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
        \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ qpat_x_assum ‘MAP FST _ = MAP FST _’ mp_tac
              \\ qpat_x_assum ‘LIST_REL combine_rel _ _’ mp_tac
              \\ rpt $ pop_assum kall_tac
              \\ rw []
              \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
        \\ IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ gvs []
            \\ pop_assum mp_tac
            \\ pop_assum mp_tac
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs []
            \\ Cases_on ‘vL2 = []’ \\ gvs []
            \\ gvs [REVERSE_APPEND, REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs [Lams_split]
            \\ IF_CASES_TAC \\ gvs [Lams_split]
            \\ strip_tac \\ strip_tac
            \\ gvs [OPTREL_def]
            \\ rename1 ‘combine_rel x0 _’ \\ Cases_on ‘x0’ \\ gvs [combine_rel_def])
        \\ qpat_x_assum ‘_ = INR (_, _, _)’ mp_tac
        \\ Cases_on ‘vL2 = []’ \\ gvs []
        \\ rw [REVERSE_APPEND] \\ gvs [Lams_split]
        >- (gvs [subst_Lams]
            \\ Cases_on ‘MAP SND (FILTER FST (ZIP (bL3, vL1)))’ \\ gvs [Lams_split]
            >- (Cases_on ‘vL2’ \\ gvs []
                \\ rename1 ‘eval_to _ (Lams vL2 _)’ \\ Cases_on ‘vL2 = []’ \\ gvs []
                >- (gvs [GSYM LAMBDA_PROD, FILTER_T, subst_APPEND, subst_def,
                         REVERSE_APPEND, subst1_notin_frees]
                    \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ expr1) _’
                    \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
                    \\ qmatch_goalsub_abbrev_tac ‘eval_to _ _ = INR (Recclosure list2 _)’
                    \\ strip_tac
                    \\ last_x_assum $ qspecl_then [‘k - 1’, ‘expr1’,
                                                   ‘App (subst_funs list2 x2)
                                                    (Force (Value w1))’] mp_tac
                    \\ gvs [] \\ impl_tac
                    >- (gvs [Abbr ‘expr1’, Abbr ‘list2’, combine_rel_def, subst_funs_def,
                             SNOC_APPEND, subst_APPEND]
                        \\ irule combine_rel_subst \\ rw []
                        >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                        >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                            \\ irule combine_rel_subst \\ gvs []
                            \\ irule_at Any combine_rel_subst \\ gvs [combine_rel_subst]
                            \\ conj_tac \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                            \\ Cases_on ‘vL1’ \\ gvs []
                            \\ simp [LENGTH_EQ_NUM_compute,PULL_EXISTS]
                            \\ Cases_on ‘bL2’ \\ fs [])
                        >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                            \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                            \\ rename1 ‘n < _’
                            \\ rename1 ‘MAP FST xs = MAP FST ys’
                            \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                            \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                            \\ Cases_on ‘vL1’ \\ gvs []
                            \\ simp [LENGTH_EQ_NUM_compute,PULL_EXISTS]
                            \\ Cases_on ‘bL2’ \\ fs []
                            \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []))
                    \\ disch_then $ qx_choose_then ‘j2’ assume_tac
                    \\ Cases_on ‘eval_to (k - 1) expr1 = INL Diverge’ \\ gvs []
                    >- (qexists_tac ‘0’
                        \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                        \\ dxrule_then assume_tac eval_to_mono
                        \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                        \\ dxrule_then assume_tac eval_to_mono
                        \\ gvs [REVERSE_SNOC, subst_def, Abbr ‘list2’]
                        \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                        \\ gvs [subst_funs_def, subst1_notin_frees]
                        \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’
                        \\ gvs []
                        \\ Cases_on ‘eval_to (k - 1) expr2 = INL Diverge’ \\ gvs []
                        \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
                    \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
                    \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1+ j2’ assume_tac
                    \\ qexists_tac ‘j + j1 + j2’ \\ gvs [REVERSE_SNOC, subst_def, Abbr ‘list2’]
                    \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                    \\ gvs [subst_funs_def, subst1_notin_frees]
                    \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’ \\ gvs []
                    \\ ‘eval_to (j2 + k - 1) expr2 ≠ INL Diverge’
                      by (strip_tac \\ Cases_on ‘eval_to (k - 1) expr1’ \\ gvs [])
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
                \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
                \\ qexists_tac ‘j + j1’
                \\ gvs [Lams_split, eval_to_def, REVERSE_SNOC, subst_def, subst_Lams]
                \\ irule v_rel_Closure \\ irule combine_rel_Lams \\ gvs []
                \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                \\ ‘∀p. (¬MEM p (TL vL2) ∧ p ≠ (HD vL2)) = ¬MEM p vL2’
                  by (Cases_on ‘vL2’ \\ gvs []
                      \\ gen_tac \\ metis_tac [CONJ_COMM])
                \\ gvs [SNOC_APPEND, subst_APPEND]
                \\ irule combine_rel_subst \\ rw []
                >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, MAP_FST_FILTER]
                >- (irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP2, EL_MAP]
                    \\ rw [] \\ rename1 ‘n < SUC (LENGTH _)’
                    \\ gvs [combine_rel_def]
                    \\ Cases_on ‘n’ \\ gvs [EL_MAP, combine_rel_def])
                >- (qabbrev_tac ‘P = λv. ¬MEM v vL2’ \\ gvs [EVERY2_MAP]
                    \\ irule LIST_REL_FILTER \\ gvs []
                    \\ conj_tac >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                    \\ irule LIST_REL_mono
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’
                    \\ rw []
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_APPEND_EQN]
                    \\ rw []
                    >- (pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                        \\ rename1 ‘n < LENGTH _’
                        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’
                        \\ qexists_tac ‘vL1’ \\ qexists_tac ‘h::vL2’
                        \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’  \\ qexists_tac ‘i’
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, Lams_split])
                    >- gvs [NOT_LESS]
                    >- (gvs [NOT_LESS, GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                        \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs []
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’
                        \\ qexists_tac ‘vL1’ \\ qexists_tac ‘h::vL2’
                        \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’  \\ qexists_tac ‘i’
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, Lams_split])
                    >- (gvs [NOT_LESS, GSYM ADD1, Once $ GSYM LESS_EQ_IFF_LESS_SUC]
                        \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM
                        \\ gvs [LESS_EQ_IFF_LESS_SUC]
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’
                        \\ qexists_tac ‘vL1’ \\ qexists_tac ‘h::vL2’
                        \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’  \\ qexists_tac ‘i’
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, Lams_split])))
            \\ gvs [eval_to_def]
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
            \\ qexists_tac ‘j + j1’ \\ gvs [REVERSE_SNOC, subst_def]
            \\ gvs [eval_to_def, subst_Lams]
            \\ irule v_rel_Closure
            \\ irule combine_rel_Lams
            \\ irule combine_rel_subst \\ rw []
            >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, MAP_FST_FILTER]
                \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                \\ AP_THM_TAC \\ AP_TERM_TAC
                \\ rename1 ‘TL (t ++ vL2)’
                \\ Cases_on ‘t’ \\ gvs [GSYM CONJ_ASSOC]
                >- (Cases_on ‘vL2’ \\ gvs [] \\ metis_tac [CONJ_COMM])
                \\ metis_tac [CONJ_COMM])
            >- (irule combine_rel_Apps \\ gvs [combine_rel_def]
                \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_MAP2, EL_APPEND_EQN]
                \\ rw [combine_rel_def])
            >- (gvs [FILTER_FILTER, LAMBDA_PROD, EVERY2_MAP]
                \\ rename1 ‘TL (t ++ vL2)’
                \\ ‘∀p. ¬MEM p (TL (t ++ vL2)) ∧ p ≠ HD (t ++ vL2) ⇔ ¬MEM p t ∧ ¬MEM p vL2’
                  by (gen_tac \\ Cases_on ‘t’ \\ gvs [GSYM CONJ_ASSOC]
                      >- (Cases_on ‘vL2’ \\ gvs [] \\ metis_tac [CONJ_COMM])
                      \\ metis_tac [CONJ_COMM])
                \\ gvs [] \\ pop_assum kall_tac
                \\ qabbrev_tac ‘P = λn. ¬MEM n t ∧ ¬MEM n vL2’ \\ gvs []
                \\ irule LIST_REL_FILTER
                \\ conj_tac
                >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_APPEND,
                        SNOC_APPEND, GSYM FST_THM]
                \\ irule LIST_REL_mono \\ gvs [MAP_SNOC, LIST_REL_SNOC]
                \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                \\ rw [] \\ gvs []
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gs [] \\ pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                    \\ rename1 ‘n < _’
                    \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                    \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘vL1’
                    \\ qexists_tac ‘i’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘bL2’
                    \\ gvs [Lams_split, LIST_REL_EL_EQN, EL_MAP]
                    \\ rw [] \\ last_x_assum $ drule_then assume_tac
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [])
                >- (gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                    \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘vL1’
                    \\ qexists_tac ‘i’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘bL2’
                    \\ gvs [Lams_split, LIST_REL_EL_EQN, EL_MAP]
                    \\ rw [] \\ last_x_assum $ drule_then assume_tac
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [])
                >- (gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                    \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘vL1’
                    \\ qexists_tac ‘i’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘bL2’
                    \\ gvs [Lams_split, LIST_REL_EL_EQN, EL_MAP]
                    \\ rw [] \\ last_x_assum $ drule_then assume_tac
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [])))
        >- (gvs [subst_Lams]
            \\ Cases_on ‘vL1’ \\ gvs []
            \\ rename1 ‘eval_to _ (Lams vL1 _)’
            \\ Cases_on ‘vL1 = []’ \\ gvs []
            >- (gvs [GSYM LAMBDA_PROD, FILTER_T]
                \\ gvs [subst_Apps, subst_def, REVERSE_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘Apps (Value (Recclosure list1 _)) _’
                \\ Cases_on ‘bL3’ \\ gvs []
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
                \\ qmatch_goalsub_abbrev_tac ‘eval_to _ g = INR (Recclosure list2 _)’
                \\ strip_tac
                \\ Cases_on ‘k = 1’ \\ gvs []
                >- (qexists_tac ‘0’ \\ gvs []
                    \\ Cases_on ‘eval_to 1 y = INL Diverge’ \\ gvs []
                    >- (rw [subst_def] \\ once_rewrite_tac [eval_to_def] \\ gvs []
                        \\ gvs [REVERSE_APPEND, eval_to_Value, Abbr ‘list1’,
                                dest_anyClosure_def])
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ Cases_on ‘eval_to 1 g = INL Diverge’ \\ gvs []
                    >- (rw [subst_def] \\ once_rewrite_tac [eval_to_def] \\ gvs []
                        \\ gvs [REVERSE_APPEND, eval_to_Value, Abbr ‘list1’,
                                 dest_anyClosure_def])
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ gvs [Abbr ‘list2’, REVERSE_SNOC, subst_def]
                    \\ rw [subst_def] \\ once_rewrite_tac [eval_to_def] \\ gvs []
                    \\ gvs [REVERSE_APPEND, eval_to_Value, Abbr ‘list1’, dest_anyClosure_def])
                \\ simp [subst_APPEND, subst_def]
                \\ rename1 ‘App (Value (Recclosure _ _)) (Value v1)’
                \\ qspecl_then [‘[Value v1]’, ‘k-1’, ‘list1’, ‘v1'’] mp_tac
                               eval_to_Apps_Recclosure_Lams_not_0
                \\ simp []
                \\ gvs [Abbr ‘list1’, REVERSE_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘App (Tick (subst_funs list1 _)) _’
                \\ disch_then kall_tac
                \\ gvs [subst_funs_def, subst_def, subst_Lams]
(*                \\ Cases_on ‘i’ \\ gvs []*)
                \\ Cases_on ‘vL2’
                \\ gvs [GSYM LAMBDA_PROD, FILTER_T,
                        subst_def, REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                \\ gvs [eval_to_def, subst_funs_def, subst_empty, dest_anyClosure_def]
                \\ gvs [subst1_def] \\ once_rewrite_tac [eval_to_def]
                \\ gvs [Abbr ‘list1’, REVERSE_APPEND, subst_def]
                \\ ‘eval_to (k - 2) (Force (Value v1)) ≠ INL Type_error’
                  by (strip_tac \\ qpat_x_assum ‘_ ≠ INL Type_error’ irule
                      \\ once_rewrite_tac [eval_to_def] \\ gvs [])
                \\ last_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’, ‘Force (Value w1)’]
                              mp_tac
                \\ ‘k - 2 < k’ by gvs []
                \\ disch_then $ dxrule_then $ dxrule_then mp_tac
                \\ impl_tac >- gvs [combine_rel_def]
                \\ disch_then $ qx_choose_then ‘j2’ assume_tac
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1)) = INL Diverge’ \\ gvs []
                >- (qexists_tac ‘0’
                    \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ gvs [Abbr ‘list2’, REVERSE_SNOC, subst_def, REVERSE_APPEND,
                            GSYM LAMBDA_PROD, FILTER_T]
                    \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def, subst_empty]
                    \\ once_rewrite_tac [eval_to_def] \\ gvs []
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs [])
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1))’ \\ gvs []
                >- (rename1 ‘INL x'’ \\ Cases_on ‘x'’ \\ gvs []
                    \\ qexists_tac ‘j + j1 + j2’
                    \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
                    \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1+ j2’ assume_tac
                    \\ gvs [REVERSE_SNOC, Abbr ‘list2’, subst_def, eval_to_Tick,
                            GSYM LAMBDA_PROD, FILTER_T, REVERSE_APPEND]
                    \\ once_rewrite_tac [eval_to_def]
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs [])
                \\ qmatch_goalsub_abbrev_tac ‘eval_to (_ - 2) expr1’
                \\ rename1 ‘eval_to (k - 2) (Force (Value v1)) = INR val1’
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs []
                \\ rename1 ‘v_rel val1 val1'’
                \\ qabbrev_tac ‘expr2 = subst (MAP (λ(g,x). (g,
                    Recclosure (SNOC (v1',Lam h (App x2 (Force (Var h))))
                                (SNOC
                                 (s,Lam h (Tick (App x2 (Force (Var h)))))
                                 ys)) g))
                              (SNOC (v1',Lam h (App x2 (Force (Var h))))
                               (SNOC (s,Lam h (Tick (App x2 (Force (Var h))))) ys)) ++
                                               [(h,w1)]) x2’
                \\ last_x_assum $ qspecl_then [‘k - 2’, ‘App expr1 (Value val1)’,
                                               ‘App expr2 (Value val1')’] mp_tac
                \\ gvs [] \\ impl_tac
                >- (conj_tac
                    >- (once_rewrite_tac [eval_to_def]
                        \\ strip_tac \\ last_x_assum irule
                        \\ once_rewrite_tac [eval_to_def]
                        \\ gvs [eval_to_Value]
                        \\ ‘∀l h2. subst1 h2 v1 (subst (FILTER (λ(n,x). n ≠ h2) l) x1)
                                   = subst l (subst1 h2 v1 x1)’
                          by (gen_tac \\ gen_tac \\ irule EQ_TRANS
                              \\ irule_at (Pos hd) subst_commutes
                              \\ gvs [MAP_FST_FILTER, MEM_FILTER]
                              \\ irule EQ_TRANS \\ irule_at (Pos last) subst_remove
                              \\ Q.REFINE_EXISTS_TAC ‘{_}’ \\ gvs []
                              \\ irule_at Any EQ_REFL \\ gvs [freevars_subst])
                        \\ gvs [subst_APPEND])
                    \\ gvs [combine_rel_def]
                    \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’]
                    \\ ‘∀l h2. subst1 h2 v1 (subst (FILTER (λ(n,x). n ≠ h2) l) x1)
                               = subst l (subst1 h2 v1 x1)’
                      by (gen_tac \\ gen_tac \\ irule EQ_TRANS
                          \\ irule_at (Pos hd) subst_commutes
                          \\ gvs [MAP_FST_FILTER, MEM_FILTER]
                          \\ irule EQ_TRANS \\ irule_at (Pos last) subst_remove
                          \\ Q.REFINE_EXISTS_TAC ‘{_}’ \\ gvs []
                          \\ irule_at Any EQ_REFL \\ gvs [freevars_subst])
                    \\ gvs [subst_APPEND]
                    \\ gvs [Abbr ‘list2’, SNOC_APPEND, subst_APPEND]
                    \\ irule combine_rel_subst \\ rw []
                    >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                    >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                        \\ irule combine_rel_subst \\ irule_at Any combine_rel_subst
                        \\ last_x_assum $ qspec_then ‘0’ assume_tac \\ gvs [combine_rel_subst]
                        \\ conj_tac \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                        \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                        \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ gvs []
                        \\ qpat_assum ‘_ ∉ freevars x1’ $ irule_at Any
                        \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ gvs []
                        \\ qexists_tac ‘[F]’ \\ gvs []
                        \\ qexists_tac ‘[F]’ \\ gvs [])
                    >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                        \\ rename1 ‘n < _’
                        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                        \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                        \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ gvs []
                        \\ qpat_assum ‘_ ∉ freevars x1’ $ irule_at Any
                        \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ simp []
                        \\ qexists_tac ‘[F]’ \\ simp []
                        \\ qexists_tac ‘[F]’ \\ simp [LIST_REL_EL_EQN, EL_MAP]))
                \\ disch_then $ qx_choose_then ‘j3’ assume_tac
                \\ Cases_on ‘eval_to (k - 2) (App expr1 (Value val1)) = INL Diverge’ \\ gvs []
                >- (Cases_on ‘eval_to (k - 2) (App expr2 (Value val1')) = INL Diverge’
                    >~[‘eval_to _ _ ≠ INL Diverge’]
                    >- (drule_then assume_tac eval_to_mono \\ gvs []
                        \\ Cases_on ‘eval_to (k - 2) (App expr2 (Value val1'))’ \\ gvs [])
                    \\ pop_assum mp_tac \\ pop_assum mp_tac \\ pop_assum kall_tac
                    \\ once_rewrite_tac [eval_to_def] \\ strip_tac \\ strip_tac
                    \\ gvs [eval_to_Value]
                    \\ qexists_tac ‘0’
                    \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ gvs [Abbr ‘list2’, REVERSE_SNOC, subst_def, REVERSE_APPEND,
                            GSYM LAMBDA_PROD, FILTER_T]
                    \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def, subst_empty]
                    \\ once_rewrite_tac [eval_to_def] \\ gvs []
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs [subst_APPEND])
                \\ ‘eval_to (j3 + k - 2) (App expr2 (Value val1')) ≠ INL Diverge’
                  by (strip_tac \\ Cases_on ‘eval_to (k - 2) (App expr1 (Value val1))’ \\ gvs [])
                \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                \\ pop_assum mp_tac \\ pop_assum kall_tac \\ pop_assum mp_tac
                \\ once_rewrite_tac [eval_to_def] \\ strip_tac
                \\ disch_then $ qspec_then ‘j + j1 + j2 + j3 + k - 1’ assume_tac
                \\ qexists_tac ‘j + j1 + j2 + j3 + 1’
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2 + j3 + 1’ assume_tac
                \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1+ j2 + j3 + 1’ assume_tac
                \\ gvs [REVERSE_SNOC, Abbr ‘list2’, subst_def, eval_to_Tick,
                        GSYM LAMBDA_PROD, FILTER_T, REVERSE_APPEND, eval_to_Value]
                \\ once_rewrite_tac [eval_to_def]
                \\ ‘eval_to (j2 + k - 2) (Force (Value w1)) ≠ INL Diverge’ by gvs []
                \\ dxrule_then assume_tac eval_to_mono \\ gvs [subst_APPEND])
            \\ qexists_tac ‘j + j1’
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
            \\ gvs []
            \\ pop_assum kall_tac \\ pop_assum kall_tac
            \\ gvs [REVERSE_SNOC]
            \\ gvs [subst_Lams, Lams_split, eval_to_def]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
            \\ irule_at (Pos hd) EQ_REFL \\ gvs []
            \\ qpat_assum ‘combine_rel x1 x2’ $ irule_at Any
            \\ qexists_tac ‘vL2’ \\ qexists_tac ‘[h]’ \\ gvs []
            \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ gvs [subst_def]
            \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ gvs [ALL_DISTINCT_APPEND]
            \\ qexists_tac ‘s’ \\ qexists_tac ‘v1'’ \\ qexists_tac ‘i’
            \\ qexists_tac ‘ys’ \\ qexists_tac ‘xs’ \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
            \\ qexists_tac ‘[w1]’ \\ qexists_tac ‘[v1]’ \\ qexists_tac ‘TL bL3’
            \\ qexists_tac ‘[HD bL3]’ \\ qexists_tac ‘bL2’ \\ gvs []
            \\ Cases_on ‘bL3’ \\ gvs [PULL_EXISTS]
            \\ rpt $ conj_tac
            >- (gvs [subst_Apps]
                \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any
                \\ conj_tac
                >- (qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                    \\ gvs [subst_APPEND, FILTER_APPEND, subst1_notin_frees]
                    \\ irule EQ_TRANS
                    \\ irule_at (Pos hd) $ GSYM subst_remove
                    \\ Q.REFINE_EXISTS_TAC ‘{_}’ \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                    \\ first_assum $ irule_at $ Pos hd
                    \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
                    \\ rw [] \\ once_rewrite_tac [CONS_APPEND] \\ gvs [Lams_split])
                \\ gvs [MAP_APPEND]
                \\ ‘∀a b c d. a = b ∧ c = d ⇒ a ++ c = b ++ d : exp list’ by gvs []
                \\ pop_assum $ irule_at Any \\ conj_tac
                >- (irule LIST_EQ \\ gvs [EL_MAP]
                    \\ IF_CASES_TAC \\ gvs [] \\ rpt $ strip_tac
                    >- (rename1 ‘EL n (_::_)’
                        \\ Cases_on ‘n’
                        \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                        \\ IF_CASES_TAC \\ gvs [EL_MAP]
                        >- (gvs[MEM_MAP]
                            \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                            \\ gvs [EL_MEM])
                        \\ IF_CASES_TAC \\ gvs []
                        >- (dxrule_then assume_tac EL_MEM
                            \\ gvs [MEM_FILTER]
                            \\ dxrule_then assume_tac MEM_SND
                            \\ gvs [MAP_ZIP])
                        \\ drule_then assume_tac EL_MEM
                        \\ gvs [MEM_FILTER]
                        \\ dxrule_then assume_tac MEM_SND
                        \\ gvs [MAP_ZIP]
                        \\ IF_CASES_TAC \\ gvs [ALOOKUP_FILTER]
                        \\ IF_CASES_TAC \\ gvs [])
                    \\ gvs [subst_def, EL_MAP, GSYM FILTER_REVERSE, ALOOKUP_FILTER,
                            REVERSE_APPEND]
                    \\ drule_then assume_tac EL_MEM
                    \\ gvs [MEM_FILTER]
                    \\ dxrule_then assume_tac MEM_SND
                    \\ gvs [MAP_ZIP]
                    \\ IF_CASES_TAC \\ gvs []
                    \\ IF_CASES_TAC \\ gvs []
                    \\ IF_CASES_TAC \\ gvs [ALOOKUP_FILTER]
                    \\ IF_CASES_TAC \\ gvs [])
                \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                \\ rw [] \\ gvs []
                >- (Cases_on ‘i’ \\ gvs [subst_def, EL_MAP2, EL_MAP]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (rename1 ‘n < SUC (MIN _ _)’
                    \\ Cases_on ‘n’ \\ gvs [subst_def, EL_MAP2, EL_MAP,
                                            GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (Cases_on ‘i’ \\ gvs [subst_def, EL_MAP2, EL_MAP]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (rename1 ‘n < SUC (MIN _ _)’
                    \\ Cases_on ‘n’ \\ gvs [subst_def, EL_MAP2, EL_MAP,
                                            GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (Cases_on ‘i’ \\ gvs [subst_def, EL_MAP2, EL_MAP,
                                            GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (rename1 ‘n < SUC (MIN _ _)’
                    \\ Cases_on ‘n’ \\ gvs [subst_def, EL_MAP2, EL_MAP,
                                            GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]))
            >- (gvs [subst_Apps]
                \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any
                \\ conj_tac
                >- (gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER,
                         REVERSE_APPEND, Lams_split]
                    \\ IF_CASES_TAC \\ gvs [])
                \\ gvs [MAP_APPEND]
                \\ ‘∀a b c d. a = b ∧ c = d ⇒ a ++ c = b ++ d : exp list’ by gvs []
                \\ pop_assum $ irule_at Any \\ conj_tac
                >- (‘∀a b c d e. a = b ++ e ∧ c = d ⇒ a ++ c = b ++ e ++ d : exp list’ by gvs []
                    \\ pop_assum $ irule_at Any \\ conj_tac
                    >- (irule LIST_EQ \\ gvs [EL_MAP]
                        \\ IF_CASES_TAC \\ gvs [] \\ rpt $ strip_tac
                        >- (rename1 ‘EL n (_::_)’
                            \\ Cases_on ‘n’ \\ gvs [subst_def, GSYM FILTER_REVERSE,
                                                    ALOOKUP_FILTER, REVERSE_APPEND]
                            \\ IF_CASES_TAC \\ gvs [EL_MAP]
                            >- (gvs[MEM_MAP]
                                \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                                \\ gvs [EL_MEM])
                            \\ IF_CASES_TAC \\ gvs []
                            >- (dxrule_then assume_tac EL_MEM
                                \\ gvs [MEM_FILTER]
                                \\ dxrule_then assume_tac MEM_SND
                                \\ gvs [MAP_ZIP])
                            \\ drule_then assume_tac EL_MEM
                            \\ gvs [MEM_FILTER]
                            \\ dxrule_then assume_tac MEM_SND
                            \\ gvs [MAP_ZIP]
                            \\ IF_CASES_TAC \\ gvs [ALOOKUP_FILTER]
                            \\ IF_CASES_TAC \\ gvs [])
                        \\ gvs [subst_def, EL_MAP, GSYM FILTER_REVERSE,
                                ALOOKUP_FILTER, REVERSE_APPEND]
                        \\ drule_then assume_tac EL_MEM
                        \\ gvs [MEM_FILTER]
                        \\ dxrule_then assume_tac MEM_SND
                        \\ gvs [MAP_ZIP]
                        \\ IF_CASES_TAC \\ gvs []
                        \\ IF_CASES_TAC \\ gvs []
                        \\ IF_CASES_TAC \\ gvs [ALOOKUP_FILTER]
                        \\ IF_CASES_TAC \\ gvs [])
                    \\ Cases_on ‘b2’
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND])
                \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                \\ gen_tac \\ strip_tac
                \\ rename1 ‘Var (EL n _)’
                \\ rename1 ‘_ ≤ i ⇒ ¬EL _ (b2::bL2)’
                \\ Cases_on ‘EL n bL2’
                \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
            >- rw []
            >- rw []
            >- (rename1 ‘b3 ⇒ b2’ \\ Cases_on ‘b3’ \\ gvs [])
            >- (rw [] \\ gvs [])
            >- (rw [] \\ gvs [])
            >- (rw [] \\ gvs [])
            >- (rename1 ‘b3 ⇒ b2’ \\ Cases_on ‘b3’ \\ gvs []))
        \\ gvs [OPTREL_def]
        \\ rename1 ‘combine_rel x0 _’ \\ Cases_on ‘x0’ \\ gvs [combine_rel_def]
        \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gvs []
        \\ pop_assum $ dxrule_then assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
        \\ qmatch_goalsub_abbrev_tac ‘eval_to _ g = INR (Recclosure list _)’ \\ strip_tac
        \\ rename1 ‘combine_rel body body'’
        \\ rename1 ‘ALOOKUP _ _ = SOME (Lam s2 body)’
        \\ first_x_assum $ qspec_then ‘subst (MAP (λ(g,x). (g, Recclosure list g)) list
                                              ++ [(s2, w1)]) body'’ mp_tac
        \\ impl_tac
        >- (gvs [Abbr ‘list’, subst_APPEND, SNOC_APPEND, MAP_APPEND]
            \\ irule combine_rel_subst
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
            \\ conj_tac
            >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                \\ irule combine_rel_subst \\ rw []
                >- (irule combine_rel_subst \\ gvs [combine_rel_subst]
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                    \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
                    \\ qexists_tac ‘i’ \\ gvs [Lams_split]
                    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
                \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
                \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’ \\ gvs [Lams_split]
                \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
            \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
            \\ rename1 ‘n < _’
            \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
            \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
            \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’ \\ gvs [Lams_split]
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN, EL_MAP])
        \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ expr1) _’
        \\ disch_then $ qx_choose_then ‘j2’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) expr1 = INL Diverge’ \\ gvs []
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
            \\ dxrule_then assume_tac eval_to_mono
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ gvs [Abbr ‘list’, REVERSE_SNOC]
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’
            \\ Cases_on ‘eval_to (k - 1) expr2 = INL Diverge’ \\ gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
        \\ qexists_tac ‘j + j1 + j2’
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1 + j2’ assume_tac
        \\ gvs [Abbr ‘list’, REVERSE_SNOC]
        \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’
        \\ ‘eval_to (j2 + k - 1) expr2 ≠ INL Diverge’
          by (strip_tac \\ Cases_on ‘eval_to (k - 1) expr1’ \\ gvs [])
        \\ dxrule_then assume_tac eval_to_mono \\ gvs [])

    (* Recclosure with inlining 2 *)
    >- (print_tac "Recclosure 3/3"
        \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
        \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ qpat_x_assum ‘MAP FST _ = MAP FST _’ mp_tac
              \\ qpat_x_assum ‘LIST_REL combine_rel _ _’ mp_tac
              \\ rpt $ pop_assum kall_tac
              \\ rw []
              \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
        \\ IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ gvs []
            \\ pop_assum mp_tac
            \\ pop_assum mp_tac
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs []
            \\ Cases_on ‘vL2 = []’ \\ gvs []
            \\ gvs [REVERSE_APPEND, REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs [Lams_split]
            \\ IF_CASES_TAC \\ gvs [Lams_split]
            \\ strip_tac \\ strip_tac
            \\ gvs [OPTREL_def]
            \\ rename1 ‘combine_rel x0 _’ \\ Cases_on ‘x0’ \\ gvs [combine_rel_def])
        \\ qpat_x_assum ‘_ = INR (_, _, _)’ mp_tac
        \\ Cases_on ‘vL2 = []’ \\ gvs []
        \\ rw [REVERSE_APPEND] \\ gvs [Lams_split]
        >- (gvs [subst_Lams]
            \\ Cases_on ‘MAP SND (FILTER FST (ZIP (bL3, vL1)))’ \\ gvs [Lams_split]
            >- (Cases_on ‘vL2’ \\ gvs []
                \\ rename1 ‘eval_to _ (Lams vL2 _)’ \\ Cases_on ‘vL2 = []’ \\ gvs []
                >- (gvs [GSYM LAMBDA_PROD, FILTER_T, subst_APPEND, subst_def,
                         REVERSE_APPEND, subst1_notin_frees]
                    \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ expr1) _’
                    \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
                    \\ qmatch_goalsub_abbrev_tac ‘eval_to _ _ = INR (Recclosure list2 _)’
                    \\ strip_tac
                    \\ last_x_assum $ qspecl_then [‘k - 1’, ‘expr1’,
                                                   ‘App (App (subst_funs list2 x2)
                                                         (Value w1))
                                                    (Force (Value w1))’] mp_tac
                    \\ gvs [] \\ impl_tac
                    >- (gvs [Abbr ‘expr1’, Abbr ‘list2’, combine_rel_def, subst_funs_def,
                             SNOC_APPEND, subst_APPEND]
                        \\ gvs [combine_rel_def]
                        \\ irule combine_rel_subst \\ rw []
                        >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                        >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                            \\ irule combine_rel_subst \\ gvs []
                            \\ irule_at Any combine_rel_subst \\ gvs [combine_rel_subst]
                            \\ rename1 ‘Lam (HD vL1) _’
                            \\ conj_tac \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                            \\ qexists_tac ‘[HD vL1]’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
                            \\ qexists_tac ‘0’ \\ gvs [Lams_split])
                        >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                            \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                            \\ rename1 ‘n < _’
                            \\ rename1 ‘MAP FST xs = MAP FST ys’
                            \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                            \\ rename1 ‘Lam (HD vL1) _’
                            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                            \\ qexists_tac ‘[HD vL1]’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
                            \\ gvs [Lams_split]
                            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                                    LIST_REL_EL_EQN, EL_MAP]))
                    \\ disch_then $ qx_choose_then ‘j2’ assume_tac
                    \\ Cases_on ‘eval_to (k - 1) expr1 = INL Diverge’ \\ gvs []
                    >- (qexists_tac ‘0’
                        \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                        \\ dxrule_then assume_tac eval_to_mono
                        \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                        \\ dxrule_then assume_tac eval_to_mono
                        \\ gvs [REVERSE_SNOC, subst_def, Abbr ‘list2’]
                        \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                        \\ gvs [subst_funs_def, subst1_notin_frees]
                        \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’
                        \\ gvs []
                        \\ Cases_on ‘eval_to (k - 1) expr2 = INL Diverge’ \\ gvs []
                        \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
                    \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
                    \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1+ j2’ assume_tac
                    \\ qexists_tac ‘j + j1 + j2’ \\ gvs [REVERSE_SNOC, subst_def, Abbr ‘list2’]
                    \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                    \\ gvs [subst_funs_def, subst1_notin_frees]
                    \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’ \\ gvs []
                    \\ ‘eval_to (j2 + k - 1) expr2 ≠ INL Diverge’
                      by (strip_tac \\ Cases_on ‘eval_to (k - 1) expr1’ \\ gvs [])
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
                \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
                \\ qexists_tac ‘j + j1’
                \\ gvs [Lams_split, eval_to_def, REVERSE_SNOC, subst_def, subst_Lams]
                \\ irule v_rel_Closure \\ irule combine_rel_Lams \\ gvs []
                \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                \\ ‘∀p. (¬MEM p (TL vL2) ∧ p ≠ (HD vL2)) = ¬MEM p vL2’
                  by (Cases_on ‘vL2’ \\ gvs []
                      \\ gen_tac \\ metis_tac [CONJ_COMM])
                \\ gvs [SNOC_APPEND, subst_APPEND]
                \\ irule combine_rel_subst \\ rw []
                >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, MAP_FST_FILTER]
                >- (irule combine_rel_Apps \\ gvs [LIST_REL_EL_EQN, EL_MAP2, EL_MAP]
                    \\ rw [] \\ rename1 ‘n < SUC (LENGTH _)’
                    \\ gvs [combine_rel_def]
                    \\ Cases_on ‘n’ \\ gvs [EL_MAP, combine_rel_def])
                >- (qabbrev_tac ‘P = λv. ¬MEM v vL2’ \\ gvs [EVERY2_MAP]
                    \\ irule LIST_REL_FILTER \\ gvs []
                    \\ conj_tac >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                    \\ irule LIST_REL_mono
                    \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’
                    \\ rw []
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_APPEND_EQN]
                    \\ rw []
                    >- (pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                        \\ rename1 ‘n < LENGTH _’
                        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’
                        \\ qexists_tac ‘vL1’ \\ qexists_tac ‘h::vL2’
                        \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’  \\ qexists_tac ‘i’
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, Lams_split])
                    >- gvs [NOT_LESS]
                    >- (gvs [NOT_LESS, GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                        \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs []
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’
                        \\ qexists_tac ‘vL1’ \\ qexists_tac ‘h::vL2’
                        \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’  \\ qexists_tac ‘i’
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, Lams_split])
                    >- (gvs [NOT_LESS, GSYM ADD1, Once $ GSYM LESS_EQ_IFF_LESS_SUC]
                        \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM
                        \\ gvs [LESS_EQ_IFF_LESS_SUC]
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                        \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’
                        \\ qexists_tac ‘vL1’ \\ qexists_tac ‘h::vL2’
                        \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’  \\ qexists_tac ‘i’
                        \\ gvs [LIST_REL_EL_EQN, EL_MAP, Lams_split])))
            \\ gvs [eval_to_def]
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
            \\ qexists_tac ‘j + j1’ \\ gvs [REVERSE_SNOC, subst_def]
            \\ gvs [eval_to_def, subst_Lams]
            \\ irule v_rel_Closure
            \\ irule combine_rel_Lams
            \\ irule combine_rel_subst \\ rw []
            >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, MAP_FST_FILTER]
                \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                \\ AP_THM_TAC \\ AP_TERM_TAC
                \\ rename1 ‘TL (t ++ vL2)’
                \\ Cases_on ‘t’ \\ gvs [GSYM CONJ_ASSOC]
                >- (Cases_on ‘vL2’ \\ gvs [] \\ metis_tac [CONJ_COMM])
                \\ metis_tac [CONJ_COMM])
            >- (irule combine_rel_Apps \\ gvs [combine_rel_def]
                \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_MAP2, EL_APPEND_EQN]
                \\ rw [combine_rel_def])
            >- (gvs [FILTER_FILTER, LAMBDA_PROD, EVERY2_MAP]
                \\ rename1 ‘TL (t ++ vL2)’
                \\ ‘∀p. ¬MEM p (TL (t ++ vL2)) ∧ p ≠ HD (t ++ vL2) ⇔ ¬MEM p t ∧ ¬MEM p vL2’
                  by (gen_tac \\ Cases_on ‘t’ \\ gvs [GSYM CONJ_ASSOC]
                      >- (Cases_on ‘vL2’ \\ gvs [] \\ metis_tac [CONJ_COMM])
                      \\ metis_tac [CONJ_COMM])
                \\ gvs [] \\ pop_assum kall_tac
                \\ qabbrev_tac ‘P = λn. ¬MEM n t ∧ ¬MEM n vL2’ \\ gvs []
                \\ irule LIST_REL_FILTER
                \\ conj_tac
                >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_APPEND,
                        SNOC_APPEND, GSYM FST_THM]
                \\ irule LIST_REL_mono \\ gvs [MAP_SNOC, LIST_REL_SNOC]
                \\ qexists_tac ‘λx y. v_rel (SND x) (SND y)’ \\ gvs []
                \\ rw [] \\ gvs []
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gs [] \\ pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (pairarg_tac \\ gvs [])
                >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                    \\ rename1 ‘n < _’
                    \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                    \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘vL1’
                    \\ qexists_tac ‘i’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘bL2’
                    \\ gvs [Lams_split, LIST_REL_EL_EQN, EL_MAP]
                    \\ rw [] \\ last_x_assum $ drule_then assume_tac
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [])
                >- (gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                    \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘vL1’
                    \\ qexists_tac ‘i’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘bL2’
                    \\ gvs [Lams_split, LIST_REL_EL_EQN, EL_MAP]
                    \\ rw [] \\ last_x_assum $ drule_then assume_tac
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [])
                >- (gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                    \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘vL1’
                    \\ qexists_tac ‘i’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘bL2’
                    \\ gvs [Lams_split, LIST_REL_EL_EQN, EL_MAP]
                    \\ rw [] \\ last_x_assum $ drule_then assume_tac
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [])))
        >- (gvs [subst_Lams]
            \\ Cases_on ‘vL1’ \\ gvs []
            \\ rename1 ‘eval_to _ (Lams vL1 _)’
            \\ Cases_on ‘vL1 = []’ \\ gvs []
            >- (gvs [GSYM LAMBDA_PROD, FILTER_T]
                \\ gvs [subst_Apps, subst_def, REVERSE_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘Apps (Value (Recclosure list1 _)) _’
                \\ Cases_on ‘bL3’ \\ gvs []
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
                \\ qmatch_goalsub_abbrev_tac ‘eval_to _ g = INR (Recclosure list2 _)’
                \\ strip_tac
                \\ Cases_on ‘k = 1’ \\ gvs []
                >- (qexists_tac ‘0’ \\ gvs []
                    \\ Cases_on ‘eval_to 1 y = INL Diverge’ \\ gvs []
                    >- (rw [subst_def] \\ once_rewrite_tac [eval_to_def]
                        \\ simp [REVERSE_APPEND, ALOOKUP_APPEND]
                        \\ once_rewrite_tac [eval_to_def]
                        \\ simp [dest_anyClosure_def, Abbr ‘list1’, REVERSE_APPEND])
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ Cases_on ‘eval_to 1 g = INL Diverge’ \\ gvs []
                    >- (rw [subst_def] \\ once_rewrite_tac [eval_to_def]
                        \\ simp [REVERSE_APPEND, ALOOKUP_APPEND]
                        \\ once_rewrite_tac [eval_to_def]
                        \\ simp [dest_anyClosure_def, Abbr ‘list1’, REVERSE_APPEND])
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ gvs [Abbr ‘list2’, REVERSE_SNOC, subst_def]
                    \\ rw [subst_def] \\ once_rewrite_tac [eval_to_def]
                    \\ simp [REVERSE_APPEND, ALOOKUP_APPEND, eval_to_Value, Abbr ‘list1’, dest_anyClosure_def])
                \\ simp [subst_def, REVERSE_APPEND]
                \\ rename1 ‘eval_to _ (App (Value (Recclosure _ _)) (Value v1))’
                \\ qspecl_then [‘[Value v1]’, ‘k-1’, ‘list1’, ‘v1'’] mp_tac
                               eval_to_Apps_Recclosure_Lams_not_0
                \\ gvs [Abbr ‘list1’, REVERSE_APPEND]
                \\ disch_then kall_tac
                \\ qmatch_goalsub_abbrev_tac ‘App (Tick (subst_funs list1 _)) _’
                \\ gvs [subst_funs_def, subst_def, subst_Lams]
                \\ Cases_on ‘vL2’
                \\ gvs [GSYM LAMBDA_PROD, FILTER_T,
                        subst_def, REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                \\ gvs [eval_to_def, subst_funs_def, subst_empty, dest_anyClosure_def]
                \\ gvs [subst1_def] \\ once_rewrite_tac [eval_to_def]
                \\ gvs [Abbr ‘list1’, REVERSE_APPEND, subst_def]
                \\ ‘eval_to (k - 2) (Force (Value v1)) ≠ INL Type_error’
                  by (strip_tac \\ qpat_x_assum ‘_ ≠ INL Type_error’ irule
                      \\ once_rewrite_tac [eval_to_def] \\ gvs [])
                \\ last_assum $ qspecl_then [‘k - 2’, ‘Force (Value v1)’, ‘Force (Value w1)’]
                              mp_tac
                \\ ‘k - 2 < k’ by gvs []
                \\ disch_then $ dxrule_then $ dxrule_then mp_tac
                \\ impl_tac >- gvs [combine_rel_def]
                \\ disch_then $ qx_choose_then ‘j2’ assume_tac
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1)) = INL Diverge’ \\ gvs []
                >- (qexists_tac ‘0’
                    \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ gvs [Abbr ‘list2’, REVERSE_SNOC, subst_def, REVERSE_APPEND,
                            GSYM LAMBDA_PROD, FILTER_T]
                    \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def, subst_empty]
                    \\ once_rewrite_tac [eval_to_def] \\ gvs []
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs [])
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1))’ \\ gvs []
                >- (rename1 ‘INL x'’ \\ Cases_on ‘x'’ \\ gvs []
                    \\ qexists_tac ‘j + j1 + j2’
                    \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
                    \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1+ j2’ assume_tac
                    \\ gvs [REVERSE_SNOC, Abbr ‘list2’, subst_def, eval_to_Tick,
                            GSYM LAMBDA_PROD, FILTER_T, REVERSE_APPEND]
                    \\ once_rewrite_tac [eval_to_def]
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs [])
                \\ qmatch_goalsub_abbrev_tac ‘eval_to (_ - 2) expr1’
                \\ rename1 ‘eval_to (k - 2) (Force (Value v1)) = INR val1’
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs []
                \\ rename1 ‘v_rel val1 val1'’
                \\ qabbrev_tac ‘expr2 = App (subst (MAP (λ(g,x). (g,
                    Recclosure (SNOC (v1',Lam h (App (App x2 (Var h)) (Force (Var h))))
                                (SNOC
                                 (s,Lam h (Tick (App (App x2 (Var h)) (Force (Var h)))))
                                 ys)) g))
                              (SNOC (v1',Lam h (App (App x2 (Var h)) (Force (Var h))))
                               (SNOC (s,Lam h (Tick (App (App x2 (Var h))
                                                     (Force (Var h))))) ys)) ++
                                                    [(h,w1)]) x2)
                                            (Value w1)’
                \\ last_x_assum $ qspecl_then [‘k - 2’, ‘App expr1 (Value val1)’,
                                               ‘App expr2 (Value val1')’] mp_tac
                \\ gvs [] \\ impl_tac
                >- (conj_tac
                    >- (once_rewrite_tac [eval_to_def]
                        \\ strip_tac \\ last_x_assum irule
                        \\ once_rewrite_tac [eval_to_def]
                        \\ gvs [eval_to_Value]
                        \\ ‘∀l h2. subst1 h2 v1 (subst (FILTER (λ(n,x). n ≠ h2) l) x1)
                                   = subst l (subst1 h2 v1 x1)’
                          by (gen_tac \\ gen_tac \\ irule EQ_TRANS
                              \\ irule_at (Pos hd) subst_commutes
                              \\ gvs [MAP_FST_FILTER, MEM_FILTER]
                              \\ irule EQ_TRANS \\ irule_at (Pos last) subst_remove
                              \\ Q.REFINE_EXISTS_TAC ‘{_}’ \\ gvs []
                              \\ irule_at Any EQ_REFL \\ gvs [freevars_subst])
                        \\ gvs [subst_APPEND])
                    \\ gvs [combine_rel_def]
                    \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’] \\ gvs [combine_rel_def]
                    \\ ‘∀l h2. subst1 h2 v1 (subst (FILTER (λ(n,x). n ≠ h2) l) x1)
                               = subst l (subst1 h2 v1 x1)’
                      by (gen_tac \\ gen_tac \\ irule EQ_TRANS
                          \\ irule_at (Pos hd) subst_commutes
                          \\ gvs [MAP_FST_FILTER, MEM_FILTER]
                          \\ irule EQ_TRANS \\ irule_at (Pos last) subst_remove
                          \\ Q.REFINE_EXISTS_TAC ‘{_}’ \\ gvs []
                          \\ irule_at Any EQ_REFL \\ gvs [freevars_subst])
                    \\ gvs [subst_APPEND]
                    \\ gvs [Abbr ‘list2’, SNOC_APPEND, subst_APPEND]
                    \\ irule combine_rel_subst \\ rw []
                    >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
                    >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                        \\ irule combine_rel_subst \\ irule_at Any combine_rel_subst
                        \\ last_x_assum $ qspec_then ‘0’ assume_tac \\ gvs [combine_rel_subst]
                        \\ conj_tac \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                        \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                        \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ gvs []
                        \\ qpat_assum ‘_ ∉ freevars x1’ $ irule_at Any
                        \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ gvs []
                        \\ qexists_tac ‘[F]’ \\ gvs []
                        \\ qexists_tac ‘[F]’ \\ gvs [])
                    >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                        \\ rename1 ‘n < _’
                        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                        \\ qpat_x_assum ‘combine_rel x1 x2’ $ irule_at Any
                        \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ gvs []
                        \\ qpat_assum ‘_ ∉ freevars x1’ $ irule_at Any
                        \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ gvs []
                        \\ qexists_tac ‘[F]’ \\ gvs []
                        \\ qexists_tac ‘[F]’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]))
                \\ disch_then $ qx_choose_then ‘j3’ assume_tac
                \\ Cases_on ‘eval_to (k - 2) (App expr1 (Value val1)) = INL Diverge’ \\ gvs []
                >- (Cases_on ‘eval_to (k - 2) (App expr2 (Value val1')) = INL Diverge’
                    >~[‘eval_to _ _ ≠ INL Diverge’]
                    >- (drule_then assume_tac eval_to_mono \\ gvs []
                        \\ Cases_on ‘eval_to (k - 2) (App expr2 (Value val1'))’ \\ gvs [])
                    \\ pop_assum mp_tac \\ pop_assum mp_tac \\ pop_assum kall_tac
                    \\ once_rewrite_tac [eval_to_def] \\ strip_tac \\ strip_tac
                    \\ gvs [eval_to_Value]
                    \\ qexists_tac ‘0’
                    \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                    \\ gvs [Abbr ‘list2’, REVERSE_SNOC, subst_def, REVERSE_APPEND,
                            GSYM LAMBDA_PROD, FILTER_T]
                    \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def, subst_empty]
                    \\ once_rewrite_tac [eval_to_def] \\ gvs []
                    \\ last_x_assum $ qspec_then ‘0’ assume_tac \\ gvs []
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
                    \\ dxrule_then assume_tac eval_to_mono
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs [])
                \\ ‘eval_to (j3 + k - 2) (App expr2 (Value val1')) ≠ INL Diverge’
                  by (strip_tac \\ Cases_on ‘eval_to (k - 2) (App expr1 (Value val1))’ \\ gvs [])
                \\ dxrule_then assume_tac eval_to_mono \\ gvs []
                \\ pop_assum mp_tac \\ pop_assum kall_tac \\ pop_assum mp_tac
                \\ once_rewrite_tac [eval_to_def] \\ strip_tac
                \\ disch_then $ qspec_then ‘j + j1 + j2 + j3 + k - 1’ assume_tac
                \\ qexists_tac ‘j + j1 + j2 + j3 + 1’
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2 + j3 + 1’ assume_tac
                \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1+ j2 + j3 + 1’ assume_tac
                \\ gvs [REVERSE_SNOC, Abbr ‘list2’, subst_def, eval_to_Tick,
                        GSYM LAMBDA_PROD, FILTER_T, REVERSE_APPEND, eval_to_Value]
                \\ once_rewrite_tac [eval_to_def]
                \\ ‘eval_to (j2 + k - 2) (Force (Value w1)) ≠ INL Diverge’ by gvs []
                \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
            \\ qexists_tac ‘j + j1’
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
            \\ gvs []
            \\ pop_assum kall_tac \\ pop_assum kall_tac
            \\ gvs [REVERSE_SNOC]
            \\ gvs [subst_Lams, Lams_split, eval_to_def]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
            \\ irule_at (Pos hd) EQ_REFL \\ gvs []
            \\ qpat_assum ‘combine_rel x1 x2’ $ irule_at Any
            \\ qexists_tac ‘vL2’ \\ qexists_tac ‘[h]’ \\ gvs []
            \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ gvs [subst_def]
            \\ rpt (‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                    \\ pop_assum $ irule_at Any)
            \\ gvs [ALL_DISTINCT_APPEND]
            \\ qexists_tac ‘s’ \\ qexists_tac ‘v1'’ \\ qexists_tac ‘i’
            \\ qexists_tac ‘ys’ \\ qexists_tac ‘xs’ \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
            \\ qexists_tac ‘[w1]’ \\ qexists_tac ‘[v1]’ \\ qexists_tac ‘TL bL3’
            \\ qexists_tac ‘[HD bL3]’ \\ qexists_tac ‘bL2’ \\ gvs []
            \\ Cases_on ‘bL3’ \\ gvs [PULL_EXISTS]
            \\ rpt $ conj_tac
            >- (gvs [subst_Apps]
                \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any
                \\ conj_tac
                >- (qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
                    \\ gvs [subst_APPEND, FILTER_APPEND, subst1_notin_frees, subst_App]
                    \\ conj_tac
                    >- (‘EL i (Var h::MAP Var vL1) = Var (EL i (h::vL1))’
                          by (Cases_on ‘i’ \\ gvs [EL_MAP]) \\ gvs [EL_MAP]
                        \\ irule EQ_TRANS
                        \\ irule_at (Pos hd) $ GSYM subst_remove
                        \\ Q.REFINE_EXISTS_TAC ‘{_}’ \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                        \\ first_assum $ irule_at $ Pos hd
                        \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
                        \\ rw [] \\ once_rewrite_tac [CONS_APPEND] \\ gvs [Lams_split])
                    \\ Cases_on ‘i’ \\ gvs [subst_def]
                    \\ Cases_on ‘h = EL n vL1’
                    \\ gvs [EL_MEM, subst_def, EL_MAP, GSYM FILTER_REVERSE, ALOOKUP_FILTER])
                \\ gvs [MAP_APPEND]
                \\ ‘∀a b c d. a = b ∧ c = d ⇒ a ++ c = b ++ d : exp list’ by gvs []
                \\ pop_assum $ irule_at Any \\ conj_tac
                >- (irule LIST_EQ \\ gvs [EL_MAP]
                    \\ IF_CASES_TAC \\ gvs [] \\ rpt $ strip_tac
                    >- (rename1 ‘EL n (_::_)’
                        \\ Cases_on ‘n’
                        \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                        \\ IF_CASES_TAC \\ gvs [EL_MAP]
                        >- (rename1 ‘n < SUC _’
                            \\ Cases_on ‘n’ \\ gvs []
                            \\ gvs[MEM_MAP]
                            \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                            \\ gvs [EL_MEM])
                        \\ rename1 ‘n < SUC _’
                        \\ Cases_on ‘n’ \\ gvs []
                        \\ IF_CASES_TAC \\ gvs []
                        >- (dxrule_then assume_tac EL_MEM
                            \\ gvs [MEM_FILTER]
                            \\ dxrule_then assume_tac MEM_SND
                            \\ gvs [MAP_ZIP])
                        \\ drule_then assume_tac EL_MEM
                        \\ gvs [MEM_FILTER]
                        \\ dxrule_then assume_tac MEM_SND
                        \\ gvs [MAP_ZIP]
                        \\ IF_CASES_TAC \\ gvs [ALOOKUP_FILTER, EL_MAP]
                        \\ IF_CASES_TAC \\ gvs [])
                    \\ gvs [subst_def, EL_MAP, GSYM FILTER_REVERSE, ALOOKUP_FILTER,
                            REVERSE_APPEND]
                    \\ drule_then assume_tac EL_MEM
                    \\ gvs [MEM_FILTER]
                    \\ dxrule_then assume_tac MEM_SND
                    \\ gvs [MAP_ZIP]
                    \\ IF_CASES_TAC \\ gvs []
                    \\ IF_CASES_TAC \\ gvs []
                    \\ IF_CASES_TAC \\ gvs [ALOOKUP_FILTER]
                    \\ IF_CASES_TAC \\ gvs [])
                \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                \\ rw [] \\ gvs []
                >- (Cases_on ‘i’ \\ gvs [subst_def, EL_MAP2, EL_MAP]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (rename1 ‘n < SUC (MIN _ _)’
                    \\ Cases_on ‘n’ \\ gvs [subst_def, EL_MAP2, EL_MAP,
                                            GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (Cases_on ‘i’ \\ gvs [subst_def, EL_MAP2, EL_MAP]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (rename1 ‘n < SUC (MIN _ _)’
                    \\ Cases_on ‘n’ \\ gvs [subst_def, EL_MAP2, EL_MAP,
                                            GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (Cases_on ‘i’ \\ gvs [subst_def, EL_MAP2, EL_MAP,
                                            GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
                >- (rename1 ‘n < SUC (MIN _ _)’
                    \\ Cases_on ‘n’ \\ gvs [subst_def, EL_MAP2, EL_MAP,
                                            GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND]
                    \\ IF_CASES_TAC
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]))
            >- (gvs [subst_Apps]
                \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any
                \\ conj_tac
                >- (gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER,
                         REVERSE_APPEND, Lams_split]
                    \\ IF_CASES_TAC \\ gvs [EL_MAP])
                \\ gvs [MAP_APPEND]
                \\ ‘∀a b c d. a = b ∧ c = d ⇒ a ++ c = b ++ d : exp list’ by gvs []
                \\ pop_assum $ irule_at Any \\ conj_tac
                >- (‘∀a b c d e. a = b ++ e ∧ c = d ⇒ a ++ c = b ++ e ++ d : exp list’ by gvs []
                    \\ pop_assum $ irule_at Any \\ conj_tac
                    >- (irule LIST_EQ \\ gvs [EL_MAP]
                        \\ IF_CASES_TAC \\ gvs [] \\ rpt $ strip_tac
                        >- (rename1 ‘EL n (_::_)’
                            \\ Cases_on ‘n’ \\ gvs [subst_def, GSYM FILTER_REVERSE,
                                                    ALOOKUP_FILTER, REVERSE_APPEND]
                            \\ IF_CASES_TAC \\ gvs [EL_MAP]
                            >- (gvs[MEM_MAP]
                                \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                                \\ gvs [EL_MEM])
                            \\ IF_CASES_TAC \\ gvs []
                            >- (dxrule_then assume_tac EL_MEM
                                \\ gvs [MEM_FILTER]
                                \\ dxrule_then assume_tac MEM_SND
                                \\ gvs [MAP_ZIP])
                            \\ drule_then assume_tac EL_MEM
                            \\ gvs [MEM_FILTER]
                            \\ dxrule_then assume_tac MEM_SND
                            \\ gvs [MAP_ZIP]
                            \\ IF_CASES_TAC \\ gvs [ALOOKUP_FILTER]
                            \\ IF_CASES_TAC \\ gvs [])
                        \\ gvs [subst_def, EL_MAP, GSYM FILTER_REVERSE,
                                ALOOKUP_FILTER, REVERSE_APPEND]
                        \\ drule_then assume_tac EL_MEM
                        \\ gvs [MEM_FILTER]
                        \\ dxrule_then assume_tac MEM_SND
                        \\ gvs [MAP_ZIP]
                        \\ IF_CASES_TAC \\ gvs []
                        \\ IF_CASES_TAC \\ gvs []
                        \\ IF_CASES_TAC \\ gvs [ALOOKUP_FILTER]
                        \\ IF_CASES_TAC \\ gvs [])
                    \\ Cases_on ‘b2’
                    \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, REVERSE_APPEND])
                \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2]
                \\ gen_tac \\ strip_tac
                \\ rename1 ‘Var (EL n _)’
                \\ rename1 ‘_ ≤ i ⇒ ¬EL _ (b2::bL2)’
                \\ Cases_on ‘EL n bL2’
                \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
                \\ rename1 ‘Force (Var (EL n2 _))’ \\ Cases_on ‘EL n2 bL2’
                \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
            >- rw []
            >- rw []
            >- (rename1 ‘b3 ⇒ b2’ \\ Cases_on ‘b3’ \\ gvs [])
            >- (rw [] \\ gvs [])
            >- (rw [] \\ gvs [])
            >- (rw [] \\ gvs [])
            >- (rename1 ‘b3 ⇒ b2’ \\ Cases_on ‘b3’ \\ gvs []))
        \\ gvs [OPTREL_def]
        \\ rename1 ‘combine_rel x0 _’ \\ Cases_on ‘x0’ \\ gvs [combine_rel_def]
        \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gvs []
        \\ pop_assum $ dxrule_then assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
        \\ qmatch_goalsub_abbrev_tac ‘eval_to _ g = INR (Recclosure list _)’ \\ strip_tac
        \\ rename1 ‘combine_rel body body'’
        \\ rename1 ‘ALOOKUP _ _ = SOME (Lam s2 body)’
        \\ first_x_assum $ qspec_then ‘subst (MAP (λ(g,x). (g, Recclosure list g)) list
                                              ++ [(s2, w1)]) body'’ mp_tac
        \\ impl_tac
        >- (gvs [Abbr ‘list’, subst_APPEND, SNOC_APPEND, MAP_APPEND]
            \\ irule combine_rel_subst
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
            \\ conj_tac
            >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                \\ irule combine_rel_subst \\ rw []
                >- (irule combine_rel_subst \\ gvs [combine_rel_subst]
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                    \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                    \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
                    \\ qexists_tac ‘i’ \\ gvs [Lams_split]
                    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
                \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
                \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’ \\ gvs [Lams_split]
                \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
            \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
            \\ rename1 ‘n < _’
            \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
            \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
            \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’ \\ gvs [Lams_split]
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN, EL_MAP])
        \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ expr1) _’
        \\ disch_then $ qx_choose_then ‘j2’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) expr1 = INL Diverge’ \\ gvs []
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
            \\ dxrule_then assume_tac eval_to_mono
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs []
            \\ gvs [Abbr ‘list’, REVERSE_SNOC]
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’
            \\ Cases_on ‘eval_to (k - 1) expr2 = INL Diverge’ \\ gvs []
            \\ dxrule_then assume_tac eval_to_mono \\ gvs [])
        \\ qexists_tac ‘j + j1 + j2’
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1 + j2’ assume_tac
        \\ gvs [Abbr ‘list’, REVERSE_SNOC]
        \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’
        \\ ‘eval_to (j2 + k - 1) expr2 ≠ INL Diverge’
          by (strip_tac \\ Cases_on ‘eval_to (k - 1) expr1’ \\ gvs [])
        \\ dxrule_then assume_tac eval_to_mono \\ gvs []))

  >~ [‘Let opt x1 y1’] >- (
    print_tac "Finished App"
    \\ Cases_on ‘opt’ >~[‘Seq x1 y1’]
    >- (gvs [combine_rel_def, eval_to_def]
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
        \\ ‘eval_to (j1 + k - 1) y2 ≠ INL Diverge’
          by (strip_tac \\ Cases_on ‘eval_to (k - 1) y1’ \\ gvs [])
        \\ dxrule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono \\ gvs [])
    \\ gvs [Once combine_rel_def, eval_to_def]
    >~[‘Apps (App _ _) _’]
    >- (IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs [])
        \\ Cases_on ‘vL2 = []’ \\ gvs []
        \\ gvs [eval_to_Lams, subst1_def, subst_Lams, subst_Apps, eval_to_def]
        \\ IF_CASES_TAC \\ gs [] >- (qexists_tac ‘0’ \\ gvs [])
        \\ last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gs []
        \\ last_x_assum irule \\ gvs []
        \\ irule combine_rel_subst \\ gvs []
        \\ irule_at Any combine_rel_subst \\ gvs []
        \\ conj_tac
        >- (irule v_rel_Closure \\ irule combine_rel_Lams
            \\ irule combine_rel_Apps \\ gvs [combine_rel_def]
            \\ rpt $ pop_assum kall_tac
            \\ rw [LIST_REL_EL_EQN, EL_MAP2, EL_MAP, EL_APPEND_EQN]
            \\ IF_CASES_TAC \\ gvs [combine_rel_def]
            \\ IF_CASES_TAC \\ gvs [combine_rel_def])
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ ‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ pop_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
        \\ pop_assum $ irule_at Any
        \\ gvs []
        \\ irule_at (Pos $ el 2) EQ_REFL
        \\ qexists_tac ‘[]’ \\ gvs []
        \\ irule_at (Pos $ el 2) EQ_REFL \\ qexists_tac ‘bL2’ \\ gvs []
        \\ rw []
        >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
            \\ pop_assum irule
            \\ conj_tac \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst1_def]
            >- (strip_tac \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER]
                \\ gvs [MEM_EL, EL_ZIP])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
            \\ pop_assum irule
            \\ conj_tac \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst1_def]
            >- (strip_tac \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER]
                \\ gvs [MEM_EL, EL_ZIP])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- gvs [EL_MEM]
        >- gvs [EL_MAP]
        >- (rename1 ‘combine_rel x1 (subst1 _ _ x2)’
            \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
            \\ gvs [subst1_notin_frees]))
    >~[‘Lams _ _’]
    >- (IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs [])
        \\ Cases_on ‘vL2 = []’ \\ gvs []
        \\ gvs [eval_to_Lams, subst1_def, subst_Lams, subst_Apps, eval_to_def]
        \\ IF_CASES_TAC \\ gs [] >- (qexists_tac ‘0’ \\ gvs [])
        \\ last_x_assum $ qspec_then ‘k - 2’ assume_tac \\ gs []
        \\ last_x_assum irule \\ gvs []
        \\ irule combine_rel_subst \\ gvs []
        \\ irule_at Any combine_rel_subst \\ gvs []
        \\ conj_tac
        >- (irule v_rel_Closure \\ irule combine_rel_Lams
            \\ irule combine_rel_Apps \\ gvs []
            \\ rpt $ pop_assum kall_tac
            \\ rw [LIST_REL_EL_EQN, EL_MAP2, EL_MAP, EL_APPEND_EQN]
            \\ IF_CASES_TAC \\ gvs [combine_rel_def]
            \\ IF_CASES_TAC \\ gvs [combine_rel_def])
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                \\ pop_assum $ irule_at Any)
        \\ gvs []
        \\ ‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ pop_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
        \\ pop_assum $ irule_at Any
        \\ gvs []
        \\ qexists_tac ‘vL2’ \\ gvs []
        \\ irule_at (Pos $ el 2) EQ_REFL \\ gvs []
        \\ qexists_tac ‘i’ \\ qexists_tac ‘bL2’ \\ gvs []
        \\ rw []
        >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
            \\ pop_assum irule
            \\ conj_tac \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst1_def]
            >- (strip_tac \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER]
                \\ gvs [MEM_EL, EL_ZIP])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (‘∀l1 l2 l3 l4 : exp list. l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
            \\ pop_assum irule
            \\ conj_tac \\ irule LIST_EQ \\ rw [EL_MAP, EL_MAP2, subst1_def]
            >- (strip_tac \\ drule_then assume_tac EL_MEM
                \\ gvs [MEM_FILTER]
                \\ gvs [MEM_EL, EL_ZIP])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM])
            >- (IF_CASES_TAC \\ gvs [EL_MEM]))
        >- (rename1 ‘combine_rel x1 (subst1 _ _ x2)’
            \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars
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
    \\ ‘combine_rel (subst1 m v1 y1) (subst1 m w1 y2)’
      by (irule combine_rel_subst \\ gs [])
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
    print_tac "If syntax"
    \\ gvs [Once combine_rel_def, eval_to_def]
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
    print_tac "Letrec"
    \\ gvs [Once combine_rel_def, eval_to_def]
    >~[‘Apps (App _ (Var (EL _ _))) _’]
    >- (IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs [])
        \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gvs []
        \\ pop_assum irule \\ gvs []
        \\ gvs [subst_funs_def, SNOC_APPEND, MAP_APPEND, subst_APPEND] \\ irule combine_rel_subst
        \\ rw []
        >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
        >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
            \\ irule combine_rel_subst \\ gvs []
            \\ irule_at Any combine_rel_subst \\ gvs [combine_rel_subst]
            \\ conj_tac \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
            \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’ \\ gvs [Lams_split]
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
        >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
            \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
            \\ rename1 ‘n < _’
            \\ rename1 ‘MAP FST f = MAP FST g’
            \\ ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs [] \\ gvs [EL_MAP]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
            \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’ \\ gvs [Lams_split]
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN, EL_MAP]))
    >~[‘SNOC _ _’]
    >- (IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs [])
        \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ gvs []
        \\ pop_assum irule \\ gvs []
        \\ gvs [subst_funs_def, SNOC_APPEND, MAP_APPEND, subst_APPEND] \\ irule combine_rel_subst
        \\ rw []
        >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
        >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
            \\ irule combine_rel_subst \\ gvs []
            \\ irule_at Any combine_rel_subst \\ gvs [combine_rel_subst]
            \\ conj_tac \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
            \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’ \\ gvs [Lams_split]
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
        >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
            \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
            \\ rename1 ‘n < _’
            \\ rename1 ‘MAP FST f = MAP FST g’
            \\ ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs [] \\ gvs [EL_MAP]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
            \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
            \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’ \\ gvs [Lams_split]
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN, EL_MAP]))
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘combine_rel x y’
    \\ last_x_assum $ qspec_then ‘k - 1’ assume_tac \\ last_x_assum kall_tac
    \\ gvs []
    \\ pop_assum irule
    \\ gvs [subst_funs_def]
    \\ irule combine_rel_subst
    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
    \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
    \\ rename1 ‘n < LENGTH g’
    \\ ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gs [] \\ gvs [EL_MAP]
    \\ irule v_rel_Recclosure
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >~ [‘Force x’] >- (
    print_tac "Force"
    \\ qpat_x_assum ‘_ ≠ INL Type_error’ mp_tac \\ rgs [Once combine_rel_def]
    \\ once_rewrite_tac [eval_to_def] \\ simp []
    \\ pop_assum kall_tac
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ simp [])
    \\ rw []
    \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gs []
    \\ first_x_assum $ qspec_then ‘x’ assume_tac \\ gs []
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
    \\ rename1 ‘combine_rel x y’ \\ gvs []
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
        >- (‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
            \\ gvs [OPTREL_def]
            \\ qpat_x_assum ‘combine_rel x0 _’ mp_tac
            \\ rw [Once combine_rel_cases] \\ gs []
            \\ Cases_on ‘x0’ \\ gvs [])
        >- (gvs [REVERSE_APPEND]
            \\ Cases_on ‘vL2 = []’ \\ gvs []
            \\ IF_CASES_TAC \\ gvs [Lams_split]
            \\ IF_CASES_TAC \\ gvs [Lams_split]
            \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP]
                  \\ ‘∀n. n < LENGTH ys ⇒ EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
                  \\ gvs [EL_MAP])
            \\ gvs [OPTREL_def]
            \\ qpat_x_assum ‘combine_rel x0 _’ mp_tac
            \\ rw [Once combine_rel_cases] \\ gs []
            \\ Cases_on ‘x0’ \\ gvs [])
        >- (gvs [REVERSE_APPEND]
            \\ Cases_on ‘vL2 = []’ \\ gvs []
            \\ IF_CASES_TAC \\ gvs [Lams_split]
            \\ IF_CASES_TAC \\ gvs [Lams_split]
            \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP]
                  \\ ‘∀n. n < LENGTH ys ⇒ EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
                  \\ gvs [EL_MAP])
            \\ gvs [OPTREL_def]
            \\ qpat_x_assum ‘combine_rel x0 _’ mp_tac
            \\ rw [Once combine_rel_cases] \\ gs []
            \\ Cases_on ‘x0’ \\ gvs []))
      \\ pairarg_tac \\ gvs []
      \\ Cases_on ‘∃xs n. v1 = Recclosure xs n’ \\ gvs [v_rel_def]
      >- (gvs [dest_anyThunk_def, v_rel_def]
          \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
          \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ qpat_x_assum ‘combine_rel x0 _’ mp_tac
          \\ rw [Once combine_rel_cases] \\ gvs []
          \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ rename1 ‘subst_funs xs x2’ \\ rename1 ‘combine_rel x2 y2’
          \\ last_x_assum $ qspecl_then [‘k - 1’, ‘subst_funs xs x2’, ‘subst_funs ys y2’] mp_tac
          \\ gs [] \\ impl_tac
          >- (gvs [subst_funs_def] \\ irule combine_rel_subst
              \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
                      LIST_REL_EL_EQN, EL_MAP]
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
      >- (gvs [dest_anyThunk_def, v_rel_def, REVERSE_APPEND, REVERSE_SNOC]
          \\ pop_assum mp_tac
          \\ ‘vL2 ≠ []’ by (strip_tac \\ gvs [])
          \\ IF_CASES_TAC \\ gvs [Lams_split]
          \\ IF_CASES_TAC \\ gvs []
          \\ strip_tac
          \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
          \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP]
                  \\ ‘∀n. n < LENGTH ys ⇒ EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
                  \\ gvs [EL_MAP])
          \\ gvs [OPTREL_def]
          \\ qpat_x_assum ‘combine_rel x0 _’ mp_tac
          \\ rw [Once combine_rel_cases] \\ gvs []
          \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ qpat_x_assum ‘eval_to _ y = _’ mp_tac
          \\ qmatch_goalsub_abbrev_tac ‘Recclosure list2 _’ \\ strip_tac
          \\ qmatch_goalsub_abbrev_tac ‘subst_funs list1 _’
          \\ rename1 ‘subst_funs _ x3’ \\ rename1 ‘combine_rel x3 y3’
          \\ last_x_assum $ qspecl_then [‘k - 1’, ‘subst_funs list1 x3’, ‘subst_funs list2 y3’]
                          mp_tac
          \\ gs [] \\ impl_tac
          >- (gvs [subst_funs_def, Abbr ‘list1’, Abbr ‘list2’, SNOC_APPEND, subst_APPEND]
              \\ irule combine_rel_subst
              \\ rw []
              >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
              >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                  \\ irule combine_rel_subst \\ gvs []
                  \\ irule_at Any combine_rel_subst \\ gvs [combine_rel_subst]
                  \\ conj_tac \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                  \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                  \\ qexists_tac ‘vL2’
                  \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’
                  \\ gvs [Lams_split]
                  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
              >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                  \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                  \\ rename1 ‘n < _’
                  \\ rename1 ‘MAP FST xs = MAP FST ys’
                  \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                  \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                  \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                  \\ qexists_tac ‘vL2’
                  \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’
                  \\ gvs [Lams_split]
                  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN, EL_MAP]))
          \\ disch_then $ qx_choose_then ‘j1’ assume_tac
          \\ Cases_on ‘eval_to (k - 1) (subst_funs list1 x3) = INL Diverge’ \\ gvs []
          >- (qexists_tac ‘0’
              \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
              \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
              \\ gvs []
              \\ Cases_on ‘eval_to (k - 1) (subst_funs list2 y3) = INL Diverge’
              \\ gvs [Abbr ‘list2’, REVERSE_SNOC]
              \\ dxrule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono \\ gvs [])
          \\ qexists_tac ‘j + j1’
          \\ ‘eval_to (j + k) y ≠ INL Diverge’ by gvs []
          \\ dxrule_then (qspec_then ‘j + j1 + k’ assume_tac) eval_to_mono \\ gvs []
          \\ ‘eval_to (j1 + k - 1) (subst_funs list2 y3) ≠ INL Diverge’
            by (strip_tac \\ Cases_on ‘eval_to (k - 1) (subst_funs list1 x3)’ \\ gvs [])
          \\ dxrule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono
          \\ gvs [Abbr ‘list2’, REVERSE_SNOC])
      >- (gvs [dest_anyThunk_def, v_rel_def, REVERSE_APPEND, REVERSE_SNOC]
          \\ pop_assum mp_tac
          \\ ‘vL2 ≠ []’ by (strip_tac \\ gvs [])
          \\ IF_CASES_TAC \\ gvs [Lams_split]
          \\ IF_CASES_TAC \\ gvs []
          \\ strip_tac
          \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
          \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP]
                  \\ ‘∀n. n < LENGTH ys ⇒ EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
                  \\ gvs [EL_MAP])
          \\ gvs [OPTREL_def]
          \\ qpat_x_assum ‘combine_rel x0 _’ mp_tac
          \\ rw [Once combine_rel_cases] \\ gvs []
          \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ qpat_x_assum ‘eval_to _ y = _’ mp_tac
          \\ qmatch_goalsub_abbrev_tac ‘Recclosure list2 _’ \\ strip_tac
          \\ qmatch_goalsub_abbrev_tac ‘subst_funs list1 _’
          \\ rename1 ‘subst_funs _ x3’ \\ rename1 ‘combine_rel x3 y3’
          \\ last_x_assum $ qspecl_then [‘k - 1’, ‘subst_funs list1 x3’, ‘subst_funs list2 y3’]
                          mp_tac
          \\ gs [] \\ impl_tac
          >- (gvs [subst_funs_def, Abbr ‘list1’, Abbr ‘list2’, SNOC_APPEND, subst_APPEND]
              \\ irule combine_rel_subst
              \\ rw []
              >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
              >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                  \\ irule combine_rel_subst \\ gvs []
                  \\ irule_at Any combine_rel_subst \\ gvs [combine_rel_subst]
                  \\ conj_tac \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                  \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                  \\ qexists_tac ‘vL2’
                  \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’
                  \\ gvs [Lams_split]
                  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
              >- (gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                  \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                  \\ rename1 ‘n < _’
                  \\ rename1 ‘MAP FST xs = MAP FST ys’
                  \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                  \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                  \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                  \\ qexists_tac ‘vL2’
                  \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’ \\ qexists_tac ‘i’
                  \\ gvs [Lams_split]
                  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, LIST_REL_EL_EQN, EL_MAP]))
          \\ disch_then $ qx_choose_then ‘j1’ assume_tac
          \\ Cases_on ‘eval_to (k - 1) (subst_funs list1 x3) = INL Diverge’ \\ gvs []
          >- (qexists_tac ‘0’
              \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
              \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
              \\ gvs []
              \\ Cases_on ‘eval_to (k - 1) (subst_funs list2 y3) = INL Diverge’
              \\ gvs [Abbr ‘list2’, REVERSE_SNOC]
              \\ dxrule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono \\ gvs [])
          \\ qexists_tac ‘j + j1’
          \\ ‘eval_to (j + k) y ≠ INL Diverge’ by gvs []
          \\ dxrule_then (qspec_then ‘j + j1 + k’ assume_tac) eval_to_mono \\ gvs []
          \\ ‘eval_to (j1 + k - 1) (subst_funs list2 y3) ≠ INL Diverge’
            by (strip_tac \\ Cases_on ‘eval_to (k - 1) (subst_funs list1 x3)’ \\ gvs [])
          \\ dxrule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono
          \\ gvs [Abbr ‘list2’, REVERSE_SNOC])
      \\ ‘∃wx' binds'. dest_anyThunk w1 = INR (wx', binds') ∧
                       (v_rel +++ combine_rel) wx wx' ∧
                       MAP FST binds = MAP FST binds' ∧
                       EVERY ok_bind (MAP SND binds) ∧
                       EVERY ok_bind (MAP SND binds') ∧
                       LIST_REL combine_rel (MAP SND binds) (MAP SND binds')’
        by (Cases_on ‘v1’ \\ Cases_on ‘w1’
            \\ gvs [v_rel_def]
            \\ gvs [dest_anyThunk_def, v_rel_def])
      \\ CASE_TAC \\ gs []
      >- (
        qexists_tac ‘j’ \\ simp []
        \\ CASE_TAC \\ gs []
        \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gs [dest_anyThunk_def])
      \\ Cases_on ‘wx'’ \\ gs []
      \\ rename1 ‘combine_rel x1 x2’
      \\ ‘combine_rel (subst_funs binds x1) (subst_funs binds' x2)’
        by (simp [subst_funs_def]
            \\ irule combine_rel_subst
            \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, EVERY2_MAP]
            \\ gvs [LIST_REL_EL_EQN] \\ rw []
            \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
            \\ rename1 ‘n < _’
            \\ ‘EL n (MAP FST binds) = EL n (MAP FST binds')’ by gvs [] \\ gvs [EL_MAP]
            \\ irule v_rel_Recclosure
            \\ gvs [EVERY2_MAP, LAMBDA_PROD]
            \\ gvs [LIST_REL_EL_EQN])
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
    \\ ‘combine_rel (Force (Value v2)) (Force (Value w2))’
      by simp [combine_rel_Force, combine_rel_Value]
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
    gvs [Once combine_rel_def, eval_to_def]
    \\ rename1 ‘combine_rel x y’
    \\ first_x_assum $ qspec_then ‘x’ assume_tac
    \\ Cases_on ‘eval_to k x = INL Type_error’ \\ gs []
    \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
    \\ qexists_tac ‘j’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
    \\ simp [v_rel_def])
  >~ [‘Prim op xs’] >- (
    print_tac "Prim"
    \\ gvs [Once combine_rel_def, eval_to_def]
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
      \\ rename1 ‘combine_rel x y’
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
      \\ rename1 ‘combine_rel x y’
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
*)
QED

Theorem combine_rel_eval:
  combine_rel x y ∧ eval x ≠ INL Type_error ⇒
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
    \\ drule_all_then (qx_choose_then ‘m’ assume_tac) combine_rel_eval_to
    \\ ‘eval_to ( MAX k j) x = eval_to k x’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to (m + MAX k j) y = eval_to j y’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ ‘eval_to j x ≠ INL Type_error’ by gvs []
    \\ drule_all_then (qx_choose_then ‘m’ assume_tac) combine_rel_eval_to \\ gs []
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
  \\ drule_all_then (qx_choose_then ‘m’ assume_tac) combine_rel_eval_to
  \\ Cases_on ‘eval_to (k + m) x’ \\ gvs []
QED

Theorem eval_Lams:
  ∀l e. l ≠ [] ⇒ eval (Lams l e) = INR (Closure (HD l) (Lams (TL l) e))
Proof
  Cases >> gvs [eval_def, eval_to_Lams] >>
  DEEP_INTRO_TAC some_intro >> rw []
QED

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

Theorem eval_App_Values_Rec:
  eval (App (Value (Recclosure (f ++ [(s1, e1); (s2, Lam s3 e2)]) s2)) (Value v))
  = eval (subst (MAP (λ(v,g). (v, Recclosure (f ++ [(s1, e1); (s2, Lam s3 e2)]) v))
                 (f ++ [(s1, e1); (s2, Lam s3 e2)]) ++ [(s3, v)]) e2)
Proof
  Cases_on ‘∀k. eval_to k (subst (MAP (λ(v,g). (v, Recclosure (f ++ [(s1, e1); (s2, Lam s3 e2)]) v))
                                        (f ++ [(s1, e1); (s2, Lam s3 e2)]) ++ [(s3, v)]) e2) = INL Diverge’ >>
  gvs []
  >- (gvs [eval_def, eval_to_def] >> gvs [dest_anyClosure_def, REVERSE_APPEND]) >>
  irule EQ_TRANS >> irule_at Any eval_to_equals_eval >>
  first_assum $ irule_at Any >>
  irule EQ_TRANS >> irule_at (Pos hd) $ GSYM eval_to_equals_eval >>
  gvs [eval_to_def, dest_anyClosure_def, REVERSE_APPEND] >>
  Q.REFINE_EXISTS_TAC ‘SUC num’ >>
  gvs [ADD1] >>
  irule_at Any EQ_REFL >>
  gvs []
QED

Theorem eval_Tick:
  eval (Tick e) = eval (e : thunkLang$exp)
Proof
  Cases_on ‘∀k. eval_to k e = INL Diverge’ >>
  gvs []
  >- (gvs [eval_def, eval_to_def] >> gvs [subst_funs_def, subst_empty]) >>
  irule EQ_TRANS >> irule_at Any eval_to_equals_eval >>
  first_assum $ irule_at Any >>
  irule EQ_TRANS >> irule_at (Pos hd) $ GSYM eval_to_equals_eval >>
  gvs [eval_to_def, subst_funs_def, subst_empty] >>
  Q.REFINE_EXISTS_TAC ‘SUC num’ >>
  gvs [ADD1] >>
  metis_tac []
QED

Theorem v_rel_eval_subst:
  v_rel (Closure s e) (Closure s f) ∧ v_rel v w ∧ eval (subst1 s v e) ≠ INL Type_error ⇒
  ($= +++ v_rel) (eval (subst1 s v e)) (eval (subst1 s w f))
Proof
  gvs [GSYM eval_App_Values]
  \\ rw [] \\ irule combine_rel_eval
  \\ gvs [combine_rel_def]
QED

Theorem combine_rel_apply_closure[local]:
  combine_rel x y ∧
  v_rel v2 w2 ∧
  apply_closure x v2 f ≠ Err ∧
  f (INL Type_error) = Err ∧
  (∀x y. ($= +++ v_rel) x y ∧ f x ≠ Err ⇒ next_rel v_rel combine_rel (f x) (g y)) ⇒
    next_rel v_rel combine_rel (apply_closure x v2 f) (apply_closure y w2 g)
Proof
  rw[apply_closure_def, with_value_def] >>
  `eval x ≠ INL Type_error` by (CCONTR_TAC >> gvs[]) >>
  dxrule_all_then assume_tac combine_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[] >- (CASE_TAC >> gvs[]) >>
  rename1 `eval x = INR v1` >> rename1 `eval y = INR w1`
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [v_rel_def, dest_anyClosure_def]
  >- (
    first_x_assum irule \\ fs []
    \\ irule combine_rel_eval
    \\ conj_tac
    >- (strip_tac \\ gvs [])
    \\ irule combine_rel_subst \\ gs [])
  >- (first_x_assum irule \\ fs []
      \\ irule v_rel_eval_subst \\ fs []
      \\ conj_tac >- (strip_tac \\ gvs [])
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
      \\ irule_at (Pos hd) EQ_REFL
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt $ irule_at Any EQ_REFL \\ gvs []
      \\ rpt $ irule_at Any EQ_REFL \\ gvs [])
  >- (first_x_assum irule \\ fs []
      \\ irule v_rel_eval_subst \\ fs []
      \\ conj_tac >- (strip_tac \\ gvs [])
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj1_tac
      \\ irule_at (Pos hd) EQ_REFL
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt $ irule_at Any EQ_REFL \\ gvs []
      \\ rpt $ irule_at Any EQ_REFL \\ gvs [])
  >- (first_x_assum irule \\ fs []
      \\ irule v_rel_eval_subst \\ fs []
      \\ conj_tac >- (strip_tac \\ gvs [])
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
      \\ irule_at (Pos hd) EQ_REFL
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt $ irule_at Any EQ_REFL \\ gvs []
      \\ rpt $ irule_at Any EQ_REFL \\ gvs [])
  >- (first_x_assum irule \\ fs []
      \\ irule v_rel_eval_subst \\ fs []
      \\ conj_tac >- (strip_tac \\ gvs [])
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
      \\ irule_at (Pos hd) EQ_REFL
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ rpt (‘∀l1 l2 e1 e2. l1=l2 ∧ e1=e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum $ irule_at Any)
      \\ gvs []
      \\ rpt $ irule_at Any EQ_REFL \\ gvs []
      \\ rpt $ irule_at Any EQ_REFL \\ gvs [])
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘combine_rel x0 _’ mp_tac
      \\ rw [Once combine_rel_cases] \\ gs []
      \\ drule_then assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
      \\ gvs [EVERY_EL, EL_MAP]
      \\ first_x_assum irule \\ fs []
      \\ irule combine_rel_eval
      \\ conj_tac >- (strip_tac \\ gvs [])
      \\ irule combine_rel_subst
      \\ simp [EVERY2_MAP, LAMBDA_PROD, v_rel_def, MAP_MAP_o, combinTheory.o_DEF,
               GSYM FST_THM]
      \\ gvs [LIST_REL_EL_EQN] \\ rw []
      \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [] \\ disj1_tac
      \\ gvs [EVERY_EL, EL_MAP]
      \\ rw [] \\ first_x_assum $ drule_then assume_tac
      >- (rename1 ‘EL n2 _ = (_, _)’
          \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP])
      \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gvs [])

  >- (Cases_on ‘vL2 = []’ \\ gvs [REVERSE_APPEND]
      \\ rw [] \\ gvs [Lams_split]
      >- (first_x_assum irule
          \\ conj_tac
          >- (qmatch_goalsub_abbrev_tac ‘_ (eval (subst (MAP fun list1 ++
                                                         list2 ++ list3) expr)) ≠ _’
              \\ gvs [])
          \\ irule combine_rel_eval
          \\ conj_tac
          >- (strip_tac \\ gvs [])
          \\ irule combine_rel_subst
          \\ rpt $ conj_tac
          >- gvs [MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
          >- (irule combine_rel_Lams \\ irule combine_rel_Apps
              \\ gvs [LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP, EL_MAP2, combine_rel_def]
              \\ rw [combine_rel_def])
          \\ gvs [LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP, EL_MAP2] \\ rw []
          >- (pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
              \\ rename1 ‘MAP FST xs = MAP FST ys’
              \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
              \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
              \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
              \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          >- (rename1 ‘MAP FST xs = MAP FST ys’
              \\ Cases_on ‘n - LENGTH ys’ \\ gvs []
              >- (gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                  \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                  \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
                  \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
                  \\ gvs [LIST_REL_EL_EQN, EL_MAP])
              \\ rename1 ‘n - LENGTH _ = SUC n2’
              \\ Cases_on ‘n2’ \\ gvs []
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
              \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
              \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
              \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          \\ gvs [NOT_LESS]
          \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [])
      >- (first_x_assum irule
          \\ conj_tac
          >- (qmatch_goalsub_abbrev_tac ‘_ (eval (subst (MAP fun list1 ++
                                                         list2 ++ list3) expr)) ≠ _’
              \\ gvs [])
          \\ irule combine_rel_eval
          \\ conj_tac
          >- (strip_tac \\ gvs [])
          \\ irule combine_rel_subst
          \\ rpt $ conj_tac
          >- gvs [MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
          >- (irule combine_rel_Lams \\ irule combine_rel_Apps
              \\ gvs [LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP, EL_MAP2, combine_rel_def]
              \\ rw [combine_rel_def])
          \\ gvs [LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP, EL_MAP2] \\ rw []
          >- (pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
              \\ rename1 ‘MAP FST xs = MAP FST ys’
              \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
              \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
              \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
              \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          >- (rename1 ‘MAP FST xs = MAP FST ys’
              \\ Cases_on ‘n - LENGTH ys’ \\ gvs []
              >- (gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                  \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                  \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
                  \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
                  \\ gvs [LIST_REL_EL_EQN, EL_MAP])
              \\ rename1 ‘n - LENGTH _ = SUC n2’
              \\ Cases_on ‘n2’ \\ gvs []
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
              \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
              \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
              \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          \\ gvs [NOT_LESS]
          \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [])
      >- (first_x_assum irule \\ fs []
          \\ Cases_on ‘vL1’ \\ gvs []
          \\ rename1 ‘Lam hd1 (Lams vL1 (Apps (Var _) _))’
          \\ Cases_on ‘vL1 = []’ \\ gvs []
          >- (Cases_on ‘bL2’ \\ gvs [] \\ Cases_on ‘vL2’
              \\ gvs [subst_def, GSYM LAMBDA_PROD, FILTER_T]
              \\ drule_then assume_tac combine_rel_freevars
              \\ gvs [subst_def, REVERSE_APPEND, subst_APPEND, subst1_notin_frees, eval_Tick, eval_App_Values_Rec]
              \\ irule combine_rel_eval
              \\ conj_tac >- (strip_tac \\ gvs [])
              \\ gvs [combine_rel_def]
              \\ irule combine_rel_subst \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
              \\ conj_tac
              >- (irule combine_rel_subst \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                  \\ qpat_x_assum ‘combine_rel _ _ ’ $ irule_at Any
                  \\ rename1 ‘Lam h (App (Var v1) (Var h))’
                  \\ qexists_tac ‘[h]’ \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ simp []
                  \\ qexists_tac ‘[F]’ \\ qexists_tac ‘[F]’ \\ simp [])
              \\ rename1 ‘MAP FST xs = MAP FST ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
              \\ rw [] \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gvs []
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
              \\ qpat_x_assum ‘combine_rel _ _ ’ $ irule_at Any
              \\ rename1 ‘Lam h (App (Var v1) (Var h))’
              \\ qexists_tac ‘[h]’ \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ simp []
              \\ qexists_tac ‘[F]’ \\ qexists_tac ‘[F]’ \\ simp [LIST_REL_EL_EQN, EL_MAP])
          \\ gvs [eval_Lams, subst_Lams]
          \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
          \\ rename1 ‘MAP FST xs = MAP FST ys’
          \\ qexists_tac ‘xs’ \\ qexists_tac ‘ys’
          \\ qexists_tac ‘v1’ \\ qexists_tac ‘s’ \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’
          \\ qexists_tac ‘[hd1]’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
          \\ qexists_tac ‘bL2’ \\ qexists_tac ‘[HD bL3]’ \\ qexists_tac ‘TL bL3’
          \\ qexists_tac ‘i’ \\ qexists_tac ‘[v2]’ \\ qexists_tac ‘[w2]’
          \\ gvs []
          \\ Cases_on ‘bL3’ \\ gvs [subst_def, subst_Apps]
          \\ rpt $ conj_tac
          >- (AP_THM_TAC \\ AP_TERM_TAC
              \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum irule
              \\ gvs [subst_def]
              \\ rpt (‘∀a b c d. a = c ∧ b = d ⇒ a ++ b = c ++ d : exp list’ by gvs []
                      \\ pop_assum $ irule_at Any)
              \\ gvs [FILTER_APPEND, REVERSE_APPEND]
              \\ rpt $ conj_tac
              >- (Cases_on ‘h’ \\ gvs [subst_def, REVERSE_APPEND]
                  >- (conj_tac
                      >- (IF_CASES_TAC \\ gvs [])
                      \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def]
                      \\ gen_tac \\ strip_tac
                      \\ gvs [REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER, ALOOKUP_APPEND]
                      \\ drule_then assume_tac EL_MEM
                      \\ gvs [MEM_FILTER]
                      \\ dxrule_then assume_tac MEM_SND \\ gvs [MAP_ZIP]
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs [])
                  \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def]
                  \\ gen_tac \\ strip_tac
                  \\ gvs [REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER, ALOOKUP_APPEND]
                  \\ drule_then assume_tac EL_MEM
                  \\ gvs [MEM_FILTER]
                  \\ dxrule_then assume_tac MEM_SND \\ gvs [MAP_ZIP]
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs [])
              >- (Cases_on ‘b2’ \\ gvs [subst_def, REVERSE_APPEND]
                  \\ IF_CASES_TAC \\ gvs [])
              >- (irule LIST_EQ \\ gvs [subst_def, EL_MAP2, EL_MAP]
                  \\ gen_tac \\ rename1 ‘n < _ ∧ _ < _ ⇒ _’ \\ strip_tac
                  \\ rename1 ‘¬EL _ (b2::bL2)’ \\ Cases_on ‘EL n bL2’
                  \\ Cases_on ‘MEM s vL1’
                  \\ gvs [subst_def, EL_MEM, GSYM FILTER_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND, ALOOKUP_FILTER]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM])
              >- (IF_CASES_TAC \\ gvs [Lams_split]
                  \\ IF_CASES_TAC \\ gvs []))
          >- (AP_THM_TAC \\ AP_TERM_TAC
              \\ gvs []
              \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum irule
              \\ gvs [subst_def]
              \\ rpt (‘∀a b c d. a = c ∧ b = d ⇒ a ++ b = c ++ d : exp list’ by gvs []
                      \\ pop_assum $ irule_at Any)
              \\ gvs [FILTER_APPEND, REVERSE_APPEND]
              \\ rpt $ conj_tac
              >- (Cases_on ‘h’ \\ gvs [subst_def, REVERSE_APPEND]
                  >- (conj_tac
                      >- (IF_CASES_TAC \\ gvs [])
                      \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def]
                      \\ gen_tac \\ strip_tac
                      \\ gvs [REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER, ALOOKUP_APPEND]
                      \\ drule_then assume_tac EL_MEM
                      \\ gvs [MEM_FILTER]
                      \\ dxrule_then assume_tac MEM_SND \\ gvs [MAP_ZIP]
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs [])
                  \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def]
                  \\ gen_tac \\ strip_tac
                  \\ gvs [REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER, ALOOKUP_APPEND]
                  \\ drule_then assume_tac EL_MEM
                  \\ gvs [MEM_FILTER]
                  \\ dxrule_then assume_tac MEM_SND \\ gvs [MAP_ZIP]
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs [])
              >- (‘∀l1 l2 l3. MAP (subst l1) (MAP2 (λb e. if b then Force e else e) l2 l3)
                              = MAP2 (λb e. if b then Force e else e) l2 (MAP (subst l1) l3)’
                    by (rpt $ pop_assum kall_tac
                        \\ gen_tac \\ Induct \\ gvs []
                        \\ Cases \\ Cases \\ gvs [subst_def])
                  \\ gvs [] \\ pop_assum kall_tac
                  \\ AP_TERM_TAC \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
                  \\ Cases_on ‘b2’ \\ gvs [subst_def, REVERSE_APPEND]
                  >- (conj_tac
                      >- (IF_CASES_TAC \\ gvs [])
                      \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2, subst_def]
                      \\ gen_tac \\ rename1 ‘n < _ ∧ _ < _ ⇒ _’ \\ strip_tac
                      \\ rename1 ‘¬EL _ (b2::bL2)’ \\ Cases_on ‘EL n bL2’
                      \\ Cases_on ‘MEM s vL1’
                      \\ gvs [subst_def, EL_MEM, GSYM FILTER_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND, ALOOKUP_FILTER]
                      \\ IF_CASES_TAC \\ gvs [EL_MEM]
                      \\ IF_CASES_TAC \\ gvs [EL_MEM]
                      \\ IF_CASES_TAC \\ gvs [EL_MEM])
                  \\ conj_tac
                  >- (IF_CASES_TAC \\ gvs [])
                  \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2, subst_def]
                  \\ gen_tac \\ rename1 ‘n < _ ∧ _ < _ ⇒ _’ \\ strip_tac
                  \\ rename1 ‘¬EL _ (b2::bL2)’ \\ Cases_on ‘EL n bL2’
                  \\ Cases_on ‘MEM s vL1’
                  \\ gvs [subst_def, EL_MEM, GSYM FILTER_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND, ALOOKUP_FILTER]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM])
              \\ gvs [GSYM LAMBDA_PROD, FILTER_T, SNOC_APPEND, Lams_split]
              \\ irule EQ_TRANS \\ irule_at (Pos hd) $ GSYM subst_remove
              \\ Q.REFINE_EXISTS_TAC ‘{_}’ \\ gvs [FILTER_FILTER, LAMBDA_PROD, FILTER_APPEND]
              \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars \\ gvs []
              \\ first_x_assum $ irule_at Any \\ gvs []
              \\ AP_THM_TAC \\ AP_TERM_TAC \\ rw [] \\ gvs [])
          >- rw []
          >- (IF_CASES_TAC \\ gvs [])
          >- (IF_CASES_TAC \\ gvs [])
          >- (qpat_x_assum ‘EVERY _ (MAP SND _)’ mp_tac
              \\ IF_CASES_TAC \\ gvs []))
      \\ rename1 ‘MAP FST xs = MAP FST ys’
      \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP]
            \\ ‘∀n. n < LENGTH ys ⇒ EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
            \\ gvs [EL_MAP])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘combine_rel x0 _’ mp_tac
      \\ rw [Once combine_rel_cases] \\ gs []
      \\ first_x_assum irule \\ fs []
      \\ irule combine_rel_eval
      \\ conj_tac >- (strip_tac \\ gvs [])
      \\ irule combine_rel_subst \\ gvs []
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
              LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP]
      \\ rw []
      >- (rename1 ‘n < _’
          \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
          \\ pairarg_tac \\ gs [] \\ pairarg_tac
          \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
          \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
          \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
          \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
          \\ gvs [LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
      \\ rename1 ‘n < _’
      \\ Cases_on ‘n - LENGTH ys’ \\ gvs []
      >- (gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
          \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
          \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
          \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
          \\ gvs [LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
      \\ rename1 ‘n - LENGTH ys = SUC n2’ \\ Cases_on ‘n2’
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
      \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
      \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
      \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])

  >- (Cases_on ‘vL2 = []’ \\ gvs [REVERSE_APPEND]
      \\ rw [] \\ gvs [Lams_split]
      >- (first_x_assum irule
          \\ conj_tac
          >- (qmatch_goalsub_abbrev_tac ‘_ (eval (subst (MAP fun list1 ++
                                                         list2 ++ list3) expr)) ≠ _’
              \\ gvs [])
          \\ irule combine_rel_eval
          \\ conj_tac
          >- (strip_tac \\ gvs [])
          \\ irule combine_rel_subst
          \\ rpt $ conj_tac
          >- gvs [MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
          >- (irule combine_rel_Lams \\ irule combine_rel_Apps
              \\ gvs [LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP, EL_MAP2, combine_rel_def]
              \\ rw [combine_rel_def])
          \\ gvs [LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP, EL_MAP2] \\ rw []
          >- (pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
              \\ rename1 ‘MAP FST xs = MAP FST ys’
              \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
              \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
              \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
              \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          >- (rename1 ‘MAP FST xs = MAP FST ys’
              \\ Cases_on ‘n - LENGTH ys’ \\ gvs []
              >- (gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                  \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                  \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
                  \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
                  \\ gvs [LIST_REL_EL_EQN, EL_MAP])
              \\ rename1 ‘n - LENGTH _ = SUC n2’
              \\ Cases_on ‘n2’ \\ gvs []
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
              \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
              \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
              \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          \\ gvs [NOT_LESS]
          \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [])
      >- (first_x_assum irule
          \\ conj_tac
          >- (qmatch_goalsub_abbrev_tac ‘_ (eval (subst (MAP fun list1 ++
                                                         list2 ++ list3) expr)) ≠ _’
              \\ gvs [])
          \\ irule combine_rel_eval
          \\ conj_tac
          >- (strip_tac \\ gvs [])
          \\ irule combine_rel_subst
          \\ rpt $ conj_tac
          >- gvs [MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
          >- (irule combine_rel_Lams \\ irule combine_rel_Apps
              \\ gvs [LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP, EL_MAP2, combine_rel_def]
              \\ rw [combine_rel_def])
          \\ gvs [LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP, EL_MAP2] \\ rw []
          >- (pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
              \\ rename1 ‘MAP FST xs = MAP FST ys’
              \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
              \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
              \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
              \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          >- (rename1 ‘MAP FST xs = MAP FST ys’
              \\ Cases_on ‘n - LENGTH ys’ \\ gvs []
              >- (gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                  \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
                  \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
                  \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
                  \\ gvs [LIST_REL_EL_EQN, EL_MAP])
              \\ rename1 ‘n - LENGTH _ = SUC n2’
              \\ Cases_on ‘n2’ \\ gvs []
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
              \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
              \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
              \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          \\ gvs [NOT_LESS]
          \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [])
      >- (first_x_assum irule \\ fs []
          \\ Cases_on ‘vL1’ \\ gvs []
          \\ rename1 ‘Lam hd1 (Lams vL1 (Apps (Var _) _))’
          \\ Cases_on ‘vL1 = []’ \\ gvs []
          >- (Cases_on ‘bL2’ \\ gvs [] \\ Cases_on ‘vL2’ \\ gvs [subst_def, GSYM LAMBDA_PROD, FILTER_T]
              \\ drule_then assume_tac combine_rel_freevars
              \\ gvs [subst_def, REVERSE_APPEND, subst_APPEND, subst1_notin_frees, eval_Tick, eval_App_Values_Rec]
              \\ irule combine_rel_eval
              \\ conj_tac >- (strip_tac \\ gvs [])
              \\ gvs [combine_rel_def]
              \\ irule combine_rel_subst \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
              \\ conj_tac
              >- (irule combine_rel_subst \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                  \\ qpat_x_assum ‘combine_rel _ _ ’ $ irule_at Any
                  \\ rename1 ‘Lam h (App (Var v1) (Var h))’
                  \\ qexists_tac ‘[h]’ \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ gvs []
                   \\ qexists_tac ‘[F]’ \\ qexists_tac ‘[F]’ \\ gvs []
                  \\ Cases \\ gvs [])
              \\ rename1 ‘MAP FST xs = MAP FST ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
              \\ rw [] \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gvs []
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
              \\ qpat_x_assum ‘combine_rel _ _ ’ $ irule_at Any
              \\ rename1 ‘Lam h (App (Var v1) (Var h))’
              \\ qexists_tac ‘[h]’ \\ Q.REFINE_EXISTS_TAC ‘[_]’ \\ gvs []
              \\ qexists_tac ‘[F]’ \\ qexists_tac ‘[F]’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
              \\ Cases \\ gvs [])
          \\ gvs [eval_Lams, subst_Lams]
          \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
          \\ rename1 ‘MAP FST xs = MAP FST ys’
          \\ qexists_tac ‘xs’ \\ qexists_tac ‘ys’
          \\ qexists_tac ‘v1’ \\ qexists_tac ‘s’ \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’
          \\ qexists_tac ‘[hd1]’ \\ qexists_tac ‘vL1’ \\ qexists_tac ‘vL2’
          \\ qexists_tac ‘bL2’ \\ qexists_tac ‘[HD bL3]’ \\ qexists_tac ‘TL bL3’
          \\ qexists_tac ‘i’ \\ qexists_tac ‘[v2]’ \\ qexists_tac ‘[w2]’
          \\ gvs []
          \\ Cases_on ‘bL3’ \\ gvs [subst_def, subst_Apps]
          \\ rpt $ conj_tac
          >- (AP_THM_TAC \\ AP_TERM_TAC
              \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum irule
              \\ gvs [subst_def]
              \\ rpt (‘∀a b c d. a = c ∧ b = d ⇒ a ++ b = c ++ d : exp list’ by gvs []
                      \\ pop_assum $ irule_at Any)
              \\ gvs [FILTER_APPEND, REVERSE_APPEND]
              \\ rpt $ conj_tac
              >- (Cases_on ‘h’ \\ gvs [subst_def, REVERSE_APPEND]
                  >- (conj_tac
                      >- (IF_CASES_TAC \\ gvs [])
                      \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def]
                      \\ gen_tac \\ strip_tac
                      \\ gvs [REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER, ALOOKUP_APPEND]
                      \\ drule_then assume_tac EL_MEM
                      \\ gvs [MEM_FILTER]
                      \\ dxrule_then assume_tac MEM_SND \\ gvs [MAP_ZIP]
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs [])
                  \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def]
                  \\ gen_tac \\ strip_tac
                  \\ gvs [REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER, ALOOKUP_APPEND]
                  \\ drule_then assume_tac EL_MEM
                  \\ gvs [MEM_FILTER]
                  \\ dxrule_then assume_tac MEM_SND \\ gvs [MAP_ZIP]
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs [])
              >- (Cases_on ‘b2’ \\ gvs [subst_def, REVERSE_APPEND]
                  \\ IF_CASES_TAC \\ gvs [])
              >- (irule LIST_EQ \\ gvs [subst_def, EL_MAP2, EL_MAP]
                  \\ gen_tac \\ rename1 ‘n < _ ∧ _ < _ ⇒ _’ \\ strip_tac
                  \\ rename1 ‘¬EL _ (b2::bL2)’ \\ Cases_on ‘EL n bL2’
                  \\ Cases_on ‘MEM s vL1’
                  \\ gvs [subst_def, EL_MEM, GSYM FILTER_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND, ALOOKUP_FILTER]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM])
              >- (IF_CASES_TAC \\ gvs [Lams_split]
                  \\ IF_CASES_TAC \\ gvs [EL_MAP]))
          >- (AP_THM_TAC \\ AP_TERM_TAC
              \\ gvs []
              \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
              \\ pop_assum irule
              \\ gvs [subst_def]
              \\ rpt (‘∀a b c d. a = c ∧ b = d ⇒ a ++ b = c ++ d : exp list’ by gvs []
                      \\ pop_assum $ irule_at Any)
              \\ gvs [FILTER_APPEND, REVERSE_APPEND]
              \\ rpt $ conj_tac
              >- (Cases_on ‘h’ \\ gvs [subst_def, REVERSE_APPEND]
                  >- (conj_tac
                      >- (IF_CASES_TAC \\ gvs [])
                      \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def]
                      \\ gen_tac \\ strip_tac
                      \\ gvs [REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER, ALOOKUP_APPEND]
                      \\ drule_then assume_tac EL_MEM
                      \\ gvs [MEM_FILTER]
                      \\ dxrule_then assume_tac MEM_SND \\ gvs [MAP_ZIP]
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs []
                      \\ IF_CASES_TAC \\ gvs [])
                  \\ irule LIST_EQ \\ gvs [EL_MAP, subst_def]
                  \\ gen_tac \\ strip_tac
                  \\ gvs [REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER, ALOOKUP_APPEND]
                  \\ drule_then assume_tac EL_MEM
                  \\ gvs [MEM_FILTER]
                  \\ dxrule_then assume_tac MEM_SND \\ gvs [MAP_ZIP]
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs [])
              >- (‘∀l1 l2 l3. MAP (subst l1) (MAP2 (λb e. if b then Force e else e) l2 l3)
                              = MAP2 (λb e. if b then Force e else e) l2 (MAP (subst l1) l3)’
                    by (rpt $ pop_assum kall_tac
                        \\ gen_tac \\ Induct \\ gvs []
                        \\ Cases \\ Cases \\ gvs [subst_def])
                  \\ gvs [] \\ pop_assum kall_tac
                  \\ AP_TERM_TAC \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
                  \\ Cases_on ‘b2’ \\ gvs [subst_def, REVERSE_APPEND]
                  >- (conj_tac
                      >- (IF_CASES_TAC \\ gvs [])
                      \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2, subst_def]
                      \\ gen_tac \\ rename1 ‘n < _ ∧ _ < _ ⇒ _’ \\ strip_tac
                      \\ rename1 ‘¬EL _ (b2::bL2)’ \\ Cases_on ‘EL n bL2’
                      \\ Cases_on ‘MEM s vL1’
                      \\ gvs [subst_def, EL_MEM, GSYM FILTER_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND, ALOOKUP_FILTER]
                      \\ IF_CASES_TAC \\ gvs [EL_MEM]
                      \\ IF_CASES_TAC \\ gvs [EL_MEM]
                      \\ IF_CASES_TAC \\ gvs [EL_MEM])
                  \\ conj_tac
                  >- (IF_CASES_TAC \\ gvs [])
                  \\ irule LIST_EQ \\ gvs [EL_MAP, EL_MAP2, subst_def]
                  \\ gen_tac \\ rename1 ‘n < _ ∧ _ < _ ⇒ _’ \\ strip_tac
                  \\ rename1 ‘¬EL _ (b2::bL2)’ \\ Cases_on ‘EL n bL2’
                  \\ Cases_on ‘MEM s vL1’
                  \\ gvs [subst_def, EL_MEM, GSYM FILTER_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND, ALOOKUP_FILTER]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM])

              >- (gvs [GSYM LAMBDA_PROD, FILTER_T, SNOC_APPEND, Lams_split]
                  \\ irule EQ_TRANS \\ irule_at (Pos hd) $ GSYM subst_remove
                  \\ Q.REFINE_EXISTS_TAC ‘{_}’ \\ gvs [FILTER_FILTER, LAMBDA_PROD, FILTER_APPEND]
                  \\ qspecl_then [‘x1’, ‘x2’] assume_tac combine_rel_freevars \\ gvs []
                  \\ first_x_assum $ irule_at Any \\ gvs []
                  \\ AP_THM_TAC \\ AP_TERM_TAC \\ rw [] \\ gvs [EL_MAP]
                  \\ Cases_on ‘i’ \\ gvs [EL_MAP])

              >- (Cases_on ‘i’ \\ gvs [GSYM LAMBDA_PROD, FILTER_T, REVERSE_APPEND]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]
                  \\ gvs [ALOOKUP_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]
                  \\ IF_CASES_TAC \\ gvs []
                  \\ IF_CASES_TAC \\ gvs [EL_MAP, EL_MEM]
                  \\ IF_CASES_TAC \\ gvs [EL_MEM]))
          >- rw []
          >- (IF_CASES_TAC \\ gvs [])
          >- (IF_CASES_TAC \\ gvs [])
          >- (qpat_x_assum ‘EVERY _ (MAP SND _)’ mp_tac
              \\ IF_CASES_TAC \\ gvs []))
      \\ rename1 ‘MAP FST xs = MAP FST ys’
      \\ ‘OPTREL combine_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP]
            \\ ‘∀n. n < LENGTH ys ⇒ EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
            \\ gvs [EL_MAP])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘combine_rel x0 _’ mp_tac
      \\ rw [Once combine_rel_cases] \\ gs []
      \\ first_x_assum irule \\ fs []
      \\ irule combine_rel_eval
      \\ conj_tac >- (strip_tac \\ gvs [])
      \\ irule combine_rel_subst \\ gvs []
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
              LIST_REL_EL_EQN, EL_APPEND_EQN, EL_MAP]
      \\ rw []
      >- (rename1 ‘n < _’
          \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
          \\ pairarg_tac \\ gs [] \\ pairarg_tac
          \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
          \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
          \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
          \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
          \\ gvs [LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
      \\ rename1 ‘n < _’
      \\ Cases_on ‘n - LENGTH ys’ \\ gvs []
      >- (gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
          \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
          \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
          \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
          \\ gvs [LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
      \\ rename1 ‘n - LENGTH ys = SUC n2’ \\ Cases_on ‘n2’
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
      \\ qexists_tac ‘x1’ \\ qexists_tac ‘x2’ \\ qexists_tac ‘vL1’
      \\ qexists_tac ‘vL2’ \\ qexists_tac ‘bL2’ \\ qexists_tac ‘bL3’
      \\ qexists_tac ‘i’ \\ gvs [Lams_split, EL_MAP]
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
QED

Theorem combine_rel_rel_ok[local]:
  rel_ok F v_rel combine_rel
Proof
  rw [rel_ok_def, v_rel_def, combine_rel_def]
  \\ rw [combine_rel_apply_closure]
QED

Theorem combine_rel_sim_ok[local]:
  sim_ok F v_rel combine_rel
Proof
  rw [sim_ok_def, combine_rel_eval, combine_rel_subst]
QED

Theorem combine_rel_semantics:
  combine_rel x y ∧
  safe_itree (semantics x Done []) ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics \\ gs []
  \\ first_assum (irule_at Any)
  \\ qexists_tac ‘F’ \\ gs []
  \\ irule_at Any combine_rel_rel_ok
  \\ irule_at Any combine_rel_sim_ok
QED

val _ = export_theory ();
