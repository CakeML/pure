(*
 Relation to rewrite function definitions to remove Delay
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory;

val _ = new_theory "thunk_Let_Lam_Forced";

Inductive force_arg_rel:
[~Var:]
  (∀n. force_arg_rel (Var n) (Var n))
[~Value:]
  (∀v w.
     v_rel v w ⇒
       force_arg_rel (Value v) (Value w))
[~Prim:]
  (∀op xs ys.
     LIST_REL force_arg_rel xs ys ⇒
       force_arg_rel (Prim op xs) (Prim op ys))
[~Monad:]
  (∀mop xs ys.
     LIST_REL force_arg_rel xs ys ⇒
       force_arg_rel (Monad mop xs) (Monad mop ys))
[~App:]
  (∀f g x y.
     force_arg_rel f g ∧
     force_arg_rel x y ⇒
       force_arg_rel (App f x) (App g y))
[~Lam:]
  (∀s x y.
     force_arg_rel x y ⇒
       force_arg_rel (Lam s x) (Lam s y))
[~Letrec:]
  (∀f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL force_arg_rel (MAP SND f) (MAP SND g) ∧
     force_arg_rel x y ⇒
     force_arg_rel (Letrec f x) (Letrec g y))
[~Letrec_Lam_Force:]
  (∀f g x1 y1 x2 y2 v1 v2 vL1 vL2 s s2 i.
     MAP FST f = MAP FST g ∧
     ALL_DISTINCT (MAP FST f) ∧
     i < LENGTH f ∧
     EL i f = (v1, Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) x2)) ∧
     SND (EL i g) = Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) y2) ∧
     ALL_DISTINCT (s2::vL1 ++ s::vL2) ∧
     ¬MEM v2 (MAP FST f++ s2::vL1 ++ s::vL2) ∧
     s ∉ freevars x2 ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL force_arg_rel (MAP SND f) (MAP SND g) ∧
     EVERY (λe. v2 ∉ freevars e) (MAP SND f) ∧ v2 ∉ freevars x1 ∧ v2 ∉ freevars x2 ∧
     force_arg_rel x1 y1 ∧ force_arg_rel x2 y2 ⇒
     force_arg_rel (Letrec f x1)
             (Letrec (SNOC (v2, Lams (vL1 ++ s2::vL2) y2)
                      (LUPDATE (v1, Lams (vL1 ++ s::vL2)
                             (Apps (Var v2) (MAP Var vL1 ++ Tick (Force (Var s))::MAP Var vL2)))
                       i g)) y1))
[~Letrec_Lam_Force2:]
  (∀f g x1 y1 x2 y2 v1 v2 vL1 vL2 s s2 i.
     MAP FST f = MAP FST g ∧
     ALL_DISTINCT (MAP FST f) ∧
     i < LENGTH f ∧
     EL i f = (v1, Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) x2)) ∧
     SND (EL i g) = Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) y2) ∧
     ALL_DISTINCT (s2::vL1 ++ s::vL2) ∧
     ¬MEM v2 (MAP FST f++ s2::vL1 ++ s::vL2) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL force_arg_rel (MAP SND f) (MAP SND g) ∧
     EVERY (λe. v2 ∉ freevars e) (MAP SND f) ∧ v2 ∉ freevars x1 ∧ v2 ∉ freevars x2 ∧
     force_arg_rel x1 y1 ∧ force_arg_rel x2 y2 ⇒
     force_arg_rel (Letrec f x1)
             (Letrec (SNOC (v2, Lams (s::vL1 ++ s2::vL2) y2)
                      (LUPDATE (v1, Lams (vL1 ++ s::vL2)
                   (Apps (Var v2) (Var s::MAP Var vL1 ++ Tick (Force (Var s))::MAP Var vL2)))
                       i g)) y1))
[~Let:]
  (∀opt x1 y1 x2 y2.
     force_arg_rel x1 x2 ∧
     force_arg_rel y1 y2 ⇒
       force_arg_rel (Let opt x1 y1) (Let opt x2 y2))
[~Let_Lams_Force_Var:]
  (∀v1 v2 vL1 vL2 s s2 x1 x2 y1 y2.
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧
     ALL_DISTINCT (vL1 ++ s::vL2) ∧
     ¬MEM v2 (vL1 ++ s::vL2) ∧ ¬MEM s2 (vL1 ++ s::vL2) ∧
     v2 ≠ v1 ∧ v2 ≠ s2 ∧ s ≠ s2 ∧
     s ∉ freevars x1 ∧
     force_arg_rel x1 x2 ∧ force_arg_rel y1 y2 ⇒
     force_arg_rel (Let (SOME v1)
              (Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) x1))
              y1)
             (Let (SOME v2)
              (Lams (vL1 ++ s2::vL2) x2)
              (Let (SOME v1)
                  (Lams (vL1 ++ s::vL2) (Apps (Var v2) (MAP Var vL1 ++ Tick (Force (Var s))::MAP Var vL2))) y2)))
[~Let_Lams_Force_Var2:]
  (∀v1 v2 vL1 vL2 s s2 x1 x2 y1 y2.
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧
     ALL_DISTINCT (vL1 ++ s::vL2) ∧
     ¬MEM v2 (vL1 ++ s::vL2) ∧ ¬MEM s2 (vL1 ++ s::vL2) ∧
     v2 ≠ v1 ∧ v2 ≠ s2 ∧ s ≠ s2 ∧
     force_arg_rel x1 x2 ∧ force_arg_rel y1 y2 ⇒
     force_arg_rel (Let (SOME v1)
              (Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) x1))
              y1)
             (Let (SOME v2)
              (Lams (s::vL1 ++ s2::vL2) x2)
              (Let (SOME v1)
               (Lams (vL1 ++ s::vL2) (Apps (Var v2) (Var s::MAP Var vL1 ++ Tick (Force (Var s))::MAP Var vL2)))
                 y2)))
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     force_arg_rel x1 x2 ∧
     force_arg_rel y1 y2 ∧
     force_arg_rel z1 z2 ⇒
       force_arg_rel (If x1 y1 z1) (If x2 y2 z2))
[~Delay:]
  (∀x y.
     force_arg_rel x y ⇒
       force_arg_rel (Delay x) (Delay y))
[~Force:]
  (∀x y.
     force_arg_rel x y ⇒
     force_arg_rel (Force x) (Force y))
[~MkTick:]
  (∀x y. force_arg_rel x y ⇒ force_arg_rel (MkTick x) (MkTick y))
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws))
[v_rel_Monadic:]
  (∀s vs ws.
     LIST_REL force_arg_rel vs ws ⇒
       v_rel (Monadic s vs) (Monadic s ws))
[v_rel_Closure:]
  (∀s x y.
     force_arg_rel x y ⇒
       v_rel (Closure s x) (Closure s y))
[v_rel_Closure_Force_TL:]
  (∀eL1 eL2 vL1 vL2 vL3 s s2 x y.
     ALL_DISTINCT (s2::vL1 ++ vL2 ++ s::vL3) ∧
     LENGTH vL1 = LENGTH eL1 ∧
     LIST_REL v_rel eL1 eL2 ∧
     s ∉ freevars x ∧
     force_arg_rel x y ⇒
     v_rel (Closure (HD (SNOC s vL2))
            (Lams (TL (vL2++s::vL3)) (subst (ZIP (vL1, eL1)) (Let (SOME s2) (Force (Var s)) x))))
           (Closure (HD (SNOC s vL2)) (Lams (TL (vL2 ++ s::vL3))
                                       (Apps (Value (Closure (HD (vL1++vL2++s2::vL3))
                                                              (Lams (TL (vL1++vL2++s2::vL3)) y)))
                                        (MAP Value eL2 ++ MAP Var vL2 ++ (Tick (Force (Var s)))::MAP Var vL3)))))
[v_rel_Closure_Force_TL2:]
  (∀eL1 eL2 vL1 vL2 vL3 s s2 x y.
     ALL_DISTINCT (s2::vL1 ++ vL2 ++ s::vL3) ∧
     LENGTH vL1 = LENGTH eL1 ∧
     LIST_REL v_rel eL1 eL2 ∧
     force_arg_rel x y ⇒
     v_rel (Closure (HD (SNOC s vL2))
            (Lams (TL (vL2++s::vL3)) (subst (ZIP (vL1, eL1)) (Let (SOME s2) (Force (Var s)) x))))
           (Closure (HD (SNOC s vL2)) (Lams (TL (vL2 ++ s::vL3))
                                       (Apps (Value (Closure s
                                                              (Lams (vL1++vL2++s2::vL3) y)))
                                        (Var s::MAP Value eL2 ++ MAP Var vL2 ++
                                           (Tick (Force (Var s)))::MAP Var vL3)))))
[v_rel_Closure_Force_HD:]
  (∀eL1 eL1' eL2 eL2' e e' vL1 vL2 vL3 s s2 x y.
     ALL_DISTINCT (s2::vL1 ++ vL2 ++ s::vL3) ∧
     LENGTH vL1 = LENGTH eL1 ∧ LENGTH vL2 = LENGTH eL2 ∧
     LIST_REL v_rel eL1 eL1' ∧ LIST_REL v_rel eL2 eL2' ∧ v_rel e e' ∧
     vL3 ≠ [] ∧
     s ∉ freevars x ∧
     force_arg_rel x y ⇒
     v_rel (Closure (HD vL3)
            (Lams (TL vL3) (subst (ZIP (vL1 ++ vL2, eL1 ++ eL2)) (Let (SOME s2) (Force (Value e)) x))))
           (Closure (HD vL3) (Lams (TL vL3)
                                       (Apps (Value (Closure (HD (vL1++s2::vL2++vL3))
                                                              (Lams (TL (vL1++s2::vL2++vL3)) y)))
                                        (MAP Value eL1' ++ (Tick (Force (Value e')))::MAP Value eL2'
                                         ++ MAP Var vL3)))))
[v_rel_Closure_Force_HD2:]
  (∀eL1 eL1' eL2 eL2' e e' vL1 vL2 vL3 s s2 x y.
     ALL_DISTINCT (s2::vL1 ++ vL2 ++ s::vL3) ∧
     LENGTH vL1 = LENGTH eL1 ∧ LENGTH vL2 = LENGTH eL2 ∧
     LIST_REL v_rel eL1 eL1' ∧ LIST_REL v_rel eL2 eL2' ∧ v_rel e e' ∧
     vL3 ≠ [] ∧
     force_arg_rel x y ⇒
     v_rel (Closure (HD vL3)
            (Lams (TL vL3) (subst (ZIP (vL1 ++ s::vL2, eL1 ++ e::eL2)) (Let (SOME s2) (Force (Var s)) x))))
           (Closure (HD vL3) (Lams (TL vL3)
                                       (Apps (Value (Closure s
                                                              (Lams (vL1++s2::vL2++vL3) y)))
                                        (Value e'::MAP Value eL1' ++ (Tick (Force (Value e')))::MAP Value eL2'
                                         ++ MAP Var vL3)))))
[v_rel_Closure_Force_TL_Rec:]
  (∀eL1 eL2 vL1 vL2 vL3 s s2 x y xs ys v1 v2 i.
     ALL_DISTINCT (MAP FST xs) ∧
     LENGTH vL1 = LENGTH eL1 ∧
     LIST_REL v_rel eL1 eL2 ∧

     MAP FST xs = MAP FST ys ∧ LIST_REL force_arg_rel (MAP SND xs) (MAP SND ys) ∧
     EVERY ok_bind (MAP SND xs) ∧ EVERY ok_bind (MAP SND ys) ∧
     EVERY (λe. v2 ∉ freevars e) (MAP SND xs) ∧
     EL i xs = (v1, Lams (vL1 ++ vL2 ++ s::vL3) (Let (SOME s2) (Force (Var s)) x)) ∧
     SND (EL i ys) = Lams (vL1 ++ vL2 ++ s::vL3) (Let (SOME s2) (Force (Var s)) y) ∧
     ¬MEM v2 (MAP FST xs ++ s2::vL1 ++ vL2 ++ s::vL3) ∧ ALL_DISTINCT (s2::vL1 ++ vL2 ++ s::vL3) ∧
     i < LENGTH xs ∧

     s ∉ freevars x ∧ v2 ∉ freevars x ∧
     force_arg_rel x y ⇒
     v_rel (Closure (HD (SNOC s vL2))
            (Lams (TL (vL2++s::vL3)) (subst (ZIP (vL1, eL1))
                                      (subst (FILTER(λ(v,x).¬MEM v (vL1++vL2++s::vL3))
                                              (MAP (λ(v,x).(v,Recclosure xs v)) xs))
                                       (Let (SOME s2) (Force (Var s)) x)))))
           (Closure (HD (SNOC s vL2))
            (Lams (TL (vL2 ++ s::vL3))
             (Apps (Value (Recclosure (SNOC (v2, Lams (vL1 ++ vL2++s2::vL3) y)
                                       (LUPDATE (v1, Lams (vL1 ++ vL2 ++ s::vL3)
                               (Apps (Var v2) (MAP Var vL1 ++ MAP Var vL2 ++
                                               Tick (Force (Var s))::MAP Var vL3)))
                                        i ys)) v2))
              (MAP Value eL2 ++ MAP Var vL2 ++ (Tick (Force (Var s)))::MAP Var vL3)))))
[v_rel_Closure_Force_TL_Rec2:]
  (∀eL1 eL2 vL1 vL2 vL3 s s2 x y xs ys v1 v2 i.
     ALL_DISTINCT (MAP FST xs) ∧
     LENGTH vL1 = LENGTH eL1 ∧
     LIST_REL v_rel eL1 eL2 ∧

     MAP FST xs = MAP FST ys ∧ LIST_REL force_arg_rel (MAP SND xs) (MAP SND ys) ∧
     EVERY ok_bind (MAP SND xs) ∧ EVERY ok_bind (MAP SND ys) ∧
     EVERY (λe. v2 ∉ freevars e) (MAP SND xs) ∧
     EL i xs = (v1, Lams (vL1 ++ vL2 ++ s::vL3) (Let (SOME s2) (Force (Var s)) x)) ∧
     SND (EL i ys) = Lams (vL1 ++ vL2 ++ s::vL3) (Let (SOME s2) (Force (Var s)) y) ∧
     ¬MEM v2 (MAP FST xs ++ s2::vL1 ++ vL2 ++ s::vL3) ∧ ALL_DISTINCT (s2::vL1 ++ vL2 ++ s::vL3) ∧
     i < LENGTH xs ∧ v2 ∉ freevars x ∧
     force_arg_rel x y ⇒
     v_rel (Closure (HD (SNOC s vL2))
            (Lams (TL (vL2++s::vL3)) (subst (ZIP (vL1, eL1))
                                      (subst (FILTER(λ(v,x).¬MEM v (vL1++vL2++s::vL3))
                                              (MAP (λ(v,x).(v,Recclosure xs v)) xs))
                                       (Let (SOME s2) (Force (Var s)) x)))))
           (Closure (HD (SNOC s vL2))
            (Lams (TL (vL2 ++ s::vL3))
             (Apps (Value (Recclosure (SNOC (v2, Lams (s::vL1 ++ vL2++s2::vL3) y)
                                       (LUPDATE (v1, Lams (vL1 ++ vL2 ++ s::vL3)
                               (Apps (Var v2) (Var s::MAP Var vL1 ++ MAP Var vL2 ++
                                               Tick (Force (Var s))::MAP Var vL3)))
                                        i ys)) v2))
              (Var s::MAP Value eL2 ++ MAP Var vL2 ++ (Tick (Force (Var s)))::MAP Var vL3)))))
[v_rel_Closure_Force_HD_Rec:]
  (∀eL1 eL1' eL2 eL2' e e' vL1 vL2 vL3 s s2 x y xs ys v1 v2 i.
     ALL_DISTINCT (MAP FST xs) ∧
     LENGTH vL1 = LENGTH eL1 ∧ LENGTH vL2 = LENGTH eL2 ∧
     LIST_REL v_rel eL1 eL1' ∧ LIST_REL v_rel eL2 eL2' ∧ v_rel e e' ∧

     MAP FST xs = MAP FST ys ∧ LIST_REL force_arg_rel (MAP SND xs) (MAP SND ys) ∧
     EVERY ok_bind (MAP SND xs) ∧ EVERY ok_bind (MAP SND ys) ∧
     EVERY (λe. v2 ∉ freevars e) (MAP SND xs) ∧
     EL i xs = (v1, Lams (vL1 ++ s::vL2 ++ vL3) (Let (SOME s2) (Force (Var s)) x)) ∧
     SND (EL i ys) = Lams (vL1 ++ s::vL2 ++ vL3) (Let (SOME s2) (Force (Var s)) y) ∧
     ¬MEM v2 (MAP FST xs ++ s2::vL1 ++ s::vL2 ++ vL3) ∧ ALL_DISTINCT (s2::vL1 ++ s::vL2 ++ vL3) ∧
     i < LENGTH xs ∧

     vL3 ≠ [] ∧
     s ∉ freevars x ∧ v2 ∉ freevars x ∧
     force_arg_rel x y ⇒
     v_rel (Closure (HD vL3)
            (Lams (TL vL3) (subst (ZIP (vL1++vL2, eL1++eL2))
                            (subst (FILTER(λ(v,x).¬MEM v (vL1++s::vL2++vL3))
                                    (MAP (λ(v,x).(v,Recclosure xs v)) xs))
                             (Let (SOME s2) (Force (Value e)) x)))))
           (Closure (HD vL3)
            (Lams (TL vL3)
             (Apps (Value (Recclosure (SNOC (v2, Lams (vL1 ++ s2::vL2 ++ vL3) y)
                 (LUPDATE (v1, Lams (vL1 ++ s::vL2 ++ vL3)
                           (Apps (Var v2) (MAP Var vL1 ++ Tick (Force (Var s))::MAP Var vL2
                                           ++ MAP Var vL3)))
                  i ys)) v2))
              (MAP Value eL1' ++ (Tick (Force (Value e')))::MAP Value eL2' ++ MAP Var vL3)))))
[v_rel_Closure_Force_HD_Rec2:]
  (∀eL1 eL1' eL2 eL2' e e' vL1 vL2 vL3 s s2 x y xs ys v1 v2 i.
     ALL_DISTINCT (MAP FST xs) ∧
     LENGTH vL1 = LENGTH eL1 ∧ LENGTH vL2 = LENGTH eL2 ∧
     LIST_REL v_rel eL1 eL1' ∧ LIST_REL v_rel eL2 eL2' ∧ v_rel e e' ∧

     MAP FST xs = MAP FST ys ∧ LIST_REL force_arg_rel (MAP SND xs) (MAP SND ys) ∧
     EVERY ok_bind (MAP SND xs) ∧ EVERY ok_bind (MAP SND ys) ∧
     EVERY (λe. v2 ∉ freevars e) (MAP SND xs) ∧
     EL i xs = (v1, Lams (vL1 ++ s::vL2 ++ vL3) (Let (SOME s2) (Force (Var s)) x)) ∧
     SND (EL i ys) = Lams (vL1 ++ s::vL2 ++ vL3) (Let (SOME s2) (Force (Var s)) y) ∧
     ¬MEM v2 (MAP FST xs ++ s2::vL1 ++ s::vL2 ++ vL3) ∧ ALL_DISTINCT (s2::vL1 ++ s::vL2 ++ vL3) ∧
     i < LENGTH xs ∧

     vL3 ≠ [] ∧ v2 ∉ freevars x ∧
     force_arg_rel x y ⇒
     v_rel (Closure (HD vL3)
            (Lams (TL vL3) (subst (ZIP (vL1++s::vL2, eL1++e::eL2))
                            (subst (FILTER(λ(v,x).¬MEM v (vL1++s::vL2++vL3))
                                    (MAP (λ(v,x).(v,Recclosure xs v)) xs))
                             (Let (SOME s2) (Force (Var s)) x)))))
           (Closure (HD vL3)
            (Lams (TL vL3)
             (Apps (Value (Recclosure (SNOC (v2, Lams (s::vL1 ++ s2::vL2 ++ vL3) y)
                 (LUPDATE (v1, Lams (vL1 ++ s::vL2 ++ vL3)
                           (Apps (Var v2) (Var s::MAP Var vL1 ++ Tick (Force (Var s))::MAP Var vL2
                                           ++ MAP Var vL3)))
                  i ys)) v2))
              (Value e'::MAP Value eL1' ++ (Tick (Force (Value e')))::MAP Value eL2'
               ++ MAP Var vL3)))))
[v_rel_Recclosure:]
  (∀f g n.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL force_arg_rel (MAP SND f) (MAP SND g) ⇒
     v_rel (Recclosure f n) (Recclosure g n))
[v_rel_Recclosure_Lam_Force:]
  (∀f g x y v1 v2 vL1 vL2 s s2 i n.
     MAP FST f = MAP FST g ∧
     ALL_DISTINCT (MAP FST f) ∧
     i < LENGTH f ∧
     EL i f = (v1, Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) x)) ∧
     SND (EL i g) = Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) y) ∧
     ALL_DISTINCT (s2::vL1 ++ s::vL2) ∧ s ∉ freevars x ∧
     ¬MEM v2 (MAP FST f++ s2::vL1 ++ s::vL2) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     EVERY (λe. v2 ∉ freevars e) (MAP SND f) ∧
     MEM n (MAP FST f) ∧ force_arg_rel x y ∧
     LIST_REL force_arg_rel (MAP SND f) (MAP SND g) ⇒
     v_rel (Recclosure f n)
             (Recclosure (SNOC (v2, Lams (vL1 ++ s2::vL2) y)
                          (LUPDATE (v1, Lams (vL1 ++ s::vL2)
                                             (Apps (Var v2) (MAP Var vL1 ++ Tick (Force (Var s))::MAP Var vL2)))
                           i g)) n))
[v_rel_Recclosure_Lam_Force2:]
  (∀f g x y v1 v2 vL1 vL2 s s2 i n.
     MAP FST f = MAP FST g ∧
     ALL_DISTINCT (MAP FST f) ∧
     i < LENGTH f ∧
     EL i f = (v1, Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) x)) ∧
     SND (EL i g) = Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) y) ∧
     ALL_DISTINCT (s2::vL1 ++ s::vL2) ∧
     ¬MEM v2 (MAP FST f++ s2::vL1 ++ s::vL2) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     EVERY (λe. v2 ∉ freevars e) (MAP SND f) ∧
     MEM n (MAP FST f) ∧ force_arg_rel x y ∧
     LIST_REL force_arg_rel (MAP SND f) (MAP SND g) ⇒
     v_rel (Recclosure f n)
             (Recclosure (SNOC (v2, Lams (s::vL1 ++ s2::vL2) y)
                          (LUPDATE (v1, Lams (vL1 ++ s::vL2)
                     (Apps (Var v2) (Var s::MAP Var vL1 ++ Tick (Force (Var s))::MAP Var vL2)))
                           i g)) n))
[v_rel_Thunk:]
  (∀x y.
     force_arg_rel x y ⇒
     v_rel (Thunk x) (Thunk y))
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x))
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
     v_rel (DoTick v) (DoTick w))
End

Theorem force_arg_rel_def =
  [“force_arg_rel (Var v) x”,
   “force_arg_rel (Value v) x”,
   “force_arg_rel (Prim op xs) x”,
   “force_arg_rel (Monad mop xs) x”,
   “force_arg_rel (App f x) y”,
   “force_arg_rel (Lam s x) y”,
   “force_arg_rel (Letrec f x) y”,
   “force_arg_rel (Let s x y) z”,
   “force_arg_rel (If x y z) w”,
   “force_arg_rel (Delay x) y”,
   “force_arg_rel (MkTick x) y”,
   “force_arg_rel (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once force_arg_rel_cases])
  |> LIST_CONJ;

Theorem v_rel_def =
  [“v_rel (Constructor s vs) v”,
   “v_rel (Monadic s vs) v”,
   “v_rel (Closure s x) v”,
   “v_rel (Recclosure f n) v”,
   “v_rel (Atom x) v”,
   “v_rel (Thunk x) v”,
   “v_rel (DoTick x) v”]
  |> map (SIMP_CONV (srw_ss()) [Once force_arg_rel_cases])
  |> LIST_CONJ

Theorem force_arg_rel_refl:
  ∀x. no_value x ⇒ force_arg_rel x x
Proof
  Induct using freevars_ind >> gvs [force_arg_rel_def, no_value_def, EVERY_CONJ] >>
  gvs [EVERY_EL, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >> rw [] >>
  disj1_tac >> rw [] >>
  last_x_assum irule >> gvs [] >>
  first_assum $ irule_at Any >>
  gvs [EL_MAP] >> irule_at Any PAIR
QED

Theorem force_arg_rel_freevars:
  ∀x y. force_arg_rel x y ⇒ freevars x = freevars y
Proof
  ‘(∀x y. force_arg_rel x y ⇒ freevars x = freevars y) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw [] >>
  ho_match_mp_tac force_arg_rel_strongind >>
  gvs [force_arg_rel_def, PULL_EXISTS, freevars_def] >> rw []
  >- (AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      gvs [LIST_REL_EL_EQN, MEM_EL, EL_MAP, PULL_EXISTS])
  >- (AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      gvs [LIST_REL_EL_EQN, MEM_EL, EL_MAP, PULL_EXISTS])
  >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
      AP_TERM_TAC >> irule LIST_EQ >>
      gvs [MEM_EL, PULL_EXISTS, EL_MAP, LIST_REL_EL_EQN] >>
      rw [] >>
      last_x_assum $ dxrule_then assume_tac >>
      pairarg_tac >> gs [] >> pairarg_tac >> gvs [])
  >>~[‘LUPDATE _ _ _’]
  >- (gvs [MAP_SNOC, LUPDATE_MAP, LIST_TO_SET_SNOC, freevars_Lams, freevars_Apps, freevars_def] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] >> gvs []
      >- (strip_tac >> gvs [])
      >- (strip_tac >> gvs [MEM_LUPDATE, EL_MEM] >>
          first_x_assum irule >>
          gvs [MEM_EL] >> first_assum $ irule_at Any >>
          rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
      >- (gvs [MEM_EL, EL_MAP, EL_LUPDATE, PULL_EXISTS] >>
          rename1 ‘_ ∈ _ (EL n f)’ >> rename1 ‘EL i f = (_, _)’ >>
          Cases_on ‘i = n’ >> gvs []
          >- (gvs [LIST_REL_CONJ, LIST_REL_EL_EQN, EL_MAP, EVERY_EL] >>
              rpt $ first_x_assum $ drule_then assume_tac >> gvs [] >>
              gvs [freevars_def, freevars_Lams, MEM_EL]) >>
          disj2_tac >> disj2_tac >> qexists_tac ‘n’ >>
          gvs [LIST_REL_CONJ, LIST_REL_EL_EQN, EL_MAP] >>
          first_x_assum $ drule_then assume_tac >>
          pairarg_tac >> gs [] >> pairarg_tac >> gs [])
      >- (strip_tac >> gvs [MEM_MAP, EVERY_MEM, PULL_EXISTS] >>
          first_x_assum $ dxrule_then assume_tac >> pairarg_tac >> gs [])
      >- (strip_tac >> gvs [MEM_LUPDATE, EL_MEM] >>
          first_x_assum irule >>
          gvs [MEM_EL] >> first_assum $ irule_at Any >>
          rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
      >- (strip_tac >> first_x_assum irule >>
          gvs [MEM_EL, EL_LUPDATE] >> first_x_assum $ irule_at Any >>
          rw [] >> rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
      >- (disj2_tac >> gvs [MEM_EL, PULL_EXISTS] >>
          first_assum $ irule_at Any >>
          gvs [EL_MAP, LIST_REL_EL_EQN] >>
          first_x_assum $ drule_then assume_tac >>
          gvs [freevars_Lams, freevars_def, MEM_EL] >>
          strip_tac >> gvs [])
      >- (strip_tac >> first_x_assum irule >>
          gvs [MEM_EL, EL_LUPDATE] >> first_x_assum $ irule_at Any >>
          rw [] >> rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
      >- (gvs [MEM_EL, EL_LUPDATE, PULL_EXISTS] >>
          rename1 ‘n = i ∧ i < LENGTH g’ >> Cases_on ‘n = i’ >> gvs [LIST_REL_EL_EQN]
          >- gvs [MEM_MAP, freevars_def]
          >- gvs [MEM_MAP, freevars_def]
          >- (disj2_tac >> qexists_tac ‘n’ >> gvs [EL_MAP] >>
              first_x_assum $ drule_then assume_tac >>
              pairarg_tac >> gs [] >> pairarg_tac >> gs []))
      >- (strip_tac >> first_x_assum irule >>
          gvs [MEM_EL, EL_LUPDATE] >> first_x_assum $ irule_at Any >>
          rw [] >> rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP]))
  >- (gvs [MAP_SNOC, LUPDATE_MAP, LIST_TO_SET_SNOC, freevars_Lams, freevars_Apps, freevars_def] >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] >> gvs []
      >- (strip_tac >> gvs [])
      >- (strip_tac >> gvs [MEM_LUPDATE, EL_MEM] >>
          first_x_assum irule >>
          gvs [MEM_EL] >> first_assum $ irule_at Any >>
          rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
      >- (gvs [MEM_EL, EL_MAP, EL_LUPDATE, PULL_EXISTS] >>
          rename1 ‘_ ∈ _ (EL n f)’ >> rename1 ‘EL i f = (_, _)’ >>
          Cases_on ‘i = n’ >> gvs []
          >- (gvs [LIST_REL_CONJ, LIST_REL_EL_EQN, EL_MAP, EVERY_EL] >>
              rpt $ first_x_assum $ drule_then assume_tac >> gvs [] >>
              gvs [freevars_def, freevars_Lams, MEM_EL]) >>
          disj2_tac >> disj2_tac >> qexists_tac ‘n’ >>
          gvs [LIST_REL_CONJ, LIST_REL_EL_EQN, EL_MAP] >>
          first_x_assum $ drule_then assume_tac >>
          pairarg_tac >> gs [] >> pairarg_tac >> gs [])
      >- (strip_tac >> gvs [MEM_MAP, EVERY_MEM, PULL_EXISTS] >>
          first_x_assum $ dxrule_then assume_tac >> pairarg_tac >> gs [])
      >- (strip_tac >> gvs [MEM_LUPDATE, EL_MEM] >>
          first_x_assum irule >>
          gvs [MEM_EL] >> first_assum $ irule_at Any >>
          rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
      >- (strip_tac >> first_x_assum irule >>
          gvs [MEM_EL, EL_LUPDATE] >> first_x_assum $ irule_at Any >>
          rw [] >> rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
      >- (disj2_tac >> gvs [MEM_EL, PULL_EXISTS] >>
          first_assum $ irule_at Any >>
          gvs [EL_MAP, LIST_REL_EL_EQN] >>
          first_x_assum $ drule_then assume_tac >>
          gvs [freevars_Lams, freevars_def, MEM_EL] >>
          strip_tac >> gvs [])
      >- (strip_tac >> first_x_assum irule >>
          gvs [MEM_EL, EL_LUPDATE] >> first_x_assum $ irule_at Any >>
          rw [] >> rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
      >- (gvs [MEM_EL, EL_LUPDATE, PULL_EXISTS] >>
          rename1 ‘n = i ∧ i < LENGTH g’ >> Cases_on ‘n = i’ >> gvs [LIST_REL_EL_EQN]
          >- gvs [MEM_MAP, freevars_def]
          >- gvs [MEM_MAP, freevars_def]
          >- (disj2_tac >> qexists_tac ‘n’ >> gvs [EL_MAP] >>
              first_x_assum $ drule_then assume_tac >>
              pairarg_tac >> gs [] >> pairarg_tac >> gs []))
      >- (strip_tac >> first_x_assum irule >>
          gvs [MEM_EL, EL_LUPDATE] >> first_x_assum $ irule_at Any >>
          rw [] >> rename1 ‘i < _’ >>
          ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP]))
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

Theorem force_arg_rel_boundvars:
  ∀x y. force_arg_rel x y ⇒ boundvars x ⊆ boundvars y
Proof
  ‘(∀x y. force_arg_rel x y ⇒ boundvars x ⊆ boundvars y) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw [] >>
  ho_match_mp_tac force_arg_rel_strongind >>
  gvs [force_arg_rel_def, PULL_EXISTS, boundvars_def] >> rw []
  >>~[‘LUPDATE _ _ _’]
  >- gvs [SUBSET_DEF]
  >- (gvs [SUBSET_DEF, IN_BIGUNION, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN, EL_MAP] >>
      rw [] >> disj1_tac >> disj2_tac >>
      rename1 ‘EL n (MAP _ f)’ >> rename1 ‘EL i f = (_, Lams _ _)’ >>
      first_x_assum $ drule_then assume_tac >> gvs [EL_MAP] >>
      pairarg_tac >> gs [] >> first_x_assum $ dxrule_then assume_tac >>
      Cases_on ‘i = n’ >> gvs []
      >- (gvs [boundvars_Lams]
          >- (qexists_tac ‘LENGTH g’ >>
              gvs [SNOC_APPEND, EL_MAP, EL_APPEND_EQN] >>
              gvs [boundvars_def, boundvars_Lams])
          >- (qexists_tac ‘i’ >> gvs [EL_MAP, EL_SNOC, EL_LUPDATE, boundvars_Lams])
          >- (qexists_tac ‘i’ >> gvs [EL_MAP, EL_SNOC, EL_LUPDATE, boundvars_Lams])
          >- (qexists_tac ‘i’ >> gvs [EL_MAP, EL_SNOC, EL_LUPDATE, boundvars_Lams])) >>
      qexists_tac ‘n’ >> gvs [EL_MAP, EL_SNOC, EL_LUPDATE] >>
      pairarg_tac >> gs [])
  >- (gvs [SUBSET_DEF, MAP_SNOC, LUPDATE_MAP] >>
      rw [] >> disj2_tac >> disj2_tac >>
      gvs [MEM_EL] >> first_assum $ irule_at Any >>
      gvs [EL_MAP, EL_LUPDATE, LIST_REL_EL_EQN] >>
      IF_CASES_TAC >> gvs [] >>
      rename1 ‘i < _’ >>
      ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
  >- gvs [SUBSET_DEF]
  >- (gvs [SUBSET_DEF, IN_BIGUNION, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN, EL_MAP] >>
      rw [] >> disj1_tac >> disj2_tac >>
      rename1 ‘EL n (MAP _ f)’ >> rename1 ‘EL i f = (_, Lams _ _)’ >>
      first_x_assum $ drule_then assume_tac >> gvs [EL_MAP] >>
      pairarg_tac >> gs [] >> first_x_assum $ dxrule_then assume_tac >>
      Cases_on ‘i = n’ >> gvs []
      >- (gvs [boundvars_Lams]
          >- (qexists_tac ‘LENGTH g’ >>
              gvs [SNOC_APPEND, EL_MAP, EL_APPEND_EQN] >>
              gvs [boundvars_def, boundvars_Lams])
          >- (qexists_tac ‘i’ >> gvs [EL_MAP, EL_SNOC, EL_LUPDATE, boundvars_Lams])
          >- (qexists_tac ‘i’ >> gvs [EL_MAP, EL_SNOC, EL_LUPDATE, boundvars_Lams])
          >- (qexists_tac ‘i’ >> gvs [EL_MAP, EL_SNOC, EL_LUPDATE, boundvars_Lams])) >>
      qexists_tac ‘n’ >> gvs [EL_MAP, EL_SNOC, EL_LUPDATE] >>
      pairarg_tac >> gs [])
  >- (gvs [SUBSET_DEF, MAP_SNOC, LUPDATE_MAP] >>
      rw [] >> disj2_tac >> disj2_tac >>
      gvs [MEM_EL] >> first_assum $ irule_at Any >>
      gvs [EL_MAP, EL_LUPDATE, LIST_REL_EL_EQN] >>
      IF_CASES_TAC >> gvs [] >>
      rename1 ‘i < _’ >>
      ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] >> gvs [EL_MAP])
  >- (gvs [SUBSET_DEF, IN_BIGUNION, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >>
      rw [] >> first_assum $ irule_at Any >>
      gvs [EL_MAP] >>
      metis_tac [])
  >- (gvs [SUBSET_DEF, IN_BIGUNION, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >>
      rw [] >> first_assum $ irule_at Any >>
      gvs [EL_MAP] >>
      metis_tac [])
  >~[‘Force (Var _)’]
  >- (gvs [boundvars_Lams, boundvars_Apps, boundvars_def, SUBSET_DEF] >>
      rw [] >> gvs [MEM_SNOC, MAP_SNOC])
  >~[‘Let opt _ _’]
  >- (Cases_on ‘opt’ >> gvs [boundvars_def, SUBSET_DEF] >>
      rw [] >> gvs []) >>
  gvs [SUBSET_DEF]
  >- (gvs [SUBSET_DEF, IN_BIGUNION, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >>
      rw [] >> disj1_tac >> disj2_tac >>
      first_assum $ irule_at Any >>
      gvs [EL_MAP] >>
      pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
      first_x_assum $ dxrule_then assume_tac >>
      gvs [])
  >- (gvs [boundvars_Lams, boundvars_Apps, boundvars_def, SUBSET_DEF] >>
      rw [] >> gvs [])
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

Theorem LUPDATE_ID:
  ∀l i e. EL i l = e ⇒ LUPDATE e i l = l
Proof
  Induct >> gvs [] >>
  strip_tac >> Cases >> gvs [LUPDATE_DEF]
QED

Theorem LUPDATE_ID_MAP_FST:
  ∀f i v. i < LENGTH f ∧ FST (EL i f) = v ⇒ LUPDATE v i (MAP FST f) = MAP FST f
Proof
  rw [] >>
  qspecl_then [‘MAP FST f’, ‘i’] assume_tac LUPDATE_ID >> gvs [EL_MAP]
QED

Theorem force_arg_rel_subst:
  ∀vs x ws y.
    MAP FST vs = MAP FST ws ∧
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    force_arg_rel x y ⇒
      force_arg_rel (subst vs x) (subst ws y)
Proof
  ‘(∀x y.
     force_arg_rel x y ⇒
     ∀vs ws.
       MAP FST vs = MAP FST ws ∧
       LIST_REL v_rel (MAP SND vs) (MAP SND ws) ⇒
         force_arg_rel (subst vs x) (subst ws y)) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw []
  \\ ho_match_mp_tac force_arg_rel_strongind \\ rw []
  >~ [‘Var v’] >- (
    rw [subst_def]
    \\ rename1 ‘LIST_REL v_rel (MAP SND vs) (MAP SND ws)’
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      by (irule LIST_REL_OPTREL
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
    \\ gs [OPTREL_def, force_arg_rel_Var, force_arg_rel_Value])
  >~ [‘Value v’] >- (
    rw [subst_def]
    \\ gs [force_arg_rel_Value])
  >~ [‘Prim op xs’] >- (
    rw [subst_def]
    \\ irule force_arg_rel_Prim
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [‘Monad op xs’] >- (
    rw [subst_def]
    \\ irule force_arg_rel_Monad
    \\ gs [EVERY2_MAP, LIST_REL_EL_EQN])
  >~ [‘App f x’] >- (
    rw [subst_def]
    \\ gs [force_arg_rel_App])
  >~ [‘Lam s x’] >- (
    rw [subst_def]
    \\ irule force_arg_rel_Lam
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >>~[‘LUPDATE _ _ _’] >- (
    gvs [subst_def, MAP_SNOC, LUPDATE_MAP] >>
    drule_then assume_tac LUPDATE_ID_MAP_FST >>
    gvs [subst_Lams, subst_def, subst_Apps, GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
    ‘∀ws s. MAP (subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) ws))
                (MAP Var vL1) = MAP Var vL1’
      by (rw [] >> irule LIST_EQ >> rw [EL_MAP] >>
          gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
    ‘∀ws s. MAP (subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) ws))
                (MAP Var vL2) = MAP Var vL2’
      by (rw [] >> irule LIST_EQ >> rw [EL_MAP] >>
          gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
    gvs [] >> irule force_arg_rel_Letrec_Lam_Force >>
    gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, EL_MAP,
         LIST_REL_EL_EQN, freevars_subst] >>
    rw []
    >- (pairarg_tac >> gvs [subst_Lams, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
        rename1 ‘subst _ y2’ >>
        gvs [FILTER_FILTER, LAMBDA_PROD] >>
        AP_THM_TAC >> AP_TERM_TAC >> gvs [] >>
        ‘∀l. subst (FILTER (λ(n,x). n ≠ s) l) y2 = subst l y2’
          by (gen_tac >> dxrule_then assume_tac force_arg_rel_freevars >>
              qspecl_then [‘l’, ‘y2’, ‘{s}’] assume_tac subst_remove >> gvs []) >>
        irule EQ_TRANS >> first_x_assum $ irule_at Any >>
        gvs [FILTER_FILTER, LAMBDA_PROD] >>
        AP_THM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
        rpt $ pop_assum kall_tac >>
        gvs [GSYM CONJ_ASSOC] >>
        metis_tac [CONJ_COMM])
    >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
        last_x_assum $ dxrule_then assume_tac >>
        pairarg_tac >> gs [] >>
        rename1 ‘ok_bind (subst _ p2)’ >>
        Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
    >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
        last_x_assum $ dxrule_then assume_tac >>
        pairarg_tac >> gs [] >>
        rename1 ‘ok_bind (subst _ p2)’ >>
        Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
    >- (qpat_x_assum ‘EVERY _ _’ assume_tac >>
        gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
        first_x_assum $ dxrule_then assume_tac >>
        pairarg_tac >> gs [freevars_subst])
    >- (rename1 ‘force_arg_rel (subst (FILTER _ vs) x) _’ >>
        qspecl_then [‘FILTER (λ(n,v). ¬MEM n (MAP FST g)) vs’, ‘x’, ‘{v2}’]
                    assume_tac $ GSYM subst_remove >>
        gvs [FILTER_FILTER, LAMBDA_PROD] >>
        first_x_assum irule >>
        qspecl_then [‘vs’, ‘ws’, ‘v_rel’, ‘λx. x ≠ v2 ∧ ¬MEM x (MAP FST g)’]
                    assume_tac LIST_FILTERED >>
        gvs [LIST_REL_EL_EQN, EL_MAP])
    >- (first_x_assum $ irule_at $ Pos last >>
        gvs [subst_Lams, subst_def, FILTER_FILTER, LAMBDA_PROD,
             GSYM FILTER_REVERSE, ALOOKUP_FILTER, freevars_subst] >>
        qmatch_goalsub_abbrev_tac ‘MAP FST _ = MAP FST (FILTER filter2 ws)’ >>
        rename1 ‘MAP FST vs = MAP FST ws’ >>
        qexists_tac ‘FILTER filter2 vs’ >>
        qspecl_then [‘vs’, ‘ws’, ‘v_rel’, ‘λn. filter2 (n, Closure n (Var n))’]
                    assume_tac LIST_FILTERED >>
        unabbrev_all_tac >> gvs [LIST_REL_EL_EQN, EL_MAP] >>
        AP_THM_TAC >> AP_TERM_TAC >> gvs [] >>
        rename1 ‘subst _ x2’ >>
        ‘∀l. subst (FILTER (λ(n,x). n ≠ s) l) x2 = subst l x2’
          by (gen_tac >> dxrule_then assume_tac force_arg_rel_freevars >>
              qspecl_then [‘l’, ‘x2’, ‘{s}’] assume_tac subst_remove >> gvs []) >>
        irule EQ_TRANS >> first_x_assum $ irule_at Any >>
        ‘∀l. subst l x2 = subst (FILTER (λ(n,x). n ≠ v2) l) x2’
          by (gen_tac >> dxrule_then assume_tac force_arg_rel_freevars >>
              qspecl_then [‘l’, ‘x2’, ‘{v2}’] assume_tac subst_remove >> gvs []) >>
        irule EQ_TRANS >> first_x_assum $ irule_at Any >>
        rpt $ pop_assum kall_tac >>
        gvs [FILTER_FILTER, LAMBDA_PROD, GSYM CONJ_ASSOC] >>
        AP_THM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
        gvs [] >> metis_tac [CONJ_COMM])
    >- (last_x_assum $ drule_then assume_tac >> gvs [] >>
        qpat_x_assum ‘EVERY _ (MAP SND _)’ assume_tac >>
        gvs [EVERY_EL] >> first_x_assum $ drule_then assume_tac >>
        pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
        rename1 ‘force_arg_rel (subst (FILTER _ vs) x3)’ >>
        qspecl_then [‘FILTER (λ(n,v). ¬MEM n (MAP FST g)) vs’, ‘x3’, ‘{v2}’]
                    assume_tac $ GSYM subst_remove >>
        gvs [EL_MAP, FILTER_FILTER, LAMBDA_PROD] >>
        first_x_assum irule >>
        qspecl_then [‘vs’, ‘ws’, ‘v_rel’, ‘λn. n ≠ v2 ∧ ¬MEM n (MAP FST g)’]
                    assume_tac LIST_FILTERED >>
        gvs [LIST_REL_EL_EQN, EL_MAP]))
  >- (gvs [subst_def, MAP_SNOC, LUPDATE_MAP] >>
      drule_then assume_tac LUPDATE_ID_MAP_FST >>
      gvs [subst_Lams, subst_def, subst_Apps, GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
      ‘∀ws s. MAP (subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) ws))
                  (MAP Var vL1) = MAP Var vL1’
        by (rw [] >> irule LIST_EQ >> rw [EL_MAP] >>
            gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
      ‘∀ws s. MAP (subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) ws))
                  (MAP Var vL2) = MAP Var vL2’
        by (rw [] >> irule LIST_EQ >> rw [EL_MAP] >>
            gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
      gvs [] >> gvs [force_arg_rel_def] >> disj2_tac >> disj2_tac >>
      irule_at (Pos hd) EQ_REFL >>
      ‘∀i1 i2 e1 e2 l1 l2. i1 = i2 ∧ e1 = e2 ∧ l1 = l2 ⇒ LUPDATE (e1: string # exp) i1 l1 = LUPDATE e2 i2 l2’
        by gvs [] >>
      pop_assum $ irule_at Any >> gvs [EL_MAP, freevars_subst, subst_Lams, subst_def] >>
      ‘∀l e1 e2. e1 = e2 ⇒ Lams l e1 = Lams l e2’ by gvs [] >> pop_assum $ irule_at Any >>
      gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, EL_MAP,
           LIST_REL_EL_EQN, freevars_subst] >>
      rw []
      >- gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
      >- (pairarg_tac >> gvs [subst_Lams, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
          rename1 ‘subst _ y2’ >>
          gvs [FILTER_FILTER, LAMBDA_PROD] >>
          AP_THM_TAC >> AP_TERM_TAC >> gvs [] >>
          AP_THM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
          rpt $ pop_assum kall_tac >>
          gvs [GSYM CONJ_ASSOC] >>
          metis_tac [CONJ_COMM])
      >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
          last_x_assum $ dxrule_then assume_tac >>
          pairarg_tac >> gs [] >>
          rename1 ‘ok_bind (subst _ p2)’ >>
          Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
      >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
          last_x_assum $ dxrule_then assume_tac >>
          pairarg_tac >> gs [] >>
          rename1 ‘ok_bind (subst _ p2)’ >>
          Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
      >- (last_x_assum $ drule_then assume_tac >> gvs [] >>
          qpat_x_assum ‘EVERY _ (MAP SND _)’ assume_tac >>
          gvs [EVERY_EL] >> first_x_assum $ drule_then assume_tac >>
          pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
          rename1 ‘force_arg_rel (subst (FILTER _ vs) x3)’ >>
          qspecl_then [‘FILTER (λ(n,v). ¬MEM n (MAP FST g)) vs’, ‘x3’, ‘{v2}’]
                      assume_tac $ GSYM subst_remove >>
          gvs [EL_MAP, FILTER_FILTER, LAMBDA_PROD] >>
          first_x_assum irule >>
          qspecl_then [‘vs’, ‘ws’, ‘v_rel’, ‘λn. n ≠ v2 ∧ ¬MEM n (MAP FST g)’]
                      assume_tac LIST_FILTERED >>
          gvs [LIST_REL_EL_EQN, EL_MAP])
      >- (qpat_x_assum ‘EVERY _ _’ assume_tac >>
          gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
          first_x_assum $ dxrule_then assume_tac >>
          pairarg_tac >> gs [freevars_subst])
      >- (rename1 ‘force_arg_rel (subst (FILTER _ vs) x) _’ >>
          qspecl_then [‘FILTER (λ(n,v). ¬MEM n (MAP FST g)) vs’, ‘x’, ‘{v2}’]
                      assume_tac $ GSYM subst_remove >>
          gvs [FILTER_FILTER, LAMBDA_PROD] >>
          first_x_assum irule >>
          qspecl_then [‘vs’, ‘ws’, ‘v_rel’, ‘λx. x ≠ v2 ∧ ¬MEM x (MAP FST g)’]
                      assume_tac LIST_FILTERED >>
          gvs [LIST_REL_EL_EQN, EL_MAP])
      >- (rename1 ‘force_arg_rel (subst _ x2) (subst _ y2)’>>
          qmatch_goalsub_abbrev_tac ‘force_arg_rel (subst l _) _’ >>
          qspecl_then [‘l’, ‘x2’, ‘{v2}’] assume_tac $ GSYM subst_remove >> gvs [] >>
          pop_assum kall_tac >> unabbrev_all_tac >>
          first_x_assum irule >>
          gvs [FILTER_FILTER] >>
          qmatch_goalsub_abbrev_tac ‘LENGTH (FILTER f1 _) = LENGTH (FILTER f2 _)’ >>
          ‘f1 = f2’ by (unabbrev_all_tac >> gvs [GSYM CONJ_ASSOC, LAMBDA_PROD] >>
                        metis_tac [CONJ_COMM]) >>
          qspecl_then [‘vs’, ‘ws’, ‘v_rel’, ‘λn. f1 (n, Closure n (Var n))’]
                      assume_tac LIST_FILTERED >>
          gvs [LIST_REL_EL_EQN, EL_MAP] >> unabbrev_all_tac >>
          gvs [LAMBDA_PROD, MAP_FST_FILTER, EL_MAP]))
  >~ [‘Letrec f x’] >- (
    rw [subst_def]
    \\ irule force_arg_rel_Letrec
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
  >~[‘App (Var _) (Var s)’]
  >- (gvs [subst_def, subst_Lams, subst_Apps, MAP_SNOC, GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
      gvs [EL_MEM, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      rename1 ‘Lams (vL1 ++ s::vL2) _’ >>
      ‘∀w. MAP (λx. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) w) (Var x)) vL1
           = MAP Var vL1’
        by (gen_tac >> irule LIST_EQ >>
            gvs [EL_MAP, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
      ‘∀w. MAP (λx. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) w) (Var x)) vL2
           = MAP Var vL2’
        by (gen_tac >> irule LIST_EQ >>
            gvs [EL_MAP, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
      rw [] >>
      gvs [force_arg_rel_def] >> disj2_tac >>
      rpt $ irule_at (Pos hd) EQ_REFL >>
      gvs [boundvars_subst, freevars_subst, FILTER_FILTER, LAMBDA_PROD, PULL_EXISTS] >>
      conj_tac
      >- (rpt $ dxrule_then assume_tac force_arg_rel_freevars >>
          ‘∀p. (p ≠ s2 ∧ ¬MEM p vL1 ∧ p ≠ s ∧ ¬MEM p vL2)
               = (¬MEM p vL1 ∧ p ≠ s ∧ p ≠ s2 ∧ ¬MEM p vL2)’
            by metis_tac [] >>
          ‘∀p. ((¬MEM p vL1 ∧ p ≠ s2 ∧ ¬MEM p vL2) ∧ p ≠ s)
               = (¬MEM p vL1 ∧ p ≠ s ∧ p ≠ s2 ∧ ¬MEM p vL2)’
            by metis_tac [] >>
          gvs [] >>
          first_x_assum irule >>
          gvs [MAP_FST_FILTER, EVERY2_MAP] >>
          qspecl_then [‘λx y. v_rel (SND x) (SND y)’,
                       ‘λv. ¬MEM v vL1 ∧ v ≠ s ∧ v ≠ s2 ∧ ¬MEM v vL2’] assume_tac
                      $ GEN_ALL LIST_REL_FILTER >>
          gvs [] >>
          pop_assum irule >>
          gvs [LIST_REL_EL_EQN])
      >- (rename1 ‘force_arg_rel _ (subst (FILTER _ ws) y2)’ >>
          qspecl_then [‘FILTER (λ(v,e). v ≠ v1) ws’, ‘y2’, ‘{v2}’] assume_tac subst_remove >>
          rpt $ dxrule_then assume_tac force_arg_rel_freevars >>
          gvs [FILTER_FILTER, LAMBDA_PROD, CONJ_COMM] >>
          first_x_assum irule >>
          gvs [MAP_FST_FILTER, EVERY2_MAP] >>
          qspecl_then [‘λx y. v_rel (SND x) (SND y)’, ‘λv. v ≠ v1’] assume_tac
                      $ GEN_ALL LIST_REL_FILTER >>
          gvs [] >>
          first_x_assum irule >>
          gvs [LIST_REL_EL_EQN]))
  >~[‘Force (Var _)’]
  >- (gvs [subst_def, subst_Lams, subst_Apps, MAP_SNOC, GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
      gvs [EL_MEM, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      rename1 ‘Lams (vL1 ++ s::vL2) _’ >>
      ‘∀w. MAP (λx. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) w) (Var x)) vL1
           = MAP Var vL1’
        by (gen_tac >> irule LIST_EQ >>
            gvs [EL_MAP, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
      ‘∀w. MAP (λx. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s ∧ ¬MEM v vL2) w) (Var x)) vL2
           = MAP Var vL2’
        by (gen_tac >> irule LIST_EQ >>
            gvs [EL_MAP, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM]) >>
      rw [] >>
      irule force_arg_rel_Let_Lams_Force_Var >>
      gvs [boundvars_subst, freevars_subst, FILTER_FILTER, LAMBDA_PROD, PULL_EXISTS] >>
      conj_tac
      >- (rename1 ‘force_arg_rel _ (subst (FILTER _ ws) y)’ >>
          qspecl_then [‘FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s2 ∧ ¬MEM v vL2) ws’, ‘y’, ‘{s}’]
                      assume_tac $ GSYM subst_remove >>
          rpt $ dxrule_then assume_tac force_arg_rel_freevars >>
          gvs [FILTER_FILTER, LAMBDA_PROD] >>
          ‘∀p. (p ≠ s2 ∧ ¬MEM p vL1 ∧ p ≠ s ∧ ¬MEM p vL2)
               = (p ≠ s ∧ ¬MEM p vL1 ∧ p ≠ s2 ∧ ¬MEM p vL2)’
            by metis_tac [] >>
          gvs [] >>
          first_x_assum irule >>
          gvs [MAP_FST_FILTER, EVERY2_MAP] >>
          qspecl_then [‘λx y. v_rel (SND x) (SND y)’,
                       ‘λv. v ≠ s ∧ ¬MEM v vL1 ∧ v ≠ s2 ∧ ¬MEM v vL2’] assume_tac
                      $ GEN_ALL LIST_REL_FILTER >>
          gvs [] >>
          pop_assum irule >>
          gvs [LIST_REL_EL_EQN])
      >- (rename1 ‘force_arg_rel _ (subst (FILTER _ ws) y2)’ >>
          qspecl_then [‘FILTER (λ(v,e). v ≠ v1) ws’, ‘y2’, ‘{v2}’] assume_tac subst_remove >>
          rpt $ dxrule_then assume_tac force_arg_rel_freevars >>
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
    \\ irule force_arg_rel_Let \\ gs []
    \\ first_x_assum irule
    \\ gvs [MAP_FST_FILTER]
    \\ rename1 ‘_ ≠ s’
    \\ qabbrev_tac ‘P = λn. n ≠ s’ \\ gs []
    \\ gs [EVERY2_MAP]
    \\ irule LIST_REL_FILTER
    \\ gvs [LIST_REL_EL_EQN])
  >~ [‘If x y z’] >- (
    rw [subst_def]
    \\ gs [force_arg_rel_If])
  >~ [‘Delay x’] >- (
    rw [subst_def]
    \\ gs [force_arg_rel_Delay])
  >~ [‘Force x’] >- (
    rw [subst_def]
    \\ gs [force_arg_rel_Force])
  >~[‘MkTick x’] >- (
    rw [subst_def]
    \\ gs [force_arg_rel_MkTick])
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
  gvs [FOLDR_SNOC, FOLDL_MAP, FOLDL_SNOC, eval_to_def] >>
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
  gvs [FOLDR_SNOC, FOLDL_MAP, FOLDL_SNOC, eval_to_def] >>
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
  gvs [FOLDR_SNOC, FOLDL_MAP, FOLDL_SNOC, eval_to_def]
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

Triviality less_1_lemma[simp]:
  n < 1 ⇔ n = 0:num
Proof
  fs []
QED

Theorem eval_App_div:
  (∃k w. eval_to k y = INR w) ∧ (∃k s v. eval_to k g = INR (Closure s v)) ⇒
  ($= +++ v_rel) (INL Diverge)
                 do
                   xv <- eval_to 0 y;
                   fv <- eval_to 0 g;
                   (s,body,binds) <-
                   do (s,x'') <- dest_Closure fv; INR (s,x'',[]) od ++
                   do
                     (f,n) <- dest_Recclosure fv;
                     case ALOOKUP (REVERSE f) n of
                       NONE => INL Type_error
                     | SOME (Var v22) => INL Type_error
                     | SOME (Prim v23 v24) => INL Type_error
                     | SOME (Monad mop xs) => INL Type_error
                     | SOME (App v25 v26) => INL Type_error
                     | SOME (Lam s x'') =>
                         INR (s,x'',MAP (λ(g,x). (g,Recclosure f g)) f)
                     | SOME (Letrec v29 v30) => INL Type_error
                     | SOME (Let v31 v32 v33) => INL Type_error
                     | SOME (If v34 v35 v36) => INL Type_error
                     | SOME (Delay v37) => INL Type_error
                     | SOME (Force v39) => INL Type_error
                     | SOME (Value v40) => INL Type_error
                     | SOME (MkTick v41) => INL Type_error
                   od;
                   INL Diverge
                 od
Proof
  rw []
  \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ simp []
  \\ dxrule_then assume_tac eval_to_mono \\ gs []
  \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ simp []
  \\ dxrule_then assume_tac eval_to_mono \\ gs []
QED

Theorem eval_App_Tick:
  k ≤ 1 ∧ (∃j w. eval_to (j + k)  y = INR w)
  ∧ (∃j s v eL e. eval_to (j + k) g = INR (Closure s (Apps v (eL ++ [Tick (Force e)])))) ⇒
  ($= +++ v_rel) (INL Diverge)
                 do
                   xv <- eval_to k y;
                   fv <- eval_to k g;
                   (s,body,binds) <-
                   do (s,x'') <- dest_Closure fv; INR (s,x'',[]) od ++
                   do
                     (f,n) <- dest_Recclosure fv;
                     case ALOOKUP (REVERSE f) n of
                       NONE => INL Type_error
                     | SOME (Var v22) => INL Type_error
                     | SOME (Prim v23 v24) => INL Type_error
                     | SOME (Monad mop xs) => INL Type_error
                     | SOME (App v25 v26) => INL Type_error
                     | SOME (Lam s x'') =>
                         INR (s,x'',MAP (λ(g,x). (g,Recclosure f g)) f)
                     | SOME (Letrec v29 v30) => INL Type_error
                     | SOME (Let v31 v32 v33) => INL Type_error
                     | SOME (If v34 v35 v36) => INL Type_error
                     | SOME (Delay v37) => INL Type_error
                     | SOME (Force v39) => INL Type_error
                     | SOME (Value v40) => INL Type_error
                     | SOME (MkTick v41) => INL Type_error
                   od;
                   eval_to (k - 1) (subst (binds ++ [(s, xv)]) body)
                 od
Proof
  rw []
  \\ Cases_on ‘eval_to k y = INL Diverge’ \\ simp []
  \\ dxrule_then assume_tac eval_to_mono \\ gs []
  \\ Cases_on ‘eval_to k g = INL Diverge’ \\ simp []
  \\ dxrule_then assume_tac eval_to_mono \\ gs []
  \\ simp [FOLDL_APPEND, subst1_def]
  \\ Cases_on ‘eval_to k g’ \\ gvs [subst_Apps, subst1_def, FOLDL_APPEND]
  \\ once_rewrite_tac [eval_to_def]
  \\ once_rewrite_tac [eval_to_def]
  \\ gvs []
QED

Theorem eval_App_Tick2:
  k ≠ 0 ∧ k ≤ 1 ∧ (∃j w. eval_to (j + k)  y = INR w) ∧
  (∃j s v eL vL e. eval_to (j + k) g = INR (Closure s (Apps v (eL ++ (Tick (Force e))::MAP Value vL ++ [Var s]))))
  ⇒ ($= +++ v_rel) (INL Diverge)
                   do
                     xv <- eval_to k y;
                     fv <- eval_to k g;
                     (s,body,binds) <-
                     do (s,x'') <- dest_Closure fv; INR (s,x'',[]) od ++
                     do
                       (f,n) <- dest_Recclosure fv;
                       case ALOOKUP (REVERSE f) n of
                         NONE => INL Type_error
                       | SOME (Var v22) => INL Type_error
                       | SOME (Prim v23 v24) => INL Type_error
                       | SOME (Monad mop xs) => INL Type_error
                       | SOME (App v25 v26) => INL Type_error
                       | SOME (Lam s x'') =>
                           INR (s,x'',MAP (λ(g,x). (g,Recclosure f g)) f)
                       | SOME (Letrec v29 v30) => INL Type_error
                       | SOME (Let v31 v32 v33) => INL Type_error
                       | SOME (If v34 v35 v36) => INL Type_error
                       | SOME (Delay v37) => INL Type_error
                       | SOME (Force v39) => INL Type_error
                       | SOME (Value v40) => INL Type_error
                       | SOME (MkTick v41) => INL Type_error
                     od;
                     eval_to (k - 1) (subst (binds ++ [(s, xv)]) body)
                   od
Proof
  rw []
  \\ Cases_on ‘eval_to k y = INL Diverge’ \\ simp []
  \\ dxrule_then assume_tac eval_to_mono \\ gs []
  \\ Cases_on ‘eval_to k g = INL Diverge’ \\ simp []
  \\ dxrule_then assume_tac eval_to_mono \\ gs []
  \\ Cases_on ‘k’ \\ fs []
  \\ rename1 ‘SUC n ≤ 1’
  \\ Cases_on ‘n’ \\ gs []
  \\ simp [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
  \\ rename1 ‘MAP _ eL ++ (Tick (Force (subst1 s w e)))::MAP Value vL ++ [Value w]’
  \\ ‘eval_to 0 (Tick (Force (subst1 s w e))) = INL Diverge’ by simp [eval_to_def]
  \\ dxrule_then (qspecl_then [‘vL ++ [w]’] assume_tac) eval_to_Apps_INL
  \\ gs [MAP_APPEND, FOLDL_APPEND]
QED

Theorem eval_App_Tick_Force_Val_Div:
  (∃j w. eval_to (j + k) y = INR w ∧ eval_to (k - 2) (Force (Value w)) = INL Diverge)
  ∧ (∃j s v eL e. eval_to (j + k) g = INR (Closure s (Apps v (eL ++ [Tick (Force (Var s))])))) ⇒
  ($= +++ v_rel) (INL Diverge)
                 do
                   xv <- eval_to k y;
                   fv <- eval_to k g;
                   (s,body,binds) <-
                   do (s,x'') <- dest_Closure fv; INR (s,x'',[]) od ++
                   do
                     (f,n) <- dest_Recclosure fv;
                     case ALOOKUP (REVERSE f) n of
                       NONE => INL Type_error
                     | SOME (Var v22) => INL Type_error
                     | SOME (Prim v23 v24) => INL Type_error
                     | SOME (Monad mop xs) => INL Type_error
                     | SOME (App v25 v26) => INL Type_error
                     | SOME (Lam s x'') =>
                         INR (s,x'',MAP (λ(g,x). (g,Recclosure f g)) f)
                     | SOME (Letrec v29 v30) => INL Type_error
                     | SOME (Let v31 v32 v33) => INL Type_error
                     | SOME (If v34 v35 v36) => INL Type_error
                     | SOME (Delay v37) => INL Type_error
                     | SOME (Force v39) => INL Type_error
                     | SOME (Value v40) => INL Type_error
                     | SOME (MkTick v41) => INL Type_error
                   od;
                   eval_to (k - 1) (subst (binds ++ [(s, xv)]) body)
                 od
Proof
  rw []
  \\ Cases_on ‘eval_to k y = INL Diverge’ \\ simp []
  \\ dxrule_then assume_tac eval_to_mono \\ gs []
  \\ Cases_on ‘eval_to k g = INL Diverge’ \\ simp []
  \\ dxrule_then assume_tac eval_to_mono
  \\ gs [subst_Apps, subst1_def]
  \\ simp [FOLDL_APPEND, eval_to_def, subst_funs_def]
QED

Theorem eval_to_Tick:
  ∀k e. k > 1 ⇒ eval_to (k - 1) (Tick e) = eval_to (k - 2) e
Proof
  rw [] \\ once_rewrite_tac [eval_to_def] \\ gvs [subst_funs_def]
QED

fun print_tac str t g = (print (str ^ "\n"); time t g);

Theorem force_arg_rel_eval_to:
  ∀k x y.
    force_arg_rel x y ⇒
      ∃j. ($= +++ v_rel) (eval_to k x) (eval_to (j + k) y)
Proof
 ho_match_mp_tac eval_to_ind \\ rw []
  >~ [‘Var m’] >- (
    gvs [Once force_arg_rel_def]
    \\ qexists_tac ‘0’
    \\ simp [eval_to_def])
  >~ [‘Value v’] >- (
    gvs [Once force_arg_rel_def]
    \\ qexists_tac ‘0’
    \\ simp [eval_to_def])
  >~ [‘Lam s x’] >- (
    gvs [Once force_arg_rel_def]
    \\ qexists_tac ‘0’
    \\ gvs [eval_to_def, v_rel_Closure])
  >~ [`Monad mop xs`]
  >- (gvs[Once force_arg_rel_def, eval_to_def] >> rw[Once v_rel_def])
 >~ [‘App f x’] >- print_tac "App" (
    gvs [Once force_arg_rel_def, eval_to_def]
    \\ rename1 ‘force_arg_rel x y’
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
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL force_arg_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ qpat_x_assum ‘force_arg_rel x0 _’ mp_tac
          \\ rw [Once force_arg_rel_cases] \\ gs []
          \\ Cases_on ‘x0’ \\ gvs [])
      >- (gvs [REVERSE_APPEND, ALOOKUP_APPEND] >>
          rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’ >>
          Cases_on ‘v2 = s’ >> gvs [] >>
          gvs [MEM_EL, EL_MAP] >>
          rename1 ‘ALOOKUP (REVERSE (LUPDATE (v1', Lams (vL1++[s]++vL2)
                                        (Apps (Var v2) _)) i ys)) (FST (EL n _))’ >>
          ‘ALL_DISTINCT (MAP FST (LUPDATE (v1', Lams (vL1 ++ [s] ++ vL2)
                         (Apps (Var v2)
                          (MAP Var vL1 ++ [Tick (Force (Var s))] ++ MAP Var vL2))) i ys))’
            by (gvs [LUPDATE_MAP] >>
                qspecl_then [‘ys’, ‘i’] assume_tac LUPDATE_ID_MAP_FST >> gvs [] >>
                ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] >>
                gvs [EL_MAP, LIST_REL_EL_EQN]) >>
          drule_then assume_tac alookup_distinct_reverse >>
          qspecl_then [‘LUPDATE (v1', Lams (vL1 ++ [s] ++ vL2)
             (Apps (Var v2) (MAP Var vL1 ++ [Tick (Force (Var s))] ++ MAP Var vL2))) i ys’, ‘n’]
                      assume_tac ALOOKUP_ALL_DISTINCT_EL >>
          qspecl_then [‘xs’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL >>
          ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] >>
          gvs [EL_MAP, EL_LUPDATE, alookup_distinct_reverse, LIST_REL_EL_EQN] >>
          Cases_on ‘n = i’ >> gvs [Lams_split] >>
          first_x_assum $ qspec_then ‘n’ assume_tac >>
          Cases_on ‘SND (EL n xs)’ >> gvs [force_arg_rel_def])
      >- (gvs [REVERSE_APPEND, ALOOKUP_APPEND] >>
          rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’ >>
          Cases_on ‘v2 = s’ >> gvs [] >>
          gvs [MEM_EL, EL_MAP] >>
          rename1 ‘ALOOKUP (REVERSE (LUPDATE (v1', Lams (vL1++[s]++vL2)
                                        (Apps (App (Var v2) _) _)) i ys)) (FST (EL n _))’ >>
          ‘ALL_DISTINCT (MAP FST (LUPDATE (v1', Lams (vL1 ++ [s] ++ vL2)
                         (Apps (Var v2)
                          (Var s::MAP Var vL1 ++ [Tick (Force (Var s))] ++ MAP Var vL2))) i ys))’
            by (gvs [LUPDATE_MAP] >>
                qspecl_then [‘ys’, ‘i’] assume_tac LUPDATE_ID_MAP_FST >> gvs [] >>
                ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] >>
                gvs [EL_MAP, LIST_REL_EL_EQN]) >>
          drule_then assume_tac alookup_distinct_reverse >>
          qspecl_then [‘LUPDATE (v1', Lams (vL1 ++ [s] ++ vL2)
       (Apps (Var v2) (Var s::MAP Var vL1 ++ [Tick (Force (Var s))] ++ MAP Var vL2))) i ys’, ‘n’]
                      assume_tac ALOOKUP_ALL_DISTINCT_EL >>
          qspecl_then [‘xs’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL >>
          ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] >>
          gvs [EL_MAP, EL_LUPDATE, alookup_distinct_reverse, LIST_REL_EL_EQN] >>
          Cases_on ‘n = i’ >> gvs [Lams_split] >>
          first_x_assum $ qspec_then ‘n’ assume_tac >>
          Cases_on ‘SND (EL n xs)’ >> gvs [force_arg_rel_def]))
    \\ pairarg_tac \\ gvs []
    \\ Cases_on ‘v2’ \\ gvs [v_rel_def, dest_anyClosure_def]
    >~[‘Closure _ _’]
    >- print_tac "Default Closure"
       (IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ rename1 ‘eval_to (k - 1) (subst1 s v1 body)’
        \\ rename1 ‘v_rel v1 w1’ \\ rename1 ‘force_arg_rel body body'’
        \\ last_x_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘body’, ‘subst1 s w1 body'’] mp_tac
        \\ impl_tac
        >- (gvs [] \\ irule force_arg_rel_subst \\ gvs [])
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
    (* Closure -> Lams (Apps ( )) HD *)
    >- print_tac "Closure 1/8" (
        IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ simp [] \\ irule eval_App_div
            \\ first_x_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any)
        \\ Cases_on ‘vL2’ \\ gvs []
        >- (gvs [subst_Lams, ALL_DISTINCT_APPEND]
            \\ rename1 ‘subst1 s v1 (subst _ (Let _ _ x2))’
            \\ Cases_on ‘vL3 = []’ \\ gvs [eval_to_Lams]
            >- (last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Letrec [] (Force (Value v1))’,
                                          ‘Letrec [] (Force (Value w1))’] mp_tac
                \\ impl_tac
                >- (gvs [subst1_def] \\ irule force_arg_rel_Letrec
                    \\ gvs [force_arg_rel_def])
                \\ disch_then $ qx_choose_then ‘j2’ assume_tac
                \\ gvs [subst_def]
                \\ CASE_TAC >~[‘ALOOKUP _ _ = SOME _’]
                >- (dxrule_then assume_tac ALOOKUP_MEM \\ gvs []
                    \\ gvs [MEM_EL, EL_ZIP])
                \\ gvs [subst1_def, subst1_notin_frees, freevars_subst]
                \\ once_rewrite_tac [eval_to_def]
                \\ IF_CASES_TAC \\ gvs []
                >- (qexists_tac ‘0’ \\ simp []
                    \\ irule eval_App_Tick
                    \\ first_x_assum $ irule_at Any
                    \\ first_x_assum $ irule_at Any
                    \\ first_x_assum $ irule_at Any)
                \\ gs [eval_to_Tick]
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1)) = INL Diverge’
                >- (qexists_tac ‘0’ \\ simp []
                    \\ irule eval_App_Tick_Force_Val_Div
                    \\ first_x_assum $ irule_at $ Pos hd
                    \\ first_x_assum $ irule_at $ Pos hd
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ simp []
                    \\ drule_then (qspecl_then [‘j2 + k - 2’] assume_tac) eval_to_mono
                    \\ gs []
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gs [])
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1))’
                >~[‘INL _’]
                >- (qexists_tac ‘j + j1 + j2’
                    \\ last_x_assum $ qspecl_then [‘j1 + j2’] assume_tac
                    \\ last_x_assum $ qspecl_then [‘j + j2’] assume_tac
                    \\ gs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, FOLDL_APPEND, eval_to_Tick]
                    \\ gs [SF ETA_ss]
                    \\ once_rewrite_tac [eval_to_def]
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gs []
                    \\ dxrule_then (qspecl_then [‘j + j1 + j2 + k - 2’] assume_tac) eval_to_mono
                    \\ gs [eval_to_Tick]
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gs [])
                \\ gs []
                \\ rename1 ‘eval_to (k - 2) (Force (Value v1)) = INR v2’
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gs []
                \\ ‘∀j3. eval_to (j + j1 + j2 + j3 + k - 2) (Force (Value w1))
                         = eval_to (j2 + k - 2) (Force (Value w1))’
                  by (gen_tac \\ irule eval_to_mono \\ gs [])
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gs []
                \\ rename1 ‘v_rel v2 w2’ \\ rename1 ‘force_arg_rel x2 y2’
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
                >- (gs [subst_APPEND]
                    \\ irule force_arg_rel_subst \\ gs [MAP_ZIP, LIST_REL_EL_EQN]
                    \\ irule force_arg_rel_subst \\ gs [force_arg_rel_def])
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
                    >- (simp [FOLDL_APPEND] \\ once_rewrite_tac [eval_to_def] \\ simp [])
                    \\ qspecl_then [‘Tick (Force (Value w1))’, ‘k - 1’] assume_tac eval_to_Apps_APPEND1
                    \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gs [eval_to_Tick]
                    \\ qspecl_then [‘vL1 ++ [s2]’, ‘eL2 ++ [w2]’, ‘y2’, ‘k - 1’]
                                   assume_tac eval_to_Apps_Lams_not_0
                    \\ gvs [LIST_REL_EL_EQN]
                    \\ gvs [subst_APPEND, subst_def, GSYM LAMBDA_PROD, FILTER_T, GSYM ZIP_APPEND]
                    \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1, eL2)) (subst1 s2 w2 y2)) = INL Diverge’
                    \\ gs []
                    \\ dxrule_then (qspecl_then [‘j3 + k - 2’] assume_tac) eval_to_mono
                    \\ gs [eval_to_Tick])
                \\ qexists_tac ‘j + j1 + j2 + j3’
                \\ last_x_assum $ qspecl_then [‘j1 + j2 + j3’] assume_tac
                \\ last_x_assum $ qspecl_then [‘j + j2 + j3’] assume_tac
                \\ gs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
                \\ gs [SF ETA_ss]
                \\ qspecl_then [‘Tick (Force (Value w1))’, ‘j + j1 + j2 + j3 + k - 1’]
                               assume_tac eval_to_Apps_APPEND1
                \\ gs [eval_to_Tick]
                \\ rename1 ‘eval_to _ (Apps (Value (Closure (HD (vL1 ++ [s2])) (Lams _ y2)))
                                       (MAP Value eL2 ++ [Value w2]))’
                \\ qspecl_then [‘vL1 ++ [s2]’, ‘eL2 ++ [w2]’, ‘y2’, ‘j + j1 + j2 + j3 + k - 1’]
                               assume_tac eval_to_Apps_Lams_not_0
                \\ gs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, subst_APPEND, subst_def]
                \\ gs [GSYM LAMBDA_PROD, FILTER_T, eval_to_Tick]
                \\ ‘eval_to (j + j1 + j2 + j3 + k - 2) (subst (ZIP (vL1, eL2)) (subst1 s2 w2 y2))
                    = eval_to (j3 + k - 2) (subst (ZIP (vL1, eL2)) (subst1 s2 w2 y2))’
                  by (irule eval_to_mono \\ gs []
                      \\ strip_tac \\ gs []
                      \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1, eL1)) (subst1 s2 v2 x2))’ \\ gs [])
                \\ gs [])
            \\ qexists_tac ‘j + j1’ \\ gvs []
            \\ last_x_assum $ qspecl_then [‘j1’] assume_tac \\ gvs []
            \\ gvs [subst_Lams, subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                    SF ETA_ss, eval_to_Lams]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
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
            \\ first_x_assum $ qspecl_then [‘EL (n - (LENGTH vL2 + 1)) vL3’] assume_tac
            \\ gvs [EL_MEM])
        \\ irule EQ_TRANS \\ irule_at Any subst_commutes
        \\ gvs [MAP_ZIP]
        \\ conj_tac >- (strip_tac \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
        \\ gvs [GSYM subst_APPEND]
        \\ qspecl_then [‘vL1’, ‘eL1’, ‘[h]’, ‘[v1]’] assume_tac ZIP_APPEND
        \\ gvs [])

    (* Closure -> Lams (Apps ( )) HD 2 *)
    >- print_tac "Closure 2/8" (
        IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ simp [] \\ irule eval_App_div
            \\ first_x_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any)
        \\ Cases_on ‘vL2’ \\ gvs []
        >- (gvs [subst_Lams, ALL_DISTINCT_APPEND]
            \\ rename1 ‘subst1 s v1 (subst _ (Let _ _ x2))’
            \\ Cases_on ‘vL3 = []’ \\ gvs [eval_to_Lams]
            >- (last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Tick (Force (Value v1))’,
                                          ‘Tick (Force (Value w1))’] mp_tac
                \\ impl_tac
                >- (gvs [subst1_def] \\ irule force_arg_rel_Letrec
                    \\ gvs [force_arg_rel_def])
                \\ disch_then $ qx_choose_then ‘j2’ assume_tac
                \\ gvs [subst_def]
                \\ CASE_TAC >~[‘ALOOKUP _ _ = SOME _’]
                >- (dxrule_then assume_tac ALOOKUP_MEM \\ gvs []
                    \\ gvs [MEM_EL, EL_ZIP])
                \\ gvs [subst1_def, subst1_notin_frees, freevars_subst]
                \\ once_rewrite_tac [eval_to_def]
                \\ IF_CASES_TAC \\ gvs []
                >- (qexists_tac ‘0’ \\ simp []
                    \\ irule eval_App_Tick
                    \\ first_x_assum $ irule_at Any
                    \\ first_x_assum $ irule_at Any
                    \\ first_x_assum $ irule_at Any)
                \\ gs [eval_to_Tick]
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1)) = INL Diverge’
                >- (qexists_tac ‘0’ \\ simp []
                    \\ irule eval_App_Tick_Force_Val_Div
                    \\ first_x_assum $ irule_at $ Pos hd
                    \\ first_x_assum $ irule_at $ Pos hd
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ simp []
                    \\ drule_then (qspecl_then [‘j2 + k - 2’] assume_tac) eval_to_mono
                    \\ gs []
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gs [])
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1))’
                >~[‘INL _’]
                >- (qexists_tac ‘j + j1 + j2’
                    \\ last_x_assum $ qspecl_then [‘j1 + j2’] assume_tac
                    \\ last_x_assum $ qspecl_then [‘j + j2’] assume_tac
                    \\ gs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, FOLDL_APPEND, eval_to_Tick]
                    \\ gs [SF ETA_ss]
                    \\ once_rewrite_tac [eval_to_def]
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gs []
                    \\ dxrule_then (qspecl_then [‘j + j1 + j2 + k - 2’] assume_tac) eval_to_mono
                    \\ gs [eval_to_Tick]
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gs [])
                \\ gs []
                \\ rename1 ‘eval_to (k - 2) (Force (Value v1)) = INR v2’
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gs []
                \\ ‘∀j3. eval_to (j + j1 + j2 + j3 + k - 2) (Force (Value w1))
                         = eval_to (j2 + k - 2) (Force (Value w1))’
                  by (gen_tac \\ irule eval_to_mono \\ gs [])
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gs []
                \\ rename1 ‘v_rel v2 w2’ \\ rename1 ‘force_arg_rel x2 y2’
                \\ ‘∀e. subst1 s2 v2 (subst1 s v1 e) = subst1 s v1 (subst1 s2 v2 e)’ by gs [subst1_commutes]
                \\ ‘subst1 s2 v2 (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1, eL1))) x2) =
                    subst (ZIP (vL1, eL1)) (subst1 s2 v2 x2)’
                  by (irule EQ_TRANS \\ irule_at Any subst_commutes
                      \\ gs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP]
                      \\ AP_THM_TAC \\ AP_TERM_TAC
                      \\ gs [FILTER_EQ_ID, EVERY_EL, MEM_EL, EL_ZIP]
                      \\ rw [] \\ rename1 ‘n < _’
                      \\ rpt $ first_x_assum $ qspecl_then [‘n’] assume_tac \\ gs [])
                \\ ‘∀e. subst1 s v1 (subst (ZIP (vL1, eL1)) e) =
                   subst (ZIP (vL1, eL1)) (subst1 s v1 e)’
                  by (gen_tac \\ irule subst_commutes \\ gs [MAP_ZIP])
                \\ gs []
                \\ last_x_assum $ qspecl_then [‘ZIP (vL1, eL1) ++ [(s, v1)]’, ‘s2’, ‘v2’, ‘Tick x2’,
                                               ‘subst ([(s, w1)] ++ ZIP(vL1, eL2) ++ [(s2, w2)]) (Tick y2)’] mp_tac
                \\ impl_tac
                >- (gs [subst_APPEND]
                    \\ qspecl_then [‘subst1 s2 w2 (Tick y2)’, ‘[(s,w1)]’,
                                    ‘ZIP (vL1,eL2)’] assume_tac subst_commutes
                    \\ gs [MAP_ZIP, LIST_REL_EL_EQN]
                    \\ irule force_arg_rel_subst \\ gs [MAP_ZIP, LIST_REL_EL_EQN]
                    \\ gs [force_arg_rel_subst, force_arg_rel_def])
                \\ disch_then $ qx_choose_then ‘j3’ assume_tac
                \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1, eL1)) (subst1 s v1 (subst1 s2 v2 x2))) = INL Diverge’
                >- (qexists_tac ‘0’
                    \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                    \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
                    \\ Cases_on ‘eval_to k y’ \\ gs []
                    \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                    \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
                    \\ Cases_on ‘eval_to k g’ \\ gs []
                    \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
                    \\ Cases_on ‘eval_to (k - 1) (Tick (Force (Value w1))) = INL Diverge’
                    >- (simp [FOLDL_APPEND] \\ once_rewrite_tac [eval_to_def] \\ simp [])
                    \\ qspecl_then [‘Tick (Force (Value w1))’, ‘k - 1’] assume_tac eval_to_Apps_APPEND1
                    \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gs [eval_to_Tick]
                    \\ first_x_assum $ qspecl_then [‘Value (Closure s
                                                            (Lams (vL1 ++ [s2]) y2))’,
                                                    ‘MAP Value eL2 ++ [Value w1]’] assume_tac
                    \\ once_rewrite_tac [CONS_APPEND] \\ gs []
                    \\ qspecl_then [‘[s] ++ vL1 ++ [s2]’, ‘[w1] ++ eL2 ++ [w2]’, ‘y2’, ‘k - 1’]
                                   assume_tac eval_to_Apps_Lams_not_0
                    \\ gs [LIST_REL_EL_EQN]
                    \\ gs [subst_APPEND, subst_def, GSYM LAMBDA_PROD, FILTER_T, GSYM ZIP_APPEND]
                    \\ Cases_on ‘eval_to (k - 2) (subst ((s, w1)::(ZIP (vL1, eL2) ++ [(s2, w2)])) y2)
                                 = INL Diverge’
                    \\ gs []
                    \\ dxrule_then (qspecl_then [‘j3 + k - 2’] assume_tac) eval_to_mono
                    \\ gs [eval_to_Tick])
                \\ qexists_tac ‘j + j1 + j2 + j3’
                \\ last_x_assum $ qspecl_then [‘j1 + j2 + j3’] assume_tac
                \\ last_x_assum $ qspecl_then [‘j + j2 + j3’] assume_tac
                \\ gs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
                \\ gs [SF ETA_ss]
                \\ qspecl_then [‘Tick (Force (Value w1))’, ‘j + j1 + j2 + j3 + k - 1’]
                               assume_tac eval_to_Apps_APPEND1
                \\ gs [eval_to_Tick]
                \\ rename1 ‘eval_to _ (Apps (App (Value (Closure s (Lams (vL1 ++ [s2]) y2))) (Value w1))
                                       (MAP Value eL2 ++ _))’
                \\ first_x_assum $ qspecl_then [‘Value (Closure s
                                                        (Lams (vL1 ++ [s2]) y2))’,
                                                ‘[Value w1] ++ MAP Value eL2’] assume_tac
                \\ qspecl_then [‘s::vL1 ++ [s2]’, ‘w1::eL2 ++ [w2]’, ‘y2’, ‘j + j1 + j2 + j3 + k - 1’]
                               assume_tac eval_to_Apps_Lams_not_0
                \\ gs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, subst_APPEND, subst_def, eval_to_Tick]
                \\ gs [GSYM LAMBDA_PROD, FILTER_T]
                \\ rename1 ‘_ (eval_to _ expr1) (eval_to _ expr2)’
                \\ ‘eval_to (j + j1 + j2 + j3 + k - 2) expr2
                    = eval_to (j3 + k - 2) expr2’
                  by (irule eval_to_mono \\ gvs []
                      \\ strip_tac \\ gvs []
                      \\ Cases_on ‘eval_to (k - 2) expr1’ \\ gvs [])
                \\ gs [])
            \\ qexists_tac ‘j + j1’ \\ gs []
            \\ last_x_assum $ qspecl_then [‘j1’] assume_tac \\ gs []
            \\ gs [subst_Lams, subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                    SF ETA_ss, eval_to_Lams]
            \\ gs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
            \\ irule_at (Pos hd) EQ_REFL
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_assum $ irule_at Any
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
            \\ first_x_assum $ irule_at Any
            \\ gs []
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_x_assum $ irule_at Any
            \\ gs []
            \\ first_x_assum $ irule_at $ Pos last
            \\ qexists_tac ‘[]’ \\ gs []
            \\ ‘∀e. subst1 s v1 (subst (ZIP (vL1, eL1)) e) = subst (ZIP (vL1 ++ [s], eL1 ++ [v1])) e’
              by (gen_tac \\ gs [GSYM ZIP_APPEND, subst_APPEND]
                  \\ irule subst_commutes \\ gs [MAP_ZIP]
                  \\ strip_tac \\ first_x_assum $ dxrule_then assume_tac \\ gs [])
            \\ gs []
            \\ irule_at (Pos $ el 2) EQ_REFL
            \\ first_x_assum $ irule_at $ Pos last
            \\ first_x_assum $ irule_at $ Pos last
            \\ gs [ALL_DISTINCT_APPEND]
            \\ irule LIST_EQ \\ rw [EL_MAP]
            \\ strip_tac \\ gs [EL_MEM])
        \\ qexists_tac ‘j + j1’ \\ gs []
        \\ last_x_assum $ qspecl_then [‘j1’] assume_tac \\ gs []
        \\ gs [subst_Lams, subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                SF ETA_ss, eval_to_Lams, ALL_DISTINCT_APPEND]
        \\ rename1 ‘HD (vL2 ++ s::vL3)’
        \\ ‘HD (vL2 ++ s::vL3) = HD (SNOC s vL2)’ by (Cases_on ‘vL2’ \\ gs []) \\ rw []
        \\ gs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by simp []
        \\ first_assum $ irule_at Any
        \\ first_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by simp []
        \\ first_x_assum $ irule_at Any
        \\ gvs []
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by simp []
        \\ first_x_assum $ irule_at Any
        \\ gs []
        \\ irule_at (Pos hd) EQ_REFL
        \\ gs [ALL_DISTINCT_APPEND]
        \\ first_x_assum $ irule_at $ Pos last \\ gs []
        \\ qexists_tac ‘eL2 ++ [w1]’ \\ qexists_tac ‘eL1 ++ [v1]’
        \\ rw [] \\ gs []
        >- (irule LIST_EQ
            \\ rw [EL_APPEND_EQN, EL_MAP] \\ gs [EL_MEM]
            \\ strip_tac \\ gs [EL_MEM]
            \\ rename1 ‘n < _’
            \\ first_x_assum $ qspecl_then [‘EL (n - (LENGTH vL2 + 1)) vL3’] assume_tac
            \\ gs [EL_MEM])
        \\ gs [GSYM ZIP_APPEND, subst_APPEND]
        \\ irule_at Any subst_commutes
        \\ gs [MAP_ZIP]
        \\ strip_tac \\ last_x_assum $ dxrule_then assume_tac \\ gs [])

    (* Closure -> Lams (Apps ( )) TL *)
    >- print_tac "Closure 3/8" (
        IF_CASES_TAC
        >- (qexists_tac ‘0’ \\ simp [] \\ irule eval_App_div
            \\ first_x_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any)
        \\ Cases_on ‘vL3’
        \\ gvs [subst_Lams, ALL_DISTINCT_APPEND]
        \\ rename1 ‘Lams vL3 (subst1 v3 _ _)’
        \\ Cases_on ‘vL3 = []’ \\ gs []
        >- (rename1 ‘Tick (Force (Value w2))::MAP _ _’ \\ rename1 ‘v_rel v2 w2’
            \\ last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Letrec [] (Force (Value v2))’,
                                         ‘Letrec [] (Force (Value w2))’] mp_tac
            \\ impl_tac
            >- (gs [subst1_def] \\ irule force_arg_rel_Letrec
                \\ gs [force_arg_rel_def])
            \\ disch_then $ qx_choose_then ‘j2’ assume_tac
            \\ gs [subst_def]
            \\ once_rewrite_tac [eval_to_def]
            \\ IF_CASES_TAC \\ gs []
            >- (qexists_tac ‘0’ \\ simp []
                \\ irule eval_App_Tick2 \\ simp []
                \\ first_x_assum $ irule_at Any
                \\ first_x_assum $ irule_at Any)
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
            \\ gs [eval_to_Tick]
            \\ Cases_on ‘eval_to (k - 2) (Force (Value v2))’
            >~[‘INL err’]
            >- (qexists_tac ‘j + j1 + j2’
                \\ last_x_assum $ qspecl_then [‘j1 + j2’] assume_tac
                \\ last_x_assum $ qspecl_then [‘j + j2’] assume_tac
                \\ gs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, eval_to_Tick]
                \\ gs [SF ETA_ss]
                \\ ‘eval_to (j + j1 + j2 + k - 1) (Tick (Force (Value w2))) = INL err’
                  by (Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2)) = INL Diverge’ \\ gs [eval_to_Tick]
                      \\ drule_then (qspecl_then [‘j + j1 + j2 + k - 2’] assume_tac) eval_to_mono
                      \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2))’ \\ gs [])
                \\ dxrule_then (qspecl_then [‘eL2' ++ [w1]’] assume_tac) eval_to_Apps_INL
                \\ gs [MAP_APPEND, FOLDL_APPEND])
            \\ rename1 ‘eval_to (k - 2) (Force (Value v2)) = INR v2'’
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2)) = INL Diverge’ \\ gs []
            \\ ‘∀j3. eval_to (j + j1 + j2 + j3 + k - 2) (Force (Value w2))
                     = eval_to (j2 + k - 2) (Force (Value w2))’
              by (gen_tac \\ irule eval_to_mono \\ simp [])
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2))’ \\ gs []
            \\ rename1 ‘v_rel v2' w2'’ \\ rename1 ‘force_arg_rel x2 y2’
            \\ ‘subst1 s2 v2' (subst1 v3 v1 (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) x2)) =
                subst (ZIP (vL1 ++ vL2, eL1 ++ eL2)) (subst1 v3 v1 (subst1 s2 v2' x2))’
              by (gs [subst1_commutes]
                  \\ ‘∀e. subst1 v3 v1 (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) e) =
                          subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) (subst1 v3 v1 e)’
                    by (gen_tac \\ irule subst_commutes \\ gs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP]
                        \\ conj_tac \\ strip_tac \\ first_x_assum $ qspecl_then [‘v3’] assume_tac \\ gs [])
                  \\ ‘∀e. subst1 s2 v2' (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) e) =
                          subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) (subst1 s2 v2' e)’
                    by (gen_tac \\ irule subst_commutes \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP])
                  \\ gs []
                  \\ AP_THM_TAC \\ AP_TERM_TAC
                  \\ gs [FILTER_EQ_ID, EVERY_EL, MEM_EL, EL_ZIP, EL_APPEND_EQN]
                  \\ rw [] \\ rename1 ‘n < _’
                  \\ strip_tac \\ gvs []
                  \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                  \\ gs [])
            \\ gs []
            \\ last_x_assum $ qspecl_then [‘ZIP (vL1 ++ vL2, eL1 ++ eL2) ++ [(v3, v1)]’, ‘s2’, ‘v2'’, ‘Tick x2’,
              ‘subst (ZIP(vL1 ++ vL2, eL1' ++ eL2') ++ [(v3, w1)] ++ [(s2, w2')]) (Tick y2)’] mp_tac
            \\ impl_tac
            >- (gs [subst_APPEND, LIST_REL_EL_EQN]
                \\ irule force_arg_rel_subst \\ gs [MAP_ZIP, LIST_REL_EL_EQN]
                \\ rw [EL_APPEND_EQN] \\ gs []
                \\ irule force_arg_rel_subst \\ gs [force_arg_rel_def]
                \\ irule force_arg_rel_subst \\ gs [force_arg_rel_def])
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
                    \\ gs [MAP_APPEND, FOLDL_APPEND])
                \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                \\ qspecl_then [‘eL2' ++ [w1]’, ‘Tick (Force (Value w2))’, ‘k - 1’] assume_tac eval_to_Apps_INR
                \\ gs [FOLDL_APPEND]
                \\ qspecl_then [‘vL1 ++ s2::vL2 ++ [v3]’, ‘eL1' ++ w2'::eL2' ++ [w1]’, ‘y2’, ‘k - 1’]
                               assume_tac eval_to_Apps_Lams_not_0
                \\ Cases_on ‘eval_to (k - 2) (Force (Value w2))’
                \\ gs [LIST_REL_EL_EQN, FOLDL_APPEND, subst_def, GSYM ZIP_APPEND, subst_APPEND, eval_to_Tick]
                \\ gs [GSYM LAMBDA_PROD, FILTER_T]
                \\ once_rewrite_tac [CONS_APPEND] \\ gs [subst_APPEND]
                \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1, eL1')) (subst1 s2 w2' (subst (ZIP (vL2, eL2'))
                                       (subst1 v3 w1 y2)))) = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j3 + k - 2’] assume_tac) eval_to_mono \\ gs []
                \\ ‘∀e. subst1 s2 w2' (subst (ZIP (vL2, eL2')) e) = subst (ZIP (vL2, eL2')) (subst1 s2 w2' e)’
                  by (gen_tac \\ irule subst_commutes \\ gs [MAP_ZIP])
                \\ gs [subst1_commutes])
            \\ qexists_tac ‘j + j1 + j2 + j3’
            \\ last_x_assum $ qspecl_then [‘j1 + j2 + j3’] assume_tac
            \\ last_x_assum $ qspecl_then [‘j + j2 + j3’] assume_tac
            \\ gs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
            \\ gs [SF ETA_ss]
            \\ qspecl_then [‘eL2' ++ [w1]’, ‘Tick (Force (Value w2))’, ‘j + j1 + j2 + j3 + k - 1’]
                           assume_tac eval_to_Apps_INR
            \\ ‘eval_to (j2 + k - 2) (Force (Value w2)) ≠ INL Diverge’ by gvs []
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + j3 + k - 2’] assume_tac) eval_to_mono
            \\ gs [FOLDL_APPEND]
            \\ qspecl_then [‘vL1 ++ [s2] ++ vL2 ++ [v3]’, ‘eL1' ++ [w2'] ++ eL2' ++ [w1]’,
                            ‘y2’, ‘j + j1 + j2 + j3 + k - 1’]
                           assume_tac eval_to_Apps_Lams_not_0
            \\ gs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, subst_APPEND, subst_def, FOLDL_APPEND]
            \\ once_rewrite_tac [CONS_APPEND] \\ gs [subst_APPEND, GSYM LAMBDA_PROD, FILTER_T, eval_to_Tick]
            \\ ‘eval_to (j3 + k - 2) (subst (ZIP (vL1, eL1')) (subst (ZIP (vL2, eL2'))
                                                               (subst1 v3 w1 (subst1 s2 w2' y2)))) ≠ INL Diverge’
              by (strip_tac
                  \\ Cases_on ‘eval_to (k − 2) (subst (ZIP (vL1,eL1))
                                                (subst (ZIP (vL2,eL2)) (subst1 v3 v1 (subst1 s2 v2' x2))))’
                  \\ gs [])
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + j3 + k - 2’] assume_tac) eval_to_mono \\ gvs []
            \\ ‘∀e. subst1 s2 w2' (subst (ZIP (vL2, eL2')) e) = subst (ZIP (vL2, eL2')) (subst1 s2 w2' e)’
              by (gen_tac \\ irule subst_commutes \\ gs [MAP_ZIP])
            \\ gs [subst1_commutes])
        \\ simp [eval_to_Lams]
        \\ qexists_tac ‘j + j1’ \\ simp []
        \\ last_x_assum $ qspecl_then [‘j1’] assume_tac
        \\ gs [subst1_def, subst_Lams, subst_Apps, eval_to_Lams]
        \\ gs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, subst1_def, SF ETA_ss]
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by simp []
        \\ first_assum $ irule_at Any
        \\ first_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by simp []
        \\ first_x_assum $ irule_at Any
        \\ gs []
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by simp []
        \\ first_x_assum $ irule_at Any
        \\ gs []
        \\ first_x_assum $ irule_at $ Pos last
        \\ Q.REFINE_EXISTS_TAC ‘l1 ++ [variable]’
        \\ gs [] \\ irule_at (Pos hd) EQ_REFL
        \\ gs [ALL_DISTINCT_APPEND]
        \\ first_assum $ irule_at $ Pos last \\ gs []
        \\ first_assum $ irule_at $ Pos last \\ gs []
        \\ qexists_tac ‘eL2' ++ [w1]’ \\ gs []
        \\ qexists_tac ‘eL2 ++ [v1]’ \\ gs []
        \\ qexists_tac ‘eL1'’ \\ qexists_tac ‘eL1’ \\ gs []
        \\ rw [] \\ gs []
        >- (irule LIST_EQ \\ rw [EL_MAP]
            \\ strip_tac \\ gs [EL_MEM])
        >- (irule EQ_TRANS \\ irule_at Any subst_commutes
            \\ gs [MAP_ZIP]
            \\ conj_tac
            >- (rw[] \\ strip_tac \\ first_x_assum $ qspecl_then [‘v3’] assume_tac \\ gs [])
            \\ gs [GSYM subst_APPEND]
            \\ qspecl_then [‘vL1 ++ vL2’, ‘eL1 ++ eL2’, ‘[v3]’, ‘[v1]’] assume_tac ZIP_APPEND
            \\ gs [])
        \\ strip_tac
        \\ first_x_assum $ qspecl_then [‘v3’] assume_tac
        \\ gs [])

    (* Closure -> Lams (Apps ( )) TL 2 *)
    >- print_tac "Closure 4/8" (
        IF_CASES_TAC
        >- (qexists_tac ‘0’ \\ simp [] \\ irule eval_App_div
            \\ first_x_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any)
        \\ Cases_on ‘vL3’
        \\ gs [subst_Lams, ALL_DISTINCT_APPEND]
        \\ rename1 ‘Lams vL3 (subst1 v3 _ _)’
        \\ Cases_on ‘vL3 = []’ \\ gs []
        >- (rename1 ‘Tick (Force (Value w2))::MAP _ _’ \\ rename1 ‘v_rel v2 w2’
            \\ last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Tick (Force (Value v2))’,
                                         ‘Tick (Force (Value w2))’] mp_tac
            \\ impl_tac
            >- (gvs [subst1_def] \\ irule force_arg_rel_Letrec
                \\ gvs [force_arg_rel_def])
            \\ disch_then $ qx_choose_then ‘j2’ assume_tac
            \\ gvs [subst_def]
            \\ once_rewrite_tac [eval_to_def]
            \\ IF_CASES_TAC \\ gvs []
            >- (qexists_tac ‘0’ \\ simp []
                \\ irule eval_App_Tick2 \\ simp []
                \\ first_x_assum $ irule_at Any
                \\ first_x_assum $ irule_at Any)
            \\ gvs [GSYM ZIP_APPEND, REVERSE_APPEND, ALOOKUP_APPEND]
            \\ CASE_TAC \\ gs []
            >~[‘ALOOKUP _ _ = SOME _’]
            >- (dxrule_then assume_tac ALOOKUP_MEM \\ gs []
                \\ dxrule_then assume_tac MEM_FST \\ gs [MAP_ZIP]
                \\ rename1 ‘MEM s vL2’
                \\ first_x_assum $ qspec_then ‘s’ assume_tac \\ gs [])
            \\ gs [subst1_def]
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
                \\ gvs [FOLDL_APPEND, MAP_APPEND]
                \\ rename1 ‘eval_to _ (App (Apps (App e _) _) _)’
                \\ first_x_assum $ qspecl_then [‘e’, ‘[]’] assume_tac \\ gvs [])
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
                \\ gvs [MAP_APPEND, FOLDL_APPEND]
                \\ rename1 ‘eval_to _ (App (Apps (App e _) _) _)’
                \\ first_x_assum $ qspecl_then [‘e’, ‘[]’] assume_tac \\ gvs [])
            \\ gvs []
            \\ rename1 ‘eval_to (k - 2) (Force (Value v2)) = INR v2'’
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2)) = INL Diverge’ \\ gvs []
            \\ ‘∀j3. eval_to (j + j1 + j2 + j3 + k - 2) (Force (Value w2))
                     = eval_to (j2 + k - 2) (Force (Value w2))’
              by (gen_tac \\ irule eval_to_mono \\ gvs [])
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2))’ \\ gvs []
            \\ rename1 ‘v_rel v2' w2'’ \\ rename1 ‘force_arg_rel x2 y2’
            \\ rename1 ‘ZIP _ ++ (s, v2)::ZIP _’
            \\ ‘subst1 s2 v2' (subst1 v3 v1 (subst (FILTER (λ(n,x). n ≠ s2)
                                                    (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2))) x2)) =
                subst (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2)) (subst1 v3 v1 (subst1 s2 v2' x2))’
              by (gvs [subst1_commutes]
                  \\ ‘∀e. subst1 v3 v1 (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2))) e) =
                          subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2))) (subst1 v3 v1 e)’
                    by (gen_tac \\ irule subst_commutes \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP]
                        \\ conj_tac \\ strip_tac \\ first_x_assum $ qspecl_then [‘v3’] assume_tac \\ gvs [])
                  \\ ‘∀e. subst1 s2 v2' (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2))) e) =
                          subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2))) (subst1 s2 v2' e)’
                    by (gen_tac \\ irule subst_commutes \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP])
                  \\ gvs []
                  \\ AP_THM_TAC \\ AP_TERM_TAC
                  \\ once_rewrite_tac [CONS_APPEND]
                  \\ gvs [FILTER_EQ_ID, EVERY_EL, MEM_EL, EL_ZIP, EL_APPEND_EQN]
                  \\ rw [] \\ rename1 ‘n < _’
                  \\ strip_tac \\ gvs []
                  >- (gvs [GSYM ADD1, NOT_LESS, GSYM LESS_EQ_IFF_LESS_SUC]
                      \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [])
                  \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                  \\ gvs [])
            \\ gvs [GSYM ZIP_APPEND]
            \\ last_x_assum $ qspecl_then [‘ZIP (vL1, eL1) ++ (s,v2)::ZIP (vL2, eL2) ++ [(v3, v1)]’,
                                           ‘s2’, ‘v2'’, ‘Tick x2’,
              ‘subst ((s, w2)::ZIP (vL1, eL1') ++ (s2, w2')::ZIP (vL2, eL2') ++ [(v3, w1)]) (Tick y2)’] mp_tac
            \\ impl_tac
            >- (once_rewrite_tac [CONS_APPEND]
                \\ gvs [GSYM ZIP_APPEND, subst_APPEND, LIST_REL_EL_EQN]
                \\ ‘∀e. subst1 s w2 (subst (ZIP (vL1, eL1')) e) = subst (ZIP (vL1, eL1')) (subst1 s w2 e)’
                  by (gen_tac \\ irule subst_commutes
                      \\ rpt $ first_x_assum $ qspec_then ‘s’ assume_tac
                      \\ gvs [MAP_ZIP, MEM_EL])
                \\ gvs []
                \\ irule force_arg_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                \\ irule force_arg_rel_subst \\ fs []
                \\ ‘∀e. subst1 s2 w2' (subst (ZIP (vL2, eL2')) e) = subst (ZIP (vL2, eL2')) (subst1 s2 w2' e)’
                  by (gen_tac \\ irule subst_commutes
                      \\ rpt $ first_x_assum $ qspec_then ‘s’ assume_tac
                      \\ gvs [MAP_ZIP, MEM_EL])
                \\ gs []
                \\ irule force_arg_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                \\ gvs [force_arg_rel_def, force_arg_rel_subst, subst1_commutes])
            \\ disch_then $ qx_choose_then ‘j3’ assume_tac
            \\ Cases_on ‘eval_to (k - 2) (subst (ZIP (vL1, eL1) ++ (s, v2)::ZIP (vL2, eL2))
                                          (subst1 v3 v1 (subst1 s2 v2' x2))) = INL Diverge’
            >- (qexists_tac ‘0’ \\ gs []
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k y’ \\ gs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘k + j1’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g’ \\ gs []
                \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
                \\ Cases_on ‘eval_to (k - 1) (Tick (Force (Value w2))) = INL Diverge’
                >- (dxrule_then (qspecl_then [‘eL2' ++ [w1]’] assume_tac) eval_to_Apps_INL
                    \\ gvs [MAP_APPEND, FOLDL_APPEND]
                    \\ rename1 ‘eval_to _ (App (Apps (App e _) _) _)’
                    \\ first_x_assum $ qspecl_then [‘e’, ‘[]’] assume_tac \\ gvs [])
                \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                \\ gvs [FOLDL_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘eval_to _ (App (Apps (App e _) _) _)’
                \\ qspecl_then [‘eL2' ++ [w1]’, ‘Tick (Force (Value w2))’, ‘k - 1’, ‘e’, ‘[]’, ‘w2'’]
                               assume_tac eval_to_Apps_INR
                \\ gvs [FOLDL_APPEND] \\ gvs [Abbr ‘e’]
                \\ qspecl_then [‘s::vL1 ++ s2::vL2 ++ [v3]’, ‘w2::eL1' ++ w2'::eL2' ++ [w1]’, ‘y2’, ‘k - 1’]
                               assume_tac eval_to_Apps_Lams_not_0
                \\ Cases_on ‘eval_to (k - 2) (Force (Value w2))’
                \\ gvs [LIST_REL_EL_EQN, FOLDL_APPEND, subst_def, GSYM ZIP_APPEND, subst_APPEND]
                \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
                \\ rename1 ‘($= +++ v_rel) _ (eval_to _ expr2)’
                \\ Cases_on ‘eval_to (k - 2) expr2 = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspecl_then [‘j3 + k - 2’] assume_tac) eval_to_mono \\ gvs [])
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
            \\ qmatch_goalsub_abbrev_tac ‘eval_to _ (App (Apps (App e _) _) _)’
            \\ first_x_assum $ qspecl_then [‘e’, ‘[]’] assume_tac
            \\ gvs [Abbr ‘e’]
            \\ qspecl_then [‘s::vL1 ++ s2::vL2 ++ [v3]’, ‘w2::eL1' ++ w2'::eL2' ++ [w1]’,
                            ‘y2’, ‘j + j1 + j2 + j3 + k - 1’]
                           assume_tac eval_to_Apps_Lams_not_0
            \\ gvs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, subst_APPEND, subst_def, FOLDL_APPEND]
            \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
            \\ rename1 ‘($= +++ v_rel) _ (eval_to _ expr2)’
            \\ ‘eval_to (j3 + k - 2) expr2 ≠ INL Diverge’
              by (strip_tac
                  \\ Cases_on ‘eval_to (k − 2) (subst (ZIP (vL1,eL1))
                                                (subst ((s,v2)::ZIP (vL2,eL2))
                                                 (subst1 v3 v1 (subst1 s2 v2' x2))))’
                  \\ gvs [])
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + j3 + k - 2’] assume_tac) eval_to_mono \\ gvs [])
        \\ gvs [eval_to_Lams]
        \\ qexists_tac ‘j + j1’ \\ gvs []
        \\ last_x_assum $ qspecl_then [‘j1’] assume_tac
        \\ gvs [subst1_def, subst_Lams, subst_Apps, eval_to_Lams]
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
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
        \\ first_x_assum $ irule_at $ Pos last
        \\ Q.REFINE_EXISTS_TAC ‘_ ++ [_]’
        \\ gvs [] \\ irule_at (Pos hd) EQ_REFL
        \\ gvs [ALL_DISTINCT_APPEND]
        \\ rename1 ‘subst1 v3 v1 (subst (ZIP (vL1 ++ s::vL2,eL1 ++ e::eL2)) _)’
        \\ ‘∀expr. subst1 v3 v1 (subst (ZIP (vL1 ++ s::vL2,eL1 ++ e::eL2)) expr)
                   = subst (ZIP (vL1 ++ s::vL2 ++ [v3],eL1 ++ e::eL2 ++ [v1])) expr’
          by (gen_tac \\ gvs [GSYM ZIP_APPEND, subst_APPEND]
              \\ irule EQ_TRANS \\ irule_at Any subst_commutes
              \\ conj_tac >- (first_x_assum $ qspec_then ‘v3’ assume_tac \\ gvs [MAP_ZIP])
              \\ AP_TERM_TAC
              \\ irule subst_commutes
              \\ first_x_assum $ qspec_then ‘v3’ assume_tac \\ gvs [MAP_ZIP])
        \\ gvs []
        \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
        \\ Q.REFINE_EXISTS_TAC ‘SNOC _ _’
        \\ gvs [LIST_REL_SNOC, PULL_EXISTS, SNOC_APPEND]
        \\ irule_at (Pos $ el 2) EQ_REFL
        \\ first_assum $ irule_at $ Pos last \\ gvs []
        \\ first_assum $ irule_at $ Pos last \\ gvs []
        \\ first_assum $ irule_at $ Pos last \\ gvs []
        \\ rw [] \\ gvs []
        >- (irule LIST_EQ \\ rw [EL_MAP]
            \\ strip_tac \\ gvs [EL_MEM])
        \\ first_x_assum $ qspecl_then [‘v3’] assume_tac
        \\ gvs [])

    (* Closure -> Lams (Apps (Recclosure )) HD *)
    >- print_tac "Closure 5/8" (
        IF_CASES_TAC \\ simp []
        >- (qexists_tac ‘0’ \\ simp []
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ simp []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gs [])
        \\ Cases_on ‘vL2’ \\ gs []
        >- (gs [subst_Lams, ALL_DISTINCT_APPEND]
            \\ rename1 ‘subst1 s v1 (subst _ (subst _ (Let _ _ x2)))’
            \\ Cases_on ‘vL3 = []’ \\ simp [eval_to_Lams]
            >- (last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Tick (Force (Value v1))’,
                                          ‘Tick (Force (Value w1))’] mp_tac
                \\ impl_tac
                >- (simp [subst1_def] \\ irule force_arg_rel_Letrec
                    \\ simp [force_arg_rel_def])
                \\ disch_then $ qx_choose_then ‘j2’ assume_tac
                \\ gs [subst_def]
                \\ simp [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                \\ simp [subst_def, subst1_notin_frees, freevars_subst]
                \\ CASE_TAC >~[‘ALOOKUP _ _ = SOME _’]
                >- (dxrule_then assume_tac ALOOKUP_MEM
                    \\ gs [] \\ gs [MEM_EL, EL_ZIP])
                \\ gs [subst1_def]
                \\ once_rewrite_tac [eval_to_def]
                \\ IF_CASES_TAC \\ simp []
                >- (qexists_tac ‘0’ \\ simp []
                    \\ qspecl_then [‘y’, ‘k’, ‘g’] assume_tac $ GEN_ALL eval_App_Tick
                    \\ Cases_on ‘k’ \\ gs []
                    \\ rename1 ‘SUC n ≤ _’ \\ Cases_on ‘n’ \\ gs []
                    \\ pop_assum irule
                    \\ first_x_assum $ irule_at Any
                    \\ first_x_assum $ irule_at Any)
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1)) = INL Diverge’
                >- (qexists_tac ‘0’ \\ simp []
                    \\ irule eval_App_Tick_Force_Val_Div
                    \\ first_x_assum $ irule_at $ Pos hd
                    \\ first_x_assum $ irule_at $ Pos hd
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gs []
                    \\ drule_then (qspecl_then [‘j2 + k - 2’] assume_tac) eval_to_mono
                    \\ gs [eval_to_Tick]
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gs [])
                \\ gs [eval_to_Tick]
                \\ Cases_on ‘eval_to (k - 2) (Force (Value v1))’
                >~[‘INL _’]
                >- (qexists_tac ‘j + j1 + j2’
                    \\ last_x_assum $ qspecl_then [‘j1 + j2’] assume_tac
                    \\ last_x_assum $ qspecl_then [‘j + j2’] assume_tac
                    \\ gs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, FOLDL_APPEND]
                    \\ gs [SF ETA_ss]
                    \\ once_rewrite_tac [eval_to_def]
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gs [eval_to_Tick]
                    \\ dxrule_then (qspecl_then [‘j + j1 + j2 + k - 2’] assume_tac) eval_to_mono
                    \\ gs []
                    \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gs [])
                \\ gs []
                \\ rename1 ‘eval_to (k - 2) (Force (Value v1)) = INR val1’
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gs [eval_to_Tick]
                \\ ‘∀j3. eval_to (j + j1 + j2 + j3 + k - 2) (Force (Value w1))
                         = eval_to (j2 + k - 2) (Force (Value w1))’
                  by (gen_tac \\ irule eval_to_mono \\ gs [])
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gs []
                \\ rename1 ‘v_rel val1 val2’ \\ rename1 ‘force_arg_rel x2 y2’
                \\ ‘∀vs expr. subst1 s2 val1 (subst (FILTER (λ(n,x). n ≠ s2) vs) expr) =
                    subst vs (subst1 s2 val1 expr)’
                  by (rpt gen_tac \\ irule EQ_TRANS \\ irule_at Any subst_commutes
                      \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP]
                      \\ qspecl_then [‘vs’, ‘subst1 s2 val1 expr’, ‘{s2}’] assume_tac subst_remove
                      \\ gvs [freevars_subst])
                \\ gvs []
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
                \\ qmatch_goalsub_abbrev_tac ‘eval_to _ g
                      = INR (Closure _ (Apps (Value (Recclosure list _)) _))’
                \\ strip_tac \\ rename1 ‘force_arg_rel x2 y2’
                \\ last_x_assum $ qspecl_then [‘ZIP (vL1, eL1)
           ++ (FILTER (λ(v,x).¬MEM v vL1 ∧ v ≠ s) (MAP (λ(v,x).(v, Recclosure xs v)) xs))’,
           ‘s2’, ‘val1’, ‘Tick x2’, ‘subst (ZIP(vL1, eL2) ++ (FILTER (λ(v,x).¬MEM v vL1 ∧ v ≠ s2)
           (MAP (λ(v,x).(v, Recclosure list v)) list)) ++ [(s2, val2)]) (Tick y2)’] mp_tac
                \\ impl_tac
                >- (gvs [subst_APPEND]
                    \\ irule force_arg_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                    \\ qspecl_then [‘x2’, ‘y2’] assume_tac force_arg_rel_freevars
                    \\ qspecl_then [‘FILTER (λ(v,x). ¬MEM v vL1 ∧ v ≠ s)
                                     (MAP (λ(v,x).(v,Recclosure xs v)) xs)’,
                      ‘subst1 s2 val1 (Tick x2)’, ‘{s2}’] assume_tac $ GSYM subst_remove
                    \\ qspecl_then [‘FILTER (λ(v,x). ¬MEM v vL1 ∧ v ≠ s2)
                                     (MAP (λ(v,x).(v,Recclosure list v)) list)’,
                      ‘subst1 s2 val2 (Tick y2)’, ‘{s}’] assume_tac $ GSYM subst_remove
                    \\ gvs [freevars_subst, freevars_def]
                    \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                    \\ pop_assum kall_tac \\ pop_assum kall_tac
                    \\ unabbrev_all_tac
                    \\ gvs [MAP_APPEND, FILTER_APPEND, SNOC_APPEND, subst_APPEND]
                    \\ gvs [subst1_def, freevars_subst, subst1_notin_frees]
                    \\ irule force_arg_rel_subst
                    \\ qmatch_goalsub_abbrev_tac ‘ MAP FST _ = MAP FST (FILTER _ (MAP _ list))’
                    \\ irule_at Any force_arg_rel_Letrec \\ gvs [force_arg_rel_subst]
                    \\ qspecl_then [‘MAP (λ(v,x). (v, Recclosure xs v)) xs’,
                ‘MAP (λ(v,x). (v, Recclosure (list ++ [(v2, Lams (vL1 ++ [s2]) y2)]) v)) list’,
                ‘v_rel’,
                ‘λv. v ≠ s2 ∧ ¬MEM v vL1 ∧ v ≠ s’]  mp_tac LIST_FILTERED
                    \\ impl_tac \\ gvs []
                    >- (gvs [MAP_MAP_o, combinTheory.o_DEF,
                             LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
                        \\ unabbrev_all_tac \\ gvs [EL_MAP, LUPDATE_MAP]
                        \\ rw []
                        >- (irule $ GSYM LUPDATE_ID
                            \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs []
                            \\ gvs [EL_MAP])
                        \\ gvs [EL_LUPDATE]
                        \\ IF_CASES_TAC \\ gvs []
                        >- (gvs [GSYM SNOC_APPEND] \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                            \\ qexists_tac ‘ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                            \\ qexists_tac ‘x2’ \\ first_x_assum $ irule_at $ Pos last
                            \\ qexists_tac ‘[]’ \\ gvs [SNOC_APPEND]
                            \\ irule_at (Pos hd) EQ_REFL \\ irule_at (Pos hd) EQ_REFL
                            \\ gvs [ALL_DISTINCT_APPEND]
                            \\ gvs [MEM_EL]
                            \\ last_assum $ irule_at $ Pos hd
                            \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP])
                        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                        \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                        \\ qexists_tac ‘ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                        \\ qexists_tac ‘x2’ \\ first_x_assum $ irule_at $ Pos last
                        \\ qexists_tac ‘[]’ \\ gvs [SNOC_APPEND]
                        \\ irule_at (Pos hd) EQ_REFL \\ irule_at (Pos hd) EQ_REFL
                        \\ gvs [ALL_DISTINCT_APPEND]
                        \\ gvs [MEM_EL]
                        \\ first_assum $ irule_at $ Pos hd \\ gvs [EL_MAP])
                    \\ ‘∀(l : (string # thunkLang$v) list).
                          FILTER (λ(p1, p2). p1 ≠ s2 ∧ ¬MEM p1 vL1 ∧ p1 ≠ s) l =
                            FILTER (λ(p1, p2). p1 ≠ s ∧ ¬MEM p1 vL1 ∧ p1 ≠ s2) l’
                      by (gen_tac \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [] \\ metis_tac [CONJ_COMM])
                    \\ strip_tac \\ gvs [])
                \\ disch_then $ qx_choose_then ‘j3’ assume_tac
                \\ gvs [subst_Tick, subst_APPEND, eval_to_Tick]
                \\ rename1 ‘($= +++ v_rel) (eval_to (k - 2) expr1) _’
                \\ Cases_on ‘eval_to (k - 2) expr1 = INL Diverge’
                >- (
                    qexists_tac ‘0’
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
                    \\ qspecl_then [‘Tick (Force (Value w1))’, ‘k - 1’]
                                   assume_tac eval_to_Apps_APPEND1
                    \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                    \\ gs []
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gs [eval_to_Tick]
                    \\ qspecl_then [‘vL1 ++ [s2]’, ‘eL2 ++ [val2]’, ‘y2’, ‘k - 1’, ‘list’, ‘v2’]
                                   mp_tac eval_to_Apps_Recclosure_Lams_not_0
                    \\ impl_tac
                    >- (gvs [LIST_REL_EL_EQN] \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC])
                    \\ rw [MAP_APPEND]
                    \\ gvs [subst_APPEND, LIST_REL_EL_EQN, GSYM ZIP_APPEND]
                    \\ ‘∀l e. subst1 s2 val2 (subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s2) l) e)
                        = subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s2) l) (subst1 s2 val2 e)’
                      by (rw [] \\ irule subst_commutes \\ gvs [MAP_FST_FILTER, MEM_FILTER])
                    \\ gs [FOLDL_APPEND]
                    \\ qmatch_goalsub_abbrev_tac ‘_ (INL Diverge) (eval_to _ expr2)’
                    \\ Cases_on ‘eval_to (k - 2) expr2 = INL Diverge’ \\ gvs []
                    \\ dxrule_then (qspecl_then [‘j3 + k - 2’] assume_tac) eval_to_mono
                    \\ gs [])
                \\ qexists_tac ‘j + j1 + j2 + j3’
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspecl_then [‘j + j2 + j3’] assume_tac
                \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspecl_then [‘j1 + j2 + j3’] assume_tac
                \\ gs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
                \\ gs [SF ETA_ss]
                \\ qspecl_then [‘Tick (Force (Value w1))’, ‘j + j1 + j2 + j3 + k - 1’]
                               assume_tac eval_to_Apps_APPEND1
                \\ gs [eval_to_Tick]
                \\ pop_assum kall_tac
                \\ qspecl_then [‘vL1 ++ [s2]’, ‘eL2 ++ [val2]’, ‘y2’,
                                ‘j + j1 + j2 + j3 + k - 1’, ‘list’, ‘v2’]
                               mp_tac eval_to_Apps_Recclosure_Lams_not_0
                \\ impl_tac
                >- (gs [LIST_REL_EL_EQN] \\ unabbrev_all_tac \\ gs [REVERSE_SNOC])
                \\ rw [MAP_APPEND]
                \\ pop_assum kall_tac
                \\ gs [subst_APPEND, LIST_REL_EL_EQN, GSYM ZIP_APPEND]
                \\ ‘∀l e. subst1 s2 val2 (subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s2) l) e)
                              = subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s2) l) (subst1 s2 val2 e)’
                      by (rw [] \\ irule subst_commutes \\ gvs [MAP_FST_FILTER, MEM_FILTER])
                \\ gs [] \\ pop_assum kall_tac
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’
                \\ ‘eval_to (j3 + k - 2) expr2 ≠ INL Diverge’
                  by (strip_tac \\ Cases_on ‘eval_to (k - 2) expr1’ \\ gvs [])
                \\ dxrule_then (qspec_then ‘j + j1 + j2 + j3 + k - 2’ assume_tac) eval_to_mono
                \\ gvs [])
            \\ qexists_tac ‘j + j1’ \\ gvs []
            \\ last_x_assum $ qspecl_then [‘j1’] assume_tac \\ gvs []
            \\ gvs [subst_Lams, subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF,
                    LAMBDA_PROD, SF ETA_ss, eval_to_Lams]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac
            \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
            \\ irule_at (Pos hd) EQ_REFL
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_assum $ irule_at Any
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
            \\ first_x_assum $ irule_at Any
            \\ gvs []
            \\ ‘∀a1 a2 b1 b2. a1 = a2 ∧ b1 = b2 ⇒ LUPDATE a1 b1 ys = LUPDATE a2 b2 ys’ by gvs []
            \\ first_x_assum $ irule_at Any \\ gvs []
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any \\ gvs []
            \\ first_x_assum $ irule_at $ Pos last
            \\ qexists_tac ‘xs’ \\ qexists_tac ‘[]’ \\ gvs []
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [ALL_DISTINCT_APPEND]
            \\ ‘∀(l1 : thunkLang$exp list) l2 l3 l4. l1 = l2 ∧ l3 = l4
                                                     ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any
            \\ irule_at (Pos hd) EQ_REFL \\ irule_at (Pos hd) EQ_REFL
            \\ first_x_assum $ irule_at $ Pos $ el 4 \\ gvs []
            \\ first_x_assum $ irule_at $ Pos $ el 3 \\ gvs []
            \\ rw [] \\ gvs []
            >- (irule LIST_EQ \\ rw [EL_MAP]
                \\ strip_tac \\ gvs [EL_MEM])
            \\ irule EQ_TRANS \\ irule_at Any subst_commutes
            \\ gvs [subst1_def, subst1_notin_frees, MAP_ZIP]
            \\ conj_tac >- (strip_tac \\ first_x_assum $ dxrule_then assume_tac \\ gvs [])
            \\ AP_TERM_TAC \\ irule EQ_TRANS \\ irule_at Any subst_commutes
            \\ gvs [MAP_FST_FILTER, MEM_FILTER, subst1_def, subst1_notin_frees, GSYM CONJ_ASSOC])
        \\ qexists_tac ‘j + j1’ \\ gvs []
        \\ last_x_assum $ qspecl_then [‘j1’] assume_tac \\ gvs []
        \\ gvs [subst_Lams, subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                SF ETA_ss, eval_to_Lams, ALL_DISTINCT_APPEND]
        \\ rename1 ‘HD (vL2 ++ s::vL3)’
        \\ ‘HD (vL2 ++ s::vL3) = HD (SNOC s vL2)’ by (Cases_on ‘vL2’ \\ gvs []) \\ rw []
        \\ gvs [v_rel_def]
        \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
        \\ first_x_assum $ irule_at Any
        \\ gvs []
        \\ ‘∀a1 a2 b1 b2. a1 = a2 ∧ b1 = b2 ⇒ LUPDATE a1 b1 ys = LUPDATE a2 b2 ys’ by gvs []
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ irule_at (Pos hd) EQ_REFL \\ gvs [ALL_DISTINCT_APPEND]
        \\ first_x_assum $ irule_at $ Pos last \\ gvs []
        \\ qexists_tac ‘xs’ \\ qexists_tac ‘eL2 ++ [w1]’ \\ qexists_tac ‘eL1 ++ [v1]’
        \\ rw [] \\ gvs []
        >- (irule LIST_EQ
            \\ rw [EL_APPEND_EQN, EL_MAP] \\ gvs [EL_MEM]
            \\ strip_tac \\ gvs [EL_MEM]
            \\ rename1 ‘n < _’
            \\ first_x_assum $ qspecl_then [‘EL (n - (LENGTH vL2 + 1)) vL3’] assume_tac
            \\ gvs [EL_MEM])
        >- (irule EQ_TRANS \\ irule_at Any subst_commutes
            \\ gvs [MAP_ZIP, GSYM ZIP_APPEND, subst_APPEND]
            \\ conj_tac >- (strip_tac \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
            \\ gvs [GSYM CONJ_ASSOC])
        >- (once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (once_rewrite_tac [CONS_APPEND] \\ gvs []))

    (* Closure -> Lams (Apps (Recclosure )) HD 2 *)
    >- print_tac "Closure 6/8" (
        IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ Cases_on ‘vL2’ \\ gvs []
        >- (gvs [subst_Lams, ALL_DISTINCT_APPEND]
            \\ rename1 ‘subst1 s v1 (subst _ (subst _ (Let _ _ x2)))’
            \\ Cases_on ‘vL3 = []’ \\ gvs [eval_to_Lams]
            >- (last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Tick (Force (Value v1))’,
                                          ‘Tick (Force (Value w1))’] mp_tac
                \\ impl_tac
                >- (gvs [subst1_def] \\ irule force_arg_rel_Letrec
                    \\ gvs [force_arg_rel_def])
                \\ disch_then $ qx_choose_then ‘j2’ assume_tac
                \\ gvs [subst_def]
                \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                \\ gvs [subst_def, subst1_notin_frees, freevars_subst]
                \\ CASE_TAC >~[‘ALOOKUP _ _ = SOME _’]
                >- (dxrule_then assume_tac ALOOKUP_MEM
                    \\ gvs [] \\ gvs [MEM_EL, EL_ZIP])
                \\ gvs [subst1_def]
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
                \\ rename1 ‘eval_to (k - 2) (Force (Value v1)) = INR val1’
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
                \\ ‘∀j3. eval_to (j + j1 + j2 + j3 + k - 2) (Force (Value w1))
                         = eval_to (j2 + k - 2) (Force (Value w1))’
                  by (gen_tac \\ irule eval_to_mono \\ gvs [])
                \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs []
                \\ rename1 ‘v_rel val1 val2’ \\ rename1 ‘force_arg_rel x2 y2’
                \\ ‘∀vs expr. subst1 s2 val1 (subst (FILTER (λ(n,x). n ≠ s2) vs) expr) =
                    subst vs (subst1 s2 val1 expr)’
                  by (rpt gen_tac \\ irule EQ_TRANS \\ irule_at Any subst_commutes
                      \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP]
                      \\ qspecl_then [‘vs’, ‘subst1 s2 val1 expr’, ‘{s2}’] assume_tac subst_remove
                      \\ gvs [freevars_subst])
                \\ gvs [subst1_commutes]
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
                \\ qmatch_goalsub_abbrev_tac ‘eval_to _ g
                      = INR (Closure _ (Apps (App (Value (Recclosure list _)) _) _))’
                \\ strip_tac \\ rename1 ‘force_arg_rel x2 y2’
                \\ last_x_assum $ qspecl_then [‘(s, v1)::ZIP (vL1, eL1) ++
      (FILTER (λ(v,x).¬MEM v vL1 ∧ v ≠ s) (MAP (λ(v,x).(v, Recclosure xs v)) xs))’,
      ‘s2’, ‘val1’, ‘Tick x2’, ‘subst ((s, w1)::ZIP(vL1, eL2) ++ [(s2, val2)]
                                       ++ (FILTER (λ(v,x).(v ≠ s ∧ ¬MEM v vL1) ∧ v ≠ s2)
                                           (MAP (λ(v,x).(v, Recclosure list v)) list)))
                                      (Tick y2)’] mp_tac
                \\ impl_tac
                >- (once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                    \\ qabbrev_tac ‘filter1 = λv. v ≠ s ∧ ¬MEM v vL1 ∧ v ≠ s2’
                    \\ qabbrev_tac ‘filter2 = λv. ¬MEM v vL1 ∧ v ≠ s’
                    \\ gvs [GSYM CONJ_ASSOC]
                    \\ ‘∀l e. subst1 s2 val2 (subst (FILTER (λ(v,x).filter1 v) l) e)
                              = subst (FILTER (λ(v,x). filter1 v) l) (subst1 s2 val2 e)’
                      by (rw [] \\ irule subst_commutes
                          \\ gvs [MAP_FST_FILTER, MEM_FILTER, Abbr ‘filter1’])
                    \\ ‘∀l e. subst1 s w1 (subst (FILTER (λ(v,x).filter1 v) l) e)
                              = subst (FILTER (λ(v,x). filter1 v) l) (subst1 s w1 e)’
                      by (rw [] \\ irule subst_commutes
                          \\ gvs [MAP_FST_FILTER, MEM_FILTER, Abbr ‘filter1’])
                    \\ ‘∀l e. subst1 s v1 (subst (FILTER (λ(v,x).filter2 v) l) e)
                              = subst (FILTER (λ(v,x). filter2 v) l) (subst1 s v1 e)’
                      by (rw [] \\ irule subst_commutes
                          \\ gvs [MAP_FST_FILTER, MEM_FILTER, Abbr ‘filter2’])
                    \\ ‘∀l e. subst (ZIP (vL1, eL1)) (subst (FILTER (λ(v,x).filter2 v) l) e)
                              = subst (FILTER (λ(v,x). filter2 v) l) (subst (ZIP (vL1, eL1)) e)’
                      by (rw [] \\ irule subst_commutes
                          \\ gvs [MAP_FST_FILTER, MEM_FILTER, Abbr ‘filter2’,
                                  MAP_ZIP, DISJOINT_ALT])
                    \\ ‘∀l e. subst (ZIP (vL1, eL2)) (subst (FILTER (λ(v,x).filter1 v) l) e)
                              = subst (FILTER (λ(v,x). filter1 v) l) (subst (ZIP (vL1, eL2)) e)’
                      by (rw [] \\ irule subst_commutes
                          \\ gvs [MAP_FST_FILTER, MEM_FILTER, Abbr ‘filter1’,
                                  MAP_ZIP, DISJOINT_ALT, LIST_REL_EL_EQN])
                    \\ gvs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
                    \\ pop_assum kall_tac \\ pop_assum kall_tac \\ pop_assum kall_tac
                    \\ qspecl_then [‘MAP (λ(v,x). (v, Recclosure xs v)) xs’,
                                    ‘subst1 s v1 (subst (ZIP (vL1, eL1))
                                                             (subst1 s2 val1 (Tick x2)))’,
                                    ‘set vL1 ∪ {s}’] assume_tac subst_remove
                    \\ gvs [DISJOINT_ALT, freevars_subst, MAP_ZIP]
                    \\ qspecl_then [‘MAP (λ(v,x). (v, Recclosure list v)) list’,
                                    ‘subst1 s w1 (subst (ZIP (vL1, eL2))
                                                             (subst1 s2 val2 (Tick y2)))’,
                                    ‘{s} ∪ set vL1 ∪ {s2}’] assume_tac subst_remove
                    \\ ‘LENGTH eL1 = LENGTH eL2’ by gvs [LIST_REL_EL_EQN]
                    \\ gvs [DISJOINT_ALT, freevars_subst, MAP_ZIP,
                            Abbr ‘filter2’, GSYM CONJ_ASSOC]
                    \\ pop_assum kall_tac \\ pop_assum kall_tac \\ pop_assum kall_tac
                    \\ qspecl_then [‘x2’, ‘y2’] assume_tac force_arg_rel_freevars
                    \\ gvs [Abbr ‘filter1’, Abbr ‘list’, MAP_APPEND, SNOC_APPEND, subst_APPEND,
                            subst1_notin_frees, freevars_subst, freevars_def]
                    \\ irule force_arg_rel_subst \\ fs []
                    \\ irule_at Any force_arg_rel_subst
                    \\ irule_at Any force_arg_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, EL_MAP]
                    \\ rw []
                    >- gvs [force_arg_rel_subst, force_arg_rel_def, DECIDE “n < 1 ⇔ n = 0:num”]
                    >- (irule LIST_EQ \\ rw [EL_MAP, EL_LUPDATE]
                        \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP])
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                    \\ rename1 ‘n < _’
                    \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                    \\ rename1 ‘v_rel _ (Recclosure _ v')’
                    \\ ‘FST (EL n ys) = v'’
                      by (pop_assum mp_tac \\ rw [EL_LUPDATE]
                          \\ Cases_on ‘EL i xs’ \\ gvs [])
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                    \\ qexists_tac ‘ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                    \\ qexists_tac ‘x2’ \\ first_x_assum $ irule_at $ Pos last
                    \\ qexists_tac ‘[]’ \\ gvs []
                    \\ rpt $ irule_at (Pos hd) EQ_REFL
                    \\ gvs [ALL_DISTINCT_APPEND, EL_LUPDATE]
                    \\ gvs [MEM_MAP]
                    \\ irule_at Any EQ_REFL \\ gvs [EL_MEM])
                \\ once_rewrite_tac [CONS_APPEND]
                \\ disch_then $ qx_choose_then ‘j3’ assume_tac
                \\ gvs [subst_Tick, subst_APPEND]
                \\ rename1 ‘_ (eval_to (k - 2) expr1) _’
                \\ Cases_on ‘eval_to (k - 2) expr1 = INL Diverge’
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
                    \\ qspecl_then [‘Tick (Force (Value w1))’, ‘k - 1’]
                                   assume_tac eval_to_Apps_APPEND1
                    \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                    \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs []
                    \\ first_x_assum $ qspecl_then [‘Value (Recclosure list v2)’,
                                                    ‘Value w1::MAP Value eL2’] assume_tac
                    \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
                    \\ qspecl_then [‘s::vL1 ++ [s2]’, ‘w1::eL2 ++ [val2]’,
                                    ‘y2’, ‘k - 1’, ‘list’, ‘v2’]
                                   mp_tac eval_to_Apps_Recclosure_Lams_not_0
                    \\ impl_tac
                    >- (gvs [LIST_REL_EL_EQN] \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
                            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
                    \\ rw [MAP_APPEND]
                    \\ gvs [subst_APPEND, LIST_REL_EL_EQN, GSYM ZIP_APPEND]
                    \\ once_rewrite_tac [CONS_APPEND]
                    \\ gvs [subst_APPEND]
                    \\ qmatch_goalsub_abbrev_tac ‘_ (INL Diverge) (eval_to _ expr2)’
                    \\ gvs []
                    \\ Cases_on ‘eval_to (k - 2) expr2 = INL Diverge’ \\ gvs []
                    \\ dxrule_then (qspecl_then [‘j3 + k - 2’] assume_tac) eval_to_mono
                    \\ gvs [])
                \\ qexists_tac ‘j + j1 + j2 + j3’
                \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspecl_then [‘j + j2 + j3’] assume_tac
                \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspecl_then [‘j1 + j2 + j3’] assume_tac
                \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
                \\ gvs [SF ETA_ss]
                \\ qspecl_then [‘Tick (Force (Value w1))’, ‘j + j1 + j2 + j3 + k - 1’]
                               assume_tac eval_to_Apps_APPEND1
                \\ gvs []
                \\ pop_assum $ qspecl_then [‘Value (Recclosure list v2)’,
                                            ‘MAP Value eL2 ++ [Value w1]’] assume_tac
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
                \\ qspecl_then [‘s::vL1 ++ [s2]’, ‘w1::eL2 ++ [val2]’, ‘y2’,
                                ‘j + j1 + j2 + j3 + k - 1’, ‘list’, ‘v2’]
                               mp_tac eval_to_Apps_Recclosure_Lams_not_0
                \\ impl_tac
                >- (gvs [LIST_REL_EL_EQN] \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
                    \\ once_rewrite_tac [CONS_APPEND] \\ gvs [])
                \\ rw [MAP_APPEND]
                \\ gvs [subst_APPEND, LIST_REL_EL_EQN, GSYM ZIP_APPEND]
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr2)’
                \\ ‘eval_to (j3 + k - 2) expr2 ≠ INL Diverge’
                  by (strip_tac \\ Cases_on ‘eval_to (k - 2) expr1’ \\ gvs [])
                \\ dxrule_then (qspec_then ‘j + j1 + j2 + j3 + k - 2’ assume_tac) eval_to_mono
                \\ gvs [])
            \\ qexists_tac ‘j + j1’ \\ gvs []
            \\ last_x_assum $ qspecl_then [‘j1’] assume_tac \\ gvs []
            \\ gvs [subst_Lams, subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF,
                    LAMBDA_PROD, SF ETA_ss, eval_to_Lams]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac
            \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
            \\ irule_at (Pos hd) EQ_REFL
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_assum $ irule_at Any
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
            \\ first_x_assum $ irule_at Any
            \\ gvs []
            \\ ‘∀a1 a2 b1 b2. a1 = a2 ∧ b1 = b2 ⇒ LUPDATE a1 b1 ys = LUPDATE a2 b2 ys’ by gvs []
            \\ first_x_assum $ irule_at Any \\ gvs []
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any \\ gvs []
            \\ first_x_assum $ irule_at $ Pos last
            \\ qpat_x_assum ‘LIST_REL _ (MAP SND _) _’ $ irule_at Any
            \\ qexists_tac ‘[]’ \\ gvs []
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [ALL_DISTINCT_APPEND]
            \\ ‘∀(l1 : thunkLang$exp list) l2 l3 l4. l1 = l2 ∧ l3 = l4
                                                     ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any
            \\ irule_at (Pos hd) EQ_REFL \\ irule_at (Pos hd) EQ_REFL
            \\ first_x_assum $ irule_at $ Pos $ el 4 \\ gvs []
            \\ first_x_assum $ irule_at $ Pos $ el 3 \\ gvs []
            \\ rw [] \\ gvs []
            >- (irule LIST_EQ \\ rw [EL_MAP]
                \\ strip_tac \\ gvs [EL_MEM])
            \\ gvs [GSYM ZIP_APPEND, GSYM CONJ_ASSOC, subst_APPEND]
            \\ irule subst_commutes
            \\ gvs [MAP_ZIP]
            \\ strip_tac \\ first_x_assum $ dxrule_then assume_tac \\ gvs [])
        \\ qexists_tac ‘j + j1’ \\ gvs []
        \\ last_x_assum $ qspecl_then [‘j1’] assume_tac \\ gvs []
        \\ gvs [subst_Lams, subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                SF ETA_ss, eval_to_Lams, ALL_DISTINCT_APPEND]
        \\ rename1 ‘HD (vL2 ++ s::vL3)’
        \\ ‘HD (vL2 ++ s::vL3) = HD (SNOC s vL2)’ by (Cases_on ‘vL2’ \\ gvs []) \\ rw []
        \\ gvs [v_rel_def]
        \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
        \\ first_x_assum $ irule_at Any
        \\ gvs []
        \\ ‘∀a1 a2 b1 b2. a1 = a2 ∧ b1 = b2 ⇒ LUPDATE a1 b1 ys = LUPDATE a2 b2 ys’ by gvs []
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ irule_at (Pos hd) EQ_REFL \\ gvs [ALL_DISTINCT_APPEND]
        \\ first_x_assum $ irule_at $ Pos last \\ gvs []
        \\ qexists_tac ‘xs’ \\ qexists_tac ‘eL2 ++ [w1]’ \\ qexists_tac ‘eL1 ++ [v1]’
        \\ rw [] \\ gvs []
        >- (‘∀(l1 : thunkLang$exp list) l2 l3 l4. l1 = l2 ∧ l3 = l4
                                                  ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any
            \\ rename1 ‘_ ∨ _ = h ∨ _’ \\ first_x_assum $ qspec_then ‘h’ assume_tac
            \\ rw [] \\ irule LIST_EQ \\ rw [EL_MAP] \\ gvs [MEM_EL, NOT_LESS])
        >- (gvs [GSYM ZIP_APPEND, subst_APPEND, GSYM CONJ_ASSOC]
            \\ irule_at Any subst_commutes
            \\ gvs [MAP_ZIP]
            \\ strip_tac \\ last_x_assum $ dxrule_then assume_tac \\ gvs [])
        >- (once_rewrite_tac [CONS_APPEND] \\ gvs [])
        >- (once_rewrite_tac [CONS_APPEND] \\ gvs []))

    (* Closure -> Lams (Apps (Recclosure ))  TL *)
    >- print_tac "Closure 7/8" (
        IF_CASES_TAC
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
        >- (rename1 ‘Recclosure _ var’
            \\ rename1 ‘Tick (Force (Value w2))::MAP _ _’ \\ rename1 ‘v_rel v2 w2’
            \\ last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Tick (Force (Value v2))’,
                                         ‘Tick (Force (Value w2))’] mp_tac
            \\ impl_tac
            >- (gvs [subst1_def] \\ irule force_arg_rel_Letrec
                \\ gvs [force_arg_rel_def])
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
            \\ rename1 ‘v_rel v2' w2'’ \\ rename1 ‘force_arg_rel x2 y2’
            \\ qmatch_goalsub_abbrev_tac ‘eval_to _ (subst1 _ _ (subst1 _ _ (subst _ expr)))’
            \\ ‘subst1 s2 v2' (subst1 v3 v1 (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ vL2, eL1 ++ eL2))) expr)) =
                subst (ZIP (vL1 ++ vL2, eL1 ++ eL2)) (subst1 v3 v1 (subst1 s2 v2' expr))’
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
            \\ gvs [] \\ unabbrev_all_tac
            \\ ‘∀l. subst1 s2 v2' (subst (FILTER (λ(n,x). n ≠ s2) l) x2) =
                         subst l (subst1 s2 v2' x2)’
              by (gen_tac
                  \\ irule EQ_TRANS \\ irule_at (Pos hd) subst_commutes
                  \\ gvs [MAP_FST_FILTER, MEM_FILTER]
                  \\ qspecl_then [‘l’, ‘subst1 s2 v2' x2’, ‘{s2}’] assume_tac subst_remove
                  \\ gvs [freevars_subst])
            \\ gvs []
            \\ rename1 ‘Lams (vL1 ++ s::vL2 ++ [v3]) (Apps _ _)’
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
            \\ qmatch_goalsub_abbrev_tac ‘Apps (Value (Recclosure list _)) _’ \\ strip_tac
            \\ last_x_assum $ qspecl_then [‘ZIP (vL1 ++ vL2, eL1 ++ eL2) ++ [(v3, v1)]
                ++ (FILTER (λ(v,x). ¬MEM v (vL1 ++ s::vL2 ++ [v3])) (MAP (λ(v,x). (v, Recclosure xs v)) xs))’,
                                           ‘s2’, ‘v2'’, ‘Tick x2’,
              ‘subst (ZIP (vL1 ++ s2::vL2 ++ [v3], eL1' ++ w2'::eL2' ++ [w1])
                ++ (FILTER (λ(v,x). ¬MEM v (vL1 ++ s2::vL2 ++ [v3])) (MAP (λ(v,x). (v, Recclosure list v)) list)))
                                                   (Tick y2)’] mp_tac
            \\ impl_tac
            >- (gvs [subst_APPEND, LIST_REL_EL_EQN, GSYM ZIP_APPEND]
                \\ irule force_arg_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                \\ ‘∀e. subst1 s2 w2' (subst (ZIP (vL2, eL2')) e) = subst (ZIP (vL2, eL2')) (subst1 s2 w2' e)’
                  by (gen_tac \\ irule subst_commutes \\ gvs [MAP_ZIP])
                \\ gvs [] \\ pop_assum kall_tac
                \\ irule force_arg_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                \\ qpat_x_assum ‘∀l. subst1 s2 _ (subst (FILTER _ _) x2) = _’ kall_tac
                \\ gvs [subst_Tick] \\ irule force_arg_rel_Letrec \\ gvs []
                \\ qmatch_goalsub_abbrev_tac ‘force_arg_rel (subst1 v3 v1 expr1) (subst1 s2 w2' (subst1 v3 w1 expr2))’
                \\ qspecl_then [‘[(v3, v1)]’, ‘expr1’, ‘[(v3, w1)]’, ‘subst1 s2 w2' expr2’] mp_tac force_arg_rel_subst
                \\ impl_tac \\ gvs [subst1_commutes]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’]
                \\ ‘subst1 s2 w2' (subst (FILTER (λ(v,x). ¬MEM v (vL1 ++ s2::vL2 ++ [v3]))
                                          (MAP (λ(v,x). (v, Recclosure list v)) list)) y2)
                    = subst (FILTER (λ(v,x). ¬MEM v (vL1 ++ s2::vL2 ++ [v3]))
                             (MAP (λ(v,x). (v, Recclosure list v)) list)) (subst1 s2 w2' y2)’
                  by (irule subst_commutes \\ gvs [MAP_FST_FILTER, MEM_FILTER])
                \\ gvs [GSYM CONJ_ASSOC]
                \\ qmatch_goalsub_abbrev_tac ‘force_arg_rel (subst l1 e1) (subst l2 e2)’
                \\ qspecl_then [‘l1’, ‘e1’, ‘{s2}’] assume_tac $ GSYM subst_remove
                \\ qspecl_then [‘l2’, ‘e2’, ‘{s}’] assume_tac $ GSYM subst_remove
                \\ qspecl_then [‘x2’, ‘y2’] assume_tac force_arg_rel_freevars
                \\ gvs [Abbr ‘l1’, Abbr ‘l2’, Abbr ‘e1’, Abbr ‘e2’, freevars_subst]
                \\ gvs [FILTER_FILTER, LAMBDA_PROD, GSYM CONJ_ASSOC]
                \\ ‘∀l. FILTER (λ(p1, (p2: thunkLang$v)). p1 ≠ s2 ∧ ¬MEM p1 vL1
                                                          ∧ p1 ≠ s ∧ ¬MEM p1 vL2 ∧ p1 ≠ v3) l
                        = FILTER (λ(p1, p2). p1 ≠ s ∧ ¬MEM p1 vL1 ∧ p1 ≠ s2 ∧ ¬MEM p1 vL2
                                             ∧ p1 ≠ v3) l’
                  by (gen_tac \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [] \\ metis_tac [CONJ_COMM])
                \\ gvs []
                \\ gvs [Abbr ‘list’, SNOC_APPEND, MAP_APPEND, FILTER_APPEND, subst_APPEND]
                \\ gvs [subst1_notin_frees, freevars_subst]
                \\ irule force_arg_rel_subst \\ gvs [force_arg_rel_subst]
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
                \\ qmatch_goalsub_abbrev_tac ‘MAP FST (FILTER filter1 l1) = MAP FST (FILTER _ l2)’
                \\ qspecl_then [‘l1’, ‘l2’, ‘v_rel’, ‘λv. filter1 (v, Recclosure [] v)’]
                               mp_tac LIST_FILTERED
                \\ impl_tac \\ gvs []
                >- (unabbrev_all_tac
                    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
                    \\ irule_at (Pos hd) $ GSYM LUPDATE_ID
                    \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE] \\ rw []
                    >- (gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                        \\ qexists_tac ‘ys’ \\ qexists_tac ‘x2’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                        \\ first_x_assum $ irule_at $ Pos $ last
                        \\ Q.REFINE_EXISTS_TAC ‘list1 ++ [var2]’ \\ gvs []
                        \\ irule_at (Pos hd) EQ_REFL
                        \\ irule_at (Pos hd) EQ_REFL \\ gvs []
                        \\ once_rewrite_tac [CONS_APPEND] \\ gvs [ALL_DISTINCT_APPEND]
                        \\ gvs [MEM_EL, SF CONJ_ss, EL_MAP]
                        \\ irule_at Any EQ_REFL \\ gvs [])
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                    \\ rename1 ‘n < _’
                    \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                    \\ qexists_tac ‘ys’ \\ qexists_tac ‘x2’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                    \\ first_x_assum $ irule_at $ Pos $ last
                    \\ Q.REFINE_EXISTS_TAC ‘list1 ++ [var2]’ \\ gvs []
                    \\ irule_at (Pos hd) EQ_REFL
                    \\ irule_at (Pos hd) EQ_REFL \\ gvs []
                    \\ once_rewrite_tac [CONS_APPEND] \\ gvs [ALL_DISTINCT_APPEND]
                    \\ gvs [MEM_EL, SF CONJ_ss, EL_MAP]
                    \\ qexists_tac ‘n’ \\ gvs [])
                \\ gvs [Abbr ‘filter1’] \\ rw []
                \\ rw [Abbr ‘l2’]
                \\ ‘vL1 ++ s2::vL2 ++ [v3] = vL1 ++ [s2] ++ vL2 ++ [v3]’
                  by (once_rewrite_tac [CONS_APPEND] \\ gvs [])
                \\ rw [])
            \\ disch_then $ qx_choose_then ‘j3’ assume_tac
            \\ gvs [GSYM CONJ_ASSOC, subst_Tick, subst_APPEND]
            \\ rename1 ‘($= +++ v_rel) (eval_to (k - 2) expr1) _’
            \\ Cases_on ‘eval_to (k - 2) expr1 = INL Diverge’
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
                \\ Cases_on ‘eval_to (k - 2) (Force (Value w2))’ \\ gvs []
                \\ qspecl_then [‘vL1 ++ s2::vL2 ++ [v3]’, ‘eL1' ++ w2' ::eL2' ++ [w1]’, ‘y2’, ‘k - 1’, ‘list’, ‘var’]
                               mp_tac eval_to_Apps_Recclosure_Lams_not_0
                \\ impl_tac
                >- (gvs [LIST_REL_EL_EQN] \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC])
                \\ rw [FOLDL_APPEND]
                \\ gvs [GSYM CONJ_ASSOC, subst_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘_ (INL Diverge) (eval_to _ expr2)’
                \\ Cases_on ‘eval_to (k - 2) expr2 = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j3 + k - 2’ assume_tac) eval_to_mono
                \\ gvs [])
            \\ qexists_tac ‘j + j1 + j2 + j3’
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspecl_then [‘j1 + j2 + j3’] assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspecl_then [‘j + j2 + j3’] assume_tac
            \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
            \\ gvs [SF ETA_ss]
            \\ qspecl_then [‘eL2' ++ [w1]’, ‘Tick (Force (Value w2))’, ‘j + j1 + j2 + j3 + k - 1’]
                           assume_tac eval_to_Apps_INR
            \\ ‘eval_to (j2 + k - 2) (Force (Value w2)) ≠ INL Diverge’ by gvs []
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + j3 + k - 2’] assume_tac) eval_to_mono
            \\ gvs [FOLDL_APPEND]
            \\ qspecl_then [‘vL1 ++ s2::vL2 ++ [v3]’, ‘eL1' ++ w2' ::eL2' ++ [w1]’, ‘y2’,
                            ‘j + j1 + j2 + j3 + k - 1’, ‘list’, ‘var’] mp_tac eval_to_Apps_Recclosure_Lams_not_0
            \\ impl_tac
            >- (gvs [LIST_REL_EL_EQN] \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC])
            \\ rw [subst_APPEND, GSYM CONJ_ASSOC, FOLDL_APPEND]
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ expr1) (eval_to _ expr2)’
            \\ ‘eval_to (j3 + k - 2) expr2 ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to (k − 2) expr1’ \\ gvs [])
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + j3 + k - 2’] assume_tac) eval_to_mono \\ gvs [])
        \\ gvs [eval_to_Lams]
        \\ qexists_tac ‘j + j1’ \\ gvs []
        \\ last_x_assum $ qspecl_then [‘j1’] assume_tac
        \\ gvs [subst1_def, subst_Lams, subst_Apps, eval_to_Lams]
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac
        \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, subst1_def, SF ETA_ss]
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ ‘∀a1 a2 b1 b2. a1 = a2 ∧ b1 = b2 ⇒ LUPDATE a1 b1 ys = LUPDATE a2 b2 ys’ by gvs []
        \\ first_x_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ qexists_tac ‘xs’
        \\ Q.REFINE_EXISTS_TAC ‘l1 ++ [variable]’
        \\ gvs [] \\ irule_at (Pos hd) EQ_REFL
        \\ rename1 ‘Tick (Force (Var s))’ \\ qexists_tac ‘s’
        \\ once_rewrite_tac [CONS_APPEND] \\ gvs [ALL_DISTINCT_APPEND]
        \\ qexists_tac ‘eL2' ++ [w1]’ \\ gvs []
        \\ qexists_tac ‘eL2 ++ [v1]’ \\ gvs []
        \\ qexists_tac ‘eL1'’ \\ qexists_tac ‘eL1’ \\ gvs []
        \\ first_x_assum $ irule_at $ Pos $ el 3
        \\ rw [] \\ gvs []
        >- (irule LIST_EQ \\ rw [EL_MAP]
            \\ strip_tac \\ gvs [EL_MEM])
        >- (irule EQ_TRANS \\ irule_at Any subst_commutes
            \\ gvs [MAP_ZIP]
            \\ conj_tac
            >- (rw[] \\ strip_tac \\ first_x_assum $ qspecl_then [‘v3’] assume_tac \\ gvs [])
            \\ gvs [GSYM subst_APPEND]
            \\ qspecl_then [‘vL1 ++ vL2’, ‘eL1 ++ eL2’, ‘[v3]’, ‘[v1]’] assume_tac ZIP_APPEND
            \\ gvs [GSYM CONJ_ASSOC]))

    (* Closure -> Lams (Apps (Recclosure ))  TL 2 *)
    >- print_tac "Closure 8/8" (
        IF_CASES_TAC
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
        >- (rename1 ‘Recclosure _ var’
            \\ rename1 ‘Tick (Force (Value w2))::MAP _ _’ \\ rename1 ‘v_rel v2 w2’
            \\ last_assum $ qspecl_then [‘[]’, ‘s’, ‘v1’, ‘Tick (Force (Value v2))’,
                                         ‘Tick (Force (Value w2))’] mp_tac
            \\ impl_tac
            >- (gvs [subst1_def] \\ irule force_arg_rel_Letrec
                \\ gvs [force_arg_rel_def])
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
                \\ gvs [MAP_APPEND, FOLDL_APPEND]
                \\ rename1 ‘App (Apps (App e _) _) _’
                \\ pop_assum $ qspecl_then [‘e’, ‘[]’] assume_tac \\ gvs [])
            \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER, GSYM ZIP_APPEND, subst_def,
                    REVERSE_APPEND, ALOOKUP_APPEND]
            \\ CASE_TAC >~[‘ALOOKUP _ _ = SOME _’]
            >- (dxrule_then assume_tac ALOOKUP_MEM
                \\ gvs []
                \\ dxrule_then assume_tac MEM_FST \\ gvs [MAP_ZIP])
            \\ gvs [subst1_def]
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
                \\ gvs [FOLDL_APPEND, MAP_APPEND]
                \\ rename1 ‘App (Apps (App e _) _) _’
                \\ pop_assum $ qspecl_then [‘e’, ‘[]’] assume_tac \\ gvs [])
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
                \\ gvs [MAP_APPEND, FOLDL_APPEND]
                \\ rename1 ‘App (Apps (App e _) _) _’
                \\ pop_assum $ qspecl_then [‘e’, ‘[]’] assume_tac \\ gvs [])
            \\ gvs []
            \\ rename1 ‘eval_to (k - 2) (Force (Value v2)) = INR v2'’
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2)) = INL Diverge’ \\ gvs []
            \\ ‘∀j3. eval_to (j + j1 + j2 + j3 + k - 2) (Force (Value w2))
                     = eval_to (j2 + k - 2) (Force (Value w2))’
              by (gen_tac \\ irule eval_to_mono \\ gvs [])
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w2))’ \\ gvs []
            \\ rename1 ‘v_rel v2' w2'’ \\ rename1 ‘force_arg_rel x2 y2’
            \\ rename1 ‘ZIP _ ++ (s, v2)::ZIP _’
            \\ qmatch_goalsub_abbrev_tac ‘eval_to _ (subst1 _ _ (subst1 _ _ (subst _ expr)))’
            \\ ‘subst1 s2 v2' (subst1 v3 v1 (subst (FILTER (λ(n,x). n ≠ s2)
                                                (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2))) expr)) =
                subst (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2)) (subst1 v3 v1 (subst1 s2 v2' expr))’
              by (gvs [subst1_commutes]
                  \\ ‘subst1 v3 v1 (subst (FILTER (λ(n,x). n ≠ s2)
                                               (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2))) expr) =
                          subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2)))
                                (subst1 v3 v1 expr)’
                    by (irule subst_commutes
                        \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP]
                        \\ conj_tac \\ strip_tac
                        \\ first_x_assum $ qspecl_then [‘v3’] assume_tac \\ gvs [])
                  \\ ‘∀e. subst1 s2 v2'
                       (subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2))) e)
                          = subst (FILTER (λ(n,x). n ≠ s2) (ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2)))
                                  (subst1 s2 v2' e)’
                    by (gen_tac \\ irule subst_commutes
                        \\ gvs [MAP_FST_FILTER, MEM_FILTER, MAP_ZIP])
                  \\ gvs []
                  \\ AP_THM_TAC \\ AP_TERM_TAC
                  \\ once_rewrite_tac [CONS_APPEND]
                  \\ gvs [FILTER_EQ_ID, EVERY_EL, MEM_EL, EL_ZIP, EL_APPEND_EQN]
                  \\ rw [] \\ rename1 ‘n < _’
                  \\ strip_tac \\ gvs []
                  >- (gvs [NOT_LESS, GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
                      \\ dxrule_then assume_tac LESS_EQUAL_ANTISYM \\ gvs [])
                  \\ last_x_assum $ resolve_then (Pos hd) assume_tac EQ_REFL
                  \\ gvs [])
            \\ gvs [GSYM ZIP_APPEND] \\ unabbrev_all_tac
            \\ pop_assum kall_tac
            \\ ‘∀l. subst1 s2 v2' (subst (FILTER (λ(n,x). n ≠ s2) l) x2) =
                         subst l (subst1 s2 v2' x2)’
              by (gen_tac
                  \\ irule EQ_TRANS \\ irule_at (Pos hd) subst_commutes
                  \\ gvs [MAP_FST_FILTER, MEM_FILTER]
                  \\ qspecl_then [‘l’, ‘subst1 s2 v2' x2’, ‘{s2}’] assume_tac subst_remove
                  \\ gvs [freevars_subst])
            \\ gvs []
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ mp_tac
            \\ qmatch_goalsub_abbrev_tac ‘Apps (App (Value (Recclosure list _)) _) _’ \\ strip_tac
            \\ last_x_assum $ qspecl_then [‘ZIP (vL1 ++ s::vL2, eL1 ++ v2::eL2) ++ [(v3, v1)]
                ++ (FILTER (λ(v,x). ¬MEM v (vL1 ++ s::vL2 ++ [v3])) (MAP (λ(v,x). (v, Recclosure xs v)) xs))’,
                                           ‘s2’, ‘v2'’, ‘Tick x2’,
              ‘subst (ZIP (s::vL1 ++ s2::vL2 ++ [v3], w2::eL1' ++ w2'::eL2' ++ [w1])
                ++ (FILTER (λ(v,x). ¬MEM v (s::vL1 ++ s2::vL2 ++ [v3])) (MAP (λ(v,x). (v, Recclosure list v)) list)))
                                                   (Tick y2)’] mp_tac
            \\ impl_tac
            >- (gvs [subst_APPEND, LIST_REL_EL_EQN, GSYM ZIP_APPEND]
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                \\ ‘∀e. subst1 s w2 (subst (ZIP (vL1, eL1')) e) = subst (ZIP (vL1, eL1')) (subst1 s w2 e)’
                  by (gen_tac \\ irule subst_commutes
                      \\ first_x_assum $ qspec_then ‘s’ assume_tac
                      \\ gvs [MAP_ZIP])
                \\ gvs [] \\ pop_assum kall_tac
                \\ irule force_arg_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                \\ irule force_arg_rel_subst \\ gs []
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs [subst_APPEND]
                \\ ‘∀e. subst1 s2 w2' (subst (ZIP (vL2, eL2')) e) = subst (ZIP (vL2, eL2')) (subst1 s2 w2' e)’
                  by (gen_tac \\ irule subst_commutes \\ gvs [MAP_ZIP])
                \\ gvs [] \\ pop_assum kall_tac
                \\ irule force_arg_rel_subst \\ gvs [MAP_ZIP, LIST_REL_EL_EQN]
                \\ qpat_x_assum ‘∀l. subst1 s2 _ (subst (FILTER _ _) x2) = _’ kall_tac
                \\ gvs [subst_Tick] \\ gvs [force_arg_rel_def]
                \\ qmatch_goalsub_abbrev_tac ‘force_arg_rel (subst1 v3 v1 expr1) (subst1 s2 w2' (subst1 v3 w1 expr2))’
                \\ qspecl_then [‘[(v3, v1)]’, ‘expr1’, ‘[(v3, w1)]’, ‘subst1 s2 w2' expr2’] mp_tac force_arg_rel_subst
                \\ impl_tac \\ gvs [subst1_commutes]
                \\ gvs [Abbr ‘expr1’, Abbr ‘expr2’]
                \\ ‘subst1 s2 w2' (subst (FILTER (λ(v,x). ¬MEM v (s::vL1 ++ s2::vL2 ++ [v3]))
                                          (MAP (λ(v,x). (v, Recclosure list v)) list)) y2)
                    = subst (FILTER (λ(v,x). ¬MEM v (s::vL1 ++ s2::vL2 ++ [v3]))
                             (MAP (λ(v,x). (v, Recclosure list v)) list)) (subst1 s2 w2' y2)’
                  by (irule subst_commutes \\ gvs [MAP_FST_FILTER, MEM_FILTER])
                \\ gvs [GSYM CONJ_ASSOC]
                \\ qmatch_goalsub_abbrev_tac ‘force_arg_rel (subst l1 e1) _’
                \\ qspecl_then [‘l1’, ‘e1’, ‘{s2}’] assume_tac $ GSYM subst_remove
                \\ qspecl_then [‘x2’, ‘y2’] assume_tac force_arg_rel_freevars
                \\ gvs [Abbr ‘l1’, Abbr ‘e1’, freevars_subst]
                \\ gvs [FILTER_FILTER, LAMBDA_PROD, GSYM CONJ_ASSOC]
                \\ ‘∀l. FILTER (λ(p1, (p2: thunkLang$v)). p1 ≠ s2 ∧ ¬MEM p1 vL1
                                                          ∧ p1 ≠ s ∧ ¬MEM p1 vL2 ∧ p1 ≠ v3) l
                        = FILTER (λ(p1, p2). p1 ≠ s ∧ ¬MEM p1 vL1 ∧ p1 ≠ s2
                                             ∧ ¬MEM p1 vL2 ∧ p1 ≠ v3) l’
                  by (gen_tac \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [] \\ metis_tac [CONJ_COMM])
                \\ gvs []
                \\ gvs [Abbr ‘list’, SNOC_APPEND, MAP_APPEND, FILTER_APPEND, subst_APPEND]
                \\ gvs [subst1_notin_frees, freevars_subst]
                \\ irule force_arg_rel_subst \\ gvs [force_arg_rel_subst]
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
                \\ qmatch_goalsub_abbrev_tac ‘MAP FST (FILTER filter1 l1) = MAP FST (FILTER _ l2)’
                \\ qspecl_then [‘l1’, ‘l2’, ‘v_rel’, ‘λv. filter1 (v, Recclosure [] v)’]
                               mp_tac LIST_FILTERED
                \\ impl_tac \\ gvs []
                >- (unabbrev_all_tac
                    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
                    \\ irule_at (Pos hd) $ GSYM LUPDATE_ID
                    \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE] \\ rw []
                    >- (gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                        \\ qexists_tac ‘ys’ \\ qexists_tac ‘x2’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                        \\ first_x_assum $ irule_at $ Pos $ last
                        \\ Q.REFINE_EXISTS_TAC ‘list1 ++ [var2]’ \\ gvs []
                        \\ irule_at (Pos hd) EQ_REFL
                        \\ irule_at (Pos hd) EQ_REFL \\ gvs []
                        \\ once_rewrite_tac [CONS_APPEND] \\ gvs [ALL_DISTINCT_APPEND]
                        \\ gvs [MEM_EL, SF CONJ_ss, EL_MAP]
                        \\ irule_at Any EQ_REFL \\ gvs [])
                    \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
                    \\ rename1 ‘n < _’
                    \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                    \\ qexists_tac ‘ys’ \\ qexists_tac ‘x2’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                    \\ first_x_assum $ irule_at $ Pos $ last
                    \\ Q.REFINE_EXISTS_TAC ‘list1 ++ [var2]’ \\ gvs []
                    \\ irule_at (Pos hd) EQ_REFL
                    \\ irule_at (Pos hd) EQ_REFL \\ gvs []
                    \\ once_rewrite_tac [CONS_APPEND] \\ gvs [ALL_DISTINCT_APPEND]
                    \\ gvs [MEM_EL, SF CONJ_ss, EL_MAP]
                    \\ qexists_tac ‘n’ \\ gvs [])
                \\ gvs [Abbr ‘filter1’] \\ rw []
                \\ rw [Abbr ‘l2’]
                \\ gvs [FOLDL_APPEND, FOLDR_APPEND])
            \\ disch_then $ qx_choose_then ‘j3’ assume_tac
            \\ gvs [GSYM CONJ_ASSOC, subst_Tick, subst_APPEND, GSYM ZIP_APPEND]
            \\ rename1 ‘($= +++ v_rel) (eval_to (k - 2) expr1) _’
            \\ Cases_on ‘eval_to (k - 2) expr1 = INL Diverge’
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
                    \\ gvs [MAP_APPEND, FOLDL_APPEND]
                    \\ rename1 ‘App (Apps (App e _) _) _’
                    \\ pop_assum $ qspecl_then [‘e’, ‘[]’] assume_tac \\ gvs [])
                \\ dxrule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono
                \\ qspecl_then [‘eL2' ++ [w1]’, ‘Tick (Force (Value w2))’, ‘k - 1’]
                               assume_tac eval_to_Apps_INR
                \\ gvs [FOLDL_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘App (Apps (App e _) _) _’
                \\ first_x_assum $ qspecl_then [‘e’, ‘[]’] assume_tac \\ gvs []
                \\ Cases_on ‘eval_to (k - 2) (Force (Value w2))’ \\ gvs [] \\ gs [Abbr ‘e’]
                \\ qspecl_then [‘s::vL1 ++ s2::vL2 ++ [v3]’, ‘w2::eL1' ++ w2' ::eL2' ++ [w1]’,
                                ‘y2’, ‘k - 1’, ‘list’, ‘var’]
                               mp_tac eval_to_Apps_Recclosure_Lams_not_0
                \\ impl_tac
                >- (gvs [LIST_REL_EL_EQN] \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
                    \\ once_rewrite_tac [CONS_APPEND] \\ gs [])
                \\ rw [FOLDL_APPEND]
                \\ qpat_x_assum ‘($= +++ v_rel) _ _’ mp_tac
                \\ once_rewrite_tac [CONS_APPEND]
                \\ gvs [GSYM CONJ_ASSOC, subst_APPEND]
                \\ qmatch_goalsub_abbrev_tac ‘_ (INL Diverge) (eval_to _ expr2)’
                \\ Cases_on ‘eval_to (k - 2) expr2 = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j3 + k - 2’ assume_tac) eval_to_mono
                \\ gvs [])
            \\ qexists_tac ‘j + j1 + j2 + j3’
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspecl_then [‘j1 + j2 + j3’] assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspecl_then [‘j + j2 + j3’] assume_tac
            \\ gvs [subst_Apps, subst1_def, MAP_MAP_o, combinTheory.o_DEF]
            \\ gvs [SF ETA_ss]
            \\ qspecl_then [‘eL2' ++ [w1]’, ‘Tick (Force (Value w2))’, ‘j + j1 + j2 + j3 + k - 1’,
                           ‘Value (Recclosure list var)’, ‘Value w2::MAP Value eL1'’]
                           assume_tac eval_to_Apps_INR
            \\ ‘eval_to (j2 + k - 2) (Force (Value w2)) ≠ INL Diverge’ by gvs []
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + j3 + k - 2’] assume_tac) eval_to_mono
            \\ gvs [FOLDL_APPEND]
            \\ qspecl_then [‘s::vL1 ++ s2::vL2 ++ [v3]’, ‘w2::eL1' ++ w2' ::eL2' ++ [w1]’, ‘y2’,
                            ‘j + j1 + j2 + j3 + k - 1’, ‘list’, ‘var’]
                           mp_tac eval_to_Apps_Recclosure_Lams_not_0
            \\ impl_tac
            >- (gvs [LIST_REL_EL_EQN] \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC])
            \\ rw [subst_APPEND, GSYM CONJ_ASSOC, FOLDL_APPEND]
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval_to _ expr1) (eval_to _ expr2)’
            \\ ‘eval_to (j3 + k - 2) expr2 ≠ INL Diverge’
              by (strip_tac \\ Cases_on ‘eval_to (k − 2) expr1’ \\ gvs [])
            \\ dxrule_then (qspecl_then [‘j + j1 + j2 + j3 + k - 2’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ gvs [eval_to_Lams]
        \\ qexists_tac ‘j + j1’ \\ gvs []
        \\ last_x_assum $ qspecl_then [‘j1’] assume_tac
        \\ gvs [subst1_def, subst_Lams, subst_Apps, eval_to_Lams]
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac
        \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, subst1_def, SF ETA_ss]
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_x_assum $ irule_at Any
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ ‘∀a1 a2 b1 b2. a1 = a2 ∧ b1 = b2 ⇒ LUPDATE a1 b1 ys = LUPDATE a2 b2 ys’ by gvs []
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_x_assum $ irule_at Any \\ gvs []
        \\ first_x_assum $ irule_at $ Pos last \\ gvs []
        \\ qpat_x_assum ‘LIST_REL force_arg_rel (MAP SND _) _’ $ irule_at Any
        \\ Q.REFINE_EXISTS_TAC ‘_ ++ [_]’
        \\ gvs [] \\ irule_at (Pos hd) EQ_REFL \\ gvs []
        \\ once_rewrite_tac [CONS_APPEND] \\ gvs [ALL_DISTINCT_APPEND]
        \\ qexists_tac ‘eL2' ++ [w1]’ \\ gvs []
        \\ qexists_tac ‘eL2 ++ [v1]’ \\ gvs []
        \\ qexists_tac ‘eL1'’ \\ qexists_tac ‘eL1’ \\ gvs []
        \\ first_x_assum $ irule_at $ Pos $ el 3
        \\ rw [] \\ gvs []
        >- (irule LIST_EQ \\ rw [EL_MAP]
            \\ strip_tac \\ gvs [EL_MEM])
        >- (irule EQ_TRANS \\ irule_at Any subst_commutes
            \\ gvs [MAP_ZIP]
            \\ conj_tac
            >- (rw[] \\ strip_tac \\ first_x_assum $ qspecl_then [‘v3’] assume_tac \\ gvs [])
            \\ gvs [GSYM ZIP_APPEND, subst_APPEND, GSYM CONJ_ASSOC]))

    (* Recclosure default *)
    >- print_tac "Recclosure 1/3" (
        rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
        \\ ‘OPTREL force_arg_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
        \\ gvs [OPTREL_def]
        \\ rename1 ‘force_arg_rel x0 _’ \\ Cases_on ‘x0’ \\ gvs [force_arg_rel_def]
        \\ IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’ \\ gvs []
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ rename1 ‘subst (_ ++ [(s2, v1)]) _’
        \\ rename1 ‘force_arg_rel body body2’
        \\ last_x_assum $ qspecl_then [‘MAP (λ(g,x). (g, Recclosure xs g)) xs’, ‘s2’, ‘v1’,
                                       ‘body’,
                                       ‘subst (MAP (λ(g,x).(g, Recclosure ys g)) ys
                                               ++ [(s2, w1)]) body2’] mp_tac
        \\ impl_tac
        >- (irule force_arg_rel_subst \\ gvs []
            \\ gvs [LIST_REL_EL_EQN, EL_MAP, MAP_MAP_o, combinTheory.o_DEF,
                    LAMBDA_PROD, GSYM FST_THM]
            \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
            \\ rename1 ‘n < _’ \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
            \\ gvs [EL_MAP]
            \\ irule v_rel_Recclosure \\ gvs [LIST_REL_EL_EQN, EL_MAP])
        \\ disch_then $ qx_choose_then ‘j2’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x). (g, Recclosure xs g)) xs
                                             ++ [(s2,v1)]) body) = INL Diverge’
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
                                         ++ [(s2,w1)]) body2) ≠ INL Diverge’
          by (strip_tac
              \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs
                                                   ++ [(s2,v1)]) body)’
              \\ gvs [])
        \\ dxrule_then (qspec_then ‘j + j1 + j2 + k - 1’ assume_tac) eval_to_mono
        \\ gvs [])

    (* Recclosure not in frees *)
    >- print_tac "Recclosure 2/3" (
        rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
        \\ gvs [MEM_EL, EL_MAP, alookup_distinct_reverse]
        \\ rename1 ‘LUPDATE (v1', Lams (vL1++s3::vL2) (Apps (Var v2) _)) i ys’
        \\ ‘ALL_DISTINCT (MAP FST (LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
                                                      (Apps (Var v2)
                      (MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys))’
          by (gvs [LUPDATE_MAP]
              \\ qspecl_then [‘ys’, ‘i’] assume_tac LUPDATE_ID_MAP_FST \\ gvs []
              \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs []
              \\ gvs [EL_MAP, LIST_REL_EL_EQN])
        \\ drule_then assume_tac alookup_distinct_reverse
        \\ qspecl_then [‘LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
     (Apps (Var v2) (MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys’,
                        ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
        \\ qspecl_then [‘xs’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
        \\ gvs [EL_MAP, EL_LUPDATE, LIST_REL_EL_EQN]
        \\ Cases_on ‘n = i’ \\ gvs []
        >~[‘ALOOKUP (LUPDATE _ _ _) _ = SOME (SND (EL n ys))’]
        >- (IF_CASES_TAC \\ gvs []
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
                \\ gvs [REVERSE_SNOC]
                \\ IF_CASES_TAC \\ gvs []
                >- (rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_MAP])
                \\ once_rewrite_tac [CONS_APPEND]
                \\ gvs [Lams_split]
                \\ first_x_assum $ dxrule_then assume_tac
                \\ Cases_on ‘SND (EL n xs)’ \\ gvs [force_arg_rel_def])
            \\ first_assum $ drule_then assume_tac
            \\ Cases_on ‘SND (EL n xs)’ \\ gvs [force_arg_rel_def]
            \\ rename1 ‘force_arg_rel body body'’
            \\ qpat_x_assum ‘∀i. _ = INR (Recclosure (SNOC _ _) _)’ mp_tac
            \\ qmatch_goalsub_abbrev_tac ‘_ = INR (Recclosure list _)’ \\ strip_tac
            \\ last_x_assum $ qspecl_then [‘MAP (λ(g,x).(g,Recclosure xs g)) xs’, ‘s’, ‘v1’, ‘body’,
                     ‘subst (MAP (λ(g,x).(g,Recclosure list g)) list ++ [(s,w1)]) body'’] mp_tac
            \\ impl_tac
            >- (unabbrev_all_tac \\ gvs [SNOC_APPEND, MAP_APPEND, subst_APPEND]
                \\ irule force_arg_rel_subst
                \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
                \\ irule_at Any $ GSYM LUPDATE_ID
                \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                \\ rw []
                >- (gvs [EVERY_EL]
                    \\ qpat_x_assum ‘∀i. _ < _ ⇒ _ ∉ freevars _’ $ qspec_then ‘n’ assume_tac
                    \\ drule_then assume_tac force_arg_rel_freevars
                    \\ gvs [EL_MAP, freevars_def, subst1_notin_frees, freevars_subst]
                    \\ irule force_arg_rel_subst \\ gvs [])
                \\ rw [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE]
                \\ IF_CASES_TAC \\ gvs []
                >- (gvs [GSYM SNOC_APPEND] \\ irule v_rel_Recclosure_Lam_Force
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL] \\ rw []
                    >- (first_assum $ irule_at Any \\ gvs [EL_MAP])
                    >- (irule_at Any EQ_REFL \\ gvs []))
                \\ rename1 ‘v_rel (_ (EL n2 _)) _’
                \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [GSYM SNOC_APPEND]
                \\ irule v_rel_Recclosure_Lam_Force
                \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL] \\ rw []
                >- (first_assum $ irule_at Any \\ gvs [EL_MAP])
                >- (irule_at Any EQ_REFL \\ gvs []))
            \\ disch_then $ qx_choose_then ‘j2’ assume_tac
            \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs++[(s,v1)]) body) = INL Diverge’
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k y’ \\ gvs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g’ \\ gvs []
                \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
                \\ IF_CASES_TAC \\ gvs []
                >- (rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_MAP])
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
                \\ qpat_x_assum ‘($= +++ v_rel) (INL Diverge) _’ mp_tac \\ once_rewrite_tac [CONS_APPEND]
                \\ gvs [] \\ strip_tac
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (INL Diverge) (eval_to _ expr)’
                \\ Cases_on ‘eval_to (k - 1) expr = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j2 + k - 1’ assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to (k - 1) expr’ \\ gvs [])
            \\ qexists_tac ‘j + j1 + j2’
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1 + j2’ assume_tac \\ gvs []
            \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_MAP])
            \\ qpat_x_assum ‘($= +++ v_rel) (eval_to _ (subst _ _)) _’ mp_tac \\ once_rewrite_tac [CONS_APPEND]
            \\ gvs [] \\ strip_tac
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr)’
            \\ ‘eval_to (j2 + k - 1) expr ≠ INL Diverge’
              by (strip_tac
                  \\ Cases_on ‘eval_to (k − 1) (subst (MAP (λ(g,x). (g,Recclosure xs g)) xs ++ [(s,v1)]) body)’
                  \\ gvs [])
            \\ dxrule_then (qspec_then ‘j + j1 + j2 + k - 1’ assume_tac) eval_to_mono \\ gvs [])
        \\ IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ once_rewrite_tac [CONS_APPEND]
            \\ gvs [Lams_split])
        \\ Cases_on ‘vL1’ \\ gvs []
        >~[‘subst _ (Lams (vL1 ++ s3::vL2) _)’]
        >- (qexists_tac ‘j + j1’
            \\ first_x_assum $ qspec_then ‘j’ assume_tac
            \\ first_x_assum $ qspec_then ‘j1’ assume_tac \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [subst_Lams]
            \\ gvs [eval_to_Lams]
            \\ ‘HD (vL1 ++ [s3] ++ vL2) = HD (SNOC s3 vL1)’
              by (Cases_on ‘vL1’ \\ gvs []) \\ gvs []
            \\ qmatch_goalsub_abbrev_tac ‘subst (FILTER _ list) (Apps _ _)’
            \\ ‘MAP (λs. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s3 ∧ ¬MEM v vL2) list) (Var s))
                vL1 = MAP Var vL1’
              by (irule LIST_EQ \\ rw [EL_MAP]
                  \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
            \\ ‘MAP (λs. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s3 ∧ ¬MEM v vL2) list) (Var s))
                vL2 = MAP Var vL2’
              by (irule LIST_EQ \\ rw [EL_MAP]
                  \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
            \\ gvs [subst_Apps, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF, GSYM CONJ_ASSOC]
            \\ gvs [subst_App, subst_Force, subst_Var, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
            \\ qpat_x_assum ‘MAP _ _ = MAP Var _’ kall_tac
            \\ qpat_x_assum ‘MAP _ _ = MAP Var _’ kall_tac
            \\ ‘¬MEM v2 vL1 ∧ ¬MEM v2 vL2’
              by (conj_tac \\ strip_tac \\ gvs [MEM_EL] \\ rename1 ‘n2 < _’
                  \\ rpt $ first_x_assum $ qspec_then ‘SUC n2’ assume_tac \\ gvs [])
            \\ gvs [FILTER_APPEND, subst_APPEND]
            \\ unabbrev_all_tac \\ gvs [MAP_APPEND, REVERSE_APPEND, ALOOKUP_APPEND]
            \\ ‘v2 ≠ h’ by (rpt $ first_x_assum $ qspec_then ‘0’ assume_tac \\ gvs [])
            \\ gvs [MAP_SNOC, REVERSE_SNOC]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
            \\ disj2_tac \\ disj1_tac
            \\ irule_at (Pos hd) EQ_REFL \\ gvs []
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any
            \\ ‘∀l1 h l2 e1 e2. h::l1 = l2 ∧ e1 = e2 ⇒ Apps (App e1 h) l1 = Apps e2 l2’ by gvs []
            \\ pop_assum $ irule_at Any \\ gvs []
            \\ rename1 ‘LUPDATE _ _ ys = _’ \\ qexists_tac ‘ys’ \\ gvs []
            \\ rename1 ‘Lam _ (Lams _ y2) = _’ \\ qexists_tac ‘y2’ \\ gvs []
            \\ first_x_assum $ irule_at $ Pos last
            \\ qexists_tac ‘xs’ \\ qexists_tac ‘vL2’ \\ gvs []
            \\ Q.REFINE_EXISTS_TAC ‘[variable]’ \\ gvs [PULL_EXISTS]
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [] \\ irule_at (Pos $ el 2) EQ_REFL
            \\ irule_at (Pos $ el 2) EQ_REFL \\ gvs []
            \\ first_x_assum $ irule_at $ Pos $ el 3
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [] \\ rw []
            >- gvs [subst_def, MAP_APPEND, FILTER_APPEND, REVERSE_APPEND,
                    GSYM FILTER_REVERSE, ALOOKUP_FILTER]
            >- (irule EQ_TRANS \\ irule_at (Pos last) subst_commutes
                \\ gvs [MAP_FST_FILTER, MEM_FILTER]
                \\ ‘∀e vs v. subst vs (subst1 h v e) = subst (FILTER (λ(n,e). n ≠ h) vs)
                                                             (subst1 h v e)’
                  by (rw [] \\ qspecl_then [‘vs’, ‘subst1 h v e’, ‘{h}’] assume_tac subst_remove
                      \\ gvs [freevars_subst])
                \\ irule EQ_TRANS \\ pop_assum $ irule_at Any
                \\ gvs [FILTER_FILTER, LAMBDA_PROD, GSYM CONJ_ASSOC])
            >- gvs [LIST_REL_EL_EQN, EL_MAP]
            >- rw [MEM_EL]
            >- (rpt $ first_x_assum $ qspec_then ‘0’ assume_tac \\ gvs [])
            >- (rw [MEM_EL] \\ rename1 ‘EL n vL1 = EL _ (_::vL1)’
                \\ rpt $ first_x_assum $ qspec_then ‘SUC n’ assume_tac \\ gvs [])
            >- (rw [MEM_EL] \\ rename1 ‘EL n vL2 = EL _ (_::vL2)’
                \\ rpt $ first_x_assum $ qspec_then ‘SUC n’ assume_tac \\ gvs [])
            >- (gvs [EVERY_EL]
                \\ qpat_x_assum ‘∀n. _ ⇒ v2 ∉ freevars _’ $ qspec_then ‘i’ assume_tac
                \\ gvs [EL_MAP, freevars_def, freevars_Lams]))
        \\ Cases_on ‘vL2’ \\ gvs []
        >~[‘eval_to _ (subst _ (Lam _ (Lams _ _)))’]
        >- (qexists_tac ‘j + j1’
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, eval_to_def]
            \\ qmatch_goalsub_abbrev_tac ‘v_rel _ (Closure _ (subst (FILTER _ list) _))’
            \\ gvs [subst_Lams, subst_Apps, subst_App, MAP_MAP_o, combinTheory.o_DEF,
                    FILTER_FILTER, LAMBDA_PROD, subst_Var, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
            \\ rename1 ‘v_rel (Closure h (Lams vL1 _)) _’
            \\ ‘¬MEM v2 (h::vL1)’ by (strip_tac \\ dxrule_then mp_tac $ iffLR MEM_EL \\ gvs [])
            \\ gvs []
            \\ ‘MAP (λx. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ h) list) (Var x)) vL1
                = MAP Var vL1’
              by (irule LIST_EQ \\ rw [EL_MAP, subst_def]
                  \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
            \\ gvs [subst_Var, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
            \\ gvs [v_rel_def]
            \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
            \\ qexists_tac ‘[]’ \\ gvs [] \\ qexists_tac ‘[]’ \\ gvs []
            \\ qexists_tac ‘v1’ \\ qexists_tac ‘w1’ \\ qexists_tac ‘h::vL1’ \\ gvs []
            \\ qpat_assum ‘EL _ _ = (_, Lam _ (Lam _ (Lams _ _)))’ $ irule_at Any \\ gvs []
            \\ first_x_assum $ irule_at $ Pos $ last \\ gvs []
            \\ qexists_tac ‘ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
            \\ qexists_tac ‘v2’ \\ gvs [] \\ rw []
            >- (AP_THM_TAC \\ AP_TERM_TAC
                \\ gvs [FILTER_APPEND, subst_APPEND, subst1_def, subst1_notin_frees]
                \\ irule EQ_TRANS \\ irule_at (Pos hd) $ GSYM subst_remove
                \\ rename1 ‘s3 ∉ freevars _’ \\ qexists_tac ‘{s3}’
                \\ gvs [freevars_def, FILTER_FILTER, LAMBDA_PROD]
                \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
                \\ gvs []
                \\ metis_tac [CONJ_COMM])
            >- (unabbrev_all_tac \\ gvs [REVERSE_APPEND, MAP_SNOC, REVERSE_SNOC]
                \\ gvs [subst_def, REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER])
            >- gvs [MEM_EL]
            >- (rpt $ first_x_assum $ qspec_then ‘0’ assume_tac \\ gvs [])
            >- (‘¬MEM s2 (h::vL1)’
                  by (strip_tac \\ dxrule_then mp_tac $ iffLR MEM_EL \\ gvs []) \\ gvs [])
            >- (gvs [EVERY_EL]
                \\ qpat_x_assum ‘∀i. _ ⇒ v2 ∉ freevars _’ $ qspec_then ‘i’ assume_tac
                \\ gvs [EL_MAP, freevars_def, freevars_Lams]))
        \\ rename1 ‘_ (eval_to _ (subst (MAP _ _ ++ [(s3, v1)]) (Let _ _ x2))) _’
        \\ last_assum $ qspecl_then [‘[]’, ‘s3’, ‘v1’, ‘Tick (Force (Value v1))’,
                                       ‘Tick (Force (Value w1))’] mp_tac
        \\ impl_tac
        >- gvs [subst_def, force_arg_rel_def]
        \\ disch_then $ qx_choose_then ‘j2’ assume_tac
        \\ ‘∀k e. k ≠ 0 ⇒ eval_to k (Tick e) = eval_to (k - 1) e’
           by (rw [eval_to_def] \\ gvs [subst_funs_def, subst_empty])
        \\ gvs [subst_APPEND, subst_def]
        \\ once_rewrite_tac [eval_to_def]
        \\ IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k y’
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k g’
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
            \\ once_rewrite_tac [eval_to_def] \\ gvs []
            \\ ‘k = 1’ by (Cases_on ‘k’ \\ gvs [])
            \\ once_rewrite_tac [eval_to_def]
            \\ gvs [])
        \\ Cases_on ‘eval_to (k - 2) (Force (Value v1)) = INL Diverge’ \\ gvs [subst1_def]
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k y’
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k g’
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
            \\ once_rewrite_tac [eval_to_def] \\ gvs []
            \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
            \\ dxrule_then (qspec_then ‘j2 + k - 2’ assume_tac) eval_to_mono
            \\ gvs []
            \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs [])
        \\ Cases_on ‘eval_to (k - 2) (Force (Value v1))’ \\ gvs []
        >- (qexists_tac ‘j + j1 + j2’
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1 + j2’ assume_tac
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
            \\ once_rewrite_tac [eval_to_def] \\ gvs []
            \\ ‘eval_to (j2 + k - 2) (Force (Value w1)) ≠ INL Diverge’ by (strip_tac \\ gvs [])
            \\ dxrule_then (qspec_then ‘j + j1 + j2 + k - 2’ assume_tac) eval_to_mono
            \\ gvs []
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs [])
        \\ gvs [subst1_notin_frees]
        \\ rename1 ‘eval_to _ (subst1 s2 val1 (subst _ _))’ \\ rename1 ‘force_arg_rel x2 y2’
        \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs []
        \\ rename1 ‘v_rel val1 val2’
        \\ qspecl_then [‘x2’, ‘[(s2, val1)]’,
                        ‘FILTER (λ(n,x). n≠ s2) (MAP (λ(g,x). (g, Recclosure xs g)) xs)’]
                       assume_tac subst_commutes
        \\ gvs [MAP_FST_FILTER, MEM_FILTER] \\ pop_assum kall_tac
        \\ qspecl_then [‘MAP (λ(g,x).(g, Recclosure xs g)) xs’,
                        ‘subst1 s2 val1 x2’, ‘{s2}’] assume_tac subst_remove
        \\ gvs [freevars_subst] \\ pop_assum kall_tac
        \\ qpat_x_assum ‘∀i. eval_to _ g = INR (Recclosure (SNOC _ _) _)’ mp_tac
        \\ qmatch_goalsub_abbrev_tac ‘eval_to _ _ = INR (Recclosure list _)’ \\ strip_tac
        \\ last_x_assum $ qspecl_then [‘MAP (λ(g,x).(g, Recclosure xs g)) xs’, ‘s2’, ‘val1’,
                                       ‘Tick x2’,
                                       ‘subst (MAP (λ(g,x).(g,Recclosure list g)) list)
                                              (subst1 s2 val2 (Tick y2))’] mp_tac
        \\ impl_tac
        >- (unabbrev_all_tac \\ gvs [SNOC_APPEND, MAP_APPEND, subst_APPEND]
            \\ irule force_arg_rel_subst
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
            \\ irule_at Any $ GSYM LUPDATE_ID
            \\ rw [EL_MAP]
            >- (gvs [EVERY_EL]
                \\ qpat_x_assum ‘∀i. _ < _ ⇒ _ ∉ freevars _’ $ qspec_then ‘i’ assume_tac
                \\ drule_then assume_tac force_arg_rel_freevars
                \\ gvs [EL_MAP, freevars_def, subst1_notin_frees, freevars_subst]
                \\ irule force_arg_rel_subst \\ gvs [force_arg_rel_def])
            \\ rw [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE]
            \\ IF_CASES_TAC \\ gvs []
            >- (gvs [GSYM SNOC_APPEND]
                \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                \\ qexists_tac ‘ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                \\ qexists_tac ‘x2’ \\ first_x_assum $ irule_at $ Pos last
                \\ qexists_tac ‘[]’ \\ qexists_tac ‘[]’ \\ gvs []
                \\ irule_at (Pos hd) EQ_REFL
                \\ gvs [MEM_EL]
                \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
            \\ rename1 ‘v_rel (_ (EL n2 _)) _’
            \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
            \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [GSYM SNOC_APPEND]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
            \\ qexists_tac ‘ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
            \\ qexists_tac ‘x2’ \\ first_x_assum $ irule_at $ Pos last
            \\ qexists_tac ‘[]’ \\ qexists_tac ‘[]’ \\ gvs []
            \\ irule_at (Pos hd) EQ_REFL
            \\ gvs [MEM_EL]
            \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
        \\ gvs [subst_Tick]
        \\ disch_then $ qx_choose_then ‘j3’ assume_tac
        \\ Cases_on ‘eval_to (k − 2) (subst (MAP (λ(g,x). (g,Recclosure xs g)) xs)
                                      (subst1 s2 val1 x2)) = INL Diverge’
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k y’
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k g’
            \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
            \\ once_rewrite_tac [eval_to_def] \\ gvs []
            \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
            \\ dxrule_then (qspec_then ‘j2 + k - 2’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs []
            \\ rw [eval_to_def] \\ gvs [dest_anyClosure_def]
            \\ gvs [REVERSE_SNOC, subst_APPEND, MAP_SNOC]
            \\ rename1 ‘_ (INL Diverge) (eval_to _ expr)’
            \\ Cases_on ‘eval_to (k - 2) expr = INL Diverge’ \\ gvs []
            \\ dxrule_then (qspec_then ‘j3 + k - 2’ assume_tac) eval_to_mono
            \\ gvs [])
        \\ qexists_tac ‘j + j1 + j2 + j3’
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2 + j3’ assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1 + j2 + j3’ assume_tac \\ gvs []
        \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
        \\ IF_CASES_TAC \\ gvs []
        >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
        \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
        \\ once_rewrite_tac [eval_to_def] \\ gvs []
        \\ ‘eval_to (j2 + k - 2) (Force (Value w1)) ≠ INL Diverge’ by gvs []
        \\ dxrule_then (qspec_then ‘j + j1 + j2 + j3 + k - 2’ assume_tac) eval_to_mono \\ gvs []
        \\ rw [eval_to_def] \\ gvs [dest_anyClosure_def]
        \\ gvs [REVERSE_SNOC, subst_APPEND, MAP_SNOC]
        \\ rename1 ‘_ (eval_to _ expr1) (eval_to _ expr2)’
        \\ ‘eval_to (j3 + k - 2) expr2 ≠ INL Diverge’
          by (strip_tac \\ Cases_on ‘eval_to (k - 2) expr1’ \\ gvs [])
        \\ dxrule_then (qspec_then ‘j + j1 + j2 + j3 + k - 2’ assume_tac) eval_to_mono \\ gvs [])

    (* Recclosure double var *)
    >- print_tac "Recclosure 3/3" (
        rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
        \\ gvs [MEM_EL, EL_MAP, alookup_distinct_reverse]
        \\ rename1 ‘LUPDATE (v1', Lams (vL1++s3::vL2) (Apps (App (Var v2) _) _)) i ys’
        \\ ‘ALL_DISTINCT (MAP FST (LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
                                                      (Apps (Var v2)
                      (Var s3::MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys))’
          by (gvs [LUPDATE_MAP]
              \\ qspecl_then [‘ys’, ‘i’] assume_tac LUPDATE_ID_MAP_FST \\ gvs []
              \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs []
              \\ gvs [EL_MAP, LIST_REL_EL_EQN])
        \\ drule_then assume_tac alookup_distinct_reverse
        \\ qspecl_then [‘LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
     (Apps (Var v2) (Var s3::MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys’,
                        ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
        \\ qspecl_then [‘xs’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
        \\ gvs [EL_MAP, EL_LUPDATE, LIST_REL_EL_EQN]
        \\ Cases_on ‘n = i’ \\ gvs []
        >~[‘ALOOKUP (LUPDATE _ _ _) _ = SOME (SND (EL n ys))’]
        >- (IF_CASES_TAC \\ gvs []
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
                \\ gvs [REVERSE_SNOC]
                \\ IF_CASES_TAC \\ gvs []
                \\ once_rewrite_tac [CONS_APPEND] \\ gs []
                \\ first_x_assum $ dxrule_then assume_tac
                \\ Cases_on ‘SND (EL n xs)’ \\ gvs [force_arg_rel_def])
            \\ first_assum $ drule_then assume_tac
            \\ Cases_on ‘SND (EL n xs)’ \\ gvs [force_arg_rel_def]
            \\ rename1 ‘force_arg_rel body body'’
            \\ qpat_x_assum ‘∀i. _ = INR (Recclosure (SNOC _ _) _)’ mp_tac
            \\ qmatch_goalsub_abbrev_tac ‘_ = INR (Recclosure list _)’ \\ strip_tac
            \\ last_x_assum $ qspecl_then [‘MAP (λ(g,x).(g,Recclosure xs g)) xs’, ‘s’, ‘v1’, ‘body’,
                     ‘subst (MAP (λ(g,x).(g,Recclosure list g)) list ++ [(s,w1)]) body'’] mp_tac
            \\ impl_tac
            >- (unabbrev_all_tac \\ gvs [SNOC_APPEND, MAP_APPEND, subst_APPEND]
                \\ irule force_arg_rel_subst
                \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
                \\ irule_at Any $ GSYM LUPDATE_ID
                \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                \\ rw []
                >- (gvs [EVERY_EL]
                    \\ qpat_x_assum ‘∀i. _ < _ ⇒ _ ∉ freevars _’ $ qspec_then ‘n’ assume_tac
                    \\ drule_then assume_tac force_arg_rel_freevars
                    \\ gvs [EL_MAP, freevars_def, subst1_notin_frees, freevars_subst]
                    \\ irule force_arg_rel_subst \\ gvs [])
                \\ rw [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE]
                \\ IF_CASES_TAC \\ gvs []
                >- (gvs [GSYM SNOC_APPEND]
                    \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                    \\ rpt $ irule_at (Pos hd) EQ_REFL
                    \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL] \\ rw []
                    \\ irule_at (Pos hd) EQ_REFL \\ rw []
                    \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
                \\ rename1 ‘v_rel (_ (EL n2 _)) _’
                \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [GSYM SNOC_APPEND]
                \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                \\ rpt $ irule_at (Pos hd) EQ_REFL \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                \\ irule_at Any EQ_REFL \\ fs []
                \\ gvs [MEM_EL] \\ rw []
                \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
            \\ disch_then $ qx_choose_then ‘j2’ assume_tac
            \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs++[(s,v1)]) body) = INL Diverge’
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k y’ \\ gvs []
                \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to k g’ \\ gvs []
                \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
                \\ IF_CASES_TAC \\ gvs []
                >- (rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_MAP])
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
                \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
                \\ qpat_x_assum ‘($= +++ v_rel) (INL Diverge) _’ mp_tac \\ once_rewrite_tac [CONS_APPEND]
                \\ gs [] \\ once_rewrite_tac [CONS_APPEND] \\ gs [] \\ strip_tac
                \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (INL Diverge) (eval_to _ expr)’
                \\ Cases_on ‘eval_to (k - 1) expr = INL Diverge’ \\ gvs []
                \\ dxrule_then (qspec_then ‘j2 + k - 1’ assume_tac) eval_to_mono
                \\ Cases_on ‘eval_to (k - 1) expr’ \\ gvs [])
            \\ qexists_tac ‘j + j1 + j2’
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1 + j2’ assume_tac \\ gvs []
            \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_MAP])
            \\ qpat_x_assum ‘($= +++ v_rel) (eval_to _ (subst _ _)) _’ mp_tac \\ once_rewrite_tac [CONS_APPEND]
            \\ gs [] \\ once_rewrite_tac [CONS_APPEND] \\ gs [] \\ strip_tac
            \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) _ (eval_to _ expr)’
            \\ ‘eval_to (j2 + k - 1) expr ≠ INL Diverge’
              by (strip_tac
                  \\ Cases_on ‘eval_to (k − 1) (subst (MAP (λ(g,x). (g,Recclosure xs g)) xs ++ [(s,v1)]) body)’
                  \\ gvs [])
            \\ dxrule_then (qspec_then ‘j + j1 + j2 + k - 1’ assume_tac) eval_to_mono \\ gvs [])
        \\ IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1’] assume_tac) eval_to_mono
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            \\ once_rewrite_tac [CONS_APPEND] \\ gs []
            \\ gvs [Lams_split])
        \\ Cases_on ‘vL1’ \\ gvs []
        >~[‘subst _ (Lams (vL1 ++ s3::vL2) _)’]
        >- (qexists_tac ‘j + j1’
            \\ first_x_assum $ qspec_then ‘j’ assume_tac
            \\ first_x_assum $ qspec_then ‘j1’ assume_tac \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ once_rewrite_tac [CONS_APPEND] \\ gs []
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs [subst_Lams]
            \\ gvs [eval_to_Lams]
            \\ ‘HD (vL1 ++ [s3] ++ vL2) = HD (SNOC s3 vL1)’
              by (Cases_on ‘vL1’ \\ gvs []) \\ gvs []
            \\ qmatch_goalsub_abbrev_tac ‘subst (FILTER _ list) (Apps _ _)’
            \\ ‘MAP (λs. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s3 ∧ ¬MEM v vL2) list) (Var s))
                vL1 = MAP Var vL1’
              by (irule LIST_EQ \\ rw [EL_MAP]
                  \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
            \\ ‘MAP (λs. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ s3 ∧ ¬MEM v vL2) list) (Var s))
                vL2 = MAP Var vL2’
              by (irule LIST_EQ \\ rw [EL_MAP]
                  \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
            \\ gvs [subst_Apps, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF, GSYM CONJ_ASSOC]
            \\ gvs [subst_App, subst_Force, subst_Var, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
            \\ qpat_x_assum ‘MAP _ _ = MAP Var _’ kall_tac
            \\ qpat_x_assum ‘MAP _ _ = MAP Var _’ kall_tac
            \\ ‘¬MEM v2 vL1 ∧ ¬MEM v2 vL2’
              by (conj_tac \\ strip_tac \\ gvs [MEM_EL] \\ rename1 ‘n2 < _’
                  \\ rpt $ first_x_assum $ qspec_then ‘SUC n2’ assume_tac \\ gvs [])
            \\ gvs [FILTER_APPEND, subst_APPEND]
            \\ unabbrev_all_tac \\ gvs [MAP_APPEND, REVERSE_APPEND, ALOOKUP_APPEND]
            \\ ‘v2 ≠ h’ by (rpt $ first_x_assum $ qspec_then ‘0’ assume_tac \\ gvs [])
            \\ gvs [MAP_SNOC, REVERSE_SNOC]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
            \\ disj2_tac \\ disj2_tac \\ disj1_tac
            \\ irule_at (Pos hd) EQ_REFL \\ gvs []
            \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
            \\ first_assum $ irule_at Any
            \\ first_x_assum $ irule_at Any
            \\ ‘∀l1 h l2 e1 e2. h::l1 = l2 ∧ e1 = e2 ⇒ Apps (App e1 h) l1 = Apps e2 l2’ by gvs []
            \\ pop_assum $ irule_at Any \\ gvs []
            \\ rename1 ‘LUPDATE _ _ ys = _’ \\ qexists_tac ‘ys’ \\ gvs []
            \\ rename1 ‘Lam _ (Lams _ y2) = _’ \\ qexists_tac ‘y2’ \\ gvs []
            \\ first_x_assum $ irule_at $ Pos last
            \\ qexists_tac ‘xs’ \\ qexists_tac ‘vL2’ \\ gvs []
            \\ Q.REFINE_EXISTS_TAC ‘[variable]’ \\ gvs [PULL_EXISTS]
            \\ gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
            \\ once_rewrite_tac [CONS_APPEND] \\ gs []
            \\ irule_at (Pos hd) EQ_REFL
            \\ gvs []
            \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
            \\ first_x_assum $ irule_at $ Pos $ el 2
            \\ rw [] \\ gvs []
            >- (irule EQ_TRANS \\ irule_at (Pos hd) $ GSYM subst_remove
                \\ rename1 ‘Lam h (Lams _ _)’ \\ qexists_tac ‘{h}’
                \\ gvs [freevars_subst]
                \\ irule EQ_TRANS \\ irule_at Any subst_commutes
                \\ gvs [MAP_FST_FILTER, MEM_FILTER]
                \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [GSYM CONJ_ASSOC] \\ metis_tac [CONJ_COMM])
            >- (AP_THM_TAC \\ AP_TERM_TAC \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [GSYM CONJ_ASSOC] \\ metis_tac [CONJ_COMM])
            >- gvs [LIST_REL_EL_EQN, EL_MAP]
            >- gvs [MEM_EL]
            >- (rpt $ first_x_assum $ qspec_then ‘0’ assume_tac \\ gs [])
            >- (rw [MEM_EL] \\ rename1 ‘EL n vL1 = EL _ (_::vL1)’
                \\ rpt $ first_x_assum $ qspec_then ‘SUC n’ assume_tac \\ gvs [])
            >- (rw [MEM_EL] \\ rename1 ‘EL n vL2 = EL _ (_::vL2)’
                \\ rpt $ first_x_assum $ qspec_then ‘SUC n’ assume_tac \\ gvs [])
            >- (gvs [EVERY_EL]
                \\ qpat_x_assum ‘∀n. _ ⇒ v2 ∉ freevars _’ $ qspec_then ‘i’ assume_tac
                \\ gvs [EL_MAP, freevars_def, freevars_Lams]))
        \\ Cases_on ‘vL2’ \\ gvs []
        >~[‘eval_to _ (subst _ (Lam _ (Lams _ _)))’]
        >- (qexists_tac ‘j + j1’
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1’ assume_tac
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, eval_to_def]
            \\ qmatch_goalsub_abbrev_tac ‘v_rel _ (Closure _ (subst (FILTER _ list) _))’
            \\ gvs [subst_Lams, subst_Apps, subst_App, MAP_MAP_o, combinTheory.o_DEF,
                    FILTER_FILTER, LAMBDA_PROD, subst_Var, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
            \\ rename1 ‘v_rel (Closure h (Lams vL1 _)) _’
            \\ ‘¬MEM v2 (h::vL1)’ by (strip_tac \\ dxrule_then mp_tac $ iffLR MEM_EL \\ gvs [])
            \\ gvs []
            \\ ‘MAP (λx. subst (FILTER (λ(v,e). ¬MEM v vL1 ∧ v ≠ h) list) (Var x)) vL1
                = MAP Var vL1’
              by (irule LIST_EQ \\ rw [EL_MAP, subst_def]
                  \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER, EL_MEM])
            \\ gvs [subst_Var, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
            \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
            \\ qexists_tac ‘[]’ \\ gvs [] \\ qexists_tac ‘[]’ \\ gvs []
            \\ qexists_tac ‘v1’ \\ qexists_tac ‘w1’ \\ qexists_tac ‘h::vL1’ \\ gvs []
            \\ qpat_assum ‘EL _ _ = (_, Lam _ (Lam _ (Lams _ _)))’ $ irule_at Any \\ gvs []
            \\ first_x_assum $ irule_at $ Pos $ last \\ gvs []
            \\ qexists_tac ‘ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
            \\ qexists_tac ‘v2’ \\ gvs [] \\ rw []
            >- (AP_THM_TAC \\ AP_TERM_TAC
                \\ gvs [FILTER_APPEND, subst_APPEND, subst1_def, subst1_notin_frees]
                \\ irule EQ_TRANS \\ irule_at (Pos hd) $ GSYM subst_remove
                \\ rename1 ‘subst1 s4 _ _’ \\ qexists_tac ‘{s4}’
                \\ gvs [freevars_def, freevars_subst, FILTER_FILTER, LAMBDA_PROD]
                \\ irule EQ_TRANS \\ irule_at (Pos last) subst_commutes
                \\ gvs [MAP_FST_FILTER, MEM_FILTER, subst1_def]
                \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
                \\ gvs []
                \\ metis_tac [CONJ_COMM])
            >- (unabbrev_all_tac \\ gvs [REVERSE_APPEND, MAP_SNOC, REVERSE_SNOC]
                \\ gvs [subst_def, REVERSE_APPEND, GSYM FILTER_REVERSE, ALOOKUP_FILTER])
            >- gvs [MEM_EL]
            >- (rpt $ first_x_assum $ qspec_then ‘0’ assume_tac \\ gvs [])
            >- (‘¬MEM s2 (h::vL1)’
                  by (strip_tac \\ dxrule_then mp_tac $ iffLR MEM_EL \\ gvs []) \\ gvs [])
            >- (gvs [EVERY_EL]
                \\ qpat_x_assum ‘∀i. _ ⇒ v2 ∉ freevars _’ $ qspec_then ‘i’ assume_tac
                \\ gvs [EL_MAP, freevars_def, freevars_Lams]))
        \\ rename1 ‘_ (eval_to _ (subst (MAP _ _ ++ [(s3, v1)]) (Let _ _ x2))) _’
        \\ last_assum $ qspecl_then [‘[]’, ‘s3’, ‘v1’, ‘Tick (Force (Value v1))’,
                                       ‘Tick (Force (Value w1))’] mp_tac
        \\ impl_tac
        >- gvs [subst_def, force_arg_rel_def]
        \\ disch_then $ qx_choose_then ‘j2’ assume_tac
        \\ ‘∀k e. k ≠ 0 ⇒ eval_to k (Tick e) = eval_to (k - 1) e’
           by (rw [eval_to_def] \\ gvs [subst_funs_def, subst_empty])
        \\ gvs [subst_APPEND, subst_def]
        \\ once_rewrite_tac [eval_to_def]
        \\ IF_CASES_TAC \\ gvs []
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k y’
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k g’
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
            \\ once_rewrite_tac [eval_to_def] \\ gvs []
            \\ ‘k = 1’ by (Cases_on ‘k’ \\ gvs [])
            \\ once_rewrite_tac [eval_to_def]
            \\ gvs [])
        \\ Cases_on ‘eval_to (k - 2) (Force (Value v1)) = INL Diverge’ \\ gvs [subst1_def]
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k y’
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k g’
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
            \\ once_rewrite_tac [eval_to_def] \\ gvs []
            \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
            \\ dxrule_then (qspec_then ‘j2 + k - 2’ assume_tac) eval_to_mono
            \\ gvs []
            \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs [])
        \\ Cases_on ‘eval_to (k - 2) (Force (Value v1))’ \\ gvs []
        >- (qexists_tac ‘j + j1 + j2’
            \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2’ assume_tac
            \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1 + j2’ assume_tac
            \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
            \\ once_rewrite_tac [eval_to_def] \\ gvs []
            \\ ‘eval_to (j2 + k - 2) (Force (Value w1)) ≠ INL Diverge’ by (strip_tac \\ gvs [])
            \\ dxrule_then (qspec_then ‘j + j1 + j2 + k - 2’ assume_tac) eval_to_mono
            \\ gvs []
            \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs [])
        \\ rename1 ‘eval_to _ (subst1 s2 val1 (subst _ _))’ \\ rename1 ‘force_arg_rel x2 y2’
        \\ Cases_on ‘eval_to (j2 + k - 2) (Force (Value w1))’ \\ gvs []
        \\ rename1 ‘v_rel val1 val2’
        \\ qspecl_then [‘subst1 s3 v1 x2’, ‘[(s2, val1)]’,
                        ‘FILTER (λ(n,x). n≠ s2) (MAP (λ(g,x). (g, Recclosure xs g)) xs)’]
                       assume_tac subst_commutes
        \\ gvs [MAP_FST_FILTER, MEM_FILTER] \\ pop_assum kall_tac
        \\ qspecl_then [‘MAP (λ(g,x).(g, Recclosure xs g)) xs’,
                        ‘subst1 s2 val1 (subst1 s3 v1 x2)’, ‘{s2}’] assume_tac subst_remove
        \\ gvs [freevars_subst] \\ pop_assum kall_tac
        \\ qpat_x_assum ‘∀i. eval_to _ g = INR (Recclosure (SNOC _ _) _)’ mp_tac
        \\ qmatch_goalsub_abbrev_tac ‘eval_to _ _ = INR (Recclosure list _)’ \\ strip_tac
        \\ last_x_assum $ qspecl_then [‘MAP (λ(g,x).(g, Recclosure xs g)) xs’, ‘s2’, ‘val1’,
                                       ‘subst1 s3 v1 (Tick x2)’,
                                       ‘subst1 s2 val2
                                        (subst (FILTER (λ(n,x). n ≠ s2) (MAP (λ(g,x).(g,Recclosure list g)) list))
                                         (subst1 s3 w1 (Tick y2)))’] mp_tac
        \\ impl_tac
        >- (‘∀l e. subst1 s2 val2 (subst (FILTER (λ(v,x). v ≠ s2) l) e)
                   = subst l (subst1 s2 val2 e)’
              by (rw [] \\ irule EQ_TRANS \\ irule_at (Pos hd) subst_commutes
                  \\ gvs [MAP_FST_FILTER, MEM_FILTER]
                  \\ irule EQ_TRANS \\ irule_at (Pos last) subst_remove
                  \\ qexists_tac ‘{s2}’ \\ gvs [freevars_subst])
            \\ gvs []
            \\ unabbrev_all_tac \\ gvs [SNOC_APPEND, MAP_APPEND, subst_APPEND]
            \\ irule force_arg_rel_subst
            \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
            \\ irule_at Any $ GSYM LUPDATE_ID
            \\ rw [EL_MAP]
            >- (gvs [EVERY_EL]
                \\ qpat_x_assum ‘∀i. _ < _ ⇒ _ ∉ freevars _’ $ qspec_then ‘i’ assume_tac
                \\ drule_then assume_tac force_arg_rel_freevars
                \\ gvs [EL_MAP, freevars_def, subst1_notin_frees, freevars_subst]
                \\ gvs [force_arg_rel_subst, force_arg_rel_def])
            \\ rw [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE]
            \\ IF_CASES_TAC \\ gvs []
            >- (gvs [GSYM SNOC_APPEND]
                \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                \\ qexists_tac ‘ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
                \\ qexists_tac ‘x2’ \\ first_x_assum $ irule_at $ Pos last
                \\ qexists_tac ‘[]’ \\ qexists_tac ‘[]’ \\ gvs []
                \\ irule_at (Pos hd) EQ_REFL
                \\ gvs [MEM_EL]
                \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
            \\ rename1 ‘v_rel (_ (EL n2 _)) _’
            \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
            \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [GSYM SNOC_APPEND]
            \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
            \\ qexists_tac ‘ys’ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
            \\ qexists_tac ‘x2’ \\ first_x_assum $ irule_at $ Pos last
            \\ qexists_tac ‘[]’ \\ qexists_tac ‘[]’ \\ gvs []
            \\ irule_at (Pos hd) EQ_REFL
            \\ gvs [MEM_EL]
            \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
        \\ gvs [subst_Tick]
        \\ disch_then $ qx_choose_then ‘j3’ assume_tac
        \\ rename1 ‘($= +++ v_rel) (eval_to _ expr1) _’
        \\ Cases_on ‘eval_to (k − 2) expr1 = INL Diverge’
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k y’
            \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
            \\ dxrule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to k g’
            \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
            \\ IF_CASES_TAC \\ gvs []
            >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
            \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
            \\ once_rewrite_tac [eval_to_def] \\ gvs []
            \\ Cases_on ‘eval_to (k - 2) (Force (Value w1)) = INL Diverge’ \\ gvs []
            \\ dxrule_then (qspec_then ‘j2 + k - 2’ assume_tac) eval_to_mono
            \\ Cases_on ‘eval_to (k - 2) (Force (Value w1))’ \\ gvs []
            \\ rw [eval_to_def] \\ gvs [dest_anyClosure_def]
            \\ gvs [REVERSE_SNOC, subst_APPEND, MAP_SNOC]
            \\ gvs [subst_def] \\ rw [eval_to_def]
            \\ rename1 ‘($= +++ v_rel) _ (eval_to _ expr2)’
            \\ Cases_on ‘eval_to (k - 2) expr2 = INL Diverge’ \\ gvs []
            \\ dxrule_then (qspec_then ‘j3 + k - 2’ assume_tac) eval_to_mono
            \\ gvs [])
        \\ qexists_tac ‘j + j1 + j2 + j3’
        \\ qpat_x_assum ‘∀i. eval_to _ g = _’ $ qspec_then ‘j + j2 + j3’ assume_tac
        \\ qpat_x_assum ‘∀i. eval_to _ y = _’ $ qspec_then ‘j1 + j2 + j3’ assume_tac \\ gvs []
        \\ unabbrev_all_tac \\ gvs [REVERSE_SNOC]
        \\ IF_CASES_TAC \\ gvs []
        >- (rpt $ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
        \\ gvs [subst_def, MAP_SNOC, REVERSE_SNOC]
        \\ once_rewrite_tac [eval_to_def] \\ gvs []
        \\ ‘eval_to (j2 + k - 2) (Force (Value w1)) ≠ INL Diverge’ by gvs []
        \\ dxrule_then (qspec_then ‘j + j1 + j2 + j3 + k - 2’ assume_tac) eval_to_mono \\ gvs []
        \\ rw [eval_to_def, subst_def] \\ gvs [dest_anyClosure_def]
        \\ gvs [REVERSE_SNOC, subst_APPEND, MAP_SNOC]
        \\ rw [eval_to_def, subst_def] \\ gvs [dest_anyClosure_def]
        \\ rename1 ‘_ (eval_to _ expr1) (eval_to _ expr2)’
        \\ ‘eval_to (j3 + k - 2) expr2 ≠ INL Diverge’
          by (strip_tac \\ Cases_on ‘eval_to (k - 2) expr1’ \\ gvs [])
        \\ dxrule_then (qspec_then ‘j + j1 + j2 + j3 + k - 2’ assume_tac) eval_to_mono \\ gvs []))
 >~ [‘Seq x1 y1’] >- print_tac "Seq" (
    gvs [Once force_arg_rel_def, eval_to_def]
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
  >~ [‘Let (SOME m) x1 y1’] >- print_tac "Let" (
    gvs [Once force_arg_rel_def, eval_to_def]
    >~[‘Apps (App _ _) (_ ++ Tick (Force _)::_)’]
    >- (IF_CASES_TAC \\ gs []
        >- (
         qexists_tac ‘0’
         \\ gs [])
        \\ gvs [eval_to_Lams, subst1_def]
        \\ drule_then assume_tac force_arg_rel_freevars
        \\ gvs [subst1_notin_frees, subst_Lams, subst_Apps, subst1_def]
        \\ gvs [eval_to_def, eval_to_Lams]
        \\ Q.REFINE_EXISTS_TAC ‘(SUC j)’
        \\ gvs [arithmeticTheory.ADD1]
        \\ last_x_assum $ irule
        \\ irule force_arg_rel_subst
        \\ gvs [MAP_SNOC, subst_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
        \\ rename1 ‘HD (vL1 ++ s::vL2)’
        \\ ‘HD (vL1 ++ s::vL2) = HD (SNOC s vL1)’ by (Cases_on ‘vL1’ >> gvs [])
        \\ rw [] \\ simp [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ irule_at (Pos hd) EQ_REFL
        \\ ‘∀e1 e2 l1 l2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
        \\ first_assum $ irule_at Any
        \\ first_x_assum $ irule_at Any
        \\ gvs []
        \\ ‘∀e1 e2 l1 l2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
        \\ first_x_assum $ irule_at Any
        \\ gvs []
        \\ qexists_tac ‘x2’ \\ first_x_assum $ irule_at $ Pos last
        \\ qexists_tac ‘vL2’ \\ qexists_tac ‘[]’ \\ gvs []
        \\ irule LIST_EQ \\ rw [EL_MAP, EL_APPEND_EQN] \\ gvs [EL_MEM]
        \\ strip_tac \\ gvs [EL_MEM])
    >~[‘Lams _ _’]
    >- (IF_CASES_TAC \\ gs []
        >- (
         qexists_tac ‘0’
         \\ gs [])
        \\ gvs [eval_to_Lams, subst1_def]
        \\ drule_then assume_tac force_arg_rel_freevars
        \\ gvs [subst1_notin_frees, subst_Lams, subst_Apps, subst1_def]
        \\ gvs [eval_to_def, eval_to_Lams]
        \\ Q.REFINE_EXISTS_TAC ‘(SUC j)’
        \\ gvs [arithmeticTheory.ADD1]
        \\ last_x_assum $ irule
        \\ irule force_arg_rel_subst
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
    \\ ‘force_arg_rel (subst1 m v1 y1) (subst1 m w1 y2)’
      by (irule force_arg_rel_subst \\ gs [])
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
  >~ [‘If x1 y1 z1’] >- print_tac "If" (
    gvs [Once force_arg_rel_def, eval_to_def]
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
  >~ [‘Letrec f x’] >- print_tac "Letrec" (
    gvs [Once force_arg_rel_def, eval_to_def]
    >~[‘Apps (App _ _) (_ ++ Tick (Force _)::_)’]
    >- (IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs [])
        \\ last_x_assum irule
        \\ gvs [subst_funs_def, MAP_SNOC]
        \\ rw [Once SNOC_APPEND]
        \\ rename1 ‘force_arg_rel x y’ \\ qspecl_then [‘x’, ‘y’] assume_tac force_arg_rel_freevars
        \\ gvs [subst_APPEND, subst1_notin_frees]
        \\ irule force_arg_rel_subst \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
        \\ irule_at Any $ GSYM LUPDATE_ID
        \\ ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] \\ gvs [EL_MAP]
        \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE] \\ rw []
        >- (gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ gvs [LIST_REL_EL_EQN, EL_MAP]
            \\ rpt $ irule_at Any EQ_REFL \\ gvs []
            \\ irule_at (Pos hd) EQ_REFL \\ gvs [EL_MAP]
            \\ gvs [MEM_EL, EL_MAP]
            \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
        \\ rename1 ‘n < _’ \\ ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs [] \\ gvs [EL_MAP]
        \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ gvs [LIST_REL_EL_EQN, EL_MAP]
        \\ rpt $ irule_at Any EQ_REFL \\ gvs []
        \\ irule_at (Pos hd) EQ_REFL \\ gvs [EL_MAP]
        \\ rw [MEM_EL]
        \\ first_assum $ irule_at Any \\ gvs [EL_MAP])
    >~[‘LUPDATE _ _ _’]
    >- (IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs [])
        \\ last_x_assum irule
        \\ gvs [subst_funs_def, MAP_SNOC]
        \\ rw [Once SNOC_APPEND]
        \\ rename1 ‘force_arg_rel x y’ \\ qspecl_then [‘x’, ‘y’] assume_tac force_arg_rel_freevars
        \\ gvs [subst_APPEND, subst1_notin_frees]
        \\ irule force_arg_rel_subst \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
        \\ irule_at Any $ GSYM LUPDATE_ID
        \\ ‘EL i (MAP FST f) = EL i (MAP FST g)’ by gvs [] \\ gvs [EL_MAP]
        \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE] \\ rw []
        >- (irule v_rel_Recclosure_Lam_Force \\ gvs [LIST_REL_EL_EQN, EL_MAP]
            \\ rw [MEM_EL]
            >- (first_assum $ irule_at Any \\ gvs [EL_MAP])
            \\ irule_at Any EQ_REFL \\ gvs [])
        \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
        \\ rename1 ‘n < _’ \\ ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs [] \\ gvs [EL_MAP]
        \\ irule v_rel_Recclosure_Lam_Force \\ gvs [LIST_REL_EL_EQN, EL_MAP]
        \\ rw [MEM_EL]
        >- (first_assum $ irule_at Any \\ gvs [EL_MAP])
        \\ irule_at Any EQ_REFL \\ gvs [])
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘force_arg_rel x y’
    \\ last_x_assum irule
    \\ gvs [subst_funs_def]
    \\ irule force_arg_rel_subst
    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
    \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
    \\ rename1 ‘n < LENGTH g’
    \\ ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gs [] \\ gvs [EL_MAP]
    \\ irule v_rel_Recclosure
    \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >~ [‘Delay x’] >- print_tac "Delay" (
    gvs [Once force_arg_rel_def, eval_to_def, v_rel_def])
  >~ [‘Force x’] >- print_tac "Force" (
    rgs [Once force_arg_rel_def]
    \\ once_rewrite_tac [eval_to_def] \\ simp []
    \\ pop_assum kall_tac
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (drule_all_then (qx_choose_then ‘j’ assume_tac))
    \\ rename1 ‘force_arg_rel x y’ \\ gvs []
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
        >- (‘OPTREL force_arg_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
            \\ gvs [OPTREL_def]
            \\ qpat_x_assum ‘force_arg_rel x0 _’ mp_tac
            \\ rw [Once force_arg_rel_cases] \\ gs []
            \\ Cases_on ‘x0’ \\ gvs [])
        \\ gvs [alookup_distinct_reverse]
        \\ qmatch_goalsub_abbrev_tac ‘ALOOKUP (REVERSE list) s’
        \\ ‘ALL_DISTINCT (MAP FST list)’
          by (unabbrev_all_tac \\ gvs [LUPDATE_MAP, ALL_DISTINCT_APPEND]
              \\ ‘FST (EL i xs) = EL i (MAP FST xs)’ by gvs [EL_MAP] \\ gvs []
              \\ gvs [LUPDATE_ID])
        \\ gvs [alookup_distinct_reverse]
        \\ gvs [MEM_EL, EL_MAP]
        \\ rename1 ‘ALOOKUP _ (FST (EL n ys))’
        \\ qspecl_then [‘xs’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
        \\ qspecl_then [‘list’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
        \\ gvs [LIST_REL_EL_EQN]
        \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
        \\ ‘LENGTH list = SUC (LENGTH ys)’ by (unabbrev_all_tac \\ gvs [LENGTH_LUPDATE])
        \\ gvs []
        \\ ‘FST (EL n list) = FST (EL n ys)’
          by (unabbrev_all_tac \\ gvs [EL_LUPDATE, EL_APPEND_EQN]
              \\ IF_CASES_TAC \\ gvs [])
        \\ gvs []
        \\ Cases_on ‘i = n’ \\ gvs []
        >- (unabbrev_all_tac \\ gvs [EL_APPEND_EQN, EL_LUPDATE] \\ gvs [Lams_split])
        >- (‘EL n list = EL n ys’ by (unabbrev_all_tac \\ gvs [EL_APPEND_EQN, EL_LUPDATE])
            \\ first_x_assum $ qspec_then ‘n’ assume_tac
            \\ Cases_on ‘SND (EL n xs)’ \\ gvs [force_arg_rel_def])
        >- (unabbrev_all_tac \\ gvs [EL_APPEND_EQN, EL_LUPDATE] \\ gvs [Lams_split])
        >- (‘EL n list = EL n ys’ by (unabbrev_all_tac \\ gvs [EL_APPEND_EQN, EL_LUPDATE])
            \\ first_x_assum $ qspec_then ‘n’ assume_tac
            \\ Cases_on ‘SND (EL n xs)’ \\ gvs [force_arg_rel_def]))
      \\ pairarg_tac \\ gvs []
      \\ Cases_on ‘∃xs n. v1 = Recclosure xs n’ \\ gvs [v_rel_def]
      >- (gvs [dest_anyThunk_def, v_rel_def]
          \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
          \\ ‘OPTREL force_arg_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ qpat_x_assum ‘force_arg_rel x0 _’ mp_tac
          \\ rw [Once force_arg_rel_cases] \\ gvs []
          \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ rename1 ‘subst_funs xs x2’ \\ rename1 ‘force_arg_rel x2 y2’
          \\ last_x_assum $ qspecl_then [‘x2’, ‘xs’, ‘subst_funs ys y2’] mp_tac
          \\ impl_tac
          >- (gvs [subst_funs_def] \\ irule force_arg_rel_subst
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
              \\ dxrule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono \\ gvs []
              \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs [])
          \\ qexists_tac ‘j + j1’
          \\ ‘eval_to (j + k) y ≠ INL Diverge’ by gvs []
          \\ dxrule_then (qspec_then ‘j + j1 + k’ assume_tac) eval_to_mono \\ gvs []
          \\ ‘eval_to (j1 + k - 1) (subst_funs ys y2) ≠ INL Diverge’
            by (strip_tac \\ Cases_on ‘eval_to (k - 1) (subst_funs xs x2)’ \\ gvs [])
          \\ dxrule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono \\ gvs []
          \\ simp [oneline sum_bind_def] \\ rpt (CASE_TAC  \\ gvs [])
          \\ cheat (* TODO v_rel_anyThunk *))

      >- (gvs [dest_anyThunk_def, v_rel_def]
          \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ gvs [MEM_EL, EL_MAP, alookup_distinct_reverse]
          \\ rename1 ‘n2 < _’
          \\ rename1 ‘LUPDATE (v1', Lams (vL1++s3::vL2) (Apps (Var v2) _)) i ys’
          \\ ‘ALL_DISTINCT (MAP FST (LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
                                       (Apps (Var v2)
                                        (MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys))’
            by (gvs [LUPDATE_MAP]
                \\ qspecl_then [‘ys’, ‘i’] assume_tac LUPDATE_ID_MAP_FST \\ gvs []
                \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] >> gvs [EL_MAP, LIST_REL_EL_EQN])
          \\ drule_then assume_tac alookup_distinct_reverse
          \\ qspecl_then [‘LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
                          (Apps (Var v2) (MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys’, ‘n2’]
                         assume_tac ALOOKUP_ALL_DISTINCT_EL
          \\ qspecl_then [‘xs’, ‘n2’] assume_tac ALOOKUP_ALL_DISTINCT_EL
          \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs []
          \\ gvs [EL_MAP, EL_LUPDATE, LIST_REL_EL_EQN]
          \\ Cases_on ‘n2 = i’ >- gvs [Lams_split]
          \\ qpat_assum ‘∀i. _ ⇒ force_arg_rel (SND _) _’ $ qspec_then ‘n2’ assume_tac
          \\ Cases_on ‘SND (EL n2 xs)’ \\ gvs [force_arg_rel_def]
          \\ rename1 ‘force_arg_rel e e'’
          \\ last_x_assum $ qspecl_then [‘e’, ‘binds’, ‘subst_funs (SNOC (v2, Lams (vL1 ++ s2::vL2) y')
                (LUPDATE (v1', Lams (vL1++s3::vL2)
                 (Apps (Var v2) (MAP Var vL1 ++ Tick (Force (Var s3))::MAP Var vL2))) i ys)) e'’] mp_tac
          \\ impl_tac
          >- (gvs [subst_funs_def, SNOC_APPEND, subst_APPEND, MAP_APPEND]
              \\ irule force_arg_rel_subst
              \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
              \\ irule_at Any $ GSYM LUPDATE_ID
              \\ ‘EL i (MAP FST binds) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ qpat_x_assum ‘EVERY (λv. _ ∉ freevars _ ) _ ’ assume_tac
              \\ gvs [EVERY_EL] \\ first_assum $ qspecl_then [‘n2’] assume_tac
              \\ gvs [freevars_def, EL_MAP]
              \\ drule_then assume_tac force_arg_rel_freevars \\ gvs [subst1_notin_frees]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE] \\ rw []
              >- (gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
                  \\ qpat_x_assum ‘EL i binds = (_, Lams _ _)’ $ irule_at Any
                  \\ irule_at (Pos hd) EQ_REFL \\ irule_at (Pos hd) EQ_REFL
                  \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL, EVERY_EL]
                  \\ gvs [SF CONJ_ss, EL_MAP] \\ irule_at Any EQ_REFL \\ gvs [])
              \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
              \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST binds) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
              \\ qpat_x_assum ‘EL i binds = (_, Lams _ _)’ $ irule_at Any
              \\ irule_at (Pos hd) EQ_REFL \\ irule_at (Pos hd) EQ_REFL
              \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL, EVERY_EL]
              \\ qexists_tac ‘n’ \\ gvs [EL_MAP])
          \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
          \\ disch_then $ qx_choose_then ‘j1’ assume_tac
          \\ Cases_on ‘eval_to (k - 1) (subst_funs binds e) = INL Diverge’ \\ gvs []
          >- (qexists_tac ‘0’
              \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
              \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
              \\ gvs [REVERSE_SNOC]
              \\ IF_CASES_TAC \\ gvs []
              >- (rpt $ first_x_assum $ qspec_then ‘n2’ assume_tac \\ gvs [EL_MAP])
              \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
              \\ rename1 ‘($= +++ v_rel) _ (eval_to _ expr)’
              \\ Cases_on ‘eval_to (k - 1) expr = INL Diverge’ \\ gvs []
              \\ dxrule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono \\ gvs []
              \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs [])
          \\ qexists_tac ‘j + j1’
          \\ qspecl_then [‘k + j’, ‘y’, ‘j + j1 + k’] assume_tac eval_to_mono
          \\ gvs [REVERSE_SNOC]
          \\ IF_CASES_TAC \\ gvs []
          >- (rpt $ first_x_assum $ qspec_then ‘n2’ assume_tac \\ gvs [EL_MAP])
          \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
          \\ rename1 ‘($= +++ v_rel) _ (eval_to _ expr)’
          \\ ‘eval_to (j1 + k - 1) expr ≠ INL Diverge’
            by (strip_tac \\ Cases_on ‘eval_to (k - 1) (subst_funs binds e)’ \\ gvs [])
          \\ dxrule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono
          \\ gvs []
          \\ simp [oneline sum_bind_def] \\ rpt (CASE_TAC \\ gvs [])
          \\ cheat (* TODO v_rel_anyThunk *))

      >- (gvs [dest_anyThunk_def, v_rel_def]
          \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ gvs [MEM_EL, EL_MAP, alookup_distinct_reverse]
          \\ rename1 ‘n2 < _’
          \\ rename1 ‘LUPDATE (v1', Lams (vL1++s3::vL2) (Apps (App (Var v2) _) _)) i ys’
          \\ ‘ALL_DISTINCT (MAP FST (LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
                                       (Apps (App (Var v2) (Var s3))
                                        (MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys))’
            by (gvs [LUPDATE_MAP]
                \\ qspecl_then [‘ys’, ‘i’] assume_tac LUPDATE_ID_MAP_FST \\ gvs []
                \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] >> gvs [EL_MAP, LIST_REL_EL_EQN])
          \\ drule_then assume_tac alookup_distinct_reverse
          \\ qspecl_then [‘LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
               (Apps (Var v2) ([Var s3] ++ MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys’, ‘n2’]
                         assume_tac ALOOKUP_ALL_DISTINCT_EL
          \\ qspecl_then [‘xs’, ‘n2’] assume_tac ALOOKUP_ALL_DISTINCT_EL
          \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs []
          \\ gvs [EL_MAP, EL_LUPDATE, LIST_REL_EL_EQN]
          \\ Cases_on ‘n2 = i’ >- gvs [Lams_split]
          \\ qpat_assum ‘∀i. _ ⇒ force_arg_rel (SND _) _’ $ qspec_then ‘n2’ assume_tac
          \\ Cases_on ‘SND (EL n2 xs)’ \\ gvs [force_arg_rel_def]
          \\ rename1 ‘force_arg_rel e e'’
          \\ last_x_assum $ qspecl_then [‘e’, ‘binds’, ‘subst_funs (SNOC (v2, Lams (s3::vL1 ++ s2::vL2) y')
                (LUPDATE (v1', Lams (vL1++s3::vL2)
                 (Apps (Var v2) (Var s3::MAP Var vL1 ++ Tick (Force (Var s3))::MAP Var vL2))) i ys)) e'’] mp_tac
          \\ impl_tac
          >- (gvs [subst_funs_def, SNOC_APPEND, subst_APPEND, MAP_APPEND]
              \\ irule force_arg_rel_subst
              \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
              \\ irule_at Any $ GSYM LUPDATE_ID
              \\ ‘EL i (MAP FST binds) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ qpat_x_assum ‘EVERY (λv. _ ∉ freevars _ ) _ ’ assume_tac
              \\ gvs [EVERY_EL] \\ first_assum $ qspecl_then [‘n2’] assume_tac
              \\ gvs [freevars_def, EL_MAP]
              \\ drule_then assume_tac force_arg_rel_freevars \\ gvs [subst1_notin_frees]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE] \\ rw []
              >- (gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
                  \\ qpat_x_assum ‘EL i binds = (_, Lams _ _)’ $ irule_at Any
                  \\ irule_at (Pos hd) EQ_REFL \\ irule_at (Pos hd) EQ_REFL
                  \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL, EVERY_EL]
                  \\ gvs [SF CONJ_ss, EL_MAP] \\ irule_at Any EQ_REFL \\ gvs [])
              \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
              \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST binds) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
              \\ qpat_x_assum ‘EL i binds = (_, Lams _ _)’ $ irule_at Any
              \\ irule_at (Pos hd) EQ_REFL \\ irule_at (Pos hd) EQ_REFL
              \\ gvs [LIST_REL_EL_EQN, EL_MAP, MEM_EL, EVERY_EL]
              \\ qexists_tac ‘n’ \\ gvs [EL_MAP])
          \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
          \\ disch_then $ qx_choose_then ‘j1’ assume_tac
          \\ Cases_on ‘eval_to (k - 1) (subst_funs binds e) = INL Diverge’ \\ gvs []
          >- (qexists_tac ‘0’
              \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
              \\ dxrule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
              \\ gvs [REVERSE_SNOC]
              \\ IF_CASES_TAC \\ gvs []
              >- (rpt $ first_x_assum $ qspec_then ‘n2’ assume_tac \\ gvs [EL_MAP])
              \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
              \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
              \\ rename1 ‘($= +++ v_rel) _ (eval_to _ expr)’
              \\ Cases_on ‘eval_to (k - 1) expr = INL Diverge’ \\ gvs []
              \\ dxrule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono \\ gvs []
              \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs [])
          \\ qexists_tac ‘j + j1’
          \\ qspecl_then [‘k + j’, ‘y’, ‘j + j1 + k’] assume_tac eval_to_mono
          \\ gvs [REVERSE_SNOC]
          \\ IF_CASES_TAC \\ gvs []
          >- (rpt $ first_x_assum $ qspec_then ‘n2’ assume_tac \\ gvs [EL_MAP])
          \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
          \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
          \\ rename1 ‘($= +++ v_rel) _ (eval_to _ expr)’
          \\ ‘eval_to (j1 + k - 1) expr ≠ INL Diverge’
            by (strip_tac \\ Cases_on ‘eval_to (k - 1) (subst_funs binds e)’ \\ gvs [])
          \\ dxrule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono
          \\ gvs []
          \\ simp [oneline sum_bind_def] \\ rpt (CASE_TAC \\ gvs [])
          \\ cheat (* TODO v_rel_anyThunk *))
      \\ rename1 ‘dest_anyThunk v1 = INR (wx, binds)’
      \\ ‘∃wx' binds'. dest_anyThunk w1 = INR (wx', binds') ∧
                       force_arg_rel wx wx' ∧
                       MAP FST binds = MAP FST binds' ∧
                       EVERY ok_bind (MAP SND binds) ∧
                       EVERY ok_bind (MAP SND binds') ∧
                       LIST_REL force_arg_rel (MAP SND binds) (MAP SND binds')’
        by (Cases_on ‘v1’ \\ Cases_on ‘w1’
            \\ gvs [v_rel_def]
            \\ gvs [dest_anyThunk_def, v_rel_def])
      \\ rename1 ‘force_arg_rel x1 x2’
      \\ ‘force_arg_rel (subst_funs binds x1) (subst_funs binds' x2)’
        by (simp [subst_funs_def]
            \\ irule force_arg_rel_subst
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
        \\ qexists_tac ‘j2’ \\ gs []
        \\ simp [oneline sum_bind_def] \\ CASE_TAC \\ gvs [])
      \\ ‘eval_to (j2 + k - 1) (subst_funs binds' x2) ≠ INL Diverge’
        by (strip_tac
            \\ Cases_on ‘eval_to (k - 1) (subst_funs binds x1)’ \\ gs [])
      \\ drule_then (qspec_then ‘j2 + j1 + j + k - 1’ assume_tac) eval_to_mono
      \\ ‘eval_to (j2 + j1 + j + k) y = eval_to (j + k) y’
        by (irule eval_to_mono \\ gs [])
      \\ qexists_tac ‘j2 + j1 + j’ \\ gs []
      \\ CASE_TAC \\ gs []
      \\ Cases_on ‘v1’ \\ Cases_on ‘w1’
      \\ (
        gvs [dest_anyThunk_def, subst_funs_def]
        \\ simp [oneline sum_bind_def] \\ rpt (CASE_TAC \\ gvs [])
        \\ cheat (* TODO v_rel_anyThunk *)))
    \\ rename1 ‘dest_Tick v1 = SOME v2’
    \\ ‘∃w2. dest_Tick w1 = SOME w2 ∧ v_rel v2 w2’
      by (Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [v_rel_def])
    \\ ‘force_arg_rel (Force (Value v2)) (Force (Value w2))’
      by simp [force_arg_rel_Force, force_arg_rel_Value]
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
    gvs [Once force_arg_rel_def, eval_to_def]
    \\ rename1 ‘force_arg_rel x y’
    \\ first_x_assum $ dxrule_then $ qx_choose_then ‘j’ assume_tac
    \\ qexists_tac ‘j’
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
    \\ simp [v_rel_def])
  >~ [‘Prim op xs’] >- (
    gvs [Once force_arg_rel_def, eval_to_def]
    \\ gvs [MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
    \\ Cases_on ‘op’ \\ gs []
    >- ((* Cons *)
      ‘∃j. ($= +++ LIST_REL v_rel) (result_map (eval_to k) xs)
                                   (result_map (eval_to (j + k)) ys)’
        suffices_by (
          disch_then (qx_choose_then ‘j’ assume_tac)
          \\ qexists_tac ‘j’ \\ gs [SF ETA_ss]
          \\ Cases_on ‘result_map (eval_to k) xs’
          \\ Cases_on ‘result_map (eval_to (j + k)) ys’ \\ gs [v_rel_def]
          \\ rw [v_rel_def]
          \\ (
            gvs [EVERY_EL, LIST_REL_EL_EQN]
            \\ qpat_x_assum ‘EXISTS _ _’ mp_tac \\ rw [EVERY_EL]
            \\ ntac 2 (first_x_assum drule \\ rw [])
            \\ cheat (* TODO v_rel_anyThunk *)))
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
      \\ rename1 ‘force_arg_rel x y’
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
      \\ rename1 ‘force_arg_rel x y’
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

Theorem force_arg_rel_eval:
  force_arg_rel x y ⇒
    ($= +++ v_rel) (eval x) (eval y)
Proof
  strip_tac
  \\ simp [eval_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  >- (
    rename1 ‘_ (eval_to k x) (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘MAX k j’ (qx_choose_then ‘m’ assume_tac)) force_arg_rel_eval_to
    \\ ‘eval_to ( MAX k j) x = eval_to k x’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ ‘eval_to (m + MAX k j) y = eval_to j y’
      by (irule eval_to_mono \\ gs [arithmeticTheory.MAX_DEF])
    \\ gs [])
  >- (
    rename1 ‘_ _ (eval_to j y)’
    \\ drule_all_then
      (qspec_then ‘j’ (qx_choose_then ‘m’ assume_tac)) force_arg_rel_eval_to \\ gs []
    \\ drule_then (qspec_then ‘m + j’ assume_tac) eval_to_mono \\ gs [])
  \\ rename1 ‘_ _ (eval_to k x)’
  \\ drule_all_then
    (qspec_then ‘k’ (qx_choose_then ‘m’ assume_tac)) force_arg_rel_eval_to
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

Theorem v_rel_eval_subst:
 v_rel (Closure s e) (Closure s f) ∧ v_rel v w ⇒ ($= +++ v_rel) (eval (subst1 s v e)) (eval (subst1 s w f))
Proof
  gvs [GSYM eval_App_Values]
  \\ rw [] \\ irule force_arg_rel_eval
  \\ gvs [force_arg_rel_def]
QED

Theorem force_arg_rel_apply_closure[local]:
  force_arg_rel x y ∧
  v_rel v2 w2 ∧
  (∀x y. ($= +++ v_rel) x y ⇒ next_rel v_rel force_arg_rel (f x) (g y)) ⇒
    next_rel v_rel force_arg_rel (apply_closure x v2 f) (apply_closure y w2 g)
Proof
  rw [thunk_semanticsTheory.apply_closure_def] >>
  simp[thunk_semanticsTheory.with_value_def] >>
  dxrule_all_then assume_tac force_arg_rel_eval >>
  Cases_on `eval x` >> Cases_on `eval y` >> gvs[] >- (CASE_TAC >> gvs[]) >>
  rename1 `eval x = INR v1` >> rename1 `eval y = INR w1`
  \\ Cases_on ‘v1’ \\ Cases_on ‘w1’ \\ gvs [v_rel_def, dest_anyClosure_def]
  >- (
    first_x_assum irule
    \\ irule force_arg_rel_eval
    \\ irule force_arg_rel_subst \\ gs [])
  >- (first_x_assum irule
      \\ irule v_rel_eval_subst
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs [])
  >- (first_x_assum irule
      \\ irule v_rel_eval_subst
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj1_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs []
      \\ metis_tac [])
  >- (first_x_assum irule
      \\ irule v_rel_eval_subst
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs []
      \\ first_x_assum $ irule_at $ Pos $ el 2 \\ gs [])
  >- (first_x_assum irule
      \\ irule v_rel_eval_subst
      \\ gvs [v_rel_def]
      \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs [])
  >- (first_x_assum irule
      \\ irule v_rel_eval_subst
      \\ gvs [v_rel_def]
      \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs []
      \\ first_x_assum $ irule_at $ Pos $ el 2 \\ gs [])
  >- (first_x_assum irule
      \\ irule v_rel_eval_subst
      \\ gvs [v_rel_def]
      \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs [])
  >- (first_x_assum irule
      \\ irule v_rel_eval_subst
      \\ gvs [v_rel_def]
      \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs [])
  >- (first_x_assum irule
      \\ irule v_rel_eval_subst
      \\ gvs [v_rel_def]
      \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs [])
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL force_arg_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
      \\ gs [OPTREL_def]
      \\ qpat_x_assum ‘force_arg_rel x0 _’ mp_tac
      \\ rw [Once force_arg_rel_cases] \\ gs []
      \\ drule_then assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
      \\ gvs [EVERY_EL, EL_MAP]
      \\ first_x_assum irule
      \\ irule force_arg_rel_eval
      \\ irule force_arg_rel_subst
      \\ simp [EVERY2_MAP, LAMBDA_PROD, v_rel_def, MAP_MAP_o, combinTheory.o_DEF,
               GSYM FST_THM]
      \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EVERY_EL, EL_MAP, LIST_EQ_REWRITE])
  >- (gvs [MEM_EL, EL_MAP, alookup_distinct_reverse]
      \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ rename1 ‘LUPDATE (v1', Lams (vL1++ [s3] ++ vL2) (Apps (Var v2') _)) i ys’
      \\ ‘ALL_DISTINCT (MAP FST (LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
                (Apps (Var v2')
                 (MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys))’
        by (gvs [LUPDATE_MAP]
            \\ qspecl_then [‘ys’, ‘i’] assume_tac LUPDATE_ID_MAP_FST \\ gvs []
            \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] >> gvs [EL_MAP, LIST_REL_EL_EQN])
      \\ drule_then assume_tac alookup_distinct_reverse
      \\ rename1 ‘EL n _’
      \\ qspecl_then [‘LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
           (Apps (Var v2') (MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys’, ‘n’]
                     assume_tac ALOOKUP_ALL_DISTINCT_EL
      \\ qspecl_then [‘xs’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
      \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
      \\ gvs [EL_MAP, EL_LUPDATE, LIST_REL_EL_EQN, REVERSE_APPEND]
      \\ IF_CASES_TAC \\ gvs []
      >- (rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_MAP])
      \\ Cases_on ‘n = i’ \\ gvs []
      >- (rw [Lams_split]
          \\ first_x_assum irule
          \\ gvs [subst_APPEND]
          \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval (subst l1 (subst1 var1 val1 expr1)))
                                    (eval (subst l2 (subst1 var2 val3 (subst1 _ val2 expr2))))’
          \\ ‘var1 ≠ var2’
            by (strip_tac \\ unabbrev_all_tac \\ dxrule_then assume_tac EQ_SYM \\ gvs []
                \\ Cases_on ‘vL1’ \\ gvs []
                \\ rpt $ first_x_assum $ qspec_then ‘0’ assume_tac \\ gvs [])
          \\ qspecl_then [‘l1’, ‘subst1 var1 val1 expr1’, ‘{var1}’] assume_tac $ GSYM subst_remove
          \\ qspecl_then [‘l2’, ‘subst1 v2' val3 (subst1 var1 val2 expr2)’, ‘{var1}’]
                         assume_tac $ GSYM subst_remove
          \\ qspecl_then [‘expr2’, ‘val3’, ‘var2’, ‘var1’, ‘val2’] assume_tac subst1_commutes
          \\ qspecl_then [‘expr1’, ‘FILTER (λ(n,x). n ≠ var1) l1’, ‘[(var1, val1)]’]
                         assume_tac subst_commutes
          \\ qspecl_then [‘subst1 var2 val3 expr2’, ‘FILTER (λ(n,x). n ≠ var1) l2’,
                          ‘[(var1, val2)]’] assume_tac subst_commutes
          \\ qspecl_then [‘val2’, ‘val1’, ‘var1’,
                          ‘subst (FILTER (λ(n,x). n ≠ var1) l2) (subst1 var2 val3 expr2)’,
                          ‘subst (FILTER (λ(n,x). n ≠ var1) l1) expr1’]
                         mp_tac $ GEN_ALL v_rel_eval_subst
          \\ ‘vL1 ++ s3::vL2 = vL1 ++ [s3] ++ vL2’ by (once_rewrite_tac [CONS_APPEND] \\ gvs [])
          \\ gvs []
          \\ gvs [freevars_subst, MAP_FST_FILTER, MEM_FILTER]
          \\ impl_tac
          >- (pop_assum kall_tac \\ pop_assum kall_tac \\ pop_assum kall_tac
              \\ pop_assum kall_tac \\ pop_assum kall_tac
              \\ unabbrev_all_tac \\ gvs [v_rel_def]
              \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
              \\ ‘HD (vL1 ++ [s3] ++ vL2) = HD (vL1 ++ [s3])’ by (Cases_on ‘vL1’ \\ gvs [])
              \\ gvs []
              \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
              \\ irule_at (Pos hd) EQ_REFL
              \\ gvs [subst_Lams]
              \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ first_assum $ irule_at $ Pos hd
              \\ first_x_assum $ irule_at Any
              \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
              \\ qexists_tac ‘ys’ \\ qexists_tac ‘y'’ \\ qexists_tac ‘xs’
              \\ qexists_tac ‘x'’ \\ qexists_tac ‘vL2’
              \\ gvs []
              \\ qexists_tac ‘[]’ \\ gvs []
              \\ qexists_tac ‘v2'’ \\ gvs []
              \\ qexists_tac ‘FST (EL i ys)’ \\ gvs []
              \\ qexists_tac ‘s2’ \\ qexists_tac ‘i’
              \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
              >- (gvs [subst_Apps, subst_def, MAP_APPEND, MAP_MAP_o,
                       combinTheory.o_DEF, SNOC_APPEND]
                  \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                  \\ pop_assum irule \\ rw []
                  >- gvs [Lams_split]
                  >- gvs [Lams_split]
                  \\ irule LIST_EQ \\ gvs [EL_MAP, EL_APPEND_EQN]
                  \\ rw []
                  >- (rename1 ‘id < LENGTH _ + 1’ \\ Cases_on ‘id’
                      \\ Cases_on ‘vL1’ \\ gvs [EL_MEM])
                  >- (gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                      \\ rename1 ‘id < LENGTH _’ \\ Cases_on ‘id’ \\ Cases_on ‘vL1’
                      \\ gvs [EL_MEM])
                  >- (AP_TERM_TAC \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                      \\ Cases_on ‘vL1’ \\ gvs [])
                  >- (Cases_on ‘vL1’ \\ gvs [EL_MEM])
                  >- (Cases_on ‘vL1’ \\ gvs [EL_MEM])
                  >- gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                  >- (gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                      \\ Cases_on ‘vL1’ \\ gvs [EL_MEM] \\ rw []))
              >- (Cases_on ‘vL1’ \\ gvs [] \\ gvs [MEM_EL]
                  \\ rename1 ‘n < _’ \\ rpt $ first_x_assum $ qspec_then ‘SUC n’ assume_tac
                  \\ gvs [])
              >- (AP_THM_TAC \\ AP_TERM_TAC
                  \\ gvs [FILTER_FILTER, LAMBDA_PROD]
                  \\ AP_THM_TAC \\ AP_TERM_TAC \\ Cases_on ‘vL1’ \\ gvs []
                  >- metis_tac [CONJ_COMM]
                  \\ gvs [GSYM CONJ_ASSOC] \\ metis_tac [CONJ_COMM])
              >- gvs [MEM_EL]
              >- gvs [MEM_EL]
              >- gvs [MEM_EL]
              >- gvs [MEM_EL]
              >- gvs [MEM_EL]
              >- (qpat_x_assum ‘EVERY (λe. _ ∉ freevars _) _’ assume_tac
                  \\ gvs [EVERY_EL] \\ pop_assum $ qspec_then ‘i’ assume_tac
                  \\ gvs [EL_MAP, freevars_Lams, freevars_def]
                  \\ gvs [MEM_EL]))
          \\ rw []
          \\ ‘subst (FILTER (λ(n,x). n ≠ var1) l2) (subst1 v2' val3 (subst1 var1 val2 expr2)) =
              subst1 var1 val2 (subst (FILTER (λ(n,x). n ≠ var1) l2) (subst1 v2' val3 expr2))’
            suffices_by rw []
          \\ irule EQ_TRANS \\ first_x_assum $ irule_at $ Pos last
          \\ AP_TERM_TAC
          \\ gvs []
          )
      \\ qpat_assum ‘∀i. _ ⇒ force_arg_rel _ _’ $ qspec_then ‘n’ assume_tac
      \\ Cases_on ‘SND (EL n xs)’ \\ gvs [force_arg_rel_def]
      \\ first_x_assum irule
      \\ gvs [subst_APPEND]
      \\ irule force_arg_rel_eval
      \\ irule force_arg_rel_subst
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
      \\ irule_at Any $ GSYM LUPDATE_ID
      \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
      \\ conj_tac
      >- (qpat_x_assum ‘EVERY (λe. _ ∉ freevars _) (MAP SND _)’ assume_tac
          \\ gvs [EVERY_EL] \\ first_x_assum $ drule_then assume_tac
          \\ drule_then assume_tac force_arg_rel_freevars
          \\ gvs [EL_MAP, freevars_def, subst1_notin_frees, freevars_subst]
          \\ gvs [force_arg_rel_subst])
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE] \\ rw []
      >- (gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
          \\ rpt $ irule_at (Pos hd) EQ_REFL
          \\ gvs []
          \\ irule_at (Pos hd) EQ_REFL
          \\ gvs [MEM_EL, LIST_REL_EL_EQN, EL_MAP]
          \\ gvs [SF CONJ_ss, EL_MAP]
          \\ irule_at (Pos last) EQ_REFL \\ gvs [])
      \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
      \\ rename1 ‘n2 < _’
      \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj1_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs [MEM_EL, LIST_REL_EL_EQN, EL_MAP]
      \\ irule_at (Pos hd) EQ_REFL \\ gvs []
      \\ qexists_tac ‘n2’ \\ gvs [EL_MAP])
  >- (gvs [MEM_EL, EL_MAP, alookup_distinct_reverse]
      \\ rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ rename1 ‘LUPDATE (v1', Lams (vL1++ [s3] ++ vL2) (Apps (App (Var v2') _) _)) i ys’
      \\ ‘ALL_DISTINCT (MAP FST (LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
                (Apps (Var v2')
                 ([Var s3] ++ MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys))’
        by (gvs [LUPDATE_MAP]
            \\ qspecl_then [‘ys’, ‘i’] assume_tac LUPDATE_ID_MAP_FST \\ gvs []
            \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] >> gvs [EL_MAP, LIST_REL_EL_EQN])
      \\ drule_then assume_tac alookup_distinct_reverse
      \\ rename1 ‘EL n _’
      \\ qspecl_then [‘LUPDATE (v1', Lams (vL1 ++ [s3] ++ vL2)
           (Apps (Var v2') ([Var s3] ++ MAP Var vL1 ++ [Tick (Force (Var s3))] ++ MAP Var vL2))) i ys’, ‘n’]
                     assume_tac ALOOKUP_ALL_DISTINCT_EL
      \\ qspecl_then [‘xs’, ‘n’] assume_tac ALOOKUP_ALL_DISTINCT_EL
      \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs []
      \\ gvs [EL_MAP, EL_LUPDATE, LIST_REL_EL_EQN, REVERSE_APPEND]
      \\ IF_CASES_TAC \\ gvs []
      >- (rpt $ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_MAP])
      \\ Cases_on ‘n = i’ \\ gvs []
      >- (once_rewrite_tac [CONS_APPEND] \\ gvs []
          \\ rw [Lams_split]
          \\ first_x_assum irule
          \\ gvs [subst_APPEND]
          \\ qmatch_goalsub_abbrev_tac ‘($= +++ v_rel) (eval (subst l1 (subst1 var1 val1 expr1)))
                                    (eval (subst l2 (subst1 var2 val3 (subst1 _ val2 expr2))))’
          \\ ‘var1 ≠ var2’
            by (strip_tac \\ unabbrev_all_tac \\ dxrule_then assume_tac EQ_SYM \\ gvs []
                \\ Cases_on ‘vL1’ \\ gvs []
                \\ rpt $ first_x_assum $ qspec_then ‘0’ assume_tac \\ gvs [])
          \\ qspecl_then [‘l1’, ‘subst1 var1 val1 expr1’, ‘{var1}’] assume_tac $ GSYM subst_remove
          \\ qspecl_then [‘l2’, ‘subst1 v2' val3 (subst1 var1 val2 expr2)’, ‘{var1}’]
                         assume_tac $ GSYM subst_remove
          \\ qspecl_then [‘expr2’, ‘val3’, ‘var2’, ‘var1’, ‘val2’] assume_tac subst1_commutes
          \\ qspecl_then [‘expr1’, ‘FILTER (λ(n,x). n ≠ var1) l1’, ‘[(var1, val1)]’]
                         assume_tac subst_commutes
          \\ qspecl_then [‘subst1 var2 val3 expr2’, ‘FILTER (λ(n,x). n ≠ var1) l2’,
                          ‘[(var1, val2)]’] assume_tac subst_commutes
          \\ qspecl_then [‘val2’, ‘val1’, ‘var1’,
                          ‘subst (FILTER (λ(n,x). n ≠ var1) l2) (subst1 var2 val3 expr2)’,
                          ‘subst (FILTER (λ(n,x). n ≠ var1) l1) expr1’]
                         mp_tac $ GEN_ALL v_rel_eval_subst
          \\ ‘vL1 ++ s3::vL2 = vL1 ++ [s3] ++ vL2’ by (once_rewrite_tac [CONS_APPEND] \\ gvs [])
          \\ gvs []
          \\ gvs [freevars_subst, MAP_FST_FILTER, MEM_FILTER]
          \\ impl_tac
          >- (pop_assum kall_tac \\ pop_assum kall_tac \\ pop_assum kall_tac
              \\ pop_assum kall_tac \\ pop_assum kall_tac
              \\ unabbrev_all_tac \\ gvs [v_rel_def]
              \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
              \\ ‘HD (vL1 ++ [s3] ++ vL2) = HD (vL1 ++ [s3])’ by (Cases_on ‘vL1’ \\ gvs [])
              \\ gvs []
              \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
              \\ irule_at (Pos hd) EQ_REFL
              \\ gvs [subst_Lams]
              \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Lams l1 e1 = Lams l2 e2’ by gvs []
              \\ first_assum $ irule_at $ Pos hd
              \\ first_x_assum $ irule_at Any
              \\ once_rewrite_tac [CONS_APPEND] \\ gvs []
              \\ qexists_tac ‘ys’ \\ qexists_tac ‘y'’ \\ qexists_tac ‘xs’
              \\ first_x_assum $ irule_at $ Pos last
              \\ irule_at (Pos $ el 2) EQ_REFL \\ gvs []
              \\ qexists_tac ‘[]’ \\ gvs []
              \\ qpat_assum ‘EL _ _ = (_, _)’ $ irule_at Any \\ gvs []
              \\ qexists_tac ‘v2'’ \\ gvs []
              \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
              >- (gvs [subst_Apps, subst_def, MAP_APPEND, MAP_MAP_o,
                       combinTheory.o_DEF, SNOC_APPEND]
                  \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                  \\ pop_assum irule \\ gvs []
                  \\ conj_tac
                  >- (gvs [Lams_split, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                      \\ Cases_on ‘vL1’ \\ gvs [])
                  \\ rpt (‘∀l1 l2 l3 (l4: exp list). l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                          \\ pop_assum $ irule_at Any)
                  \\ gvs [] \\ conj_tac
                  >- (irule LIST_EQ \\ rw [EL_MAP, subst_def]
                      \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                      \\ rename1 ‘x2 < _’
                      \\ Cases_on ‘x2’ \\ Cases_on ‘vL1’ \\ gvs [EL_MEM])
                  \\ conj_tac
                  >- (Cases_on ‘vL1’ \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER])
                  >- (irule LIST_EQ \\ rw [EL_MAP, subst_def]
                      \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                      \\ Cases_on ‘vL1’ \\ gvs [EL_MEM]))
              >- (gvs [subst_Apps, subst_def, MAP_APPEND, MAP_MAP_o,
                       combinTheory.o_DEF, SNOC_APPEND]
                  \\ ‘∀l1 l2 e1 e2. l1 = l2 ∧ e1 = e2 ⇒ Apps e1 l1 = Apps e2 l2’ by gvs []
                  \\ pop_assum irule \\ gvs []
                  \\ conj_tac
                  >- (gvs [Lams_split, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                      \\ Cases_on ‘vL1’ \\ gvs [] \\ gvs [MEM_EL]
                      \\ rename1 ‘n < _’
                      \\ rpt $ first_x_assum $ qspec_then ‘SUC n’ assume_tac \\ gvs [])
                  \\ rpt (‘∀l1 l2 l3 (l4: exp list). l1 = l2 ∧ l3 = l4 ⇒ l1 ++ l3 = l2 ++ l4’ by gvs []
                          \\ pop_assum $ irule_at Any)
                  \\ gvs [] \\ conj_tac
                  >- (irule LIST_EQ \\ rw [EL_MAP, subst_def]
                      \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                      \\ rename1 ‘x2 < _’
                      \\ Cases_on ‘x2’ \\ Cases_on ‘vL1’ \\ gvs [EL_MEM])
                  \\ conj_tac
                  >- (Cases_on ‘vL1’ \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER])
                  >- (irule LIST_EQ \\ rw [EL_MAP, subst_def]
                      \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
                      \\ Cases_on ‘vL1’ \\ gvs [EL_MEM]))
              >- (Cases_on ‘vL1’ \\ gvs [FILTER_FILTER, LAMBDA_PROD, GSYM CONJ_ASSOC]
                  \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
                  \\ gvs [] \\ metis_tac [CONJ_ASSOC])
              >- gvs [MEM_EL]
              >- gvs [MEM_EL]
              >- gvs [MEM_EL]
              >- gvs [MEM_EL]
              >- gvs [MEM_EL]
              >- (qpat_x_assum ‘EVERY (λe. _ ∉ freevars _) _’ assume_tac
                  \\ gvs [EVERY_EL] \\ pop_assum $ qspec_then ‘i’ assume_tac
                  \\ gvs [EL_MAP, freevars_Lams, freevars_def]
                  \\ gvs [MEM_EL]))
          \\ rw []
          \\ ‘subst (FILTER (λ(n,x). n ≠ var1) l2) (subst1 v2' val3 (subst1 var1 val2 expr2)) =
              subst1 var1 val2 (subst (FILTER (λ(n,x). n ≠ var1) l2) (subst1 v2' val3 expr2))’
            suffices_by rw []
          \\ irule EQ_TRANS \\ first_x_assum $ irule_at $ Pos last
          \\ AP_TERM_TAC
          \\ gvs [subst1_commutes]
          )
      \\ qpat_assum ‘∀i. _ ⇒ force_arg_rel _ _’ $ qspec_then ‘n’ assume_tac
      \\ Cases_on ‘SND (EL n xs)’ \\ gvs [force_arg_rel_def]
      \\ first_x_assum irule
      \\ gvs [subst_APPEND]
      \\ irule force_arg_rel_eval
      \\ irule force_arg_rel_subst
      \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LUPDATE_MAP]
      \\ irule_at Any $ GSYM LUPDATE_ID
      \\ ‘EL i (MAP FST xs) = EL i (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
      \\ conj_tac
      >- (qpat_x_assum ‘EVERY (λe. _ ∉ freevars _) (MAP SND _)’ assume_tac
          \\ gvs [EVERY_EL] \\ first_x_assum $ drule_then assume_tac
          \\ drule_then assume_tac force_arg_rel_freevars
          \\ gvs [EL_MAP, freevars_def, subst1_notin_frees, freevars_subst]
          \\ gvs [force_arg_rel_subst])
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, EL_LUPDATE] \\ rw []
      >- (gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
          \\ rpt $ irule_at (Pos hd) EQ_REFL
          \\ gvs []
          \\ irule_at (Pos hd) EQ_REFL
          \\ gvs [MEM_EL, LIST_REL_EL_EQN, EL_MAP]
          \\ gvs [SF CONJ_ss, EL_MAP]
          \\ irule_at (Pos last) EQ_REFL \\ gvs [])
      \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
      \\ rename1 ‘n2 < _’
      \\ ‘EL n2 (MAP FST xs) = EL n2 (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
      \\ gvs [v_rel_def] \\ disj2_tac \\ disj2_tac
      \\ rpt $ irule_at (Pos hd) EQ_REFL
      \\ gvs [MEM_EL, LIST_REL_EL_EQN, EL_MAP]
      \\ irule_at (Pos hd) EQ_REFL \\ gvs []
      \\ qexists_tac ‘n2’ \\ gvs [EL_MAP])
QED

Theorem force_arg_rel_rel_ok[local]:
  rel_ok T v_rel force_arg_rel
Proof
  rw [rel_ok_def, v_rel_def, force_arg_rel_def]
  \\ rw [force_arg_rel_apply_closure]
QED

Theorem force_arg_rel_sim_ok[local]:
  sim_ok T v_rel force_arg_rel
Proof
  rw [sim_ok_def, force_arg_rel_eval, force_arg_rel_subst]
QED

Theorem force_arg_rel_semantics:
  force_arg_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  strip_tac
  \\ irule sim_ok_semantics \\ gs []
  \\ first_assum (irule_at Any)
  \\ qexists_tac ‘T’ \\ gs []
  \\ irule_at Any force_arg_rel_rel_ok
  \\ irule_at Any force_arg_rel_sim_ok
QED

val _ = export_theory ();
