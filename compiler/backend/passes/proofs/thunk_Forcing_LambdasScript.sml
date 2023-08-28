(*
 Relation to rewrite function definitions to remove Delay
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory
     thunk_Let_Lam_ForcedTheory thunk_combine_Forcing_LambdasTheory
     thunk_remove_unuseful_bindingsTheory;

val _ = new_theory "thunk_Forcing_Lambdas";

val _ = set_grammar_ancestry ["thunk_Let_Lam_Forced", "thunk_combine_Forcing_Lambdas",
                              "thunk_remove_unuseful_bindings"];

Inductive forcing_lam_rel:
[~Var:]
  (∀n. forcing_lam_rel s (Var n) (Var n)) ∧
[~Prim:]
  (∀s op xs ys.
     LIST_REL (forcing_lam_rel s) xs ys ⇒
       forcing_lam_rel s (Prim op xs) (Prim op ys)) ∧
[~Monad:]
  (∀s mop xs ys.
     LIST_REL (forcing_lam_rel s) xs ys ⇒
       forcing_lam_rel s (Monad mop xs) (Monad mop ys)) ∧
[~App:]
  (∀s f g x y.
     forcing_lam_rel s f g ∧
     forcing_lam_rel s x y ⇒
       forcing_lam_rel s (App f x) (App g y)) ∧
[~Lam:]
  (∀s v x y.
     forcing_lam_rel s x y ⇒
       forcing_lam_rel s (Lam v x) (Lam v y)) ∧
[~Letrec:]
  (∀s f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL (forcing_lam_rel s) (MAP SND f) (MAP SND g) ∧
     forcing_lam_rel s x y ⇒
     forcing_lam_rel s (Letrec f x) (Letrec g y)) ∧
[~Let:]
  (∀s opt x1 y1 x2 y2.
     forcing_lam_rel s x1 x2 ∧
     forcing_lam_rel s y1 y2 ⇒
     forcing_lam_rel s (Let opt x1 y1) (Let opt x2 y2)) ∧
[~Let_Lams_Force_Var:]
  (∀set v1 v2 vL1 vL2 s s2 x1 x2 y1 y2.
     v2 ∉ boundvars x1 ∧ v2 ∉ boundvars y1 ∧
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧ v2 ∉ set ∧
     ALL_DISTINCT (vL1 ++ s::vL2) ∧
     ¬MEM v2 (vL1 ++ s::vL2) ∧ ¬MEM s2 (vL1 ++ s::vL2) ∧
     v2 ≠ v1 ∧ v2 ≠ s2 ∧ s ≠ s2 ∧
     s ∉ freevars x1 ∧
     forcing_lam_rel (set ∪ {v2}) x1 x2 ∧ forcing_lam_rel (set ∪ {v2}) y1 y2 ⇒
     forcing_lam_rel set (Let (SOME v1)
              (Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) x1))
              y1)
             (Let (SOME v2)
              (Lams (vL1 ++ s2::vL2) x2)
              (Let (SOME v1)
                  (Lams (vL1 ++ s::vL2) (Apps (Var v2) (MAP Var vL1 ++ Force (Var s)::MAP Var vL2))) y2))) ∧
[~Let_Lams_Force_Var2:]
  (∀set v1 v2 vL1 vL2 s s2 x1 x2 y1 y2.
     v2 ∉ boundvars x1 ∧ v2 ∉ boundvars y1 ∧
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧ v2 ∉ set ∧
     ALL_DISTINCT (vL1 ++ s::vL2) ∧
     ¬MEM v2 (vL1 ++ s::vL2) ∧ ¬MEM s2 (vL1 ++ s::vL2) ∧
     v2 ≠ v1 ∧ v2 ≠ s2 ∧ s ≠ s2 ∧
     forcing_lam_rel (set ∪ {v2}) x1 x2 ∧ forcing_lam_rel (set ∪ {v2}) y1 y2 ⇒
     forcing_lam_rel set (Let (SOME v1)
              (Lams (vL1 ++ s::vL2) (Let (SOME s2) (Force (Var s)) x1))
              y1)
             (Let (SOME v2)
              (Lams (s::vL1 ++ s2::vL2) x2)
              (Let (SOME v1)
               (Lams (vL1 ++ s::vL2) (Apps (Var v2) (Var s::MAP Var vL1 ++ Force (Var s)::MAP Var vL2)))
                 y2))) ∧
[~Let_Lams_combine1:]
  (∀set v1 v2 v3 vL1 vL2 vL5 bL bL2 vL3 vL4 s s2 x1 x2 y1 y2.
     LENGTH vL2 = LENGTH bL ∧
     v3 ∉ set ∧
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧
     v3 ∉ freevars y1 ∧ v3 ∉ boundvars y2 ∧
     v3 ∉ boundvars x1 ∧ v3 ∉ boundvars y1 ∧
     ALL_DISTINCT (s2::v1::v2::v3::vL1 ++ s::vL2) ∧
     ALL_DISTINCT (s2::v1::v2::v3::vL1 ++ s::vL5) ∧
     ALL_DISTINCT (MAP SND (FILTER FST (ZIP (bL2, vL2))) ++ vL5) ∧
     ALL_DISTINCT (MAP SND (FILTER FST (ZIP (bL2, vL5))) ++ vL2) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL2 bL ∧
     LENGTH vL5 = LENGTH vL2 ∧
     (∀i. i < LENGTH vL2 ⇒ (EL i vL2 = EL i vL5 ⇔ ¬EL i bL)) ∧
     vL4 = MAP SND (FILTER FST (ZIP (bL2, vL5))) ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL2, vL2))) ∧
     v2 ≠ v1 ∧ v2 ≠ s2 ∧ s ≠ s2 ∧
     s ∉ freevars x1 ∧
     forcing_lam_rel (set ∪ {v3}) x1 x2 ∧ forcing_lam_rel (set ∪ {v3}) y1 y2 ⇒
     forcing_lam_rel set (Let (SOME v2)
              (Lams (vL3 ++ vL1 ++ s::vL5) (Let (SOME s2) (Force (Var s)) x1))
              (Let (SOME v1) (Lams (vL1 ++ s::vL2) (Apps (Var v2)
                                        (MAP Var (vL3 ++ vL1 ++ [s]) ++ MAP2 (λb e. if b then Force e else e)
                                                             bL (MAP Var vL2))))
               y1))
             (Let (SOME v3)
              (Lams (vL3 ++ vL1 ++ s2::vL5) x2)
              (Let (SOME v1)
               (Lams (vL1 ++ s::vL2) (Apps (Var v3) (MAP Var (vL3 ++ vL1) ++ Force (Var s)
                                                                         ::MAP2 (λb e. if b then Force e else e)
                                                                         bL (MAP Var vL2)))) y2))) ∧
[~Let_Lams_combine2:]
  (∀set v1 v2 v3 vL1 vL2 vL5 bL bL2 vL3 vL4 s s2 x1 x2 y1 y2.
     LENGTH vL2 = LENGTH bL ∧
     v3 ∉ set ∧
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧
     v3 ∉ freevars y1 ∧ v3 ∉ boundvars y2 ∧
     v3 ∉ boundvars x1 ∧ v3 ∉ boundvars y1 ∧
     ALL_DISTINCT (s2::v1::v2::v3::vL1 ++ s::vL2) ∧
     ALL_DISTINCT (s2::v1::v2::v3::vL1 ++ s::vL5) ∧
     ALL_DISTINCT (MAP SND (FILTER FST (ZIP (bL2, vL2))) ++ vL5) ∧
     ALL_DISTINCT (MAP SND (FILTER FST (ZIP (bL2, vL5))) ++ vL2) ∧
     LIST_REL (λb3 b2. b3 ⇒ b2) bL2 bL ∧
     LENGTH vL5 = LENGTH vL2 ∧
     (∀i. i < LENGTH vL2 ⇒ (EL i vL2 = EL i vL5 ⇔ ¬EL i bL)) ∧
     vL4 = MAP SND (FILTER FST (ZIP (bL2, vL5))) ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL2, vL2))) ∧
     v2 ≠ v1 ∧ v2 ≠ s2 ∧ s ≠ s2 ∧
     forcing_lam_rel (set ∪ {v3}) x1 x2 ∧ forcing_lam_rel (set ∪ {v3}) y1 y2 ⇒
     forcing_lam_rel set (Let (SOME v2)
              (Lams (vL3 ++ vL1 ++ s::vL5) (Let (SOME s2) (Force (Var s)) x1))
              (Let (SOME v1) (Lams (vL1 ++ s::vL2) (Apps (Var v2)
                                        (MAP Var (vL3 ++ vL1 ++ [s]) ++ MAP2 (λb e. if b then Force e else e)
                                                             bL (MAP Var vL2))))
               y1))
             (Let (SOME v3)
              (Lams (s::vL3 ++ vL1 ++ s2::vL5) x2)
              (Let (SOME v1)
               (Lams (vL1 ++ s::vL2) (Apps (Var v3) (MAP Var (s::vL3 ++ vL1) ++ Force (Var s)
                                                                         ::MAP2 (λb e. if b then Force e else e)
                                                                         bL (MAP Var vL2)))) y2))) ∧
[~If:]
  (∀set x1 y1 z1 x2 y2 z2.
     forcing_lam_rel set x1 x2 ∧
     forcing_lam_rel set y1 y2 ∧
     forcing_lam_rel set z1 z2 ⇒
       forcing_lam_rel set (If x1 y1 z1) (If x2 y2 z2)) ∧
[~Delay:]
  (∀set x y.
     forcing_lam_rel set x y ⇒
       forcing_lam_rel set (Delay x) (Delay y)) ∧
[~Box:]
  (∀set x y.
     forcing_lam_rel set x y ⇒
       forcing_lam_rel set (Box x) (Box y)) ∧
[~Force:]
  (∀set x y.
     forcing_lam_rel set x y ⇒
     forcing_lam_rel set (Force x) (Force y)) ∧
[~MkTick:]
  (∀set x y. forcing_lam_rel set x y ⇒ forcing_lam_rel set (MkTick x) (MkTick y))
End

Theorem forcing_lam_rel_def =
  [“forcing_lam_rel s (Var v) x”,
   “forcing_lam_rel s (Prim op xs) x”,
   “forcing_lam_rel s (Monad mop xs) x”,
   “forcing_lam_rel s (App f x) y”,
   “forcing_lam_rel s (Lam v x) y”,
   “forcing_lam_rel s (Letrec f x) y”,
   “forcing_lam_rel s (Let opt x y) z”,
   “forcing_lam_rel s (If x y z) w”,
   “forcing_lam_rel s (Delay x) y”,
   “forcing_lam_rel s (Box x) y”,
   “forcing_lam_rel s (MkTick x) y”,
   “forcing_lam_rel s (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once forcing_lam_rel_cases])
  |> LIST_CONJ;

Theorem forcing_lam_rel_freevars:
  ∀s x y. forcing_lam_rel s x y ⇒ freevars x = freevars y
Proof
  ho_match_mp_tac forcing_lam_rel_strongind >>
  gvs [forcing_lam_rel_def, PULL_EXISTS, freevars_def] >> rw []
  >- (simp [SET_EQ_SUBSET, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, MEM_EL, SUBSET_DEF] >>
      rw [] >> gs [LIST_REL_EL_EQN] >>
      first_assum $ irule_at $ Pos last >>
      metis_tac [])
  >- (simp [SET_EQ_SUBSET, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, MEM_EL, SUBSET_DEF] >>
      rw [] >> gs [LIST_REL_EL_EQN] >>
      first_assum $ irule_at $ Pos last >>
      metis_tac [])
  >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
      simp [SET_EQ_SUBSET, BIGUNION_SUBSET, MEM_MAP, PULL_EXISTS, MEM_EL, SUBSET_DEF] >>
      rw [] >> gs [LIST_REL_EL_EQN] >>
      last_x_assum $ drule_then assume_tac >> gs [EL_MAP] >>
      first_assum $ irule_at $ Pos last >>
      pairarg_tac >> gs [] >>
      pairarg_tac >> gs [] >>
      metis_tac [])
  >>~[‘Lams _ (Let _ _ _)’]
  >- (simp [freevars_Lams, freevars_Apps, freevars_def, SET_EQ_SUBSET, SUBSET_DEF] >>
      rw [] >> gs [MEM_MAP, freevars_def])
  >- (simp [freevars_Lams, freevars_Apps, freevars_def, SET_EQ_SUBSET, SUBSET_DEF] >>
      rw [] >> gs [MEM_MAP, freevars_def])
  >- (simp [freevars_Lams, freevars_Apps, freevars_def, SET_EQ_SUBSET, SUBSET_DEF] >>
      rw [] >> gs []
      >- (disj2_tac >> strip_tac
          >- (disj1_tac >> disj2_tac >> disj1_tac >> disj1_tac >>
              first_x_assum $ irule_at Any >>
              first_x_assum $ irule_at Any)
          >- (strip_tac >>
              gvs [MEM_MAP, MEM_FILTER, freevars_def, MEM_EL, LIST_REL_EL_EQN, EL_ZIP]))
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >> gs [MEM_MAP, freevars_def])
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >> gs [MEM_MAP, MEM_EL, EL_MAP2, EL_MAP, freevars_def] >>
          rename1 ‘if EL n bL then _ else _’ >>
          Cases_on ‘EL n bL’ >> gs [freevars_def])
      >- (strip_tac >> gs [])
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >>
          gvs [MEM_MAP, MEM_FILTER, freevars_def, MEM_EL, LIST_REL_EL_EQN, EL_ZIP])
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >> gs [MEM_MAP, freevars_def])
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >> gs [MEM_MAP, MEM_EL, EL_MAP2, EL_MAP, freevars_def] >>
          rename1 ‘if EL n bL then _ else _’ >>
          Cases_on ‘EL n bL’ >> gs [freevars_def])
      >- (rw [] >> gs []))
  >- (simp [freevars_Lams, freevars_Apps, freevars_def, SET_EQ_SUBSET, SUBSET_DEF] >>
      rw [] >> gs []
      >- (disj2_tac >> strip_tac
          >- (disj1_tac >> disj2_tac >> disj1_tac >> disj1_tac >>
              first_x_assum $ irule_at Any >>
              first_x_assum $ irule_at Any)
          >- (strip_tac >>
              gvs [MEM_MAP, MEM_FILTER, freevars_def, MEM_EL, LIST_REL_EL_EQN, EL_ZIP]))
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >> gs [MEM_MAP, freevars_def])
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >> gs [MEM_MAP, MEM_EL, EL_MAP2, EL_MAP, freevars_def] >>
          rename1 ‘if EL n bL then _ else _’ >>
          Cases_on ‘EL n bL’ >> gs [freevars_def])
      >- (strip_tac >> gs [])
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >>
          gvs [MEM_MAP, MEM_FILTER, freevars_def, MEM_EL, LIST_REL_EL_EQN, EL_ZIP])
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >> gs [MEM_MAP, freevars_def])
      >- (disj2_tac >> strip_tac >- metis_tac [] >>
          strip_tac >> gs [MEM_MAP, MEM_EL, EL_MAP2, EL_MAP, freevars_def] >>
          rename1 ‘if EL n bL then _ else _’ >>
          Cases_on ‘EL n bL’ >> gs [freevars_def])
      >- (rw [] >> gs []))
  >~[‘Let opt _ _’]
  >- (Cases_on ‘opt’ >> gs [freevars_def])
QED

Theorem forcing_lam_rel_refl:
  ∀x s. no_value x ⇒ forcing_lam_rel s x x
Proof
  Induct using freevars_ind >> gs [forcing_lam_rel_def, no_value_def]
  >- gs [MEM_EL, EVERY_EL, LIST_REL_EL_EQN, PULL_EXISTS]
  >- gs [MEM_EL, EVERY_EL, LIST_REL_EL_EQN, PULL_EXISTS]
  >- (gs [MEM_EL, EVERY_EL, LIST_REL_EL_EQN, PULL_EXISTS] >>
      rw [] >>
      last_x_assum irule >>
      rpt $ first_assum $ irule_at Any >>
      simp [EL_MAP] >> irule_at Any PAIR)
QED

Theorem forcing_lam_rel_subset:
  ∀s x y. forcing_lam_rel s x y ⇒ ∀s2. s2 ⊆ s ⇒ forcing_lam_rel s2 x y
Proof
  Induct using forcing_lam_rel_ind >> rw [] >> gs [forcing_lam_rel_def]
  >- gs [LIST_REL_EL_EQN]
  >- gs [LIST_REL_EL_EQN]
  >- gs [LIST_REL_EL_EQN]
  >- (disj1_tac >>
      rpt $ irule_at (Pos hd) EQ_REFL >>
      rw []
      >- (strip_tac >> gs [SUBSET_DEF]) >>
      first_x_assum $ irule >> gs [SUBSET_DEF])
  >- (disj2_tac >>
      rpt $ irule_at (Pos hd) EQ_REFL >>
      rw []
      >- (strip_tac >> gs [SUBSET_DEF]) >>
      first_x_assum $ irule >> gs [SUBSET_DEF])
  >- (disj1_tac >>
      rpt $ irule_at (Pos hd) EQ_REFL >>
      rw []
      >- (strip_tac >> gs [SUBSET_DEF]) >>
      first_x_assum $ irule >> gs [SUBSET_DEF])
  >- (disj2_tac >>
      rpt $ irule_at (Pos hd) EQ_REFL >>
      rw []
      >- (strip_tac >> gs [SUBSET_DEF]) >>
      first_x_assum $ irule >> gs [SUBSET_DEF])
QED

(*Theorem UNION_INTER_EMPTY:
  ∀s1 s2 s3. (s1 ∪ s2) ∩ s3 = {} ⇔ s1 ∩ s3 = {} ∧ s2 ∩ s3 = {}
Proof
  rpt $ gen_tac >> eq_tac >> rw [] >>
  irule $ iffLR SUBSET_EMPTY >>
  irule $ iffRL SUBSET_DEF >>
  dxrule_then assume_tac $ iffRL SUBSET_EMPTY >>
  dxrule_then assume_tac $ iffLR SUBSET_DEF
  >- (gs [] >> gen_tac >>
      rename1 ‘x ∉ _’ >>
      pop_assum $ qspec_then ‘x’ assume_tac >> gs [])
  >- (gs [] >> gen_tac >>
      rename1 ‘x ∉ _’ >>
      pop_assum $ qspec_then ‘x’ assume_tac >> gs [])
  >- (dxrule_then assume_tac $ iffRL SUBSET_EMPTY >>
      dxrule_then assume_tac $ iffLR SUBSET_DEF >>
      gs [] >> gen_tac >>
      rename1 ‘x ∉ _’ >>
      pop_assum $ qspec_then ‘x’ assume_tac >> gs [])
QED

Theorem UNION_INTER_EMPTY2:
  ∀s1 s2 s3. s3 ∩ (s1 ∪ s2) = {} ⇔ s3 ∩ s1 = {} ∧ s3 ∩ s2 = {}
Proof
  rpt $ gen_tac >> eq_tac >> rw [] >>
  irule $ iffLR SUBSET_EMPTY >>
  irule $ iffRL SUBSET_DEF >>
  dxrule_then assume_tac $ iffRL SUBSET_EMPTY >>
  dxrule_then assume_tac $ iffLR SUBSET_DEF
  >- (gs [] >> gen_tac >>
      rename1 ‘x ∉ _’ >>
      pop_assum $ qspec_then ‘x’ assume_tac >> gs [])
  >- (gs [] >> gen_tac >>
      rename1 ‘x ∉ _’ >>
      pop_assum $ qspec_then ‘x’ assume_tac >> gs [])
  >- (dxrule_then assume_tac $ iffRL SUBSET_EMPTY >>
      dxrule_then assume_tac $ iffLR SUBSET_DEF >>
      gs [] >> gen_tac >>
      rename1 ‘x ∉ _’ >>
      pop_assum $ qspec_then ‘x’ assume_tac >> gs [])
QED

Theorem UNION_INTER_SING_EMPTY:
  s ∩ {v} = {} ⇔ v ∉ s
Proof
  rpt $ gen_tac >> eq_tac >> rw []
  >- (dxrule_then assume_tac $ iffRL SUBSET_EMPTY >>
      dxrule_then assume_tac $ iffLR SUBSET_DEF >>
      gs [])
  >- (irule $ iffLR SUBSET_EMPTY >>
      irule $ iffRL SUBSET_DEF >>
      gs [])
QED

Theorem UNION_INTER_SING_EMPTY2:
  {v} ∩ s = {} ⇔ v ∉ s
Proof
  rpt $ gen_tac >> eq_tac >> rw []
  >- (dxrule_then assume_tac $ iffRL SUBSET_EMPTY >>
      dxrule_then assume_tac $ iffLR SUBSET_DEF >>
      gs [])
  >- (irule $ iffLR SUBSET_EMPTY >>
      irule $ iffRL SUBSET_DEF >>
      gs [])
QED*)

Theorem LIST_REL_EXISTS:
  ∀l1 l5 R1 R2 R3 R4 s. LIST_REL (λx1 x5. DISJOINT (boundvars x1) s ⇒
                                        ∃x2 x3 x4.
                                          R1 x1 x2 ∧ boundvars x2 = boundvars x3 ∧
                                          DISJOINT (boundvars x3) s ∧ R2 x2 x3 ∧
                                          R3 x3 x4 ∧ R4 x4 x5) l1 l5 ⇒
                        DISJOINT (BIGUNION (set (MAP boundvars l1))) s
                        ⇒ ∃l2 l3 l4.
                            LIST_REL R1 l1 l2 ∧ LIST_REL R2 l2 l3 ∧
                            LIST_REL R3 l3 l4 ∧ LIST_REL R4 l4 l5 ∧
                            MAP boundvars l2 = MAP boundvars l3 ∧
                            DISJOINT (BIGUNION (set (MAP boundvars l3))) s
Proof
  Induct >> simp [PULL_EXISTS] >>
  rw [] >> last_x_assum $ drule_then assume_tac >>
  gs [SF DNF_ss] >>
  first_x_assum $ irule_at $ Pos hd >> simp [] >>
  first_x_assum $ irule_at $ Pos hd >> simp [] >>
  first_x_assum $ irule_at $ Pos hd >> simp [] >>
  first_x_assum $ irule_at $ Pos hd >> simp [] >>
  first_x_assum $ irule_at $ Pos hd >> simp [] >>
  first_x_assum $ irule_at $ Pos hd >> simp []
QED

Theorem GENLIST_EQ_ZERO:
  ∀l. GENLIST (λn. n = 0) (SUC (LENGTH l)) = T::MAP (K F) l
Proof
  once_rewrite_tac [GSYM LIST_REL_eq] >>
  gen_tac >>
  irule $ iffRL LIST_REL_EL_EQN >>
  simp [EL_GENLIST, EL_CONS] >>
  Cases >> gs [EL_MAP]
QED

Theorem MAP_Forcing_K_T:
  ∀l1 l2. LENGTH l1 = LENGTH l2 ⇒ MAP2 (λb e. if b then Force e else e) (MAP (K F) l1) l2 = l2
Proof
  once_rewrite_tac [GSYM LIST_REL_eq] >>
  gen_tac >> gen_tac >> strip_tac >>
  irule $ iffRL LIST_REL_EL_EQN >>
  simp [EL_MAP2, EL_MAP]
QED

Theorem FILTER_FST_ZIP_K_F:
  ∀l. FILTER FST (ZIP (MAP (K F) l, l)) = []
Proof
  Induct >> gs []
QED

Theorem LIST_REL_remove_Tick:
  ∀l1 l2 l3 s.
    LIST_REL clean_rel
             (MAP Var l1 ++ MAP Var l2 ++ Tick (Force (Var s))::MAP Var l3)
             (MAP Var l1 ++ MAP Var l2 ++ Force (Var s)::MAP Var l3)
Proof
  rw [LIST_REL_EL_EQN, EL_APPEND_EQN] >>
  IF_CASES_TAC >> simp []
  >- (IF_CASES_TAC >>
      simp [EL_MAP, clean_rel_def]) >>
  once_rewrite_tac [CONS_APPEND] >>
  simp [EL_APPEND_EQN] >>
  IF_CASES_TAC >>
  gvs [EL_MAP, clean_rel_def] >>
  rename1 ‘EL (n - (LENGTH l1 + LENGTH l2))’ >>
  ‘n = (LENGTH l1 + LENGTH l2)’ by gvs [] >> gvs [] >>
  irule clean_rel_remove_Letrec >>
  simp [clean_rel_def]
QED

Theorem EVERY_no_value_Force_Var:
  ∀vL bL. EVERY no_value (MAP2 (λb e. if b then Force e else e) bL (MAP Var vL))
Proof
  rw [EVERY_EL, EL_MAP2, EL_MAP] >>
  IF_CASES_TAC >> simp [no_value_def]
QED

Theorem EL_ZIP2:
  ∀l1 l2 n. n < LENGTH l1 ∧ n < LENGTH l2 ⇒ EL n (ZIP (l1, l2)) = (EL n l1, EL n l2)
Proof
  Induct >> gs [] >>
  gen_tac >> Induct >> gs [] >>
  gen_tac >> Cases >> gvs []
QED

Theorem MEM_MAP_FILTER_ZIP:
  ∀v l1 l2. MEM v (MAP SND (FILTER FST (ZIP (l1, l2)))) ⇒ MEM v l2
Proof
  rw [MEM_MAP, MEM_FILTER] >>
  gvs [MEM_EL, EL_ZIP] >>
  first_assum $ irule_at Any >>
  gs [EL_ZIP2]
QED

Theorem ALL_DISTINCT_MAP_FILTER:
  ∀bL vL. LENGTH bL = LENGTH vL ∧ ALL_DISTINCT vL ⇒ ALL_DISTINCT (MAP SND (FILTER FST (ZIP (bL, vL))))
Proof
  Induct >> gs [] >> gen_tac >>
  Cases >> gs [] >>
  rw [] >> gs [] >>
  strip_tac >> dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> gs []
QED

Theorem forcing_lam_rel_combined:
  ∀s x y. forcing_lam_rel s x y
        ⇒ DISJOINT (boundvars x) s
        ⇒ ∃x2 x3 x4.
            force_arg_rel x x2 ∧
            boundvars x2 = boundvars x3 ∧
            clean_rel x2 x3 ∧
            DISJOINT (boundvars x3) s ∧
            combine_rel x3 x4 ∧
            clean_rel x4 y
Proof
  qspec_then ‘(λs x1 x5. DISJOINT (boundvars x1) s ⇒ ∃x2 x3 x4.
                         force_arg_rel x1 x2 ∧
                         boundvars x2 = boundvars x3 ∧
                         DISJOINT (boundvars x3) s ∧
                         clean_rel x2 x3 ∧
                         combine_rel x3 x4 ∧
                         clean_rel x4 x5)’
             mp_tac forcing_lam_rel_strongind >>
  impl_tac >> rw []
  >- (irule_at Any force_arg_rel_Var >>
      irule_at Any clean_rel_Var >>
      irule_at Any combine_rel_Var >>
      irule_at Any clean_rel_Var >>
      simp [])
  >- (irule_at Any force_arg_rel_Prim >>
      irule_at Any clean_rel_Prim >>
      irule_at Any combine_rel_Prim >>
      irule_at Any clean_rel_Prim >>
      gvs [LIST_REL_CONJ, boundvars_def, SF ETA_ss] >>
      dxrule_then assume_tac LIST_REL_EXISTS >> gs [] >>
      first_x_assum $ irule_at Any >> simp [] >>
      first_x_assum $ irule_at Any >> simp [] >>
      first_x_assum $ irule_at Any >>
      simp [boundvars_def, SF ETA_ss])
  >- (irule_at Any force_arg_rel_Monad >>
      irule_at Any clean_rel_Monad >>
      irule_at Any combine_rel_Monad >>
      irule_at Any clean_rel_Monad >>
      gvs [LIST_REL_CONJ, boundvars_def, SF ETA_ss] >>
      dxrule_then assume_tac LIST_REL_EXISTS >> gs [] >>
      first_x_assum $ irule_at Any >> simp [] >>
      first_x_assum $ irule_at Any >> simp [] >>
      first_x_assum $ irule_at Any >>
      simp [boundvars_def, SF ETA_ss])
  >- (gs [boundvars_def] >>
      irule_at Any force_arg_rel_App >>
      irule_at Any combine_rel_App >>
      irule_at (Pos last) clean_rel_App >>
      irule_at (Pos last) clean_rel_App >>
      simp [boundvars_def] >> metis_tac [])
  >- (gs [boundvars_def] >>
      irule_at Any force_arg_rel_Lam >>
      irule_at Any combine_rel_Lam >>
      irule_at (Pos last) clean_rel_Lam >>
      irule_at (Pos last) clean_rel_Lam >>
      simp [boundvars_def] >> metis_tac [])
  >- (gs [boundvars_def] >>
      irule_at Any force_arg_rel_Letrec >>
      irule_at Any combine_rel_Letrec >> simp [] >>
      irule_at (Pos last) clean_rel_Letrec >> simp [] >>
      irule_at (Pos last) clean_rel_Letrec >> simp [] >>
      gvs [LIST_REL_CONJ] >>
      dxrule_then assume_tac LIST_REL_EXISTS >>
      gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      qpat_x_assum ‘combine_rel _ _’ $ irule_at Any >> simp [] >>
      qpat_x_assum ‘force_arg_rel _ _’ $ irule_at Any >> simp [] >>
      rename1 ‘LIST_REL _ (MAP SND f) l2’ >>
      rename1 ‘LIST_REL combine_rel l3 l4’ >>
      qexists_tac ‘ZIP (MAP FST f, l3)’ >>
      qexists_tac ‘ZIP (MAP FST f, l4)’ >>
      qexists_tac ‘ZIP (MAP FST f, l2)’ >>
      ‘LENGTH f = LENGTH l2’ by gs [LIST_REL_EL_EQN] >>
      ‘LENGTH g = LENGTH l4’ by gs [LIST_REL_EL_EQN] >>
      ‘LENGTH l3 = LENGTH l4’ by gs [LIST_REL_EL_EQN] >>
      ‘LENGTH l2 = LENGTH l3’ by gs [LIST_REL_EL_EQN] >>
      simp [MAP_ZIP, boundvars_def] >>
      gs [LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> rw [] >>
      rpt $ last_x_assum $ drule_then assume_tac
      >~[‘_ ∪ _ = _ ∪ _’]
      >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
          AP_TERM_TAC >> AP_TERM_TAC >>
          irule LIST_EQ >> gs [EL_MAP, EL_ZIP] >>
          ‘∀n. n < LENGTH l2 ⇒ EL n (MAP boundvars l2) = EL n (MAP boundvars l3)’ by gs [] >>
          gs [EL_MAP])
      >~[‘MEM s' (MAP _ _)’]
      >- (first_x_assum irule >>
          gs [MEM_EL, EL_MAP, EL_ZIP] >>
          first_assum $ irule_at Any >> simp [EL_MAP]) >>
      rename1 ‘force_arg_rel a b’ >>
      Cases_on ‘a’ >> gs [ok_bind_def] >>
      gs [force_arg_rel_def, combine_rel_def, clean_rel_def])
  >- (rename1 ‘Let opt _ _’ >> Cases_on ‘opt’ >>
      gs [boundvars_def] >>
      irule_at Any force_arg_rel_Let >>
      irule_at Any combine_rel_Let >>
      irule_at (Pos last) clean_rel_Let >>
      irule_at (Pos last) clean_rel_Let >>
      simp [boundvars_def] >> metis_tac [])

  >- (gs [boundvars_def, boundvars_Lams, boundvars_Apps, DISJOINT_SYM] >>
      irule_at Any force_arg_rel_Let_Lams_Force_Var >> simp [] >>
      qpat_assum ‘force_arg_rel _ _’ $ irule_at Any >>
      irule_at (Pos last) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lams >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at (Pos hd) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lams >>
      irule_at (Pos hd) clean_rel_Apps >>
      irule_at (Pos hd) clean_rel_Var >>
      qspec_then ‘[]’ assume_tac LIST_REL_remove_Tick >> gs [] >>
      pop_assum $ irule_at Any >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at Any combine_rel_Let >>
      irule_at Any combine_rel_Let >>
      irule_at Any combine_rel_Lams >>
      irule_at Any combine_rel_Lams >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at Any combine_rel_Apps >>
      irule_at Any combine_rel_Var >>
      first_x_assum $ irule_at $ Pos $ el 2 >>
      irule_at Any clean_rel_Let >>
      irule_at Any clean_rel_Let >>
      irule_at Any clean_rel_Lams >>
      irule_at Any clean_rel_Lams >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at Any clean_rel_Apps >>
      irule_at Any clean_rel_Var >> simp [] >>
      rename1 ‘MAP Var vL1 ++ Tick (Force (Var s))::MAP Var l2’ >>
      qexists_tac ‘MAP Var vL1 ++ Tick (Force (Var s))::MAP Var l2’ >>
      rw []
      >- (simp [LIST_REL_APPEND_EQ] >>
          gs [LIST_REL_EL_EQN, clean_rel_def, EL_MAP])
      >- (simp [LIST_REL_APPEND_EQ] >>
          gs [LIST_REL_EL_EQN, combine_rel_def, EL_MAP])
      >- gs [boundvars_def, boundvars_Lams]
      >- (gs [boundvars_def, boundvars_Lams, boundvars_Apps, boundvars_def, DISJOINT_SYM] >>
          simp [MAP_MAP_o,combinTheory.o_DEF, LAMBDA_PROD, boundvars_def, MEM_MAP, PULL_EXISTS]))

  >- (gs [boundvars_def, boundvars_Lams, boundvars_Apps, DISJOINT_SYM] >>
      irule_at Any force_arg_rel_Let_Lams_Force_Var2 >> simp [] >>
      qpat_assum ‘force_arg_rel _ _’ $ irule_at Any >>
      irule_at (Pos last) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lam >>
      irule_at (Pos hd) clean_rel_Lams >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at (Pos hd) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lams >>
      irule_at (Pos hd) clean_rel_Apps >>
      irule_at (Pos hd) clean_rel_App >>
      irule_at (Pos hd) clean_rel_Var >>
      irule_at (Pos hd) clean_rel_Var >>
      qspec_then ‘[]’ assume_tac LIST_REL_remove_Tick >> gs [] >>
      pop_assum $ irule_at Any >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at Any combine_rel_Let >>
      irule_at Any combine_rel_Let >>
      irule_at Any combine_rel_Lams >>
      irule_at Any combine_rel_Lam >>
      irule_at Any combine_rel_Lams >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at Any combine_rel_Apps >>
      irule_at Any combine_rel_App >>
      irule_at Any combine_rel_Var >>
      irule_at Any combine_rel_Var >>
      first_x_assum $ irule_at $ Pos $ el 2 >>
      irule_at Any clean_rel_Let >>
      irule_at Any clean_rel_Let >>
      irule_at Any clean_rel_Lams >>
      irule_at Any clean_rel_Lam >>
      irule_at Any clean_rel_Lams >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at Any clean_rel_Apps >>
      irule_at Any clean_rel_App >>
      irule_at Any clean_rel_Var >>
      irule_at Any clean_rel_Var >> simp [] >>
      rename1 ‘MAP Var vL1 ++ Tick (Force (Var s))::MAP Var l2’ >>
      qexists_tac ‘MAP Var vL1 ++ Tick (Force (Var s))::MAP Var l2’ >>
      rw []
      >- (simp [LIST_REL_APPEND_EQ] >>
          gs [LIST_REL_EL_EQN, clean_rel_def, EL_MAP])
      >- (simp [LIST_REL_APPEND_EQ] >>
          gs [LIST_REL_EL_EQN, combine_rel_def, EL_MAP])
      >- gs [boundvars_def, boundvars_Lams]
      >- (gs [boundvars_def, boundvars_Lams, boundvars_Apps, boundvars_def, DISJOINT_SYM] >>
          simp [MEM_MAP, PULL_EXISTS, boundvars_def]))

  >- (gs [boundvars_def, boundvars_Lams, boundvars_Apps, DISJOINT_SYM] >>
      irule_at Any force_arg_rel_Let_Lams_Force_Var >> simp [] >>
      qpat_assum ‘force_arg_rel _ _’ $ irule_at Any >>
      irule_at Any force_arg_rel_Let >>
      qpat_assum ‘force_arg_rel _ _’ $ irule_at Any >>
      irule_at Any force_arg_rel_refl >>
      irule_at (Pos $ el 14) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lams >>
      first_assum $ irule_at $ Pos $ hd >>
      irule_at (Pos hd) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lams >>
      irule_at (Pos $ el 2) clean_rel_Let >>
      first_assum $ irule_at $ Pos $ el 2 >>
      irule_at (Pos hd) clean_rel_Lams >>
      irule_at (Pos hd) clean_rel_refl >>
      irule_at (Pos $ el 2) clean_rel_Apps >>
      irule_at (Pos hd) clean_rel_Var >>
      irule_at (Pos hd) LIST_REL_remove_Tick >>
      simp [no_value_Apps, no_value_Lams, EVERY_MAP, no_value_def, EVERY_no_value_Force_Var] >>
      irule_at Any combine_rel_Let >> simp [] >>
      irule_at Any combine_rel_Lams >>
      first_assum $ irule_at $ Pos hd >>
      rename1 ‘combine_rel
            (Let (SOME v2)
               (Lams (MAP SND (FILTER FST (ZIP (bL2,vL2))) ++ vL1 ++ s::vL5)
                  (Apps (Var _)
                     (MAP Var (MAP SND (FILTER FST (ZIP (bL2,vL2)))) ++
                      MAP Var vL1 ++ Force (Var s)::MAP Var vL5)))
               (Let (SOME v1)
                  (Lams (vL1 ++ s::vL2)
                     (Apps (Var v2)
                        (MAP Var (MAP SND (FILTER FST (ZIP (bL2,vL2)))) ++
                         MAP Var vL1 ++ [Var s] ++
                         MAP2 (λb e. if b then Force e else e) bL
                           (MAP Var vL2)))) x3')) _’ >>
      qspecl_then [‘v2’, ‘v1’, ‘vL1 ++ s::vL2’, ‘vL1 ++ s::vL5’, ‘MAP SND (FILTER FST (ZIP (bL2, vL2)))’,
                   ‘MAP (K F) vL1 ++ T::MAP (K F) bL’, ‘MAP (K F) vL1 ++ F::bL’,
                   ‘MAP (K F) vL1 ++ F::bL2’, ‘Var v3’, ‘Var v3’, ‘x3'’, ‘x4'’, ‘LENGTH vL1’]
                  assume_tac combine_rel_Let_Lams_combine1 >>
      ‘∀x y z. combine_rel x z ∧ x = y ⇒ combine_rel y z’ by simp [] >>
      pop_assum $ irule_at $ Pos hd >>
      pop_assum $ irule_at $ Pos hd >>
      gs [GENLIST_EQ_ZERO, MAP_Forcing_K_T, GSYM ZIP_APPEND, FILTER_APPEND, FILTER_FST_ZIP_K_F, MAP2_APPEND] >>
      irule_at (Pos last) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lams >> simp [] >>
      rw []
      >- (irule clean_rel_remove_Let >>
          irule_at Any clean_rel_Let >>
          irule_at Any clean_rel_Lams >>
          irule_at Any clean_rel_remove_Letrec >>
          simp [] >>
          irule_at Any clean_rel_Apps >>
          irule_at Any clean_rel_Var >>
          rw []
          >- (rw [LIST_REL_APPEND_EQ, EVERY2_MAP] >>
              simp [LIST_REL_EL_EQN, clean_rel_Var]
              >- simp [clean_rel_def] >>
              rw [EL_MAP2, EL_MAP, clean_rel_def])
          >- (Cases_on ‘MAP SND (FILTER FST (ZIP (bL2,vL2)))’ >>
              simp [no_op_def] >>
              Cases_on ‘vL1’ >> simp [no_op_def])
          >- (rpt $ dxrule_then assume_tac clean_rel_freevars >>
              rpt $ dxrule_then assume_tac combine_rel_freevars >>
              rpt $ dxrule_then assume_tac force_arg_rel_freevars >>
              gs [freevars_def, freevars_Lams, freevars_Apps, MEM_MAP, PULL_FORALL,
                  MEM_FILTER, FORALL_PROD, SUBSET_DEF, DISJ_EQ_IMP, MEM_EL] >>
              rw [] >> strip_tac >> gs [EL_MAP2, EL_MAP, EL_ZIP2] >>
              rename1 ‘n < LENGTH bL’ >>
              Cases_on ‘EL n bL’ >> gs [freevars_def]))
      >- gs [LIST_REL_EL_EQN]
      >- (rw [EL_APPEND_EQN, EL_MAP]
          >- (rename1 ‘EL (i - LENGTH vL1) _’ >>
              ‘i = LENGTH vL1’ by gs [] >> gs [])
          >- gs []
          >- (once_rewrite_tac [CONS_APPEND] >> gs [EL_APPEND_EQN]))
      >- gs [LIST_REL_APPEND_EQ, LIST_REL_EL_EQN, EL_MAP]
      >- gs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_FST_ZIP_K_F, FILTER_APPEND]
      >- gs [EL_APPEND_EQN, EL_MAP, LESS_OR_EQ]
      >- (irule LIST_EQ >> rw [EL_APPEND_EQN, EL_MAP] >>
          eq_tac >> gvs [])
      >- fs [freevars_def]
      >- gs [freevars_def, EVERY_MEM]
      >- gs [freevars_def, EVERY_MEM]
      >- fs [freevars_def]
      >- gs [freevars_def, EVERY_MEM]
      >- (gs [EVERY_MEM, freevars_def] >>
          strip_tac >> dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
          gs [])
      >- simp [combine_rel_def]
      >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> gs [])
      >- (rpt $ dxrule_then assume_tac clean_rel_freevars >>
          rpt $ dxrule_then assume_tac combine_rel_freevars >>
          rpt $ dxrule_then assume_tac force_arg_rel_freevars >>
          gs [freevars_def, freevars_Lams, freevars_Apps, MEM_MAP, PULL_FORALL,
              MEM_FILTER, FORALL_PROD, SUBSET_DEF, DISJ_EQ_IMP, MEM_EL] >>
          rw [] >> strip_tac >> gs [EL_MAP2, EL_MAP, EL_ZIP2] >>
          rename1 ‘n < LENGTH bL’ >>
          Cases_on ‘EL n bL’ >> gs [freevars_def])
      >- (rw [boundvars_def, boundvars_Lams, boundvars_Apps, DISJ_EQ_IMP]
          >- (gs [MEM_MAP] >> rw [] >> gs [boundvars_def])
          >- (gs [MEM_MAP] >> rw [] >> gs [boundvars_def])
          >- (strip_tac >> gs [MEM_EL, EL_MAP2, EL_MAP] >>
              pop_assum mp_tac >> IF_CASES_TAC >> gs [boundvars_def]))
      >- (gs [ALL_DISTINCT_APPEND] >> rw [] >> gs []
          >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> strip_tac >> gs [])
          >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> strip_tac >> gs []))
      >- (strip_tac >> dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> gs [])
      >- (strip_tac >> dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> gs [])
      >- (simp [boundvars_def, boundvars_Lams, boundvars_Apps, SET_EQ_SUBSET, SUBSET_DEF] >>
          rw [] >> gs [])
      >- (gs [boundvars_def, boundvars_Lams, boundvars_Apps, DISJOINT_SYM] >>
          simp [MEM_MAP, PULL_EXISTS, boundvars_def]))

  >- (gs [boundvars_def, boundvars_Lams, boundvars_Apps, DISJOINT_SYM] >>
      irule_at Any force_arg_rel_Let_Lams_Force_Var2 >> simp [] >>
      qpat_assum ‘force_arg_rel _ _’ $ irule_at Any >>
      irule_at Any force_arg_rel_Let >>
      qpat_assum ‘force_arg_rel _ _’ $ irule_at Any >>
      irule_at Any force_arg_rel_refl >>
      irule_at (Pos $ el 14) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lam >>
      irule_at (Pos hd) clean_rel_Lams >>
      first_assum $ irule_at $ Pos $ hd >>
      irule_at (Pos hd) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lams >>
      irule_at (Pos $ el 2) clean_rel_Let >>
      first_assum $ irule_at $ Pos $ el 2 >>
      irule_at (Pos hd) clean_rel_Lams >>
      irule_at (Pos hd) clean_rel_refl >>
      irule_at (Pos $ el 2) clean_rel_Apps >>
      irule_at (Pos hd) clean_rel_App >>
      irule_at (Pos hd) clean_rel_Var >>
      irule_at (Pos hd) clean_rel_Var >>
      irule_at (Pos hd) LIST_REL_remove_Tick >>
      simp [no_value_Apps, no_value_Lams, EVERY_MAP, no_value_def, EVERY_no_value_Force_Var] >>
      irule_at Any combine_rel_Let >> simp [] >>
      irule_at Any combine_rel_Lam >> irule_at Any combine_rel_Lams >>
      first_assum $ irule_at $ Pos hd >>
      rename1 ‘combine_rel
            (Let (SOME v2)
               (Lams (MAP SND (FILTER FST (ZIP (bL2,vL2))) ++ vL1 ++ s::vL5)
                  (Apps (App (Var _) (Var s))
                     (MAP Var (MAP SND (FILTER FST (ZIP (bL2,vL2)))) ++
                      MAP Var vL1 ++ Force (Var s)::MAP Var vL5)))
               (Let (SOME v1)
                  (Lams (vL1 ++ s::vL2)
                     (Apps (Var v2)
                        (MAP Var (MAP SND (FILTER FST (ZIP (bL2,vL2)))) ++
                         MAP Var vL1 ++ [Var s] ++
                         MAP2 (λb e. if b then Force e else e) bL
                           (MAP Var vL2)))) x3')) _’ >>
      qspecl_then [‘v2’, ‘v1’, ‘vL1 ++ s::vL2’, ‘vL1 ++ s::vL5’, ‘MAP SND (FILTER FST (ZIP (bL2, vL2)))’,
                   ‘MAP (K F) vL1 ++ T::MAP (K F) bL’, ‘MAP (K F) vL1 ++ F::bL’,
                   ‘MAP (K F) vL1 ++ F::bL2’, ‘Var v3’, ‘Var v3’, ‘x3'’, ‘x4'’, ‘LENGTH vL1’]
                  assume_tac combine_rel_Let_Lams_combine2 >>
      ‘∀x y z. combine_rel x z ∧ x = y ⇒ combine_rel y z’ by simp [] >>
      pop_assum $ irule_at $ Pos hd >>
      pop_assum $ irule_at $ Pos hd >>
      gs [GENLIST_EQ_ZERO, MAP_Forcing_K_T, GSYM ZIP_APPEND, FILTER_APPEND, FILTER_FST_ZIP_K_F, MAP2_APPEND] >>
      irule_at (Pos last) clean_rel_Let >>
      irule_at (Pos hd) clean_rel_Lam >>
      irule_at (Pos hd) clean_rel_Lams >> simp [] >>
      rw []
      >- (irule clean_rel_remove_Let >>
          irule_at Any clean_rel_Let >>
          irule_at Any clean_rel_Lams >>
          irule_at Any clean_rel_remove_Letrec >>
          simp [] >>
          irule_at Any clean_rel_Apps >>
          simp [clean_rel_def, EL_APPEND_EQN] >>
          rw []
          >- (rw [LIST_REL_APPEND_EQ, EVERY2_MAP] >>
              simp [LIST_REL_EL_EQN, clean_rel_Var]
              >- simp [clean_rel_def] >>
              rw [EL_MAP2, EL_MAP, clean_rel_def])
          >- (Cases_on ‘MAP SND (FILTER FST (ZIP (bL2,vL2)))’ >>
              simp [no_op_def] >>
              Cases_on ‘vL1’ >> simp [no_op_def])
          >- (rpt $ dxrule_then assume_tac clean_rel_freevars >>
              rpt $ dxrule_then assume_tac combine_rel_freevars >>
              rpt $ dxrule_then assume_tac force_arg_rel_freevars >>
              gs [freevars_def, freevars_Lams, freevars_Apps, MEM_MAP, PULL_FORALL,
                  MEM_FILTER, FORALL_PROD, SUBSET_DEF, DISJ_EQ_IMP, MEM_EL] >>
              rw [] >> strip_tac >> gs [EL_MAP2, EL_MAP, EL_ZIP2] >>
              rename1 ‘n < LENGTH bL’ >>
              Cases_on ‘EL n bL’ >> gs [freevars_def]))
      >- gs [LIST_REL_EL_EQN]
      >- (rw [EL_APPEND_EQN, EL_MAP]
          >- (rename1 ‘EL (i - LENGTH vL1) _’ >>
              ‘i = LENGTH vL1’ by gs [] >> gs [])
          >- gs []
          >- (once_rewrite_tac [CONS_APPEND] >> gs [EL_APPEND_EQN]))
      >- gs [LIST_REL_APPEND_EQ, LIST_REL_EL_EQN, EL_MAP]
      >- gs [LIST_REL_EL_EQN, GSYM ZIP_APPEND, FILTER_FST_ZIP_K_F, FILTER_APPEND]
      >- gs [EL_APPEND_EQN, EL_MAP, LESS_OR_EQ]
      >- (irule LIST_EQ >> rw [EL_APPEND_EQN, EL_MAP] >>
          eq_tac >> gvs [])
      >- fs [freevars_def]
      >- gs [freevars_def, EVERY_MEM]
      >- gs [freevars_def, EVERY_MEM]
      >- fs [freevars_def]
      >- gs [freevars_def, EVERY_MEM]
      >- (gs [EVERY_MEM, freevars_def] >>
          strip_tac >> dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
          gs [])
      >- simp [combine_rel_def]
      >- simp [EL_APPEND_EQN]
      >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> gs [])
      >- (rpt $ dxrule_then assume_tac clean_rel_freevars >>
          rpt $ dxrule_then assume_tac combine_rel_freevars >>
          rpt $ dxrule_then assume_tac force_arg_rel_freevars >>
          gs [freevars_def, freevars_Lams, freevars_Apps, MEM_MAP, PULL_FORALL,
              MEM_FILTER, FORALL_PROD, SUBSET_DEF, DISJ_EQ_IMP, MEM_EL] >>
          rw [] >> strip_tac >> gs [EL_MAP2, EL_MAP, EL_ZIP2] >>
          rename1 ‘n < LENGTH bL’ >>
          Cases_on ‘EL n bL’ >> gs [freevars_def])
      >- (rw [boundvars_def, boundvars_Lams, boundvars_Apps, DISJ_EQ_IMP]
          >- (gs [MEM_MAP] >> rw [] >> gs [boundvars_def])
          >- (gs [MEM_MAP] >> rw [] >> gs [boundvars_def])
          >- (strip_tac >> gs [MEM_EL, EL_MAP2, EL_MAP] >>
              pop_assum mp_tac >> IF_CASES_TAC >> gs [boundvars_def]))
      >- (gs [ALL_DISTINCT_APPEND] >> rw [] >> gs []
          >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> strip_tac >> gs [])
          >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> strip_tac >> gs []))
      >- (strip_tac >> dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> gs [])
      >- (strip_tac >> dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> gs [])
      >- (simp [boundvars_def, boundvars_Lams, boundvars_Apps, SET_EQ_SUBSET, SUBSET_DEF] >>
          rw [] >> gs [])
      >- (gs [boundvars_def, boundvars_Lams, boundvars_Apps, DISJOINT_SYM] >>
          simp [MEM_MAP, PULL_EXISTS, boundvars_def]))

  >- (gs [boundvars_def] >>
      irule_at Any force_arg_rel_If >>
      irule_at Any combine_rel_If >>
      irule_at (Pos last) clean_rel_If >>
      irule_at (Pos last) clean_rel_If >>
      gs [boundvars_def] >>
      rpt $ qpat_x_assum ‘force_arg_rel _ _’ $ irule_at Any >>
      rpt $ first_x_assum $ irule_at $ Pos hd >> simp [])
  >- (gs [boundvars_def] >>
      irule_at Any force_arg_rel_Delay >>
      irule_at Any combine_rel_Delay >>
      irule_at (Pos last) clean_rel_Delay >>
      irule_at (Pos last) clean_rel_Delay >>
      simp [boundvars_def] >>
      metis_tac [])
  >- (gs [boundvars_def] >>
      gs [boundvars_def] >>
      irule_at Any force_arg_rel_Box >>
      irule_at Any combine_rel_Box >>
      irule_at (Pos last) clean_rel_Box >>
      irule_at (Pos last) clean_rel_Box >>
      simp [boundvars_def] >> metis_tac [])
  >- (gs [boundvars_def] >>
      irule_at Any force_arg_rel_Force >>
      irule_at Any combine_rel_Force >>
      irule_at (Pos last) clean_rel_Force >>
      irule_at (Pos last) clean_rel_Force >>
      simp [boundvars_def] >> metis_tac [])
  >- (gs [boundvars_def] >>
      irule_at Any force_arg_rel_MkTick >>
      irule_at Any combine_rel_MkTick >>
      irule_at (Pos last) clean_rel_MkTick >>
      irule_at (Pos last) clean_rel_MkTick >>
      simp [boundvars_def] >> metis_tac [])
  >- (first_x_assum $ dxrule_all_then assume_tac >>
      fs [] >> metis_tac [])
QED

Theorem forcing_lam_rel_semantics:
  forcing_lam_rel {} x y ∧
  pure_semantics$safe_itree (semantics x Done []) ∧
  closed x ⇒
  semantics x Done [] = semantics y Done []
Proof
  rw [] >>
  dxrule_then assume_tac forcing_lam_rel_combined >> gs [] >>
  drule_then assume_tac combine_rel_freevars >>
  dxrule_then assume_tac combine_rel_semantics >>
  drule_then assume_tac clean_rel_freevars >>
  dxrule_then assume_tac clean_rel_semantics >>
  drule_then assume_tac clean_rel_freevars >>
  dxrule_then assume_tac clean_rel_semantics >>
  drule_then assume_tac force_arg_rel_freevars >>
  dxrule_then assume_tac force_arg_rel_semantics >>
  gs [closed_def]
QED

val _ = export_theory ();
