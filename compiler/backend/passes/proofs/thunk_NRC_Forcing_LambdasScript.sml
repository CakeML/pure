(*
 Relation to rewrite function definitions to remove Delay
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory
     thunk_NRC_relTheory thunk_Forcing_LambdasTheory thunk_Let_Lam_ForcedTheory;

val _ = new_theory "thunk_NRC_Forcing_Lambdas";

val _ = set_grammar_ancestry ["thunk_Let_Lam_Forced",
                              "thunk_Forcing_Lambdas"];

Definition lets_force_def:
  lets_force [] x = x ∧
  lets_force ((v1, v2)::tl) x = lets_force tl (Let (SOME v1) (Force (Var v2)) x)
End

Definition merge_inside_def:
  merge_inside [] l2 l3 = [] ∧
  merge_inside l1 [] l3 = [] ∧
  merge_inside (v::l1) (F::l2) l3 = v::merge_inside l1 l2 l3 ∧
  merge_inside (_::l1) (T::l2) (v::l3) = v::merge_inside l1 l2 l3 ∧
  merge_inside l1 l2 [] = []
End

Inductive exp_rel:
[~Var:]
  (∀s n. exp_rel s (Var n) (Var n)) ∧
[~Prim:]
  (∀s op xs ys.
     LIST_REL (exp_rel s) xs ys ⇒
       exp_rel s (Prim op xs) (Prim op ys)) ∧
[~Monad:]
  (∀s mop xs ys.
     LIST_REL (exp_rel s) xs ys ⇒
       exp_rel s (Monad mop xs) (Monad mop ys)) ∧
[~App:]
  (∀s f g x y.
     exp_rel s f g ∧
     exp_rel s x y ⇒
       exp_rel s (App f x) (App g y)) ∧
[~Lam:]
  (∀s v x y.
     exp_rel s x y ⇒
       exp_rel s (Lam v x) (Lam v y)) ∧
[~Letrec:]
  (∀s f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL (exp_rel s) (MAP SND f) (MAP SND g) ∧
     exp_rel s x y ⇒
     exp_rel s (Letrec f x) (Letrec g y)) ∧
[~Let:]
  (∀s opt x1 y1 x2 y2.
     exp_rel s x1 x2 ∧
     exp_rel s y1 y2 ⇒
     exp_rel s (Let opt x1 y1) (Let opt x2 y2)) ∧
[~Let_Lams_combine:]
  (∀set v1 v2 vL vL1 vL2 vL3 vL4 bL bL2 x1 x2 y1 y2.
     LENGTH vL = LENGTH bL ∧ MEM T bL ∧
     vL1 = MAP SND (FILTER FST (ZIP (bL, vL))) ∧
     LENGTH vL2 = LENGTH vL1 ∧
     vL3 = MAP SND (FILTER FST (ZIP (bL2, vL))) ∧
     LIST_REL (λ(b, b2) v. b ⇒ (b2 ⇔ v ∈ freevars x1)) (ZIP (bL, bL2)) vL ∧
     LIST_REL (λb2 b. b2 ⇒ b) bL2 bL ∧
     v2 ∉ set ∧
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧
     v2 ∉ boundvars x1 ∧ v2 ∉ boundvars y1 ∧
     ALL_DISTINCT (v1::v2::vL ++ vL2) ∧
     vL4 = merge_inside vL bL vL2 ∧
     exp_rel (set ∪ {v2}) x1 x2 ∧ exp_rel (set ∪ {v2}) y1 y2 ⇒
     exp_rel set (Let (SOME v1)
                (Lams vL (lets_force (ZIP (vL2, vL1)) x1)) y1)
             (Let (SOME v2)
              (Lams (vL3 ++ vL4) x2)
              (Let (SOME v1)
               (Lams vL (Apps (Var v2) (MAP Var vL3 ++
                                          MAP2 (λb e. if b then Force e else e)
                                               bL (MAP Var vL)))) y2))) ∧
[~If:]
  (∀set x1 y1 z1 x2 y2 z2.
     exp_rel set x1 x2 ∧
     exp_rel set y1 y2 ∧
     exp_rel set z1 z2 ⇒
       exp_rel set (If x1 y1 z1) (If x2 y2 z2)) ∧
[~Delay:]
  (∀set x y.
     exp_rel set x y ⇒
       exp_rel set (Delay x) (Delay y)) ∧
[~Force:]
  (∀set x y.
     exp_rel set x y ⇒
     exp_rel set (Force x) (Force y)) ∧
[~MkTick:]
  (∀set x y. exp_rel set x y ⇒ exp_rel set (MkTick x) (MkTick y))
End

Theorem exp_rel_def =
  [“exp_rel s (Var v) x”,
   “exp_rel s (Prim op xs) x”,
   “exp_rel s (Monad mop xs) x”,
   “exp_rel s (App f x) y”,
   “exp_rel s (Lam v x) y”,
   “exp_rel s (Letrec f x) y”,
   “exp_rel s (Let opt x y) z”,
   “exp_rel s (If x y z) w”,
   “exp_rel s (Delay x) y”,
   “exp_rel s (MkTick x) y”,
   “exp_rel s (Value x) y”,
   “exp_rel s (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once exp_rel_cases])
  |> LIST_CONJ;

Theorem freevars_lets_force:
  ∀l1 l2 x.
    LENGTH l1 = LENGTH l2 ∧ ALL_DISTINCT (l1 ++ l2)
    ⇒ freevars (lets_force (ZIP (l1, l2)) x) = (freevars x DIFF (set l1)) ∪ set l2
Proof
  Induct >> gs [lets_force_def] >>
  gen_tac >> Cases >>
  gs [lets_force_def, freevars_def, ALL_DISTINCT_APPEND] >>
  rw [] >>
  rw [SET_EQ_SUBSET, SUBSET_DEF] >> gs [] >>
  strip_tac >> first_x_assum $ dxrule_then assume_tac >> fs []
QED

Theorem boundvars_lets_force:
  ∀l1 l2 x.
    LENGTH l1 = LENGTH l2
    ⇒ boundvars (lets_force (ZIP (l1, l2)) x) = boundvars x ∪ set l1
Proof
  Induct >> gs [lets_force_def] >>
  gen_tac >> Cases >>
  gs [lets_force_def, freevars_def, ALL_DISTINCT_APPEND, boundvars_def] >>
  rw [SET_EQ_SUBSET, SUBSET_DEF] >> gs []
QED

Theorem MEM_merge_inside:
  ∀l1 l2 l3 x.
    MEM x (merge_inside l1 l2 l3) ⇒ MEM x l1 ∨ MEM x l3
Proof
  Induct >> simp [merge_inside_def] >>
  gen_tac >> Cases >> simp [merge_inside_def] >>
  rename1 ‘merge_inside _ (b::_)’ >> Cases_on ‘b’
  >- (Cases >> simp [merge_inside_def] >>
      rw [] >>
      last_x_assum $ dxrule_then assume_tac >> fs [])
  >- (simp [merge_inside_def] >>
      rw [] >>
      last_x_assum $ dxrule_then assume_tac >> fs [])
QED

Theorem NEG_MEM_merge_inside:
  ∀l1 l2 l3 x.
    ¬MEM x (merge_inside l1 l2 l3) ∧
    LENGTH l1 = LENGTH l2 ∧
    LENGTH l3 = LENGTH (FILTER FST (ZIP (l2, l1)))
    ⇒ ¬MEM x l3 ∧ (∀i. i < LENGTH l1 ⇒ EL i l1 = x ⇒ EL i l2)
Proof
  Induct >> simp [merge_inside_def] >>
  gen_tac >> Cases >> simp [] >>
  rename1 ‘merge_inside _ (b::_)’ >> Cases_on ‘b’
  >- (Cases >> simp [merge_inside_def] >>
      rw [] >>
      last_x_assum $ dxrule_then assume_tac >> fs [] >>
      rename1 ‘EL i (T::_)’ >> Cases_on ‘i’ >>
      gs [])
  >- (simp [merge_inside_def] >>
      rw [] >>
      last_x_assum $ dxrule_then assume_tac >> fs [] >>
      rename1 ‘EL i (F::_)’ >> Cases_on ‘i’ >>
      gs [])
QED

Theorem exp_rel_freevars:
  ∀s x y. exp_rel s x y ⇒ freevars x = freevars y
Proof
  Induct using exp_rel_ind >> simp [freevars_def] >>
  rw []
  >- (AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      gs [LIST_REL_EL_EQN, EL_MAP])
  >- (AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      gs [LIST_REL_EL_EQN, EL_MAP])
  >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
      AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      gs [LIST_REL_EL_EQN, EL_MAP] >>
      rw [] >> first_x_assum $ dxrule_then assume_tac >>
      pairarg_tac >> gs [] >>
      pairarg_tac >> gs [])
  >- (rename1 ‘Let opt _ _’ >>
      Cases_on ‘opt’ >> simp [freevars_def])
  >- (rename1 ‘(ZIP (vL2, MAP SND (FILTER FST (ZIP (bL, vL)))))’ >>
      qspecl_then [‘vL2’,  ‘MAP SND (FILTER FST (ZIP (bL, vL)))’] mp_tac freevars_lets_force >>
      impl_tac >> simp [freevars_Lams, freevars_Apps, freevars_def]
      >- (gs [ALL_DISTINCT_APPEND, ALL_DISTINCT_MAP_FILTER] >>
          rw [] >> strip_tac >>
          dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
          gs []) >>
      disch_then kall_tac >>
      rw [SET_EQ_SUBSET, SUBSET_DEF] >> gs []
      >- (disj1_tac >> conj_tac
          >- (strip_tac >>
              dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
              gs [])
          >- (strip_tac >>
              dxrule_then assume_tac MEM_merge_inside >>
              gs []))
      >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >> gs [])
      >- (dxrule_then assume_tac NEG_MEM_merge_inside >>
          gs [] >>
          rename1 ‘¬MEM x2 vL ∨ _’ >>
          Cases_on ‘MEM x2 vL’ >> gs [] >>
          gs [MEM_MAP, MEM_FILTER, MEM_EL, LIST_REL_EL_EQN, FORALL_PROD, EL_ZIP] >>
          rename1 ‘EL n2 _ ∈  _’ >>
          rpt $ last_x_assum $ qspec_then ‘n2’ assume_tac >>
          gs [EL_ZIP])
      >- gs [MEM_MAP, MEM_FILTER, MEM_EL, freevars_def, EL_MAP, PULL_EXISTS, LIST_REL_EL_EQN, EL_ZIP]
      >- (gs [MEM_EL, EL_MAP2, EL_MAP] >>
          rename1 ‘if EL n2 bL then _ else _’ >>
          Cases_on ‘EL n2 bL’ >> gs [freevars_def]))
QED

Theorem exp_rel_Lams:
  ∀l s x y. exp_rel s (Lams l x) (Lams l y) ⇔ exp_rel s x y
Proof
  Induct >> gs [exp_rel_def]
QED

Theorem exp_rel_Apps:
  ∀l1 l2 s x y. exp_rel s x y ∧ LIST_REL (exp_rel s) l1 l2 ⇒ exp_rel s (Apps x l1) (Apps y l2)
Proof
  Induct >> gs [exp_rel_def, PULL_EXISTS]
QED

Theorem exp_rel_lets_force:
  ∀l s x y. exp_rel s (lets_force l x) (lets_force l y) ⇔ exp_rel s x y
Proof
  Induct >> gs [lets_force_def, FORALL_PROD, exp_rel_def]
QED

Theorem forcing_lam_rel_lets_force:
  ∀l s x y. forcing_lam_rel s (lets_force l x) (lets_force l y) ⇔ forcing_lam_rel s x y
Proof
  Induct >> gs [lets_force_def, FORALL_PROD, forcing_lam_rel_def]
QED

Theorem forcing_lam_rel_Lams:
  ∀l s x y. forcing_lam_rel s (Lams l x) (Lams l y) ⇔ forcing_lam_rel s x y
Proof
  Induct >> gs [forcing_lam_rel_def]
QED

Theorem forcing_lam_rel_Apps:
  ∀l1 l2 s x y. LENGTH l1 = LENGTH l2 ⇒ (forcing_lam_rel s (Apps x l1) (Apps y l2) ⇔
                  forcing_lam_rel s x y ∧ LIST_REL (forcing_lam_rel s) l1 l2)
Proof
  Induct >> gs [forcing_lam_rel_def] >>
  gen_tac >> Cases >> gs [forcing_lam_rel_def] >>
  metis_tac []
QED

Theorem forcing_lam_rel_refl:
  ∀s x y. exp_rel s x y ⇒ ∀s2. forcing_lam_rel s2 x x
Proof
  qspec_then ‘(λs x y. ∀s2. forcing_lam_rel s2 x x)’
             mp_tac exp_rel_strongind >>
  impl_tac >> rw [forcing_lam_rel_def, forcing_lam_rel_Lams, forcing_lam_rel_Apps] >>
  gs []
  >- gs [LIST_REL_CONJ, LIST_REL_EL_EQN]
  >- gs [LIST_REL_CONJ, LIST_REL_EL_EQN]
  >- gs [LIST_REL_CONJ, LIST_REL_EL_EQN]
  >- simp [forcing_lam_rel_lets_force]
QED

Theorem lets_force_APPEND:
  ∀l1 l2 x. lets_force (l1 ++ l2) x = lets_force l2 (lets_force l1 x)
Proof
  Induct >> gs [lets_force_def, FORALL_PROD]
QED

Theorem APPEND_CONS_RW:
  ∀l1 v l2. l1 ++ v::l2 = l1 ++ [v] ++ l2
Proof
  Induct >> gs []
QED

Theorem merge_inside_soundness_lemma:
  ∀vL bL vL2.
    LENGTH vL = LENGTH bL ∧ LENGTH vL2 = LENGTH (FILTER FST (ZIP (bL, vL))) ∧
    ALL_DISTINCT (vL ++ vL2) ⇒
    ∀i. i < LENGTH vL ⇒
        (EL i vL = EL i (merge_inside vL bL vL2) ⇔ ¬EL i bL)
Proof
  Induct >> gs [] >>
  gen_tac >> Cases >> simp [] >>
  IF_CASES_TAC >> gs []
  >- (Cases >> simp [merge_inside_def] >>
      strip_tac >>
      Cases >> simp [] >>
      rw [] >> last_x_assum irule >>
      gs [ALL_DISTINCT_APPEND]) >>
  gen_tac >> strip_tac >>
  Cases >> simp [merge_inside_def]
QED

Theorem NEG_MEM_T_IMP_K_F:
  ∀bL vL. ¬MEM T bL ∧ LENGTH vL = LENGTH bL ⇒ bL = MAP (K F) vL
Proof
  Induct >> gs [] >>
  Cases >> gs []
QED

Theorem LIST_REL_IMP_K_F:
  ∀l1 l2. LIST_REL (λb2 b. b2 ⇒ b) l2 (MAP (K F) l1) ⇒ l2 = MAP (K F) l1
Proof
  Induct >> gs [PULL_EXISTS]
QED

Theorem merge_inside_K_F:
  ∀l. merge_inside l (MAP (K F) l) [] = l
Proof
  Induct >> gs [merge_inside_def]
QED

Theorem ALL_DISTINCT_merge_inside:
  ∀l1 bL l2. ALL_DISTINCT (l1 ++ l2) ⇒ ALL_DISTINCT (merge_inside l1 bL l2)
Proof
  Induct >> simp [merge_inside_def] >>
  gen_tac >> Cases >> simp [merge_inside_def] >>
  rename1 ‘merge_inside _ (b::_)’ >>
  Cases_on ‘b’ >> gs [merge_inside_def]
  >- (Cases >> rw [merge_inside_def]
      >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >>
          gs [ALL_DISTINCT_APPEND] >>
          first_x_assum $ dxrule_then assume_tac >> gs []) >>
      last_x_assum $ irule >>
      gvs [ALL_DISTINCT_APPEND]) >>
  rw [] >> strip_tac >>
  dxrule_then assume_tac MEM_merge_inside >>
  gs [ALL_DISTINCT_APPEND]
QED

Theorem LENGTH_merge_inside:
  ∀l1 bL l2. LENGTH l1 = LENGTH bL ∧ LENGTH l2 = LENGTH (FILTER FST (ZIP (bL, l1))) ⇒
             LENGTH (merge_inside l1 bL l2) = LENGTH l1
Proof
  Induct >> simp [merge_inside_def] >>
  gen_tac >> Cases >> simp [] >>
  IF_CASES_TAC >> simp [merge_inside_def] >>
  Cases >> simp [merge_inside_def]
QED

Theorem MEM_FILTER_merge_inside:
  ∀l1 bL1 l2 bL2 v.
    MEM v (MAP SND (FILTER FST (ZIP (bL2, l1)))) ∧
    LENGTH l1 = LENGTH bL1 ∧
    LENGTH l2 = LENGTH (FILTER FST (ZIP (bL1, l1))) ∧
    ALL_DISTINCT (l1 ++ l2) ∧
    LIST_REL (λb2 b. b2 ⇒ b) bL2 bL1
    ⇒ ¬MEM v (merge_inside l1 bL1 l2)
Proof
  Induct >> simp [merge_inside_def] >>
  gen_tac >> Cases >> simp [] >>
  IF_CASES_TAC >> gs []
  >- (Cases >> simp [merge_inside_def, PULL_EXISTS] >>
      gen_tac >> Cases >> rw [] >> gs []
      >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [])
      >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
          strip_tac >> gs [ALL_DISTINCT_APPEND] >>
          first_x_assum $ dxrule_then assume_tac >> fs [])
      >- (last_x_assum $ drule_then irule >>
          gs [ALL_DISTINCT_APPEND])
      >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
          strip_tac >> gs [ALL_DISTINCT_APPEND] >>
          first_x_assum $ dxrule_then assume_tac >> fs [])
      >- (last_x_assum $ drule_then irule >>
          gs [ALL_DISTINCT_APPEND])) >>
  simp [merge_inside_def, PULL_EXISTS] >>
  rw []
  >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
      strip_tac >> gs [ALL_DISTINCT_APPEND] >>
      first_x_assum $ dxrule_then assume_tac >> fs []) >>
  last_x_assum $ drule_then irule >>
  gs [ALL_DISTINCT_APPEND]
QED

Theorem exp_rel_Force_Let_induction:
  ∀vLs vLf bLs bLf bL2s bL2f vL2s vL2f s x y v1 v2.
    MEM T bLs ∧
    FINITE s ∧
    ¬MEM v1 (vLf ++ vLs ++ vL2f ++ vL2s) ∧
    v2 ∉ s ∪ freevars y ∪ boundvars y ∪ boundvars x ∪ set (v1::vL2f ++ vL2s ++ vLf ++ vLs) ∧
    LENGTH bLf = LENGTH vLf ∧ LENGTH bLs = LENGTH vLs ∧
    LENGTH bL2f = LENGTH bLf ∧ LENGTH bL2s = LENGTH bLs ∧
    LIST_REL (λb2 b. b2 ⇒ b) bL2f bLf ∧ LIST_REL (λb2 b. b2 ⇒ b) bL2s bLs ∧
    LIST_REL (λ(b, b2) v. b ⇒ (b2 ⇔ v ∈ freevars x)) (ZIP (bLs, bL2s)) vLs ∧
    LENGTH vL2f = LENGTH (FILTER FST (ZIP (bLf, vLf))) ∧
    LENGTH vL2s = LENGTH (FILTER FST (ZIP (bLs, vLs))) ∧
    ALL_DISTINCT (vL2s ++ vL2f ++ vLf ++ vLs) ∧
    (∀s2. forcing_lam_rel s2 x x) ∧ (∀s2. forcing_lam_rel s2 y y) ⇒
    NRC (forcing_lam_rel s) (LENGTH vLs)
        (Let (SOME v1) (Lams (vLf ++ vLs) (lets_force (ZIP (vL2f ++ vL2s,
                                                      MAP SND (FILTER FST (ZIP (bLf++bLs, vLf++vLs))))) x)) y)
        (Let (SOME v2) (Lams (MAP SND (FILTER FST (ZIP (bL2s, vLs)))
                              ++ vLf ++ merge_inside vLs bLs vL2s)
                        (lets_force (ZIP (vL2f, MAP SND (FILTER FST (ZIP (bLf, vLf))))) x))
         (Let (SOME v1) (Lams (vLf ++ vLs) (Apps (Var v2)
                        (MAP Var (MAP SND (FILTER FST (ZIP (bL2s, vLs)))) ++
                         MAP Var vLf ++ MAP2 (λb e. if b then Force e else e) bLs (MAP Var vLs)))) y))
Proof

  Induct >> gs [] >>
  gen_tac >> gen_tac >> Cases >> gs [PULL_EXISTS] >>
  IF_CASES_TAC >> gs [GSYM ZIP_APPEND, FILTER_APPEND, lets_force_APPEND, LIST_REL_LENGTH] >>
  once_rewrite_tac [APPEND_CONS_RW]
  >- (
    gen_tac >> gen_tac >>
    Cases >> simp [lets_force_def] >>
    rpt $ gen_tac >> IF_CASES_TAC >> simp [] >>
    once_rewrite_tac [APPEND_CONS_RW]
    >- (
      rw [] >>
      rename1 ‘NRC _ _ (Let (SOME v1)
                        (Lams (vLf ++ [h] ++ vLs)
                         (lets_force (ZIP (vL2s,MAP SND (FILTER FST (ZIP (bLs,vLs)))))
                          (Let (SOME h2) (Force (Var h))
                           (lets_force
                            (ZIP (vL2f,MAP SND (FILTER FST (ZIP (bLf,vLf)))))
                            x)))) y)’ >>
      Cases_on ‘MEM T bLs’ >> gs []
      >- (
        rw [NRC_SUC_RECURSE_LEFT] >>
        ‘∃v3. v3 ∉ s ∪ freevars y ∪ boundvars x ∪ boundvars y ∪ set (v1::v2::h::h2::vL2s ++ vL2f ++ vLf ++ vLs)’
         by (‘INFINITE 𝕌(:string)’ by simp [] >>
             dxrule_then (irule_at Any) $ iffLR NOT_IN_FINITE >>
             simp [FINITE_freevars, FINITE_boundvars]) >>
        rename1 ‘v3 ∉ _ ∪ _’ >>
        last_x_assum $ qspecl_then [‘vLf ++ [h]’, ‘bLs’, ‘MAP (K F) vLf ++ [F]’, ‘xs’, ‘MAP (K F) vLf ++ [F]’,
          ‘vL2s’, ‘[]’, ‘s’,
          ‘Let (SOME h2) (Force (Var h)) (lets_force (ZIP (vL2f, MAP SND (FILTER FST (ZIP (bLf, vLf))))) x)’,
          ‘y’, ‘v1’, ‘v3’] assume_tac >>
        gs [lets_force_def, GSYM ZIP_APPEND, FILTER_APPEND, FILTER_FST_ZIP_K_F] >>
        pop_assum $ irule_at Any >>
        rpt $ conj_tac
        >- simp [boundvars_def, boundvars_lets_force]
        >- simp [LIST_REL_EL_EQN, EL_MAP]
        >- (gs [LIST_REL_EL_EQN, EL_MAP, EL_ZIP] >>
            rw [freevars_def] >>
            qspecl_then [‘vL2f’, ‘MAP SND (FILTER FST (ZIP (bLf, vLf)))’, ‘x’] mp_tac freevars_lets_force >>
            impl_tac >> gs [ALL_DISTINCT_APPEND, ALL_DISTINCT_MAP_FILTER]
            >- (rw [] >> strip_tac >>
                dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
                rename1 ‘MEM e _’ >>
                first_x_assum $ qspec_then ‘e’ assume_tac >> gs []) >>
            disch_then kall_tac >>
            eq_tac >> rw []
            >- (disj2_tac >> conj_tac
                >- (disj1_tac >> rename1 ‘EL n _’ >> strip_tac >>
                    first_x_assum $ qspec_then ‘EL n vLs’ assume_tac >>
                    gs [EL_MEM])
                >- (strip_tac >> dxrule_then assume_tac EQ_SYM >> gs [EL_MEM]))
            >- (rename1 ‘EL n _’ >>
                first_x_assum $ qspec_then ‘EL n vLs’ assume_tac >>
                gs [EL_MEM])
            >- (gs [MEM_MAP, MEM_FILTER] >>
                dxrule_then assume_tac $ iffLR MEM_EL >>
                gs [EL_ZIP] >>
                rename1 ‘EL n2 vLf ∈ _’ >>
                first_x_assum $ qspec_then ‘EL n2 vLf’ assume_tac >> gs [EL_MEM] >>
                qpat_x_assum ‘EL _ _ = EL _ _’ assume_tac >>
                dxrule_then assume_tac EQ_SYM >> gs [EL_MEM]))
        >- (gs [ALL_DISTINCT_APPEND] >> rw [] >>
            first_x_assum $ irule >> gs [])
        >- gs [forcing_lam_rel_def, forcing_lam_rel_lets_force] >>
        gs [merge_inside_def, GSYM APPEND_CONS_RW] >>
        ‘∀s a b c d. forcing_lam_rel s a b ∧ a = c ∧ b = d ⇒ forcing_lam_rel s c d’ by simp [] >>
        pop_assum irule >>
        irule_at Any forcing_lam_rel_Let_Lams_combine2 >>
        simp [] >>
        qexists_tac ‘lets_force (ZIP (vL2f,MAP SND (FILTER FST (ZIP (bLf,vLf))))) x’ >>
        qexists_tac ‘lets_force (ZIP (vL2f,MAP SND (FILTER FST (ZIP (bLf,vLf))))) x’ >>
        qexists_tac ‘merge_inside vLs bLs vL2s’ >>
        qexists_tac ‘vLs’ >> qexists_tac ‘vLf’ >>
        simp [] >>
        once_rewrite_tac [APPEND_CONS_RW] >> simp [] >>
        qexists_tac ‘h2’ >> simp [] >>
        qexists_tac ‘xs’ >> qexists_tac ‘bLs’ >> simp [] >>
        gs [ALL_DISTINCT_APPEND, boundvars_lets_force] >>
        rpt $ conj_tac
        >- (gen_tac >> rename1 ‘MEM e _ ∨ _ ⇒ _’ >> strip_tac >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gvs [])
        >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [])
        >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [])
        >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [])
        >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [])
        >- (irule ALL_DISTINCT_merge_inside >>
            simp [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gvs [])
        >- (rw [] >> strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [] >>
            rename1 ‘MEM e vL2s’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gs [])
        >- simp [ALL_DISTINCT_MAP_FILTER]
        >- (irule ALL_DISTINCT_merge_inside >>
            simp [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gvs [])
        >- (rw [] >> dxrule_then irule MEM_FILTER_merge_inside >>
            gs [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gs [])
        >- (irule ALL_DISTINCT_MAP_FILTER >> gs [LENGTH_merge_inside] >>
            irule ALL_DISTINCT_merge_inside >>
            simp [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gvs [])
        >- (qpat_x_assum ‘LIST_REL _ xs bLs’ mp_tac >>
            qpat_x_assum ‘LENGTH vL2s = LENGTH (FILTER _ _)’ mp_tac >>
            qpat_x_assum ‘LENGTH bLs = LENGTH vLs’ mp_tac >>
            ‘ALL_DISTINCT (vLs ++ vL2s)’
              by (simp [ALL_DISTINCT_APPEND] >>
                  rw [] >> strip_tac >>
                  rename1 ‘MEM e _’ >>
                  first_x_assum $ qspec_then ‘e’ assume_tac >> gs []) >>
            pop_assum mp_tac >>
            rpt $ pop_assum kall_tac >> qid_spec_tac ‘vL2s’ >>
            qid_spec_tac ‘xs’ >> qid_spec_tac ‘bLs’ >>
            Induct_on ‘vLs’ >> simp [] >>
            gen_tac >> Cases >> simp [PULL_EXISTS, PULL_FORALL] >>
            IF_CASES_TAC >> simp [merge_inside_def]
            >- (Cases >> simp [merge_inside_def] >>
                rw [ALL_DISTINCT_APPEND] >> gs []
                >- (strip_tac >> first_x_assum $ dxrule_then assume_tac >> gs [])
                >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
                    dxrule_then assume_tac MEM_merge_inside >>
                    strip_tac >> gs [])
                >- (last_x_assum irule >>
                    rpt $ first_x_assum $ irule_at $ Pos last >>
                    simp [ALL_DISTINCT_APPEND])
                >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
                    dxrule_then assume_tac MEM_merge_inside >>
                    strip_tac >> gs [])
                >- (last_x_assum irule >>
                    rpt $ first_x_assum $ irule_at $ Pos last >>
                    simp [ALL_DISTINCT_APPEND]))
            >- (rw []
                >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
                    dxrule_then assume_tac MEM_merge_inside >>
                    strip_tac >> gs [])
                >- (last_x_assum irule >>
                    rpt $ first_x_assum $ irule_at $ Pos last >>
                    simp [ALL_DISTINCT_APPEND])))
        >- simp [LENGTH_merge_inside]
        >- (rw [] >> irule merge_inside_soundness_lemma >>
            simp [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gs [])
        >- simp [forcing_lam_rel_lets_force])
      >- (dxrule_then (qspec_then ‘vLs’ assume_tac) NEG_MEM_T_IMP_K_F >>
          gs [] >>
          dxrule_then assume_tac LIST_REL_IMP_K_F >>
          gs [FILTER_FST_ZIP_K_F, lets_force_def, NRC] >>
          once_rewrite_tac [GSYM APPEND_CONS_RW] >>
          irule_at Any forcing_lam_rel_Let_Lams_Force_Var2 >>
          gs [merge_inside_def, merge_inside_K_F, MAP_Forcing_K_T] >>
          irule_at Any NRC_refl >>
          simp [forcing_lam_rel_def, forcing_lam_rel_lets_force, forcing_lam_rel_Lams, forcing_lam_rel_Apps,
                LIST_REL_APPEND_EQ, LIST_REL_EL_EQN, EL_MAP, boundvars_lets_force] >>
          gs [ALL_DISTINCT_APPEND])) >>

      rw [] >>
      rename1 ‘NRC _ _ (Let (SOME v1)
                        (Lams (vLf ++ [h] ++ vLs)
                         (lets_force (ZIP (vL2s,MAP SND (FILTER FST (ZIP (bLs,vLs)))))
                          (Let (SOME h2) (Force (Var h))
                           (lets_force
                            (ZIP (vL2f,MAP SND (FILTER FST (ZIP (bLf,vLf)))))
                            x)))) y)’ >>
      Cases_on ‘MEM T bLs’ >> gs []
      >- (
        rw [NRC_SUC_RECURSE_LEFT] >>
        ‘∃v3. v3 ∉ s ∪ freevars y ∪ boundvars x ∪ boundvars y ∪ set (v1::v2::h::h2::vL2s ++ vL2f ++ vLf ++ vLs)’
         by (‘INFINITE 𝕌(:string)’ by simp [] >>
             dxrule_then (irule_at Any) $ iffLR NOT_IN_FINITE >>
             simp [FINITE_freevars, FINITE_boundvars]) >>
        rename1 ‘v3 ∉ _ ∪ _’ >>
        last_x_assum $ qspecl_then [‘vLf ++ [h]’, ‘bLs’, ‘MAP (K F) vLf ++ [F]’, ‘xs’, ‘MAP (K F) vLf ++ [F]’,
          ‘vL2s’, ‘[]’, ‘s’,
          ‘Let (SOME h2) (Force (Var h)) (lets_force (ZIP (vL2f, MAP SND (FILTER FST (ZIP (bLf, vLf))))) x)’,
          ‘y’, ‘v1’, ‘v3’] assume_tac >>
        gs [lets_force_def, GSYM ZIP_APPEND, FILTER_APPEND, FILTER_FST_ZIP_K_F] >>
        pop_assum $ irule_at Any >>
        rpt $ conj_tac
        >- simp [boundvars_def, boundvars_lets_force]
        >- simp [LIST_REL_EL_EQN, EL_MAP]
        >- (gs [LIST_REL_EL_EQN, EL_MAP, EL_ZIP] >>
            rw [freevars_def] >>
            qspecl_then [‘vL2f’, ‘MAP SND (FILTER FST (ZIP (bLf, vLf)))’, ‘x’] mp_tac freevars_lets_force >>
            impl_tac >> gs [ALL_DISTINCT_APPEND, ALL_DISTINCT_MAP_FILTER]
            >- (rw [] >> strip_tac >>
                dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
                rename1 ‘MEM e _’ >>
                first_x_assum $ qspec_then ‘e’ assume_tac >> gs []) >>
            disch_then kall_tac >>
            eq_tac >> rw []
            >- (disj2_tac >> conj_tac
                >- (disj1_tac >> rename1 ‘EL n _’ >> strip_tac >>
                    first_x_assum $ qspec_then ‘EL n vLs’ assume_tac >>
                    gs [EL_MEM])
                >- (strip_tac >> dxrule_then assume_tac EQ_SYM >> gs [EL_MEM]))
            >- (rename1 ‘EL n _’ >>
                first_x_assum $ qspec_then ‘EL n vLs’ assume_tac >>
                gs [EL_MEM])
            >- (gs [MEM_MAP, MEM_FILTER] >>
                dxrule_then assume_tac $ iffLR MEM_EL >>
                gs [EL_ZIP] >>
                rename1 ‘EL n2 vLf ∈ _’ >>
                first_x_assum $ qspec_then ‘EL n2 vLf’ assume_tac >> gs [EL_MEM] >>
                qpat_x_assum ‘EL _ _ = EL _ _’ assume_tac >>
                dxrule_then assume_tac EQ_SYM >> gs [EL_MEM]))
        >- (gs [ALL_DISTINCT_APPEND] >> rw [] >>
            first_x_assum $ irule >> gs [])
        >- gs [forcing_lam_rel_def, forcing_lam_rel_lets_force] >>
        gs [merge_inside_def, GSYM APPEND_CONS_RW] >>
        ‘∀s a b c d. forcing_lam_rel s a b ∧ a = c ∧ b = d ⇒ forcing_lam_rel s c d’ by simp [] >>
        pop_assum irule >>
        irule_at Any forcing_lam_rel_Let_Lams_combine1 >>
        simp [] >>
        qexists_tac ‘lets_force (ZIP (vL2f,MAP SND (FILTER FST (ZIP (bLf,vLf))))) x’ >>
        qexists_tac ‘lets_force (ZIP (vL2f,MAP SND (FILTER FST (ZIP (bLf,vLf))))) x’ >>
        qexists_tac ‘merge_inside vLs bLs vL2s’ >>
        qexists_tac ‘vLs’ >> qexists_tac ‘vLf’ >>
        simp [] >>
        once_rewrite_tac [APPEND_CONS_RW] >> simp [] >>
        qexists_tac ‘h2’ >> qexists_tac ‘h’ >> simp [] >>
        qexists_tac ‘xs’ >> qexists_tac ‘bLs’ >> simp [] >>
        gs [ALL_DISTINCT_APPEND, boundvars_lets_force] >>
        rpt $ conj_tac
        >- (gen_tac >> rename1 ‘MEM e _ ∨ _ ⇒ _’ >> strip_tac >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gvs [])
        >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [])
        >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [])
        >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [])
        >- (strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [])
        >- (irule ALL_DISTINCT_merge_inside >>
            simp [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gvs [])
        >- (rw [] >> strip_tac >> dxrule_then assume_tac MEM_merge_inside >> gs [] >>
            rename1 ‘MEM e vL2s’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gs [])
        >- simp [ALL_DISTINCT_MAP_FILTER]
        >- (irule ALL_DISTINCT_merge_inside >>
            simp [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gvs [])
        >- (rw [] >> dxrule_then irule MEM_FILTER_merge_inside >>
            gs [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gs [])
        >- (irule ALL_DISTINCT_MAP_FILTER >> gs [LENGTH_merge_inside] >>
            irule ALL_DISTINCT_merge_inside >>
            simp [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gvs [])
        >- (qpat_x_assum ‘LIST_REL _ xs bLs’ mp_tac >>
            qpat_x_assum ‘LENGTH vL2s = LENGTH (FILTER _ _)’ mp_tac >>
            qpat_x_assum ‘LENGTH bLs = LENGTH vLs’ mp_tac >>
            ‘ALL_DISTINCT (vLs ++ vL2s)’
              by (simp [ALL_DISTINCT_APPEND] >>
                  rw [] >> strip_tac >>
                  rename1 ‘MEM e _’ >>
                  first_x_assum $ qspec_then ‘e’ assume_tac >> gs []) >>
            pop_assum mp_tac >>
            rpt $ pop_assum kall_tac >> qid_spec_tac ‘vL2s’ >>
            qid_spec_tac ‘xs’ >> qid_spec_tac ‘bLs’ >>
            Induct_on ‘vLs’ >> simp [] >>
            gen_tac >> Cases >> simp [PULL_EXISTS, PULL_FORALL] >>
            IF_CASES_TAC >> simp [merge_inside_def]
            >- (Cases >> simp [merge_inside_def] >>
                rw [ALL_DISTINCT_APPEND] >> gs []
                >- (strip_tac >> first_x_assum $ dxrule_then assume_tac >> gs [])
                >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
                    dxrule_then assume_tac MEM_merge_inside >>
                    strip_tac >> gs [])
                >- (last_x_assum irule >>
                    rpt $ first_x_assum $ irule_at $ Pos last >>
                    simp [ALL_DISTINCT_APPEND])
                >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
                    dxrule_then assume_tac MEM_merge_inside >>
                    strip_tac >> gs [])
                >- (last_x_assum irule >>
                    rpt $ first_x_assum $ irule_at $ Pos last >>
                    simp [ALL_DISTINCT_APPEND]))
            >- (rw []
                >- (dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
                    dxrule_then assume_tac MEM_merge_inside >>
                    strip_tac >> gs [])
                >- (last_x_assum irule >>
                    rpt $ first_x_assum $ irule_at $ Pos last >>
                    simp [ALL_DISTINCT_APPEND])))
        >- simp [LENGTH_merge_inside]
        >- (rw [] >> irule merge_inside_soundness_lemma >>
            simp [ALL_DISTINCT_APPEND] >>
            rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
            first_x_assum $ qspec_then ‘e’ assume_tac >> gs [])
        >- (qspecl_then [‘vL2f’, ‘MAP SND (FILTER FST (ZIP (bLf, vLf)))’, ‘x’] mp_tac freevars_lets_force >>
            impl_tac >> gs [ALL_DISTINCT_APPEND, ALL_DISTINCT_MAP_FILTER]
            >- (rw [] >> strip_tac >>
                dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
                rename1 ‘MEM e _’ >>
                first_x_assum $ qspec_then ‘e’ assume_tac >> gs []) >>
            disch_then kall_tac >>
            strip_tac >> dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
            first_x_assum $ qspec_then ‘h’ assume_tac >> gs [])
        >- simp [forcing_lam_rel_lets_force])
      >- (dxrule_then (qspec_then ‘vLs’ assume_tac) NEG_MEM_T_IMP_K_F >>
          gs [] >>
          dxrule_then assume_tac LIST_REL_IMP_K_F >>
          gs [FILTER_FST_ZIP_K_F, lets_force_def, NRC] >>
          once_rewrite_tac [GSYM APPEND_CONS_RW] >>
          irule_at Any forcing_lam_rel_Let_Lams_Force_Var >>
          gs [merge_inside_def, merge_inside_K_F, MAP_Forcing_K_T] >>
          irule_at Any NRC_refl >>
          simp [forcing_lam_rel_def, forcing_lam_rel_lets_force, forcing_lam_rel_Lams, forcing_lam_rel_Apps,
                LIST_REL_APPEND_EQ, LIST_REL_EL_EQN, EL_MAP, boundvars_lets_force] >>
          gs [ALL_DISTINCT_APPEND] >>
          qspecl_then [‘vL2f’, ‘MAP SND (FILTER FST (ZIP (bLf, vLf)))’, ‘x’] mp_tac freevars_lets_force >>
          impl_tac >> gs [ALL_DISTINCT_APPEND, ALL_DISTINCT_MAP_FILTER]
          >- (rw [] >> strip_tac >>
              dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
              rename1 ‘MEM e _’ >>
              first_x_assum $ qspec_then ‘e’ assume_tac >> gs []) >>
          disch_then kall_tac >>
          strip_tac >> dxrule_then assume_tac MEM_MAP_FILTER_ZIP >>
          first_x_assum $ qspec_then ‘h’ assume_tac >> gs [])) >>
  simp [merge_inside_def] >> rw [NRC] >>
  irule_at Any forcing_lam_rel_Let >>
  irule_at Any $ iffRL forcing_lam_rel_Lams >>
  irule_at Any $ iffRL forcing_lam_rel_lets_force >>
  irule_at Any $ iffRL forcing_lam_rel_lets_force >>
  first_assum $ irule_at $ Pos hd >>
  first_assum $ irule_at $ Pos hd >>
  rename1 ‘Let (SOME v1) (Lams (vLf ++ [h] ++ vLs)
                          (lets_force (ZIP (vL2s, MAP SND (FILTER FST (ZIP (bLs, vLs)))))
                           (lets_force (ZIP (vL2f, MAP SND (FILTER FST (ZIP (bLf, vLf))))) x))) y’ >>
  last_x_assum $ qspecl_then [‘vLf ++ [h]’, ‘bLs’, ‘bLf ++ [F]’, ‘xs’, ‘bL2f ++ [F]’,
                              ‘vL2s’, ‘vL2f’, ‘s’, ‘x’, ‘y’, ‘v1’, ‘v2’] assume_tac >>
  gs [GSYM ZIP_APPEND, FILTER_APPEND, lets_force_APPEND, LIST_REL_LENGTH] >>
  once_rewrite_tac [APPEND_CONS_RW] >> simp []
QED

Theorem exp_rel_Force_Let_lemma:
 MEM T bL ∧
 LENGTH bL = LENGTH vL ∧
 LIST_REL (λb2 b. b2 ⇒ b) bL2 bL ∧
 LENGTH vL2 = LENGTH (FILTER FST (ZIP (bL, vL))) ∧
 ALL_DISTINCT (vL2 ++ vL) ∧ FINITE s ∧
 LIST_REL (λ(b, b2) v. b ⇒ (b2 ⇔ v ∈ freevars x)) (ZIP (bL, bL2)) vL ∧
 ¬MEM v1 (vL ++ vL2) ∧
 v2 ∉ s ∪ set (v1::vL ++ vL2) ∪ boundvars x ∪ boundvars y ∪ freevars y ∧
 (∀s2. forcing_lam_rel s2 x x) ∧ (∀s2. forcing_lam_rel s2 y y) ⇒
 NRC (forcing_lam_rel s) (LENGTH vL)
     (Let (SOME v1) (Lams vL (lets_force (ZIP (vL2,MAP SND (FILTER FST (ZIP (bL,vL))))) x)) y)
     (Let (SOME v2) (Lams (MAP SND (FILTER FST (ZIP (bL2,vL))) ++ merge_inside vL bL vL2) x)
      (Let (SOME v1) (Lams vL (Apps (Var v2)
                               (MAP Var (MAP SND (FILTER FST (ZIP (bL2,vL)))) ++
                                MAP2 (λb e. if b then Force e else e) bL (MAP Var vL)))) y))
Proof
  rw [] >>
  qspecl_then [‘vL’, ‘[]’, ‘bL’, ‘[]’, ‘bL2’, ‘[]’, ‘vL2’, ‘[]’, ‘s’, ‘x’, ‘y’, ‘v1’, ‘v2’]
              assume_tac exp_rel_Force_Let_induction >>
  gs [lets_force_def] >>
  first_x_assum irule >>
  gs [LIST_REL_EL_EQN]
QED

Theorem exp_rel_NRC:
  ∀s x y. exp_rel s x y ⇒ FINITE s ⇒
          ∃n. NRC (forcing_lam_rel s) n x y
Proof
  qspec_then ‘(λs x y. FINITE s ⇒
                       ∃n. NRC (forcing_lam_rel s) n x y)’
             mp_tac exp_rel_strongind >>
  impl_tac >> rw [forcing_lam_rel_def] >> gs []
  >- (qexists_tac ‘0’ >> gs [])
  >- (irule_at Any NRC_rel_Prim >>
      simp [forcing_lam_rel_def] >>
      irule_at Any LIST_REL_NRC_MAX_1 >>
      gs [LIST_REL_CONJ, LIST_REL_EL_EQN] >>
      rw [] >> last_x_assum $ dxrule_then assume_tac >>
      dxrule_then irule forcing_lam_rel_refl)
  >- (irule_at Any NRC_rel_Monad >>
      simp [forcing_lam_rel_def] >>
      irule_at Any LIST_REL_NRC_MAX_1 >>
      gs [LIST_REL_CONJ, LIST_REL_EL_EQN] >>
      rw [] >> last_x_assum $ dxrule_then assume_tac >>
      dxrule_then irule forcing_lam_rel_refl)
  >- (irule_at Any NRC_rel_App_MAX >>
      gs [forcing_lam_rel_def] >>
      dxrule_then (irule_at Any) forcing_lam_rel_refl >>
      dxrule_then (irule_at Any) forcing_lam_rel_refl >>
      first_x_assum $ irule_at Any >>
      first_x_assum $ irule_at Any)
  >- (irule_at Any NRC_rel_Lam >>
      gs [forcing_lam_rel_def] >>
      first_x_assum $ irule_at Any)
  >- (irule_at Any NRC_rel_Letrec_MAX >>
      gs [forcing_lam_rel_def, rel_uses_Letrecs_def, LIST_REL_CONJ] >>
      rw []
      >- (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac >>
          qpat_x_assum ‘EVERY ok_bind _’ mp_tac >>
          rpt $ pop_assum kall_tac >>
          rw [EVERY_EL, LIST_REL_EL_EQN] >> gs [EL_MAP] >>
          last_x_assum $ drule_then assume_tac >>
          last_x_assum $ drule_then assume_tac >>
          rename1 ‘forcing_lam_rel _ e’ >>
          Cases_on ‘e’ >> gs [ok_bind_def, forcing_lam_rel_def])
      >- dxrule_then irule forcing_lam_rel_refl
      >- (gs [LIST_REL_EL_EQN] >> gen_tac >> strip_tac >>
          last_x_assum $ dxrule_then assume_tac >>
          dxrule_then irule forcing_lam_rel_refl)
      >- (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac >>
          rpt $ qpat_x_assum ‘EVERY ok_bind _’ mp_tac >>
          rpt $ pop_assum kall_tac >>
          rw [EVERY_EL, LIST_REL_EL_EQN] >> gs [EL_MAP] >>
          last_x_assum $ drule_then assume_tac >>
          last_x_assum $ drule_then assume_tac >>
          rename1 ‘forcing_lam_rel _ e’ >>
          Cases_on ‘e’ >> gs [ok_bind_def, forcing_lam_rel_def])
      >- first_x_assum $ irule_at Any)
  >- (irule_at Any NRC_rel_Let_MAX >>
      gs [forcing_lam_rel_def] >>
      dxrule_then (irule_at Any) forcing_lam_rel_refl >>
      dxrule_then (irule_at Any) forcing_lam_rel_refl >>
      first_x_assum $ irule_at Any >>
      first_x_assum $ irule_at Any)

  >- (irule_at Any NRC_ADD_I >>
      irule_at (Pos hd) exp_rel_Force_Let_lemma >> simp [] >>
      first_assum $ irule_at $ Pos hd >>
      first_assum $ irule_at $ Pos $ el 2 >> simp [] >>
      irule_at (Pos last) NRC_rel_Let_MAX >>
      simp [forcing_lam_rel_def, forcing_lam_rel_Lams, forcing_lam_rel_Apps, LIST_REL_APPEND_EQ] >>
      drule_then (irule_at Any) forcing_lam_rel_refl >>
      drule_then (irule_at Any) forcing_lam_rel_refl >>
      irule_at Any NRC_rel_Lams >> simp [forcing_lam_rel_Lam] >>
      irule_at Any NRC_rel_Let_MAX >>
      simp [forcing_lam_rel_def, forcing_lam_rel_Lams, forcing_lam_rel_Apps, LIST_REL_APPEND_EQ] >>
      drule_then (irule_at Any) forcing_lam_rel_refl >>
      irule_at Any NRC_rel_Lams >> simp [forcing_lam_rel_Lam] >>
      irule_at (Pos hd) $ iffRL NRC_0 >> simp [] >>
      irule_at Any NRC_change_rel >> first_x_assum $ irule_at Any >>
      irule_at Any NRC_change_rel >> first_x_assum $ irule_at Any >>
      rw []
      >- (dxrule_then irule forcing_lam_rel_subset >>
          simp [SUBSET_DEF])
      >- simp [LIST_REL_EL_EQN, EL_MAP, forcing_lam_rel_Var]
      >- (simp [LIST_REL_EL_EQN, EL_MAP, EL_MAP2] >> rw [forcing_lam_rel_def])
      >- (gs [ALL_DISTINCT_APPEND] >>
          rw [] >> strip_tac >> rename1 ‘MEM e _’ >>
          first_x_assum $ qspec_then ‘e’ assume_tac >> gs [])
      >- dxrule_then irule forcing_lam_rel_refl
      >- dxrule_then irule forcing_lam_rel_refl)

  >- (irule_at Any NRC_rel_If_MAX >>
      gs [forcing_lam_rel_def] >>
      dxrule_then (irule_at Any) forcing_lam_rel_refl >>
      dxrule_then (irule_at Any) forcing_lam_rel_refl >>
      dxrule_then (irule_at Any) forcing_lam_rel_refl >>
      first_x_assum $ irule_at Any >>
      first_x_assum $ irule_at Any >>
      first_x_assum $ irule_at Any)
  >- (irule_at Any NRC_rel_Delay >>
      gs [forcing_lam_rel_def] >>
      first_x_assum $ irule_at Any)
  >- (irule_at Any NRC_rel_Force >>
      gs [forcing_lam_rel_def] >>
      first_x_assum $ irule_at Any)
  >- (irule_at Any NRC_rel_MkTick >>
      gs [forcing_lam_rel_def] >>
      first_x_assum $ irule_at Any)
QED

Theorem exp_rel_semantics:
  exp_rel {} x y ∧
  pure_semantics$safe_itree (semantics x Done []) ∧
  closed x ⇒
  semantics x Done [] = semantics y Done []
Proof
  rw [] >>
  irule NRC_semantics_safe_full >> simp [] >>
  first_x_assum $ irule_at $ Pos last >>
  qexists_tac ‘forcing_lam_rel {}’ >>
  gs [exp_rel_NRC, forcing_lam_rel_semantics] >>
  rw [] >>
  dxrule_then assume_tac forcing_lam_rel_freevars >>
  gs [closed_def]
QED

val _ = export_theory ();
