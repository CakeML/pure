(*
  Description required
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory;

val _ = new_theory "thunk_Delay_Lam";


Definition ok_bind_def[simp]:
  ok_bind (Delay x) = T ∧
  ok_bind (Lam s x) = T ∧
  ok_bind _ = F
End

Definition is_Lam_def[simp]:
  is_Lam (Lam s x) = T ∧
  is_Lam _ = F
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
[~Letrec_Delay_Lam:]
  (∀f g x y vL bL.
     MAP FST f = MAP FST g ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     ALL_DISTINCT vL ∧ ALL_DISTINCT (MAP FST g) ∧
     LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧
     EVERY (λv. EVERY (λ(v2, e). v ≠ v2) g ∧ EVERY (λ(v2, e). v ∉ freevars e) g
                ∧ EVERY (λ(v2, e). v ∉ boundvars e) g
                ∧ v ∉ freevars x ∧ v ∉ boundvars x) vL ∧
     exp_rel x y ⇒
     exp_rel (Letrec f x) (Letrec (FLAT $ MAP2 (λ(v1, e) (v2, b). case e of
                                       | Delay e2 => if is_Lam e2 ∧ b
                                                     then [(v2, e2);(v1, Delay (Var v2))]
                                                     else [v1, e]
                                       | _ => [v1, e]) g (ZIP (vL, bL))) y)) ∧
[~Let_Delay_Lam:]
  (∀opt v x1 y1 x2 y2.
     is_Lam x1 ∧ exp_rel x1 x2 ∧
     exp_rel y1 y2 ∧
     v ∉ freevars y1 ∧ (∀s. opt = SOME s ⇒ s ≠ v)
     ⇒ exp_rel (Let opt (Delay x1) y1) (Let (SOME v) x2 (Let opt (Delay (Var v)) y2))) ∧
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
[v_rel_Recclosure_Delay_Lam:]
  (∀f g n vL bL.
     MAP FST f = MAP FST g ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     ALL_DISTINCT vL ∧ ALL_DISTINCT (MAP FST g) ∧
     LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧
     MEM n (MAP FST f) ∧
     EVERY (λv. ¬MEM v (MAP FST g) ∧ EVERY (λ(v2, e). v ∉ freevars e) g
                ∧ EVERY (λ(v2, e). v ∉ boundvars e) g
                ∧ v ∉ freevars x ∧ v ∉ boundvars x) vL ⇒
     v_rel (Recclosure f n)
           (Recclosure (FLAT $ MAP2 (λ(v1, e) (v2, b).
                                       case e of
                                       | Delay e2 => if is_Lam e2 ∧ b
                                                     then [(v2, e2);(v1, Delay (Var v2))]
                                                     else [v1, e]
                                       | _ => [v1, e]) g (ZIP (vL, bL))) n)) ∧
[v_rel_Closure_Recclosure:]
  (∀f g vL bL i s ef.
     MAP FST f = MAP FST g ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     ALL_DISTINCT vL ∧ ALL_DISTINCT (MAP FST g) ∧
     LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧
     EVERY (λv. ¬MEM v (MAP FST g) ∧ EVERY (λ(v2, e). v ∉ freevars e) g
                ∧ EVERY (λ(v2, e). v ∉ boundvars e) g
                ∧ v ∉ freevars x ∧ v ∉ boundvars x) vL ∧
     i < LENGTH vL ∧ SND (EL i f) = Delay (Lam s ef) ∧ EL i bL ⇒
     v_rel (Closure s (subst (FILTER (λ(v,e). v≠s) (MAP (λ(v,x).(v, Recclosure f v)) f)) ef))
           (Recclosure (FLAT $ MAP2 (λ(v1, e) (v2, b).
                                       case e of
                                       | Delay e2 => if is_Lam e2 ∧ b
                                                     then [(v2, e2);(v1, Delay (Var v2))]
                                                     else [v1, e]
                                       | _ => [v1, e]) g (ZIP (vL, bL))) (EL i vL))) ∧
[v_rel_Thunk_INL:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INL v)) (Thunk (INL w))) ∧
[v_rel_Thunk_INR:]
  (∀x y.
     exp_rel x y ⇒
     v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_Thunk_INR_Lam:]
  (∀x y s.
     exp_rel x y ⇒
     v_rel (Thunk (INR (Lam s x))) (Thunk (INR (Value (Closure s y))))) ∧
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
  |> LIST_CONJ;

Theorem FILTERED:
  ∀vs n. ALOOKUP (REVERSE (FILTER (λ(n', x). n' ≠ n) vs)) n = NONE
Proof
  Induct using SNOC_INDUCT >> gvs [FORALL_PROD, FILTER_SNOC] >>
  rw [] >> gvs [REVERSE_SNOC]
QED

Theorem is_Lam_subst:
  ∀x vs. is_Lam x ⇒ is_Lam (subst vs x)
Proof
  Cases >> gvs [is_Lam_def, subst_def]
QED

Theorem exp_rel_Apps:
  ∀ys f e. exp_rel (Apps f ys) e ⇔
             ∃ys' f'. e = Apps f' ys' ∧ exp_rel f f' ∧ LIST_REL exp_rel ys ys'
Proof
  Induct \\ gvs [exp_rel_def]
  \\ rpt $ gen_tac \\ eq_tac \\ rw []
  >- (Q.REFINE_EXISTS_TAC ‘_::_’ \\ gvs []
      \\ irule_at (Pos hd) EQ_REFL
      \\ simp [])
  \\ simp []
  \\ irule_at (Pos hd) EQ_REFL \\ gvs []
QED

Theorem exp_rel_Lams:
  ∀vL x y. exp_rel (Lams vL x) y ⇔
             ∃y'. y = Lams vL y' ∧ exp_rel x y'
Proof
  Induct \\ gvs [exp_rel_def]
  \\ rpt $ gen_tac \\ eq_tac \\ rw []
  \\ metis_tac []
QED

Theorem exp_rel_is_Lam:
  ∀x y. exp_rel x y ⇒ is_Lam x = is_Lam y
Proof
  Cases >> gvs [exp_rel_def, is_Lam_def, PULL_EXISTS] >>
  rw [] >> gvs [is_Lam_def]
QED

Theorem Letrec_Delay_SUBSET:
  ∀g vL bL. LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ⇒
         set (MAP FST (FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                       | Delay e2 => if is_Lam e2 ∧ b
                                                     then [(v2, e2);(v1, Delay (Var v2))]
                                                     else [v1, e]
                                       | _ => [v1, e]) g (ZIP (vL, bL)))))
             ⊆ set (MAP FST g) ∪ set vL
Proof
  Induct >> gvs [FORALL_PROD] >>
  gen_tac >> gen_tac >> Cases >> Cases >> gs [Once INSERT_SING_UNION] >>
  strip_tac >> last_x_assum $ dxrule_then assume_tac >>
  CASE_TAC
  >~[‘is_Lam e2’]
  >- (IF_CASES_TAC >> once_rewrite_tac [INSERT_SING_UNION] >> gs [] >>
      irule SUBSET_TRANS >> last_x_assum $ irule_at Any >> rw [SUBSET_DEF]) >>
  gs [] >> irule SUBSET_TRANS >> last_x_assum $ irule_at Any >>
  rw [SUBSET_DEF]
QED

Theorem Letrec_Delay_SUBSET2:
  ∀g vL bL. LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ⇒
         set (MAP FST g) ⊆ set (MAP FST (FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                       | Delay e2 => if is_Lam e2 ∧ b
                                                     then [(v2, e2);(v1, Delay (Var v2))]
                                                     else [v1, e]
                                       | _ => [v1, e]) g (ZIP (vL, bL)))))
Proof
  Induct >> gvs [FORALL_PROD] >>
  gen_tac >> gen_tac >> Cases >> Cases >> gs [Once INSERT_SING_UNION] >>
  strip_tac >> last_x_assum $ dxrule_then assume_tac >>
  CASE_TAC
  >~[‘is_Lam e2’]
  >- (IF_CASES_TAC >> once_rewrite_tac [INSERT_SING_UNION] >> gs [] >>
      irule SUBSET_TRANS >> last_x_assum $ drule_then $ irule_at Any >> rw [SUBSET_DEF]) >>
  gs [] >> irule SUBSET_TRANS >> last_x_assum $ drule_then $ irule_at Any >>
  rw [SUBSET_DEF]
QED

Theorem Letrec_Delay_SUBSET3:
  ∀g vL bL. LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ⇒
         BIGUNION (set (MAP (λ(n, e). freevars e)
                        (FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                       | Delay e2 => if is_Lam e2 ∧ b
                                                     then [(v2, e2);(v1, Delay (Var v2))]
                                                     else [v1, e]
                                       | _ => [v1, e]) g (ZIP (vL, bL))))))
                  ⊆ BIGUNION (set (MAP (λ(n, e). freevars e) g))
                  ∪ set (MAP FST
                         (FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                       | Delay e2 => if is_Lam e2 ∧ b
                                                     then [(v2, e2);(v1, Delay (Var v2))]
                                                     else [v1, e]
                                       | _ => [v1, e]) g (ZIP (vL, bL)))))
Proof
  Induct >> gvs [FORALL_PROD] >>
  gen_tac >> gen_tac >> Cases >> Cases >> gs [Once INSERT_SING_UNION] >>
  strip_tac >> last_x_assum $ dxrule_then $ dxrule_then assume_tac >>
  CASE_TAC
  >~[‘is_Lam e2’]
  >- (IF_CASES_TAC >> gs [freevars_def, GSYM UNION_ASSOC] >> rw [] >>
      irule SUBSET_TRANS >> last_x_assum $ irule_at Any >> rw [SUBSET_DEF]) >>
  gs [GSYM UNION_ASSOC] >> irule SUBSET_TRANS >> last_x_assum $ irule_at Any >>
  rw [SUBSET_DEF]
QED

Theorem Letrec_Delay_SUBSET4:
  ∀g vL bL. LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ⇒
         BIGUNION (set (MAP (λ(n, e). freevars e) g)) ⊆
         BIGUNION (set (MAP (λ(n, e). freevars e)
                        (FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                       | Delay e2 => if is_Lam e2 ∧ b
                                                     then [(v2, e2);(v1, Delay (Var v2))]
                                                     else [v1, e]
                                       | _ => [v1, e]) g (ZIP (vL, bL))))))
Proof
  Induct >> gvs [FORALL_PROD] >>
  gen_tac >> gen_tac >> Cases >> Cases >> gs [Once INSERT_SING_UNION] >>
  strip_tac >> last_x_assum $ dxrule_then $ dxrule_then assume_tac >>
  CASE_TAC
  >~[‘is_Lam e2’]
  >- (IF_CASES_TAC >> gs [freevars_def, GSYM UNION_ASSOC] >> rw [] >>
      irule SUBSET_TRANS >> last_x_assum $ irule_at Any >> rw [SUBSET_DEF]) >>
  gs [GSYM UNION_ASSOC] >> irule SUBSET_TRANS >> last_x_assum $ irule_at Any >>
  rw [SUBSET_DEF]
QED

Theorem DIFF_DIFF_SUBSET:
  ∀s1 s2 s3 s4. s1 ∪ s4 ⊆ s3 ∪ s4 ∧ (∀x. x ∈ s4 ∧ x ∉ s2 ⇒ x ∉ s1)
                ⇒ s1 DIFF s2 ⊆ s3 DIFF s4
Proof
  rw [SUBSET_DEF, IN_DIFF]
  >- (last_x_assum $ drule_then assume_tac \\ gs [])
  \\ strip_tac \\ gvs []
QED

Theorem DIFF_DIFF_EQ:
  ∀s1 s2 s3 s4. s1 ∪ s4 = s3 ∪ s4 ∧ (∀x. x ∈ s4 ∧ x ∉ s2 ⇒ x ∉ s1)
                ∧ s2 ⊆ s4
                ⇒ s1 DIFF s2 = s3 DIFF s4
Proof
  rw [SET_EQ_SUBSET]
  >- (irule DIFF_DIFF_SUBSET \\ gvs [])
  \\ irule SUBSET_TRANS
  \\ qexists_tac ‘s1 DIFF s4’
  \\ gvs [SUBSET_DEF, IN_DIFF] \\ rw []
  >- (first_x_assum $ dxrule_then assume_tac \\ gvs [])
  \\ strip_tac \\ gvs []
QED

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
  Induct using freevars_ind >> gvs [exp_rel_def, PULL_EXISTS, freevars_def] >> rw []
  >- (AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      gvs [EL_MAP, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN])
  >- (rpt $ first_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rpt $ first_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rpt $ first_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (first_x_assum $ dxrule_then assume_tac >>
      dxrule_then assume_tac exp_rel_Delay >>
      first_x_assum $ dxrule_then assume_tac >>
      gvs [freevars_def, DIFF_SAME_UNION] >>
      AP_TERM_TAC >>
      gvs [SET_EQ_SUBSET, SUBSET_DEF, IN_DIFF])
  >- (rpt $ first_x_assum $ dxrule_then assume_tac >> gvs [freevars_def])
  >- (first_x_assum $ dxrule_then assume_tac >>
      dxrule_then assume_tac exp_rel_Delay >>
      first_x_assum $ dxrule_then assume_tac >>
      gvs [freevars_def, DIFF_SAME_UNION] >>
      AP_TERM_TAC >>
      gvs [SET_EQ_SUBSET, SUBSET_DEF, IN_DIFF])
  >- (rpt $ first_x_assum $ dxrule_then assume_tac >> gvs [freevars_def])
  >- (first_x_assum $ dxrule_then assume_tac >> gvs [freevars_def] >>
      AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
      irule LIST_EQ >>
      gvs [EL_MAP, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >>
      rw [] >> first_x_assum $ drule_then assume_tac >>
      rename1 ‘_ (EL i f) = _ (EL i g)’ >>
      qabbrev_tac ‘p1 = EL i f’ >> qabbrev_tac ‘p2 = EL i g’ >>
      PairCases_on ‘p1’ >> PairCases_on ‘p2’ >>
      last_x_assum $ drule_then assume_tac >> gvs [])
  >- (first_x_assum $ dxrule_then assume_tac
      \\ gvs [freevars_def]
      \\ irule DIFF_DIFF_EQ
      \\ gvs [Letrec_Delay_SUBSET2]
      \\ conj_tac
      >- (rw []
          \\ dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET
          \\ gvs [SUBSET_DEF]
          \\ first_x_assum $ dxrule_then assume_tac \\ gs [EVERY_MEM]
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gvs [MEM_EL, PULL_EXISTS]
          \\ rename1 ‘x2 ∉ s ∨ _’ \\ Cases_on ‘x2 ∈ s’ \\ gs []
          \\ rpt $ strip_tac \\ gs [EL_MAP, LIST_REL_EL_EQN]
          \\ rpt $ first_x_assum $ drule_then assume_tac
          \\ rename1 ‘exp_rel (SND p1) (SND p2)’ \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’ \\ gs []
          \\ first_x_assum $ drule_then assume_tac \\ gs [])
      \\ rename1 ‘LIST_REL exp_rel (MAP SND f) (MAP SND g)’
      \\ ‘MAP (λ(n, e). freevars e) f = MAP (λ(n, e). freevars e) g’
        by (irule LIST_EQ \\ rw [EL_MAP]
            \\ gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP]
            \\ rpt $ first_x_assum $ drule_then assume_tac
            \\ rename1 ‘_ p1 = _ p2’ \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’ \\ gs [])
      \\ gvs [SET_EQ_SUBSET] \\ rw [] \\ gvs [GSYM UNION_ASSOC]
      >- (irule SUBSET_TRANS \\ drule_then (drule_then $ irule_at Any) Letrec_Delay_SUBSET4
          \\ rw [SUBSET_DEF])
      \\ irule SUBSET_TRANS
      \\ irule_at Any Letrec_Delay_SUBSET3 \\ gvs []
      \\ rw [SUBSET_DEF])
QED

Theorem Letrec_Delay_boundvars:
  ∀g vL bL s. LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧
              MEM s (MAP (λ(n, x). boundvars x) g)
              ⇒ MEM s (MAP (λ(n, x). boundvars x)
                       (FLAT (MAP2 (λ(v1, e) (v2, b).
                                      case e of
                                      | Delay e2 => if is_Lam e2 ∧ b
                                                    then [(v2, e2); (v1, Delay (Var v2))]
                                                    else [(v1, e)]
                                      | _ => [(v1, e)]) g (ZIP (vL, bL)))))
Proof
  Induct >> gvs [FORALL_PROD] >>
  gen_tac >> gen_tac >> Cases >> Cases >> rw []
  >- (disj1_tac >>
      CASE_TAC >> rw [boundvars_def]) >>
  disj2_tac >> last_x_assum irule >>
  gvs []
QED

Theorem exp_rel_boundvars:
  ∀x y. exp_rel x y ⇒ boundvars x ⊆ boundvars y
Proof
  Induct using freevars_ind >>
  gvs [exp_rel_def, PULL_EXISTS, boundvars_def, SUBSET_DEF] >> rw [] >>
  gvs [boundvars_def]
  >- (gvs [MEM_EL, EL_MAP, LIST_REL_EL_EQN, PULL_EXISTS] >>
      first_assum $ irule_at Any >> first_x_assum $ drule_then assume_tac >>
      first_x_assum $ drule_then $ drule_then assume_tac >> gvs [EL_MAP])
  >- gvs [exp_rel_def, PULL_EXISTS, boundvars_def]
  >- gvs [exp_rel_def, PULL_EXISTS, boundvars_def]
  >- (gvs [LIST_REL_EL_EQN, MEM_EL, EL_MAP, PULL_EXISTS] >>
      rpt $ first_x_assum $ drule_then assume_tac >>
      rename1 ‘exp_rel (SND (EL n f)) (SND (EL _ g))’ >> Cases_on ‘EL n f’ >> gvs [] >>
      first_x_assum  $ drule_all_then assume_tac >>
      disj1_tac >> disj2_tac >> first_assum $ irule_at Any >>
      Cases_on ‘EL n g’ >> gvs [EL_MAP])
  >- (drule_then (drule_then assume_tac) Letrec_Delay_boundvars >>
      gvs [MEM_EL, PULL_EXISTS, EL_MAP, LIST_REL_EL_EQN] >>
      rpt $ first_x_assum $ drule_then assume_tac >>
      disj1_tac >> disj2_tac >> gvs [] >>
      first_x_assum $ irule_at Any >>
      rename1 ‘exp_rel (SND p1) (SND p2)’ >>
      Cases_on ‘p1’ >> Cases_on ‘p2’ >> gvs [] >>
      first_x_assum $ dxrule_then $ dxrule_then assume_tac >> gvs [])
  >- (drule_then (drule_then assume_tac) Letrec_Delay_SUBSET2 >>
      gvs [SUBSET_DEF])
QED

Theorem FILTER_COMM:
  ∀l f1 f2. FILTER f1 (FILTER f2 l) = FILTER f2 (FILTER f1 l)
Proof
  Induct >> rw []
QED

Theorem FILTER_CONJ:
  ∀l f1 f2. FILTER f1 (FILTER f2 l) = FILTER (λx. f1 x ∧ f2 x) l
Proof
  Induct >> rw [] >> gvs []
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

Theorem change_Filter:
  ∀e s1 s2 vs.
    (∀n. n ∈ s1 ∪ s2 ∧ n ∉ s1 ∩ s2 ⇒ n ∉ freevars e ∩ set (MAP FST vs))
    ⇒ subst (FILTER (λ(n, v). n ∉ s1) vs) e = subst (FILTER (λ(n, v). n ∉ s2) vs) e
Proof
  Induct using freevars_ind >> rw [subst_def] >> gvs [freevars_def]
  >- (rpt $ first_x_assum mp_tac
      \\ Induct_on ‘vs’ using SNOC_INDUCT
      \\ gvs [FORALL_PROD, FILTER_SNOC, MAP_SNOC, MEM_SNOC] \\ rw [REVERSE_SNOC]
      \\ rpt $ IF_CASES_TAC
      \\ gvs []
      \\ first_x_assum irule \\ gvs []
      \\ strip_tac \\ gvs [])
  >- (irule LIST_EQ >> gvs [EL_MAP, MEM_EL, PULL_EXISTS, freevars_def] >>
      rpt $ strip_tac >> last_x_assum irule >> rw [] >>
      rename1 ‘n ∈ _’ >> first_x_assum $ qspecl_then [‘n’] assume_tac >> gs [] >>
      rename1 ‘EL n2 xs’ >>
      first_x_assum $ qspecl_then [‘freevars (EL n2 xs)’] assume_tac >> gs [] >>
      first_x_assum $ qspecl_then [‘n2’] assume_tac >> gs [EL_MAP])
  >- (first_x_assum irule >> rw [] >> rename1 ‘n ∈ _’ >>
      first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [])
  >- (first_x_assum irule >> rw [] >> rename1 ‘n ∈ _’ >>
      first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [])
  >- (first_x_assum irule >> rw [] >> rename1 ‘n ∈ _’ >>
      first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [])
  >- (first_x_assum irule >> rw [] >> rename1 ‘n ∈ _’ >>
      first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [])
  >- (first_x_assum irule >> rw [] >> rename1 ‘n ∈ _’ >>
      first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [])
  >- (once_rewrite_tac [FILTER_COMM] >>
      last_x_assum $ irule >> rw [] >>
      rename1 ‘n ∈ _’ >> last_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [] >>
      disj2_tac >> gvs [MEM_MAP, MEM_FILTER, FORALL_PROD])
  >- (first_x_assum irule >> rw [] >> rename1 ‘n ∈ _’ >>
      first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [])
  >- (first_x_assum irule >> rw [] >> rename1 ‘n ∈ _’ >>
      first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [])
  >- (first_x_assum irule >> rw [] >> rename1 ‘n ∈ _’ >>
      first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [])
  >- (once_rewrite_tac [FILTER_COMM] >>
      last_x_assum $ irule >> rw [] >>
      rename1 ‘n ∈ _’ >> last_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [] >>
      disj2_tac >> gvs [MEM_MAP, MEM_FILTER, FORALL_PROD])
  >- (irule LIST_EQ >> rw [EL_MAP] >>
      rename1 ‘EL x f’ >> qabbrev_tac ‘pair = EL x f’ >> PairCases_on ‘pair’ >>
      gvs [Once MEM_EL, PULL_EXISTS] >> last_x_assum $ drule_then assume_tac >> gs [] >>
      once_rewrite_tac [FILTER_COMM] >>
      last_x_assum $ irule >> rw [] >>
      rename1 ‘n ∈ _’ >> last_x_assum $ qspecl_then [‘n’] assume_tac >> gvs []
      >- (pop_assum $ qspecl_then [‘freevars (SND (EL x f))’] assume_tac >> gvs [] >>
          disj2_tac >> gvs [MEM_MAP, MEM_FILTER, FORALL_PROD] >>
          first_x_assum $ qspecl_then [‘FST (EL x f)’, ‘SND (EL x f)’] assume_tac >>
          gvs [MEM_EL]) >>
      gvs [MEM_MAP, MEM_FILTER]
      >- (disj2_tac >> rw [] >> disj1_tac >> rename1 ‘FST y1 = FST y2’ >> PairCases_on ‘y2’ >> gvs [] >>
          first_x_assum $ irule_at Any >> gvs [])
      >- (first_x_assum $ qspecl_then [‘freevars (SND (EL x f))’] assume_tac >> gs [] >>
          pop_assum $ qspecl_then [‘EL x f’] assume_tac >> gvs [MEM_EL])
      >- (disj2_tac >> rw [] >> disj1_tac >> rename1 ‘FST y1 = FST y2’ >> PairCases_on ‘y2’ >> gvs [] >>
          first_x_assum $ irule_at Any >> gvs []))
  >- (once_rewrite_tac [FILTER_COMM] >> first_x_assum irule >>
      rw [] >> rename1 ‘n ∈ _’ >> first_x_assum $ qspecl_then [‘n’] assume_tac >>
      gvs [MEM_MAP, MEM_FILTER] >>
      disj2_tac >> rw [] >> disj1_tac >>
      rename1 ‘FST y1 = FST y2’ >> PairCases_on ‘y2’ >> gs [] >>
      first_x_assum $ irule_at Any >> gs [])
  >- first_x_assum $ drule_then irule
  >- first_x_assum $ drule_then irule
  >- first_x_assum $ drule_then irule
  >- first_x_assum $ drule_then irule
QED

Theorem subst_Letrec_Delay:
  ∀g bL vL filter vs f.
    LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧
    EVERY ok_bind (MAP SND g) ∧
    EVERY (λn. EVERY (λ(n2, e). n ∉ freevars e) g) vL ∧
    f = (λl1 l2. FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                  | Delay e2 => if is_Lam e2 ∧ b
                                                then [(v2, e2);(v1, Delay (Var v2))]
                                                else [v1, e]
                                  | _ => [v1, e]) l1 l2)) ⇒
    MAP (λ(n, e). (n, subst (FILTER (λ(n, v). ¬MEM n (MAP FST (f g (ZIP (vL, bL)))))
                             (FILTER (λ(n,v). filter n) vs)) e))
        (f g (ZIP (vL, bL))) =
    f (MAP (λ(n1, e1). (n1,
                        subst (FILTER (λ(n2, v). ¬MEM n2 (MAP FST g))
                               (FILTER (λ(n2, v). filter n2) vs)) e1)) g)
      (ZIP (vL, MAP2 (λx y. x ∧ y) bL (MAP (λ(v, e).
                                              case e of | Delay e2 => is_Lam e2 | _ => F) g)))
Proof
  rw [MAP_FLAT] >>
  AP_TERM_TAC >>
  irule LIST_EQ >>
  rw [EL_MAP, EL_MAP2] >>
  rename1 ‘_ = _ (_ (EL n1 g)) (EL _ (ZIP (vL, MAP2 _ bL _)))’ >>
  qabbrev_tac ‘pair = EL n1 g’ >> PairCases_on ‘pair’ >> gs [EVERY_EL, EL_MAP, EL_ZIP, EL_MAP2] >>
  last_x_assum $ drule_then assume_tac >>
  Cases_on ‘SND (EL n1 g)’ >> gvs [subst_def, ok_bind_def]
  >- (once_rewrite_tac [FILTER_COMM] >>
      irule change_Filter >>
      rw []
      >- (dxrule_then assume_tac Letrec_Delay_SUBSET >> gvs [SUBSET_DEF, MAP_FLAT] >>
          first_x_assum $ dxrule_then $ dxrule_then assume_tac >> gvs [MEM_EL] >>
          last_x_assum $ dxrule_then $ dxrule_then assume_tac >> gvs [freevars_def] >>
          disj2_tac >> rw [] >> strip_tac >> gvs [EL_MAP] >>
          dxrule_then assume_tac EL_MEM >>
          gvs [MEM_FILTER] >> pairarg_tac >> gs [])
      >- (dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET2 >>
          gvs [SUBSET_DEF, MAP_FLAT])) >>
  IF_CASES_TAC >> gvs [is_Lam_subst]
  >- (irule_at Any change_Filter >> rw []
      >- (dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET >>
          gvs [SUBSET_DEF, MAP_FLAT] >>
          first_x_assum $ dxrule_then assume_tac >> gvs [MEM_EL] >>
          last_x_assum $ dxrule_then $ dxrule_then assume_tac >> gvs [freevars_def])
      >- (dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET2 >>
          gvs [SUBSET_DEF, MAP_FLAT])
      >- (gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
          IF_CASES_TAC >> gvs [MEM_FLAT, MEM_EL] >>
          first_x_assum $ qspecl_then [‘[EL n1 vL; FST (EL n1 g)]’] assume_tac >>
          gvs []
          >- (pop_assum $ qspecl_then [‘n1’] assume_tac >> gvs [EL_MAP, EL_MAP2, EL_ZIP])
          >- (pop_assum $ qspecl_then [‘0’] assume_tac >> gvs [])))
  >- (gvs [subst_def] >> irule change_Filter >> rw []
      >- (dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET >>
          gvs [SUBSET_DEF, MAP_FLAT] >>
          first_x_assum $ dxrule_then assume_tac >> gvs [MEM_EL] >>
          last_x_assum $ dxrule_then $ dxrule_then assume_tac >> gvs [freevars_def])
      >- (dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET2 >>
          gvs [SUBSET_DEF, MAP_FLAT]))
  >- (gvs [subst_def] >> irule change_Filter >> rw []
      >- (dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET >>
          gvs [SUBSET_DEF, MAP_FLAT] >>
          first_x_assum $ dxrule_then assume_tac >> gvs [MEM_EL] >>
          last_x_assum $ dxrule_then $ dxrule_then assume_tac >> gvs [freevars_def])
      >- (dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET2 >>
          gvs [SUBSET_DEF, MAP_FLAT]))
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
  >~[‘FLAT (MAP2 _ g (ZIP (vL, bL)))’] >- (
    rw [subst_def]
    \\ drule_then (drule_then $ qspecl_then [‘K T’] assume_tac) subst_Letrec_Delay
    \\ gvs [EVERY_CONJ, GSYM LAMBDA_PROD, FILTER_T]
    \\ pop_assum kall_tac
    \\ irule exp_rel_Letrec_Delay_Lam
    \\ rw [LIST_REL_EL_EQN]
    >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
    >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
    >- (gvs [EVERY_EL, EL_MAP] \\ rw []
        \\ last_x_assum $ drule_then assume_tac
        \\ rename1 ‘EL n f’ \\ qabbrev_tac ‘pair = EL n f’ \\ PairCases_on ‘pair’ \\ fs []
        \\ Cases_on ‘SND (EL n f)’ \\ gvs [subst_def, ok_bind_def])
    >- (gvs [EVERY_EL, EL_MAP] \\ rw []
        \\ last_x_assum $ drule_then assume_tac
        \\ rename1 ‘EL n g’ \\ qabbrev_tac ‘pair = EL n g’ \\ PairCases_on ‘pair’ \\ fs []
        \\ Cases_on ‘SND (EL n g)’ \\ gvs [subst_def, ok_bind_def])
    >- (gvs [EVERY_EL] \\ rw [EL_MAP]
        >~[‘EL n vL ∉ freevars (subst _ _)’]
        >- (rpt $ first_x_assum $ drule_then assume_tac
            \\ gvs [freevars_subst])
        >~[‘EL n vL ∉ boundvars (subst _ _)’]
        >- (rpt $ first_x_assum $ drule_then assume_tac
            \\ gvs [boundvars_subst])
        \\ rename1 ‘¬(_ (EL n vL) _)’
        \\ rpt $ last_x_assum $ qspecl_then [‘n’] assume_tac
        \\ gvs []
        \\ rename1 ‘_ (_ (EL n2 g))’
        \\ rpt $ first_x_assum $ qspecl_then [‘n2’] assume_tac
        \\ qabbrev_tac ‘pair = EL n2 g’ \\ PairCases_on ‘pair’ \\ gvs [freevars_subst, boundvars_subst])
    >- (rename1 ‘exp_rel x y’
        \\ qsuff_tac ‘subst
            (FILTER
               (λ(n,v). ¬MEM n (MAP FST (FLAT
                            (MAP2
                               (λ(v1,e) (v2,b).
                                    case e of
                                      Var v22 => [(v1,e)]
                                    | Prim v23 v24 => [(v1,e)]
                                    | App v25 v26 => [(v1,e)]
                                    | Lam v27 v28 => [(v1,e)]
                                    | Letrec v29 v30 => [(v1,e)]
                                    | Let v31 v32 v33 => [(v1,e)]
                                    | If v34 v35 v36 => [(v1,e)]
                                    | Delay e2 =>
                                      if is_Lam e2 ∧ b then
                                        [(v2,e2); (v1,Delay (Var v2))]
                                      else [(v1,e)]
                                    | Box v38 => [(v1,e)]
                                    | Force v39 => [(v1,e)]
                                    | Value v40 => [(v1,e)]
                                    | MkTick v41 => [(v1,e)]) g (ZIP (vL,bL))))))
               ws) y = subst (FILTER (λ(n,v). ¬MEM n (MAP FST g)) ws) y’
        >- (rw [] \\ first_x_assum irule
            \\ dxrule_then (dxrule_then assume_tac) LIST_FILTERED
            \\ gvs [])
        \\ irule change_Filter
        \\ rw []
        >- (drule_then (drule_then assume_tac) Letrec_Delay_SUBSET
            \\ gvs [SUBSET_DEF] \\ first_x_assum $ dxrule_then assume_tac
            \\ dxrule_then assume_tac exp_rel_freevars
            \\ gvs [EVERY_MEM])
        >- (drule_then (drule_then assume_tac) Letrec_Delay_SUBSET2
            \\ gvs [SUBSET_DEF]))
    >- metis_tac [LENGTH_MAP]
    >- (rename1 ‘MAP FST f = MAP FST g’
        \\ ‘LENGTH f = LENGTH g’ by metis_tac [LENGTH_MAP]
        \\ gvs [EL_MAP, Once LIST_REL_EL_EQN]
        \\ last_x_assum $ drule_then assume_tac \\ gs []
        \\ rename1 ‘subst _ (SND p1)’ \\ PairCases_on ‘p1’ \\ gvs []
        \\ rename1 ‘subst _ (SND p2)’ \\ PairCases_on ‘p2’ \\ gvs []
        \\ first_x_assum $ irule_at Any
        \\ drule_then (drule_then assume_tac) LIST_FILTERED
        \\ gvs []))
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
  >~ [‘Let (SOME v) x2 (Let s _ y2)’] >- (
    rename1 ‘LIST_REL v_rel (MAP SND vs) (MAP SND ws)’
    \\ Cases_on ‘s’ \\ rw [subst_def, FILTERED]
    \\ irule exp_rel_Let_Delay_Lam
    \\ gvs [is_Lam_subst, freevars_subst]
    >- (qspecl_then [‘ws’, ‘y2’, ‘{v}’] assume_tac subst_remove >>
        drule_then assume_tac exp_rel_freevars >>
        gvs []) >>
    gvs [FILTER_COMM] >>
    rename1 ‘subst (FILTER (λ(n, x). n ≠ v) (FILTER (λ(n, x). n ≠ v2) ws)) y2’ >>
    qspecl_then [‘FILTER (λ(n, x). n ≠ v2) ws’, ‘y2’, ‘{v}’] assume_tac subst_remove >>
    drule_then assume_tac exp_rel_freevars >> gs [] >>
    last_x_assum $ irule_at Any >>
    dxrule_then (dxrule_then assume_tac) LIST_FILTERED >>
    gvs [])
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
QED

Theorem ALL_DISTINCT_Letrec_Delay:
  ∀g vL bL.
    LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧
    ALL_DISTINCT vL ∧ ALL_DISTINCT (MAP FST g) ∧
    EVERY (λv. ¬MEM v (MAP FST g)) vL ⇒
    ALL_DISTINCT (MAP FST (FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                                         | Delay e2 => if is_Lam e2 ∧ b
                                                                       then [(v2, e2); (v1, Delay (Var v2))]
                                                                       else [(v1, e)]
                                                         | _ => [(v1, e)]) g (ZIP (vL, bL)))))
Proof
  Induct >> gvs [FORALL_PROD] >>
  gen_tac >> gen_tac >> Cases >> Cases >> rw [ALL_DISTINCT_APPEND]
  >- (CASE_TAC >> gs [] >>
      IF_CASES_TAC >> gs [])
  >- (last_x_assum irule >> gs [EVERY_CONJ])
  >- (strip_tac >>
      dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET >>
      gvs [SUBSET_DEF] >> first_x_assum $ dxrule_then assume_tac >>
      rename1 ‘[(p_1, p_2)]’ >> Cases_on ‘p_2’ >>
      gvs [EVERY_CONJ, EVERY_MEM] >>
      rename1 ‘is_Lam e2 ∧ b’ >> Cases_on ‘is_Lam e2 ∧ b’ >> gvs [])
QED

Theorem ALOOKUP_Letrec_Delay:
  ∀g vL bL s e i.
    LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧
    ALL_DISTINCT vL ∧ ALL_DISTINCT (MAP FST g) ∧
    EVERY (λv. ¬MEM v (MAP FST g)) vL ∧
    i < LENGTH g ∧ EL i g = (s, e) ⇒
    ALOOKUP (REVERSE (FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                                         | Delay e2 => if is_Lam e2 ∧ b
                                                                       then [(v2, e2); (v1, Delay (Var v2))]
                                                                       else [(v1, e)]
                                                         | _ => [(v1, e)]) g (ZIP (vL, bL))))) s =
    SOME (case e of
          | Delay e2 => if is_Lam e2 ∧ EL i bL
                        then Delay (Var (EL i vL))
                        else e
          | _ => e)
Proof
  Induct >> gvs [FORALL_PROD, EVERY_CONJ] >>
  gen_tac >> gen_tac >> Cases >> Cases >> rw [ALL_DISTINCT_APPEND] >>
  rename1 ‘i < SUC _’ >> Cases_on ‘i’ >> gvs [ALOOKUP_APPEND, REVERSE_APPEND]
  >- (rename1 ‘ALOOKUP (REVERSE (FLAT (MAP2 _ g (ZIP (vL, bL))))) p_1’ >>
      Cases_on ‘ALOOKUP (REVERSE (FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                                 | Delay e2 => if is_Lam e2 ∧ b
                                                               then [(v2, e2); (v1, Delay (Var v2))]
                                                               else [(v1, e)]
                                                 | _ => [(v1, e)]) g (ZIP (vL, bL))))) p_1’ >> gs []
      >- (CASE_TAC >> rw []) >>
      dxrule_then assume_tac ALOOKUP_MEM >>
      dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET >>
      gvs [SUBSET_DEF, MEM_MAP, PULL_EXISTS] >>
      first_x_assum $ dxrule_then assume_tac >> gvs [FORALL_PROD]
      >- (rename1 ‘FST y’ >> PairCases_on ‘y’ >> gs [])
      >- gvs [EVERY_MEM]) >>
  rename1 ‘LENGTH _ = LENGTH vL’ >>
  last_x_assum $ qspecl_then [‘vL’] assume_tac >> gs [] >>
  first_x_assum $ drule_all_then assume_tac >> gvs []
QED

Theorem ALOOKUP_Letrec_Delay2:
  ∀g vL bL n name e handler.
    LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧ n < LENGTH vL ∧
    ALL_DISTINCT vL ∧ ALL_DISTINCT (MAP FST g) ∧ EVERY (λv. ¬MEM v (MAP FST g)) vL ∧
    EL n bL ∧ is_Lam e ∧ EL n g = (name, Delay e) ∧
    handler = FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                            | Delay e2 => if is_Lam e2 ∧ b
                                                          then [(v2, e2); (v1, Delay (Var v2))]
                                                          else [(v1, e)]
                                            | _ => [(v1, e)]) g (ZIP (vL, bL))) ⇒
    ALOOKUP (REVERSE (MAP (λ(g, x). (g, Recclosure handler g)) handler)) (EL n vL)
    = SOME (Recclosure handler (EL n vL))
Proof
  rw [] >> irule ALOOKUP_ALL_DISTINCT_MEM >>
  gvs [MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
  irule_at Any ALL_DISTINCT_Letrec_Delay >> gvs [] >>
  gvs [MEM_MAP, EXISTS_PROD] >>
  gvs [MEM_FLAT] >>
  irule_at (Pos hd) $ iffRL MEM_EL >> gvs [] >>
  first_assum $ irule_at Any >> gvs [EL_MAP2, EL_ZIP] >>
  metis_tac []
QED

Theorem ALOOKUP_Letrec_Delay3:
  ∀g vL bL s e i.
    LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧
    ALL_DISTINCT vL ∧ ALL_DISTINCT (MAP FST g) ∧
    EVERY (λv. ¬MEM v (MAP FST g)) vL ∧
    i < LENGTH g ∧ EL i g = (s, Delay e) ∧ is_Lam e ∧ EL i bL ⇒
    ALOOKUP (REVERSE (FLAT (MAP2 (λ(v1, e) (v2, b).
                                    case e of
                                    | Delay e2 => if is_Lam e2 ∧ b
                                                  then [(v2, e2); (v1, Delay (Var v2))]
                                                  else [(v1, e)]
                                    | _ => [(v1, e)]) g (ZIP (vL, bL))))) (EL i vL)  =
    SOME e
Proof
  rw [] >> irule ALOOKUP_ALL_DISTINCT_MEM >>
  gvs [MAP_REVERSE, MEM_FLAT] >>
  irule_at Any ALL_DISTINCT_Letrec_Delay >> gvs [] >>
  irule_at (Pos hd) $ iffRL MEM_EL >> gvs [] >>
  first_assum $ irule_at Any >>
  gvs [EL_MAP2, EL_ZIP]
QED

Theorem ALOOKUP_FUN:
  ∀l f n. MEM n (MAP FST l) ⇒ ALOOKUP (REVERSE (MAP (λ(n2, x). (n2, f n2)) l)) n = SOME (f n)
Proof
  Induct using SNOC_INDUCT >> gvs [FORALL_PROD, REVERSE_SNOC, MAP_SNOC] >>
  rw []
QED

Theorem exp_rel_subst_Letrec:
  ∀x filter y f g vL bL s.
    LENGTH g = LENGTH vL ∧ LENGTH bL = LENGTH vL ∧
    EVERY ok_bind (MAP SND f) ∧ EVERY ok_bind (MAP SND g) ∧
    MAP FST g = MAP FST f ∧
    EVERY (λv. ¬MEM v (MAP FST g) ∧ EVERY (λ(v2, e). v ∉ freevars e) g
               ∧ EVERY (λ(v2, e). v ∉ boundvars e) g
               ∧ v ∉ freevars x ∧ v ∉ boundvars x) vL ∧
    LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
    exp_rel x y ∧
    ALL_DISTINCT vL ∧ ALL_DISTINCT (MAP FST f) ⇒
    ∀funs. funs = (λf. (MAP (λ(g, x). (g, Recclosure f g)) f)) ⇒
           exp_rel (subst (FILTER (λ(k, x). filter k) (funs f)) x)
                   (subst (FILTER (λ(k, x). filter k)
                           (funs (FLAT (MAP2 (λ(v1, e) (v2, b). case e of
                                           | Delay e2 => if is_Lam e2 ∧ b
                                                         then [(v2, e2); (v1, Delay (Var v2))]
                                                         else [(v1, e)]
                                           | _ => [(v1, e)]) g (ZIP (vL, bL)))))) y)
Proof
  Induct using freevars_ind \\ rw []
  >- (gvs [subst_funs_def, EVERY_CONJ, subst_def, exp_rel_def] >> CASE_TAC
      >- (CASE_TAC >> gvs [exp_rel_def, ALOOKUP_NONE] >>
          dxrule_then assume_tac ALOOKUP_MEM >>
          gvs [MEM_MAP, MEM_FILTER] >>
          dxrule_then (dxrule_then assume_tac) Letrec_Delay_SUBSET >> gvs [SUBSET_DEF] >>
          gvs [Once MEM_MAP, PULL_EXISTS] >>
          first_x_assum $ dxrule_then assume_tac >>
          rename1 ‘MEM (FST y) _’ >> PairCases_on ‘y’ >> gvs [MEM_MAP]
          >- (gvs [FORALL_PROD, MEM_EL] >>
              rename1 ‘n < _’ >>
              first_x_assum $ resolve_then (Pos hd) mp_tac PAIR >>
              gvs []) >>
          gvs [EVERY_MEM, freevars_def, boundvars_def])
      >- (dxrule_then assume_tac ALOOKUP_MEM >>
          gvs [MEM_MAP, MEM_FILTER] >>
          pairarg_tac >> gvs [] >>
          drule_then (drule_then assume_tac) Letrec_Delay_SUBSET2 >> gvs [SUBSET_DEF] >>
          gvs [Once MEM_MAP, PULL_EXISTS] >> pop_assum $ drule_then assume_tac >> fs [] >>
          rename1 ‘MAP2 _ g (ZIP (vL, bL))’ >>
          drule_then (qspecl_then
                      [‘Recclosure (FLAT (MAP2 (λ(v1, e) (v2, b).
                             case e of
                             | Delay e2 => if is_Lam e2 ∧ b
                                           then [(v2, e2); (v1, Delay (Var v2))]
                                           else [(v1, e)]
                             | _ => [(v1, e)]) g (ZIP (vL, bL))))’] assume_tac)
                     ALOOKUP_FUN >>
          gvs [ALOOKUP_FILTER, GSYM FILTER_REVERSE, exp_rel_def] >>
          irule v_rel_Recclosure_Delay_Lam >> gvs [EVERY_CONJ] >> rw [MEM_MAP] >>
          first_x_assum $ irule_at Any >> gvs [FORALL_PROD]))
  >~[‘Prim op’]
  >- (gvs [subst_funs_def, subst_def, exp_rel_def] >> rpt $ strip_tac >>
      gvs [LIST_REL_EL_EQN, EL_MAP] >> rw [] >>
      first_x_assum irule >> gvs [EVERY_CONJ, EL_MEM] >>
      rename1 ‘MAP FST g = MAP FST f’ >>
      ‘LENGTH g = LENGTH f’ by metis_tac [LENGTH_MAP] >>
      gvs [EL_MAP, freevars_def, boundvars_def, EVERY_MEM, PULL_EXISTS] >>
      rw [] >> rpt $ first_x_assum $ drule_then assume_tac
      >~ [‘freevars (EL n2 xs)’]
      >- (first_x_assum $ qspecl_then [‘freevars (EL n2 xs)’] assume_tac >> gvs [MEM_MAP] >>
          first_x_assum $ qspecl_then [‘EL n2 xs’] assume_tac >> gvs [MEM_EL])
      >~ [‘boundvars (EL n2 xs)’]
      >- (rpt $ first_x_assum $ qspecl_then [‘boundvars (EL n2 xs)’] assume_tac >>
          gvs [MEM_MAP] >>
          rpt $ first_x_assum $ qspecl_then [‘EL n2 xs’] assume_tac >> gvs [MEM_EL]))
  >~[‘If’]
  >- (gvs [subst_funs_def, subst_def, exp_rel_def] >> rpt $ strip_tac >>
      first_x_assum irule >> gvs [EVERY_CONJ] >>
      rename1 ‘MAP FST g = MAP FST f’ >>
      ‘LENGTH g = LENGTH f’ by metis_tac [LENGTH_MAP] >>
      gvs [EL_MAP, freevars_def, boundvars_def, EVERY_MEM, PULL_EXISTS])
  >~[‘App x1 y1’]
  >- (gvs [subst_funs_def, subst_def, exp_rel_def] >> rpt $ strip_tac >>
      first_x_assum irule >> gvs [EVERY_CONJ] >>
      rename1 ‘MAP FST g = MAP FST f’ >>
      ‘LENGTH g = LENGTH f’ by metis_tac [LENGTH_MAP] >>
      gvs [EL_MAP, freevars_def, boundvars_def, EVERY_MEM, PULL_EXISTS])
  >~[‘Lam s x’]
  >- (gvs [subst_def, exp_rel_def, FILTER_FILTER, LAMBDA_PROD] >>
      rename1 ‘_ ≠ s ∧ filter2 _’ >>
      last_x_assum $ qspecl_then [‘λx. x ≠ s ∧ filter2 x’] assume_tac >> gvs [] >>
      first_x_assum irule >> gvs [EVERY_CONJ, freevars_def, boundvars_def, EVERY_MEM])
  >~[‘Seq x1 y1’]
  >-(gvs [exp_rel_def, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, is_Lam_subst,
          freevars_subst]
     >- (rename1 ‘freevars (Delay x1)’ >> rename1 ‘exp_rel x1 x2’ >>
         rename1 ‘FILTER (λ(k, x). filter2 k) _’ >>
         last_x_assum $ qspecl_then [‘filter2’, ‘Delay x2’] assume_tac >> gvs [subst_def] >>
         first_x_assum $ irule_at Any >> gvs [EVERY_CONJ, freevars_def, boundvars_def] >>
         rename1 ‘subst (FILTER (λ(k,x). filter2 k) (MAP _ f)) y1’ >>
         rename1 ‘v ∉ _ ’ >>
         qspecl_then [‘FILTER (λ(k,x). filter2 k) (MAP (λ(g,x). (g,Recclosure f g)) f)’,
                      ‘y1’, ‘{v}’] assume_tac
                     $ GSYM subst_remove >>
         gvs [FILTER_FILTER, LAMBDA_PROD])
     >- (rpt $ first_assum $ irule_at Any >> gvs [EVERY_CONJ, freevars_def, boundvars_def]))
  >~[‘Let (SOME s) x1 y1’]
  >- (gvs [exp_rel_def, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER,
           is_Lam_subst, freevars_subst]
      >- (rename1 ‘freevars (Delay x1)’ >> rename1 ‘exp_rel x1 x2’ >>
          rename1 ‘FILTER _ (FILTER (λ(k, x). filter2 k) _)’ >>
          last_x_assum $ qspecl_then [‘filter2’, ‘Delay x2’] assume_tac >> gvs [subst_def] >>
          first_x_assum $ irule_at Any >> gvs [EVERY_CONJ, freevars_def, boundvars_def] >>
          rename1 ‘subst (FILTER _ (FILTER (λ(k,x). filter2 k) (MAP _ f))) y1’ >>
          rename1 ‘v ∉ _ ’ >>
          qspecl_then [‘FILTER (λ(k, x). k ≠ s) (FILTER (λ(k,x). filter2 k)
                                                 (MAP (λ(g,x). (g,Recclosure f g)) f))’,
                       ‘y1’, ‘{v}’] assume_tac $ GSYM subst_remove >>
          gvs [FILTER_COMM] >> gvs [FILTER_FILTER, LAMBDA_PROD] >>
          last_x_assum $ qspecl_then [‘λx. (filter2 x ∧ x ≠ s) ∧ x ≠ v’] assume_tac >> gvs [] >>
          first_x_assum irule >> gvs [EVERY_CONJ, EVERY_MEM] >> rw [] >>
          rpt $ first_x_assum $ drule_then assume_tac >> gvs [])
      >- (first_x_assum $ irule_at Any >>
          gvs [EVERY_CONJ, freevars_def, boundvars_def, FILTER_FILTER, LAMBDA_PROD] >>
          rename1 ‘_ ≠ s ∧ filter2 _’ >>
          last_x_assum $ qspecl_then [‘λx. x ≠ s ∧ filter2 x’] assume_tac >> gvs [] >>
          first_x_assum $ irule_at Any >>
          gvs [EVERY_CONJ, EVERY_MEM] >> rw [] >>
          rpt $ first_x_assum $ drule_then assume_tac >> gvs []))
  >~[‘Letrec’]
  >- (gvs [exp_rel_def, subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, freevars_subst,
           MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM SND_THM, GSYM FST_THM]
      >- (disj1_tac >> rw [EVERY_EL, LIST_REL_EL_EQN, EL_MAP]
          >- (rename1 ‘EL n f’ >> gvs [EVERY_EL, EL_MAP] >>
              first_x_assum $ dxrule_then assume_tac >>
              qabbrev_tac ‘pair = EL n f’ >> PairCases_on ‘pair’ >>
              Cases_on ‘SND (EL n f)’ >> gvs [ok_bind_def, subst_def])
          >- (rename1 ‘EL n g2’ >> gvs [EVERY_EL, EL_MAP] >>
              first_x_assum $ dxrule_then assume_tac >>
              qabbrev_tac ‘pair = EL n g2’ >> PairCases_on ‘pair’ >>
              Cases_on ‘SND (EL n g2)’ >> gvs [ok_bind_def, subst_def])
          >- metis_tac [LENGTH_MAP]
          >- (rename1 ‘MAP FST f = MAP FST g2’ >>
              gvs [EL_MAP, Once MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >>
              last_x_assum $ drule_then assume_tac >>
              rename1 ‘n < _’ >>
              qabbrev_tac ‘pair1 = EL n f’ >> PairCases_on ‘pair1’ >>
              qabbrev_tac ‘pair2 = EL n g2’ >> PairCases_on ‘pair2’ >>
              gvs [FILTER_FILTER, LAMBDA_PROD] >>
              rename1 ‘ ¬MEM _ (MAP FST g2) ∧ filter2 _’ >>
              first_x_assum $ qspecl_then [‘λx. ¬MEM x (MAP FST g2) ∧ filter2 x’] assume_tac >>
              gvs [] >>
              first_x_assum $ irule_at Any >>
              first_x_assum $ drule_then assume_tac >>
              gvs [EVERY_CONJ, freevars_def, boundvars_def, EVERY_MEM] >>
              conj_tac
              >- (rename1 ‘EL _ (MAP SND g1)’ >> rename1 ‘MAP FST g1 = MAP FST f1’ >>
                  ‘LENGTH g1 = LENGTH f1’ by metis_tac [LENGTH_MAP] >> gvs [EL_MAP]) >>
              rw [] >> rename1 ‘MEM v vL’ >>
              rpt $ last_x_assum $ qspecl_then [‘v’] assume_tac >> gvs []
              >- (rpt $ first_x_assum $ qspecl_then [‘freevars (SND (EL n f))’] assume_tac >>
                      gvs [MEM_MAP, MEM_EL])
              >- (rpt $ first_x_assum $ qspecl_then [‘boundvars (SND (EL n f))’] assume_tac >>
                  gvs [MEM_MAP, MEM_EL]))
          >- (gvs [FILTER_FILTER, LAMBDA_PROD] >>
              rename1 ‘ ¬MEM _ (MAP FST g2) ∧ filter2 _’ >>
              first_x_assum $ qspecl_then [‘λx. ¬MEM x (MAP FST g2) ∧ filter2 x’] assume_tac >>
              gvs [] >>
              first_x_assum $ irule_at Any >>
              gvs [EVERY_CONJ, freevars_def, boundvars_def, EVERY_MEM])) >>
      disj2_tac >>
      assume_tac subst_Letrec_Delay >> gvs [] >> pop_assum $ irule_at Any >> rw []
      >- gvs [EVERY_CONJ]
      >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
      >- (gvs [LIST_REL_EL_EQN, EL_MAP] >> rw [FILTER_FILTER] >>
          gvs [MEM_EL, PULL_EXISTS] >> last_x_assum $ drule_then assume_tac >>
          rename1 ‘MAP FST f = MAP FST g2’ >>
          rename1 ‘EL n f’ >> Cases_on ‘EL n f’ >> Cases_on ‘EL n g2’ >> gvs [] >>
          rename1 ‘EL _ (MAP FST g2)’ >>
          rename1 ‘FILTER (λx. _ x ∧ (λ(n2, v). filter2 n2) x)’ >>
          first_x_assum $ qspecl_then [‘λx. (¬MEM x (MAP FST g2) ∧ filter2 x)’] assume_tac >>
          gvs [MEM_EL, LAMBDA_PROD] >>
          first_x_assum $ irule >> gvs [EVERY_CONJ, EVERY_MEM, EL_MAP] >> rw []
          >- (strip_tac >> gvs [EL_MAP] >> rpt $ first_x_assum $ drule_then assume_tac >>
              pop_assum kall_tac >>
              rename1 ‘FST (EL n2 f2) = _’ >>
              first_x_assum $ qspecl_then [‘n2’] assume_tac >> gvs [EL_MAP])
          >- (rpt $ first_x_assum $ drule_then assume_tac >> pop_assum kall_tac >>
              gvs [freevars_def, boundvars_def] >>
              rename1 ‘v ∉ freevars r’ >>
              first_x_assum $ qspecl_then [‘freevars r’] assume_tac >>
              gvs [MEM_EL, PULL_EXISTS] >>
              first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [EL_MAP])
          >- (rpt $ first_x_assum $ drule_then assume_tac >> pop_assum kall_tac >>
              gvs [freevars_def, boundvars_def] >>
              rename1 ‘v ∉ boundvars r’ >>
              last_x_assum $ qspecl_then [‘boundvars r’] assume_tac >>
              gvs [MEM_EL, PULL_EXISTS] >>
              first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [EL_MAP]) >>
          first_x_assum $ drule_then assume_tac >> gvs [])
      >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
          rw [] >> first_x_assum $ drule_then assume_tac >>
          rename1 ‘ok_bind (subst _ expr)’ >> Cases_on ‘expr’ >> gvs [ok_bind_def, subst_def])
      >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
          rw [] >> first_x_assum $ drule_then assume_tac >>
          rename1 ‘ok_bind (subst _ expr)’ >> Cases_on ‘expr’ >> gvs [ok_bind_def, subst_def])
      >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
      >- (gvs [EVERY_MEM] >> gen_tac >> strip_tac >> first_x_assum $ drule_then assume_tac >>
          gvs [boundvars_subst, FORALL_PROD] >> rw [MEM_MAP]
          >- (pairarg_tac >> gvs [])
          >- (pairarg_tac >> gvs [] >>
              first_x_assum $ drule_then assume_tac >>
              first_x_assum $ dxrule_then assume_tac >> gvs [freevars_subst]) >>
          pairarg_tac >> gvs [boundvars_subst] >>
          first_x_assum $ drule_then assume_tac >> gvs [])
      >- (rename1 ‘exp_rel _ (subst (FILTER (λ(n,v). ¬MEM n (MAP FST (FLAT (MAP2 _ g2 (ZIP (vL2, bL2))))))
                                     (FILTER (λ(k,x). filter2 k)
                                     (MAP _ (FLAT (MAP2 _ g1 (ZIP (vL1, bL1))))))) y2)’ >>
          qabbrev_tac ‘handler = (λ(v1, e) (v2, b). case e of
                    | Delay e2 => if is_Lam e2 ∧ b
                                  then [(v2, e2); (v1, Delay (Var v2))]
                                  else [(v1, e)]
                    | _ => [(v1, e)])’ >>
          qspecl_then [‘y2’, ‘set (MAP FST (FLAT (MAP2 handler g2 (ZIP (vL2, bL2)))))’,
                       ‘set (MAP FST g2)’,
                       ‘FILTER (λ(k, x). filter2 k) (MAP
                      (λ(g', x). (g', Recclosure (FLAT (MAP2 handler g1 (ZIP (vL1, bL1)))) g'))
                      (FLAT (MAP2 handler g1 (ZIP (vL1, bL1)))))’]
                      mp_tac change_Filter >>
          impl_tac
          >- (rw []
              >- (qspecl_then [‘g2’, ‘vL2’, ‘bL2’] assume_tac Letrec_Delay_SUBSET >>
                  gvs [SUBSET_DEF] >>
                  first_x_assum $ dxrule_then assume_tac >> gvs [EVERY_MEM] >>
                  dxrule_then assume_tac exp_rel_freevars >>
                  gvs []) >>
              qspecl_then [‘g2’, ‘vL2’, ‘bL2’] assume_tac Letrec_Delay_SUBSET2 >>
              gvs [SUBSET_DEF]) >>
          rw [FILTER_FILTER, LAMBDA_PROD] >>
          first_x_assum $ qspecl_then [‘λx. ¬MEM x (MAP FST g2) ∧ filter2 x’] assume_tac >>
          gvs [] >> first_x_assum $ irule >>
          gvs [EVERY_CONJ, freevars_def, boundvars_def, EVERY_MEM]))
  >~[‘Delay x’]
  >- (gvs [exp_rel_def, subst_def] >>
      last_x_assum $ irule >>
      gvs [freevars_def, boundvars_def])
  >~[‘Box x’]
  >- (gvs [exp_rel_def, subst_def] >>
      last_x_assum $ irule >>
      gvs [freevars_def, boundvars_def])
  >~[‘Force x’]
  >- (gvs [exp_rel_def, subst_def] >>
      last_x_assum $ irule >>
      gvs [freevars_def, boundvars_def])
  >~[‘Value x’]
  >- gvs [exp_rel_def, subst_def]
  >~[‘MkTick x’]
  >- (gvs [exp_rel_def, subst_def] >>
      last_x_assum $ irule >>
      gvs [freevars_def, boundvars_def])
QED

Theorem eval_to_Letrec:
  ∀k binds e. k ≠ 0 ⇒
              eval_to k (Letrec binds e) =
              eval_to (k - 1) (subst (MAP (λ(g,x). (g, Recclosure binds g)) binds) e)
Proof
  gvs [eval_to_def, subst_funs_def]
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
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
          \\ rw [Once exp_rel_cases] \\ gs []
          \\ Cases_on ‘x0’ \\ gvs [])
      >- (Cases_on ‘ALOOKUP (REVERSE l) s’ >> gs [ALOOKUP_NONE]
          >~[‘ALOOKUP (REVERSE l) s = SOME x’]
          >- (dxrule_then assume_tac ALOOKUP_MEM >>
              gvs [MEM_EL, EVERY_CONJ, LIST_REL_EL_EQN, EL_MAP] >>
              rename1 ‘EL n2 l’ >> rename1 ‘exp_rel (SND (EL _ l)) (SND (EL _ g2))’ >>
              qspecl_then [‘g2’] assume_tac ALOOKUP_Letrec_Delay >>
              first_x_assum $ drule_then $ drule_then $ assume_tac >> gs [MEM_EL] >>
              qabbrev_tac ‘pair = EL n2 g2’ >> PairCases_on ‘pair’ >> gvs [] >>
              first_x_assum $ drule_then $ drule_then assume_tac >> gvs [] >>
              ‘EL n2 (MAP FST g2) = EL n2 (MAP FST l)’ by gvs [] >> gvs [EL_MAP] >>
               qabbrev_tac ‘pair2 = EL n2 l’ >> PairCases_on ‘pair2’ >> gvs [] >>
              first_x_assum $ drule_then assume_tac >> gvs [] >>
              Cases_on ‘SND (EL n2 l)’ >> gvs [exp_rel_def] >>
              rw [])
           >- gvs [MAP_REVERSE]))
    \\ pairarg_tac \\ gvs []
    \\ ‘∃body' binds'. dest_anyClosure w2 = INR (s,body',binds')’
      by (Cases_on ‘v2’ \\ Cases_on ‘w2’ \\ gs [dest_anyClosure_def, v_rel_def]
          >- (qspecl_then [‘g'’, ‘vL’, ‘bL’] assume_tac ALOOKUP_Letrec_Delay3 >>
              gvs [EVERY_CONJ, LIST_REL_EL_EQN] >>
              pop_assum $ drule_then assume_tac >>
              first_assum $ drule_then assume_tac >> gvs [EL_MAP] >>
              Cases_on ‘EL i g'’ >> gvs [exp_rel_def])
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
                \\ gs [ok_bind_def])
            >- (Cases_on ‘ALOOKUP (REVERSE l) s'’ >> gs [ALOOKUP_NONE] >>
                dxrule_then assume_tac ALOOKUP_MEM >>
                gvs [MEM_EL, EVERY_CONJ, LIST_REL_EL_EQN, EL_MAP] >>
                rename1 ‘EL n2 l’ >> rename1 ‘exp_rel (SND (EL _ l)) (SND (EL _ g2))’ >>
                qspecl_then [‘g2’] assume_tac ALOOKUP_Letrec_Delay >>
                first_x_assum $ drule_then $ drule_then $ assume_tac >> gs [MEM_EL] >>
                qabbrev_tac ‘pair = EL n2 g2’ >> PairCases_on ‘pair’ >> gvs [] >>
                first_x_assum $ drule_then $ drule_then assume_tac >> gvs [] >>
                ‘EL n2 (MAP FST g2) = EL n2 (MAP FST l)’ by gvs [] >> gvs [EL_MAP] >>
                qabbrev_tac ‘pair2 = EL n2 l’ >> PairCases_on ‘pair2’ >> gvs [] >>
                first_x_assum $ drule_then assume_tac >> gvs [] >>
                Cases_on ‘SND (EL n2 l)’ >> gvs [exp_rel_def] >>
                rw []))
    \\ IF_CASES_TAC \\ gs []
    >- (
      qexists_tac ‘0’ \\ gs []
      \\ Cases_on ‘eval_to 0 y = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j’ assume_tac) eval_to_mono \\ gs []
      \\ Cases_on ‘eval_to 0 g = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j1’ assume_tac) eval_to_mono \\ gs [])
    \\ ‘exp_rel (subst (binds ++ [s,v1]) body) (subst (binds' ++ [s,w1]) body')’
      by (Cases_on ‘v2’ \\ Cases_on ‘w2’
          \\ gvs [dest_anyClosure_def, v_rel_def, subst_APPEND]
          >- (irule exp_rel_subst \\ gvs [])
          >- (rename1 ‘exp_rel (subst1 s v1 (subst (FILTER _ (MAP _ f2)) ef))
                       (subst binds2 (subst1 s w1 body2))’ >>
              qspecl_then [‘ef’, ‘[(s, v1)]’,
                           ‘FILTER (λ(v, e). v ≠ s)
                            (MAP (λ(v,x). (v, Recclosure f2 v)) f2)’]
                          mp_tac subst_commutes >>
              impl_tac
              >- (gvs [] >> strip_tac >> gvs [MEM_MAP, MEM_FILTER] >>
                  pairarg_tac >> gvs []) >>
              rw [] >>
              qspecl_then [‘MAP (λ(v,x). (v, Recclosure f2 v)) f2’, ‘subst1 s v1 ef’, ‘{s}’]
                          assume_tac subst_remove >>
              gvs [freevars_subst] >>
              qspecl_then [‘g'’, ‘vL’, ‘bL’] assume_tac ALOOKUP_Letrec_Delay3 >>
              gvs [EVERY_CONJ] >>
              first_x_assum $ drule_then assume_tac >>
              Cases_on ‘EL i g'’ >> gvs [LIST_REL_EL_EQN] >>
              last_assum $ drule_then assume_tac >> gvs [EL_MAP, exp_rel_def] >>
              qspecl_then [‘subst1 s v1 ef’, ‘λx. T’] assume_tac exp_rel_subst_Letrec >>
              gvs [GSYM LAMBDA_PROD, FILTER_T] >> pop_assum irule >>
              irule_at Any exp_rel_subst >>
              gvs [EVERY_CONJ, freevars_subst, boundvars_subst, LIST_REL_EL_EQN, EVERY_MEM] >>
              rw []
              >- (rpt $ last_x_assum $ drule_then assume_tac >>
                  gvs [MEM_EL, PULL_EXISTS, exp_rel_def] >>
                  rpt $ last_x_assum $ qspecl_then [‘i’] assume_tac >>
                  drule_then assume_tac exp_rel_freevars >>
                  dxrule_then assume_tac exp_rel_boundvars >>
                  gvs [SUBSET_DEF, freevars_def, boundvars_def])
              >- (rpt $ last_x_assum $ drule_then assume_tac >>
                  gvs [MEM_EL, PULL_EXISTS, exp_rel_def] >>
                  rpt $ last_x_assum $ qspecl_then [‘i’] assume_tac >>
                  drule_then assume_tac exp_rel_freevars >>
                  dxrule_then assume_tac exp_rel_boundvars >>
                  strip_tac >>
                  gvs [SUBSET_DEF, freevars_def, boundvars_def])
              >- gvs [EL_MAP])
          >- (irule exp_rel_subst
              \\ rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
              \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
                by (irule LIST_REL_OPTREL
                    \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
              \\ irule_at Any exp_rel_subst
              \\ gvs [OPTREL_def]
              \\ gvs [CaseEqs ["option", "exp"], v_rel_def]
              \\ gs [Once exp_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                     GSYM FST_THM, EVERY2_MAP, v_rel_def]
              \\ gvs [LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP, ELIM_UNCURRY])
          >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’, ‘subst1 s2 _ _’]
              \\ qspecl_then [‘subst1 s2 v1 body’, ‘λx. T’, ‘subst1 s2 w1 body'’, ‘xs’, ‘ys’]
                             assume_tac exp_rel_subst_Letrec
              \\ gvs [FILTER_T, GSYM LAMBDA_PROD]
              \\ Cases_on ‘ALOOKUP (REVERSE xs) s’ \\ gs []
              \\ rename1 ‘ALOOKUP (REVERSE xs) s = SOME e1’
              \\ Cases_on ‘e1’ \\ gs []
              \\ dxrule_then assume_tac ALOOKUP_MEM
              \\ gvs [MEM_EL]
              \\ drule_then (drule_then assume_tac) ALOOKUP_Letrec_Delay
              \\ gs [EVERY_CONJ, MEM_EL, LIST_REL_EL_EQN]
              \\ first_x_assum $ drule_then assume_tac
              \\ rename1 ‘EL n2 ys’ \\ gvs [EL_MAP]
              \\ drule_then (qspecl_then [‘n’, ‘n2’] assume_tac) ALL_DISTINCT_EL_IMP
              \\ gvs [EL_MAP]
              \\ ‘∀i. i < LENGTH ys ⇒ FST (EL i xs) = FST (EL i ys)’
                by (rw [] >>
                    ‘i < LENGTH xs’ by gs [] >>
                    dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                    ‘i < LENGTH ys’ by gs [] >>
                    dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                    rw [])
              \\ Cases_on ‘EL n2 xs’ \\ gvs []
              \\ first_x_assum $ qspecl_then [‘n2’] assume_tac
              \\ gvs [] \\ rename1 ‘EL n _’
              \\ Cases_on ‘EL n ys’ \\ gvs []
              \\ first_x_assum $ qspecl_then [‘vL’, ‘bL’] assume_tac \\ gvs []
              \\ last_x_assum $ qspecl_then [‘n’] assume_tac
              \\ Cases_on ‘SND (EL n ys)’ \\ gvs [exp_rel_def]
              \\ first_x_assum $ irule_at Any
              \\ gvs [freevars_subst, boundvars_subst, exp_rel_subst, EVERY_EL]
              \\ rw []
              \\ rename1 ‘EL n2 _ ∉ _’
              \\ rpt $ last_x_assum $ qspecl_then [‘n2’] $ drule_then $ qspecl_then [‘n’] assume_tac
              \\ drule_then assume_tac exp_rel_freevars
              \\ drule_then assume_tac exp_rel_boundvars
              \\ gvs [freevars_def, boundvars_def, SUBSET_DEF]
              \\ strip_tac \\ gvs []))
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
    >~ [‘is_Lam _’] >- (
      IF_CASES_TAC \\ gs []
      \\ drule_then assume_tac exp_rel_freevars
      >- (qexists_tac ‘0’ >> gs [])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ drule_then assume_tac exp_rel_is_Lam
      \\ rename1 ‘is_Lam x1 ⇔ is_Lam x2’
      \\ Cases_on ‘x2’ \\ gs [is_Lam_def]
      \\ gvs [eval_to_def, subst_def, subst1_notin_frees]
      \\ rename1 ‘j + _ - 1’ \\ qexists_tac ‘j + 1’
      \\ gs [])
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
    >~ [‘is_Lam x1’]
    >- (
      IF_CASES_TAC \\ gs []
      \\ drule_then assume_tac exp_rel_freevars
      >- (qexists_tac ‘0’ >> gs [])
      \\ Cases_on ‘x1’ \\ fs [is_Lam_def, Once exp_rel_def, eval_to_def, subst_def, PULL_EXISTS]
      \\ Q.REFINE_EXISTS_TAC ‘j + n’
      \\ qexists_tac ‘1’ \\ gvs [subst1_notin_frees]
      \\ rename1 ‘_ (eval_to _ (subst1 m (Thunk (INR (Lam s x1))) y1))
                  (eval_to _ (subst1 _ (Thunk (INR (Value (Closure s x2)))) y2))’
      \\ ‘exp_rel (subst1 m (Thunk (INR (Lam s x1))) y1)
                  (subst1 m (Thunk (INR (Value (Closure s x2)))) y2)’
        by (irule exp_rel_subst \\ gs [v_rel_Thunk_INR_Lam])
      \\ last_x_assum $ dxrule_then $ qx_choose_then ‘j1’ assume_tac
      \\ qexists_tac ‘j1’ \\ gvs [])
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
    >- (IF_CASES_TAC \\ gs []
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
    \\ IF_CASES_TAC \\ gs []
    >- (qexists_tac ‘0’ \\ gs [])
    \\ rename1 ‘exp_rel x y’
    \\ last_x_assum irule
    \\ gvs [subst_funs_def]
    \\ qspecl_then [‘x’, ‘λx. T’] assume_tac exp_rel_subst_Letrec
    \\ gvs [GSYM LAMBDA_PROD, FILTER_T]
    \\ pop_assum irule \\ gvs [EVERY_CONJ, EVERY_MEM]
    \\ rw [] \\ last_x_assum $ drule_then assume_tac
    \\ strip_tac \\ gvs [MEM_EL, PULL_EXISTS, EL_MAP]
    \\ first_x_assum $ drule_then assume_tac
    \\ pairarg_tac \\ gvs [])
 >~ [‘Delay x’] >- (
    gvs [Once exp_rel_def, eval_to_def, v_rel_def])
  >~ [‘Box x’] >- (
    gvs [Once exp_rel_def, eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘∃j. ($= +++ v_rel) (eval_to k x) (eval_to (j + k) y)’
      suffices_by (
        disch_then (qx_choose_then ‘j’ assume_tac)
        \\ qexists_tac ‘j’
        \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to (j + k) y’ \\ gs []
        \\ simp [v_rel_def])
    \\ first_x_assum (irule_at Any) \\ gs [])
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
        >- (drule_then (drule_then assume_tac) ALOOKUP_Letrec_Delay3
            \\ gvs [EVERY_CONJ]
            \\ first_x_assum $ drule_then assume_tac
            \\ rename1 ‘EL i g = (_, _)’
            \\ Cases_on ‘EL i g’
            \\ gvs [LIST_REL_EL_EQN, EL_MAP]
            \\ last_x_assum $ drule_then assume_tac
            \\ gvs [exp_rel_def])
        >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
            \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
              by (irule LIST_REL_OPTREL
                  \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
            \\ gvs [OPTREL_def]
            \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
            \\ rw [Once exp_rel_cases] \\ gs []
            \\ Cases_on ‘x0’ \\ gvs [])
        >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’, ‘ALOOKUP _ s’]
            \\ Cases_on ‘ALOOKUP (REVERSE xs) s’ \\ gvs [ALOOKUP_NONE, MAP_REVERSE]
            \\ dxrule_then assume_tac ALOOKUP_MEM \\ gvs [MEM_EL]
            \\ drule_then (drule_then assume_tac) ALOOKUP_Letrec_Delay \\ gvs [EVERY_CONJ, MEM_EL]
            \\ pop_assum $ drule_then assume_tac
            \\ rename1 ‘EL n (MAP FST ys)’ \\ Cases_on ‘EL n ys’ \\ gvs [EL_MAP, LIST_REL_EL_EQN]
            \\ last_x_assum $ qspecl_then [‘n’] assume_tac
            \\ rename1 ‘(_, _) = EL n2 xs’
            \\ drule_then (qspecl_then [‘n’, ‘n2’] assume_tac) ALL_DISTINCT_EL_IMP \\ gvs [EL_MAP]
            \\ ‘∀i. i < LENGTH ys ⇒ FST (EL i xs) = FST (EL i ys)’
              by (rw [] >>
                  ‘i < LENGTH xs’ by gs [] >>
                  dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                  ‘i < LENGTH ys’ by gs [] >>
                  dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                  rw [])
            \\ first_x_assum $ qspecl_then [‘n2’] assume_tac \\ gvs []
            \\ Cases_on ‘EL n2 xs’ \\ gvs []
            \\ rename1 ‘EL n _’ \\ Cases_on ‘SND (EL n xs)’ \\ gvs [exp_rel_def]))
      \\ pairarg_tac \\ gvs []
      \\ Cases_on ‘∃s x y. v1 = Thunk (INR (Lam s x)) ∧
                           w1 = Thunk (INR (Value (Closure s y))) ∧ exp_rel x y’
      \\ gs []
      >- (gvs [dest_anyThunk_def, subst_funs_def, subst_empty]
          \\ qexists_tac ‘j’ \\ gs []
          \\ rw [eval_to_def, v_rel_Closure])
      \\ Cases_on ‘∃f n. v1 = Recclosure f n’ \\ gs [v_rel_def]
      >~[‘FLAT’]
      >- (gvs [dest_anyThunk_def] >>
          rename1 ‘ALOOKUP (REVERSE f) n’ >> Cases_on ‘ALOOKUP (REVERSE f) n’ >>
          gvs [ALOOKUP_NONE] >>
          dxrule_then assume_tac ALOOKUP_MEM >> gvs [] >> rename1 ‘MEM (n, e) f’ >>
          drule_then (drule_then assume_tac) ALOOKUP_Letrec_Delay >>
          Cases_on ‘e’ >> gvs [MEM_EL, EVERY_CONJ, LIST_REL_EL_EQN] >>
          first_assum $ drule_then assume_tac >>
          rename1 ‘MAP FST binds = MAP FST g’ >>
          ‘LENGTH binds = LENGTH g’ by metis_tac [LENGTH_MAP] >>
          gvs [EL_MAP] >>
          rename1 ‘(FST (EL n1 _), _) = EL n2 _’ >>
          drule_then (qspecl_then [‘n1’, ‘n2’] assume_tac) ALL_DISTINCT_EL_IMP >> gvs [EL_MAP] >>
          ‘∀i. i < LENGTH binds ⇒ FST (EL i binds) = FST (EL i g)’
              by (rw [] >>
                  ‘i < LENGTH g’ by gs [] >>
                  dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                  ‘i < LENGTH binds’ by gs [] >>
                  dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                  rw []) >>
          first_x_assum $ qspecl_then [‘n2’] assume_tac >> gvs [] >>
          Cases_on ‘EL n2 binds’ >> Cases_on ‘EL n1 g’ >> gvs [] >>
          rename1 ‘EL n1 binds = (name, Delay e1)’ >> rename1 ‘EL n1 g = (name, e2)’ >>
          ‘exp_rel (Delay e1) e2’ by (last_x_assum $ qspecl_then [‘n1’] assume_tac >> gvs []) >>
          gvs [exp_rel_def] >>
          first_x_assum $ drule_then assume_tac >> gvs [] >>
          rename1 ‘is_Lam y2 ∧ EL n1 bL’ >> Cases_on ‘is_Lam y2 ∧ EL n1 bL’ >> gvs []
          >- (rename1 ‘exp_rel y1 y2’ >>
              qabbrev_tac ‘handler = (FLAT (MAP2 (λ(v1,e) (v2,b).
                                    case e of
                                    | Delay e2 => if is_Lam e2 ∧ b
                                                  then [(v2,e2); (v1,Delay (Var v2))]
                                                  else [(v1,e)]
                                    | _ => [(v1,e)]) g (ZIP (vL,bL))))’ >>
              qexists_tac ‘j’ >>
              gvs [subst_funs_def, subst_def] >>
              qspecl_then [‘g’, ‘vL’, ‘bL’] assume_tac ALOOKUP_Letrec_Delay2 >>
              gvs [] >>
              pop_assum $ drule_then assume_tac >>
              gvs [MEM_EL] >>
              Cases_on ‘y1’ >> gvs [exp_rel_def, is_Lam_def, subst_def] >>
              rw [eval_to_def] >>
              unabbrev_all_tac >>
              irule v_rel_Closure_Recclosure >>
              gvs [LIST_REL_EL_EQN, EVERY_CONJ, EL_MAP, MEM_EL] >>
              first_x_assum $ irule_at Any >> gvs []) >>
          rename1 ‘exp_rel y1 y2’ >>
          qabbrev_tac ‘handler = (FLAT (MAP2 (λ(v1,e) (v2,b).
                                                case e of
                                                | Delay e2 => if is_Lam e2 ∧ b
                                                              then [(v2,e2); (v1,Delay (Var v2))]
                                                              else [(v1,e)]
                                                | _ => [(v1,e)]) g (ZIP (vL,bL))))’ >>
          Cases_on ‘eval_to (k - 1) (subst_funs binds y1) = INL Diverge’ >> gs []
          >>~[‘($= +++ v_rel) (INL Diverge) _’]
          >- (qexists_tac ‘0’ >> Cases_on ‘eval_to k y = INL Diverge’ >> gs [] >>
              dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono >>
              gvs [] >>
              Cases_on ‘eval_to (k - 1) (subst_funs handler y2) = INL Diverge’ >> gs [] >>
              last_x_assum $ qspecl_then [‘y1’, ‘binds’, ‘subst_funs handler y2’] assume_tac >>
              qspecl_then [‘y1’, ‘λx. T’, ‘y2’, ‘binds’, ‘g’, ‘vL’, ‘bL’]
                          assume_tac exp_rel_subst_Letrec >>
              gvs [EVERY_CONJ, GSYM LAMBDA_PROD, FILTER_T, LIST_REL_EL_EQN, EL_MAP] >>
              pop_assum mp_tac >> impl_tac >>
              gvs [MEM_EL, EVERY_EL] >> rw [] >> gvs []
              >- rpt $ first_x_assum $ irule_at Any
              >- (rpt $ last_x_assum $ drule_then $ qspecl_then [‘n1’] assume_tac >>
                  dxrule_then assume_tac exp_rel_freevars >> gvs [freevars_def])
              >- (rpt $ last_x_assum $ drule_then $ qspecl_then [‘n1’] assume_tac >>
                  dxrule_then assume_tac exp_rel_boundvars >> strip_tac >>
                  gvs [boundvars_def, SUBSET_DEF]) >>
              Cases_on ‘eval_to (k - 1) (subst_funs handler y2) = INL Diverge’ >>
              gvs [subst_funs_def] >> rename1 ‘j2 + k - 1’ >>
              drule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono >> gvs [])
          >- (qexists_tac ‘0’ >> Cases_on ‘eval_to k y = INL Diverge’ >> gs [] >>
              dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono >>
              gvs [] >>
              Cases_on ‘eval_to (k - 1) (subst_funs handler y2) = INL Diverge’ >> gs [] >>
              last_x_assum $ qspecl_then [‘y1’, ‘binds’, ‘subst_funs handler y2’] assume_tac >>
              qspecl_then [‘y1’, ‘λx. T’, ‘y2’, ‘binds’, ‘g’, ‘vL’, ‘bL’]
                          assume_tac exp_rel_subst_Letrec >>
              gvs [EVERY_CONJ, GSYM LAMBDA_PROD, FILTER_T, LIST_REL_EL_EQN, EL_MAP] >>
              pop_assum mp_tac >> impl_tac >>
              gvs [MEM_EL, EVERY_EL] >> rw [] >> gvs []
              >- rpt $ first_x_assum $ irule_at Any
              >- (rpt $ last_x_assum $ drule_then $ qspecl_then [‘n1’] assume_tac >>
                  dxrule_then assume_tac exp_rel_freevars >> gvs [freevars_def])
              >- (rpt $ last_x_assum $ drule_then $ qspecl_then [‘n1’] assume_tac >>
                  dxrule_then assume_tac exp_rel_boundvars >> strip_tac >>
                  gvs [boundvars_def, SUBSET_DEF]) >>
              Cases_on ‘eval_to (k - 1) (subst_funs handler y2) = INL Diverge’ >>
              gvs [subst_funs_def] >> rename1 ‘j2 + k - 1’ >>
              drule_then (qspecl_then [‘j2 + k - 1’] assume_tac) eval_to_mono >> gvs []) >>
          Q.REFINE_EXISTS_TAC ‘j1 + j’ >>
          ‘∀i. eval_to (i + j + k) y = eval_to (j + k) y’
            by (gen_tac >> irule eval_to_mono >> gvs []) >>
          rw [] >>
          last_x_assum $ qspecl_then [‘y1’, ‘binds’, ‘subst_funs handler y2’] mp_tac >>
          impl_tac
          >- (qspecl_then [‘y1’, ‘λx. T’, ‘y2’, ‘binds’, ‘g’, ‘vL’, ‘bL’]
                        assume_tac exp_rel_subst_Letrec >>
              gvs [EVERY_CONJ, GSYM LAMBDA_PROD, FILTER_T, LIST_REL_EL_EQN,
                   EL_MAP, subst_funs_def] >>
              first_x_assum irule >> gvs [MEM_EL] >> gvs [EVERY_MEM] >> rw [] >>
              rpt $ last_x_assum $ drule_then assume_tac >> gvs [MEM_EL, PULL_EXISTS] >>
              rpt $ first_x_assum $ qspecl_then [‘n1’] assume_tac >> gvs [] >>
              drule_then assume_tac exp_rel_boundvars >> drule_then assume_tac exp_rel_freevars >>
              strip_tac >> gvs [SUBSET_DEF, freevars_def, boundvars_def])
          >- (disch_then $ qx_choose_then ‘j1’ assume_tac >>
              ‘eval_to (j + j1 + k - 1) (subst_funs handler y2)
               = eval_to (j1 + k - 1) (subst_funs handler y2)’
                by (irule eval_to_mono >>
                    Cases_on ‘eval_to (j1 + k - 1) (subst_funs handler y2)’ >>
                    Cases_on ‘eval_to (k - 1) (subst_funs binds y1)’ >>
                    gvs []) >>
              qexists_tac ‘j1’ >> gvs [])
          >- (qspecl_then [‘y1’, ‘λx. T’, ‘y2’, ‘binds’, ‘g’, ‘vL’, ‘bL’]
                   assume_tac exp_rel_subst_Letrec >>
              gvs [EVERY_CONJ, GSYM LAMBDA_PROD, FILTER_T, LIST_REL_EL_EQN,
                   EL_MAP, subst_funs_def] >>
              first_x_assum irule >> gvs [MEM_EL] >> gvs [EVERY_MEM] >> rw [] >>
              rpt $ last_x_assum $ drule_then assume_tac >> gvs [MEM_EL, PULL_EXISTS] >>
              rpt $ first_x_assum $ qspecl_then [‘n1’] assume_tac >> gvs [] >>
              drule_then assume_tac exp_rel_boundvars >> drule_then assume_tac exp_rel_freevars >>
              strip_tac >> gvs [SUBSET_DEF, freevars_def, boundvars_def])
          >- (disch_then $ qx_choose_then ‘j1’ assume_tac >>
              ‘eval_to (j + j1 + k - 1) (subst_funs handler y2)
               = eval_to (j1 + k - 1) (subst_funs handler y2)’
                by (irule eval_to_mono >>
                    Cases_on ‘eval_to (j1 + k - 1) (subst_funs handler y2)’ >>
                    Cases_on ‘eval_to (k - 1) (subst_funs binds y1)’ >>
                    gvs []) >>
              qexists_tac ‘j1’ >> gvs []))
      >- (rename [‘LIST_REL _ (MAP SND xs) (MAP SND ys)’]
          \\ ‘∀s. OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
            by (gen_tac \\ irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, LIST_EQ_REWRITE, EL_MAP])
          \\ gvs [OPTREL_def]
          \\ CASE_TAC
          >- (qexists_tac ‘j’
              \\ gvs [dest_anyThunk_def]
              \\ rename1 ‘ALOOKUP _ n’ \\ first_x_assum $ qspecl_then [‘n’] assume_tac
              \\ gvs []
              \\ rename1 ‘exp_rel x0 _’
              \\ Cases_on ‘x0’ \\ gvs [exp_rel_def])
          \\ rename1 ‘subst_funs binds y1’
          \\ Cases_on ‘eval_to (k - 1) (subst_funs binds y1) = INL Diverge’ \\ gs []
          >- (qexists_tac ‘0’
              \\ Cases_on ‘eval_to k y = INL Diverge’ \\ gs []
              \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono
              \\ gvs [dest_anyThunk_def]
              \\ rename1 ‘ALOOKUP _ n’ \\ first_x_assum $ qspecl_then [‘n’] assume_tac
              \\ gvs []
              \\ rename1 ‘exp_rel x0 _’
              \\ Cases_on ‘x0’ \\ gvs [exp_rel_def]
              \\ rename1 ‘_ (INL Diverge) (eval_to _ (subst_funs binds2 y2))’
              \\ last_x_assum $ qspecl_then [‘e’, ‘binds’, ‘subst_funs binds2 y2’] mp_tac
              \\ impl_tac
              >- (gvs [subst_funs_def] \\ irule exp_rel_subst
                  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                          GSYM FST_THM, GSYM SND_THM, LIST_REL_EL_EQN]
                  \\ rw [EL_MAP]
                  \\ ‘∀i. i < LENGTH binds2 ⇒ FST (EL i binds) = FST (EL i binds2)’
                    by (rw [] >>
                        ‘i < LENGTH binds’ by gs [] >>
                        dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                        ‘i < LENGTH binds2’ by gs [] >>
                    dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                        rw [])
                  \\ first_x_assum $ drule_then assume_tac \\ gvs []
                  \\ rename1 ‘v_rel (_ p1) (_ p2)’ \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’
                  \\ gvs [v_rel_def, LIST_REL_EL_EQN])
              \\ disch_then $ qx_choose_then ‘j1’ assume_tac
              \\ Cases_on ‘eval_to (k - 1) (subst_funs binds2 y2) = INL Diverge’ \\ gs []
              \\ drule_then (qspecl_then [‘j1 + k - 1’] assume_tac) eval_to_mono
              \\ gvs [])
          \\ Q.REFINE_EXISTS_TAC ‘j1 + j’
          \\ ‘∀i. eval_to (i + j + k) y = eval_to (j + k) y’
            by (gen_tac \\ irule eval_to_mono >> gvs [])
          \\ rw []
          \\ gvs [dest_anyThunk_def]
          \\ rename1 ‘ALOOKUP _ n’ \\ first_x_assum $ qspecl_then [‘n’] assume_tac
          \\ gvs []
          \\ rename1 ‘exp_rel x0 _’
          \\ Cases_on ‘x0’ \\ gvs [exp_rel_def]
          \\ rename1 ‘_ (eval_to _ (subst_funs binds y1)) (eval_to _ (subst_funs binds2 y2))’
          \\ last_x_assum $ qspecl_then [‘y1’, ‘binds’, ‘subst_funs binds2 y2’] mp_tac
          \\ impl_tac
          >- (gvs [subst_funs_def] \\ irule exp_rel_subst
              \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                      GSYM FST_THM, GSYM SND_THM, LIST_REL_EL_EQN]
              \\ rw [EL_MAP]
              \\ ‘∀i. i < LENGTH binds2 ⇒ FST (EL i binds) = FST (EL i binds2)’
                by (rw [] >>
                    ‘i < LENGTH binds’ by gs [] >>
                    dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                    ‘i < LENGTH binds2’ by gs [] >>
                    dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                    rw [])
              \\ first_x_assum $ drule_then assume_tac \\ gvs []
              \\ rename1 ‘v_rel (_ p1) (_ p2)’ \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’
              \\ gvs [v_rel_def, LIST_REL_EL_EQN])
          \\ disch_then $ qx_choose_then ‘j1’ assume_tac \\ qexists_tac ‘j1’
          \\ ‘eval_to (j + j1 + k - 1) (subst_funs binds2 y2)
                  = eval_to (j1 + k - 1) (subst_funs binds2 y2)’
            by (irule eval_to_mono \\ gvs []
                \\ strip_tac \\ Cases_on ‘eval_to (k - 1) (subst_funs binds y1)’ \\ gs [])
          \\ gvs [])
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
    gvs [Once exp_rel_def, eval_to_def])
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
  >- (rename1 ‘MAP2 _ g2 (ZIP (vL, bL))’
      \\ qspecl_then [‘g2’, ‘vL’, ‘bL’] assume_tac ALOOKUP_Letrec_Delay3
      \\ gvs [EVERY_CONJ]
      \\ first_x_assum $ drule_then assume_tac
      \\ rename1 ‘EL i _’ \\ Cases_on ‘EL i g2’
      \\ gvs [LIST_REL_EL_EQN]
      \\ last_assum $ drule_then assume_tac \\ gvs [EL_MAP, exp_rel_def]
      \\ first_x_assum irule
      \\ gvs [subst_APPEND]
      \\ rename1 ‘_ (eval (subst1 s v2 (subst (FILTER _ (MAP _ f2)) ef))) _’
      \\ qspecl_then [‘ef’, ‘[(s, v2)]’,
                      ‘FILTER (λ(v,e). v ≠ s) (MAP (λ(v,x). (v, Recclosure f2 v)) f2)’]
                     mp_tac subst_commutes
      \\ impl_tac
      >- (gvs [] \\ strip_tac
          \\ gvs [MEM_MAP, MEM_FILTER]
          \\ pairarg_tac \\ gvs [])
      \\ rw []
      \\ qspecl_then [‘MAP (λ(v,x).(v,Recclosure f2 v)) f2’, ‘subst1 s v2 ef’, ‘{s}’]
                     assume_tac subst_remove
      \\ gvs [freevars_subst]
      \\ irule exp_rel_eval
      \\ qspecl_then [‘subst1 s v2 ef’, ‘K T’] assume_tac exp_rel_subst_Letrec
      \\ gvs [FILTER_T, GSYM LAMBDA_PROD]
      \\ first_x_assum irule
      \\ irule_at Any exp_rel_subst
      \\ gvs [LIST_REL_EL_EQN, EVERY_CONJ, EVERY_MEM] \\ rw []
      >- (rpt $ first_x_assum $ drule_then assume_tac
          \\ gvs [MEM_EL, PULL_EXISTS]
          \\ rpt $ first_x_assum $ qspecl_then [‘i’] assume_tac
          \\ drule_then assume_tac exp_rel_freevars
          \\ dxrule_then assume_tac exp_rel_boundvars
          \\ gvs [freevars_def, boundvars_def, SUBSET_DEF, freevars_subst])
      >- (rpt $ first_x_assum $ drule_then assume_tac
          \\ gvs [MEM_EL, PULL_EXISTS]
          \\ rpt $ first_x_assum $ qspecl_then [‘i’] assume_tac
          \\ drule_then assume_tac exp_rel_freevars
          \\ dxrule_then assume_tac exp_rel_boundvars
          \\ rename1 ‘EL n vL ∉ _’
          \\ strip_tac
          \\ gvs [freevars_def, boundvars_def, SUBSET_DEF, boundvars_subst]
          \\ first_x_assum $ qspecl_then [‘EL n vL’] assume_tac
          \\ gvs [])
      \\ gvs [EL_MAP])
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
  >- (CASE_TAC \\ gvs [ALOOKUP_NONE, MAP_REVERSE]
      \\ dxrule_then assume_tac ALOOKUP_MEM \\ gvs []
      \\ drule_then (drule_then assume_tac) ALOOKUP_Letrec_Delay
      \\ gvs [EVERY_CONJ, MEM_EL, PULL_EXISTS, EL_MAP, LIST_REL_EL_EQN]
      \\ first_x_assum $ drule_then assume_tac
      \\ rename1 ‘(FST (EL n g2), _) = EL n2 l’
      \\ drule_then (qspecl_then [‘n’, ‘n2’] assume_tac) ALL_DISTINCT_EL_IMP \\ gvs [EL_MAP]
      \\ ‘∀i. i < LENGTH g2 ⇒ FST (EL i g2) = FST (EL i l)’
        by (rw [] >>
            ‘i < LENGTH g2’ by gs [] >>
            dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
            ‘i < LENGTH l’ by gs [] >>
            dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
            rw [])
      \\ Cases_on ‘EL n2 l’ \\ gvs []
      \\ rename1 ‘EL n _’ \\ Cases_on ‘EL n g2’ \\ gvs []
      \\ first_x_assum $ drule_then assume_tac \\ gs []
      \\ rename1 ‘EL n l = (name, e1)’ \\ rename1 ‘EL n g2 = (name, e2)’
      \\ ‘exp_rel e1 e2’ by (last_x_assum $ dxrule_then assume_tac \\ gvs [])
      \\ Cases_on ‘e1’ \\ gvs [exp_rel_def] \\ rw []
      \\ first_x_assum irule
      \\ irule exp_rel_eval
      \\ gvs [subst_APPEND]
      \\ rename1 ‘exp_rel (subst _ (subst1 s v2 e)) _’
      \\ qspecl_then [‘subst1 s v2 e’, ‘K T’] assume_tac exp_rel_subst_Letrec
      \\ gvs [FILTER_T, GSYM LAMBDA_PROD]
      \\ first_x_assum irule
      \\ irule_at Any exp_rel_subst
      \\ gvs [EVERY_CONJ, freevars_subst, boundvars_subst, LIST_REL_EL_EQN, EL_MAP, EVERY_MEM]
      \\ rw []
      \\ rpt $ first_x_assum $ drule_then assume_tac
      \\ gvs [MEM_EL, PULL_EXISTS]
      \\ rpt $ first_x_assum $ qspecl_then [‘n’] assume_tac
      \\ drule_then assume_tac exp_rel_freevars
          \\ drule_then assume_tac exp_rel_boundvars
      >- (‘∀(A : string -> bool) B. A = B ⇒ ∀x. x ∈ A ⇒ x ∈ B’ by gvs []
          \\ pop_assum $ dxrule_then assume_tac
          \\ gvs [freevars_def, boundvars_def]
          \\ strip_tac \\ first_x_assum $ dxrule_then assume_tac
          \\ gvs [])
      \\ gvs [freevars_def, boundvars_def, SUBSET_DEF]
      \\ rename1 ‘EL n2 vL ∉ boundvars _’ \\ first_x_assum $ qspecl_then [‘EL n2 vL’] assume_tac
      \\ strip_tac \\ gvs [])
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
