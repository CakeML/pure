(*
  Defines and prove correctness of a relation to rewrite
     Let v = Delay (Var v2) in Force (Var v)
  into
     Let v = Delay (Var v2) in (Var v2)

  This relation comes with the one defined in thunk_Delay_Lam.
*)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLangTheory
     thunkLang_primitivesTheory dep_rewrite wellorderTheory arithmeticTheory;
open pure_miscTheory thunkLangPropsTheory thunk_semanticsTheory thunk_NRC_relTheory;

val _ = new_theory "thunk_Let_Delay_Var";

Definition ok_bind_def[simp]:
  ok_bind (Delay x) = T ∧
  ok_bind (Lam s x) = T ∧
  ok_bind _ = F
End

Definition is_Lam_def[simp]:
  is_Lam (Lam s x) = T ∧
  is_Lam _ = F
End

Definition replace_Force_def:
  (replace_Force expr v1 (Force (Var v2)) = if v1 = v2
                                          then expr
                                          else Force (Var v2)) ∧
  (replace_Force expr v (Lam s e) = if v = s
                                   then Lam s e
                                   else Lam s (replace_Force expr v e)) ∧
  (replace_Force expr v1 (Var v2) = Var v2) ∧
  (replace_Force expr v (App e1 e2) = App (replace_Force expr v e1) (replace_Force expr v e2)) ∧
  (replace_Force expr v (Prim op eL) = Prim op (MAP (λe. replace_Force expr v e) eL)) ∧
  (replace_Force expr v (If e1 e2 e3) = If (replace_Force expr v e1)
                                          (replace_Force expr v e2) (replace_Force expr v e3)) ∧
  (replace_Force expr v (Seq e1 e2) = Seq (replace_Force expr v e1) (replace_Force expr v e2)) ∧
  (replace_Force expr v (Let (SOME s) e1 e2) = if v = s
                                          then Let (SOME s) (replace_Force expr v e1) e2
                                          else Let (SOME s) (replace_Force expr v e1) (replace_Force expr v e2)) ∧
  (replace_Force expr v (Delay e) = Delay (replace_Force expr v e)) ∧
  (replace_Force expr v (Box e) = Box (replace_Force expr v e)) ∧
  (replace_Force expr v (MkTick e) = MkTick (replace_Force expr v e)) ∧
  (replace_Force expr v (Value val) = Value val) ∧
  (replace_Force expr v (Force e) = Force (replace_Force expr v e)) ∧
  (replace_Force expr v (Letrec binds e) = if MEM v (MAP FST binds)
                                          then Letrec binds e
                                          else Letrec (MAP (λ(n,e). (n, replace_Force expr v e)) binds)
                                                      (replace_Force expr v e))
Termination
  WF_REL_TAC ‘measure $ exp_size o (SND o SND)’ \\ rw []
End

Definition unreplace_Force_def:
  (unreplace_Force w v (Lam s e) = if v = s
                                   then Lam s e
                                   else Lam s (unreplace_Force w v e)) ∧
  (unreplace_Force w v1 (Var v2) = if v1 = v2 then Force (Var w) else Var v2) ∧
  (unreplace_Force w v (App e1 e2) = App (unreplace_Force w v e1) (unreplace_Force w v e2)) ∧
  (unreplace_Force w v (Prim op eL) = Prim op (MAP (λe. unreplace_Force w v e) eL)) ∧
  (unreplace_Force w v (If e1 e2 e3) = If (unreplace_Force w v e1)
                                          (unreplace_Force w v e2) (unreplace_Force w v e3)) ∧
  (unreplace_Force w v (Seq e1 e2) = Seq (unreplace_Force w v e1) (unreplace_Force w v e2)) ∧
  (unreplace_Force w v (Let (SOME s) e1 e2) = if v = s
                                          then Let (SOME s) (unreplace_Force w v e1) e2
                                              else Let (SOME s) (unreplace_Force w v e1)
                                                       (unreplace_Force w v e2)) ∧
  (unreplace_Force w v (Delay e) = Delay (unreplace_Force w v e)) ∧
  (unreplace_Force w v (Box e) = Box (unreplace_Force w v e)) ∧
  (unreplace_Force w v (MkTick e) = MkTick (unreplace_Force w v e)) ∧
  (unreplace_Force w v (Value val) = Value val) ∧
  (unreplace_Force w v (Force e) = Force (unreplace_Force w v e)) ∧
  (unreplace_Force w v (Letrec binds e) = if MEM v (MAP FST binds)
                                          then Letrec binds e
                                          else Letrec (MAP (λ(n,e).
                                                              (n, unreplace_Force w v e)) binds)
                                                      (unreplace_Force w v e))
Termination
  WF_REL_TAC ‘measure $ exp_size o (SND o SND)’ \\ rw []
End

Theorem unreplace_Force_notin_frees:
  ∀e v w. w ∉ freevars e
          ⇒
          unreplace_Force v w e = e
Proof
  Induct using freevars_ind
  \\ gvs [unreplace_Force_def, freevars_def]
  >- (rw [] \\ irule LIST_EQ \\ rw [EL_MAP]
      \\ last_x_assum irule
      \\ rename1 ‘EL n xs’
      \\ last_x_assum $ qspec_then ‘freevars (EL n xs)’ assume_tac
      \\ gvs [MEM_MAP, EL_MEM]
      \\ first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL \\ simp [EL_MEM])
  >- rw [unreplace_Force_def]
  >- rw []
  >- (rw []
      \\ irule LIST_EQ \\ rw [EL_MAP]
      \\ pairarg_tac \\ gs []
      \\ last_x_assum irule
      \\ rename1 ‘EL i f = (n, e2)’
      \\ last_x_assum $ qspec_then ‘freevars e2’ assume_tac
      \\ gvs [MEM_MAP, MEM_EL]
      >- metis_tac [])
QED

Theorem unreplace_replace_Force:
  ∀e v w. w ∉ freevars e ∧ w ∉ boundvars e
          ⇒
          unreplace_Force v w (replace_Force (Var w) v e) = e
Proof
  Induct using freevars_ind
  \\ gvs [replace_Force_def, unreplace_Force_def, freevars_def, boundvars_def]
  >- (rw [] \\ irule LIST_EQ \\ rw [EL_MAP]
      \\ last_x_assum irule
      \\ rename1 ‘EL n xs’
      \\ last_x_assum $ qspec_then ‘freevars (EL n xs)’ assume_tac
      \\ last_x_assum $ qspec_then ‘boundvars (EL n xs)’ assume_tac
      \\ gvs [MEM_MAP, EL_MEM]
      \\ first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL \\ simp [EL_MEM])
  >- (rw [unreplace_Force_def] \\ gvs [unreplace_Force_notin_frees])
  >- (rw [unreplace_Force_def] \\ gvs [unreplace_Force_notin_frees])
  >- (rw [unreplace_Force_def] \\ gvs [unreplace_Force_notin_frees, MEM_EL, PULL_EXISTS]
      >- (irule LIST_EQ \\ rw [EL_MAP]
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs [EL_MAP]
          \\ irule unreplace_Force_notin_frees
          \\ rename1 ‘EL n2 f = (_, _)’
          \\ last_x_assum $ qspec_then ‘freevars (SND (EL n2 f))’ assume_tac \\ gs []
          \\ first_x_assum $ qspec_then ‘n2’ assume_tac \\ gvs [EL_MAP])
      \\ rw []
      >- (gvs [EL_MAP]
          \\ pairarg_tac \\ rename1 ‘n < _’
          \\ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_MAP])
      >- (gvs [EL_MAP]
          \\ pairarg_tac \\ rename1 ‘n < _’
          \\ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [EL_MAP])
      \\ irule LIST_EQ \\ rw [EL_MAP]
      \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gvs []
      \\ last_x_assum $ drule_then assume_tac \\ gs []
      \\ pop_assum irule
      \\ rename1 ‘EL i f = (_, _)’
      \\ last_x_assum $ qspec_then ‘freevars (SND (EL i f))’ assume_tac
      \\ last_x_assum $ qspec_then ‘boundvars (SND (EL i f))’ assume_tac
      \\ gvs []
      \\ first_x_assum $ qspec_then ‘i’ assume_tac \\ gvs [EL_MAP])
  \\ rw []
  \\ last_x_assum $ drule_all_then assume_tac
  \\ rename1 ‘Force e’
  \\ Cases_on ‘e’ \\ gvs [replace_Force_def, unreplace_Force_def]
  \\ rw [unreplace_Force_def]
QED

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
[~Letrec_Delay_Var:]
  (∀f g x y v1 v2.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
     ALL_DISTINCT (MAP FST f) ∧
     v1 ≠ v2 ∧ EVERY (λe. v2 ∉ boundvars e) (MAP SND g) ∧ v2 ∉ boundvars y ∧
     MEM v2 (MAP FST f) ∧ MEM (v1, Delay (Var v2)) f ∧
     exp_rel x y ⇒
     exp_rel (Letrec f x)
             (Letrec (MAP (λ(v,e). (v, replace_Force (Var v2) v1 e)) g)
              (replace_Force (Var v2) v1 y))) ∧
[~Let:]
  (∀opt x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let opt x1 y1) (Let opt x2 y2)) ∧
[~Let_Delay_Var:]
  (∀v1 v2 x1 x2 y1 y2.
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y2 ∧ v1 ≠ v2 ∧
     exp_rel x1 x2 ∧ exp_rel y1 y2 ⇒
     exp_rel (Let (SOME v2) x1 (Let (SOME v1) (Delay (Var v2)) y1))
             (Let (SOME v2) x2 (Let (SOME v1) (Delay (Var v2)) (replace_Force (Var v2) v1 y2)))) ∧
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
[~Force_Value:]
  (∀v1 v2.
     v_rel v1 v2 ⇒
     exp_rel (Force (Value (Thunk (INR (Value v1))))) (Value v2)) ∧
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
[v_rel_Recclosure_Delay_Var:]
  (∀f g n v1 v2.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
     ALL_DISTINCT (MAP FST f) ∧
     v1 ≠ v2 ∧ EVERY (λe. v2 ∉ boundvars e) (MAP SND g) ∧
     MEM v2 (MAP FST f) ∧ MEM (v1, Delay (Var v2)) f ⇒
     v_rel (Recclosure f n) (Recclosure (MAP (λ(v,e). (v, replace_Force (Var v2) v1 e)) g) n)) ∧
[~Force_Recclosure_Delay_Var:]
  (∀f g v1 v2.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
     ALL_DISTINCT (MAP FST f) ∧
     v1 ≠ v2 ∧ EVERY (λe. v2 ∉ boundvars e) (MAP SND g) ∧
     MEM v2 (MAP FST f) ∧ MEM (v1, Delay (Var v2)) f ⇒
     exp_rel (Force (Value (Recclosure f v1)))
             (Value (Recclosure (MAP (λ(v,e). (v, replace_Force (Var v2) v1 e)) g) v2))) ∧
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
  |> LIST_CONJ;

Theorem subst_replace_Force:
  ∀e expr v l. DISJOINT (freevars expr) (boundvars e) ∧ ¬MEM v (MAP FST l) ⇒
               subst l (replace_Force expr v e) = replace_Force (subst l expr) v (subst l e)
Proof
  Induct using freevars_ind >>
  gvs [replace_Force_def, subst_def, boundvars_def, freevars_def] >> rw []
  >- (CASE_TAC >> gvs [replace_Force_def])
  >- (irule LIST_EQ >> rw [EL_MAP] >>
      last_x_assum irule >> gvs [EL_MEM, MEM_EL, PULL_EXISTS, EL_MAP])
  >- (last_x_assum $ irule >> gvs [DISJOINT_DEF, INTER_COMM])
  >- (last_x_assum $ irule >> gvs [DISJOINT_DEF, INTER_COMM])
  >- (last_x_assum $ irule >> gvs [DISJOINT_DEF, INTER_COMM])
  >- (last_x_assum $ irule >> gvs [DISJOINT_DEF, INTER_COMM])
  >- (last_x_assum $ irule >> gvs [DISJOINT_DEF, INTER_COMM])
  >- gvs [subst_def]
  >- (gvs [subst_def] >> irule EQ_TRANS >>
      last_x_assum $ irule_at Any >>
      gvs [MEM_MAP, MEM_FILTER, DISJOINT_DEF, INTER_COMM] >>
      AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
      rename1 ‘subst (FILTER (λ(n,x). n ≠ s) l) expr = _’ >>
      qspecl_then [‘l’, ‘expr’, ‘{s}’] assume_tac subst_remove >> gvs [])
  >- (last_x_assum $ irule >> gvs [DISJOINT_DEF, INTER_COMM])
  >- (last_x_assum $ irule >> gvs [DISJOINT_DEF, INTER_COMM])
  >- (gvs [subst_def] >>
      last_x_assum $ irule >> gvs [DISJOINT_DEF, INTER_COMM])
  >- (gvs [subst_def] >>
      last_x_assum $ irule_at Any >> gvs [DISJOINT_DEF, INTER_COMM] >>
      irule EQ_TRANS >>
      first_x_assum $ irule_at Any >> gvs [MEM_MAP, MEM_FILTER] >>
      AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
      rename1 ‘subst (FILTER (λ(n,x). n ≠ s) l) expr = _’ >>
      qspecl_then [‘l’, ‘expr’, ‘{s}’] assume_tac subst_remove >> gvs [])
  >- gvs [subst_def] >>
  gvs [subst_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  >- (irule_at Any LIST_EQ >>
      rw [EL_MAP]
      >~[‘EL n _’]
      >- (pairarg_tac >> gs [] >>
          irule EQ_TRANS >> last_x_assum $ irule_at Any >>
          gvs [MEM_MAP, MEM_FILTER] >>
          gvs [MEM_EL, PULL_EXISTS] >>
          first_assum $ irule_at Any >>
          first_x_assum $ drule_then assume_tac >>
          gvs [DISJOINT_DEF, INTER_COMM] >>
          AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
          rename1 ‘MAP FST f’ >>
          rename1 ‘subst (FILTER _ l) expr = _’ >>
          qspecl_then [‘l’, ‘expr’, ‘set (MAP FST f)’] assume_tac subst_remove >>
          gvs [MEM_MAP, MEM_EL, DISJOINT_DEF, INTER_COMM]) >>
      irule EQ_TRANS >> first_x_assum $ irule_at Any >>
      gvs [MEM_MAP, MEM_FILTER, DISJOINT_DEF, INTER_COMM] >>
      AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
      rename1 ‘MAP FST f’ >>
      rename1 ‘subst (FILTER _ l) expr = _’ >>
      qspecl_then [‘l’, ‘expr’, ‘set (MAP FST f)’] assume_tac subst_remove >>
      gvs [MEM_MAP, DISJOINT_DEF, INTER_COMM]) >>
  rename1 ‘Force e’ >> Cases_on ‘e’ >>
  gvs [replace_Force_def, subst_def]
  >- (IF_CASES_TAC
      >- (CASE_TAC >> gvs [replace_Force_def, subst_def] >>
          dxrule_then assume_tac ALOOKUP_MEM >>
          gvs [MEM_MAP])
      >- (CASE_TAC >> gvs [subst_def, replace_Force_def])) >>
  rename1 ‘Let opt e1 e2’ >>
  Cases_on ‘opt’ >> gvs [subst_def, replace_Force_def]
QED

Theorem replace_Force_ignore:
  ∀e expr v. v ∉ freevars e ⇒ replace_Force expr v e = e
Proof
  Induct using freevars_ind >>
  gvs [replace_Force_def, freevars_def] >> rw []
  >- (irule LIST_EQ >> rw [EL_MAP] >>
      last_x_assum irule >>
      rename1 ‘freevars (EL n xs)’ >>
      last_x_assum $ qspecl_then [‘freevars (EL n xs)’] assume_tac >>
      gvs [EL_MEM, MEM_MAP] >>
      strip_tac >> first_x_assum $ resolve_then (Pos hd) irule EQ_REFL >>
      gvs [EL_MEM])
  >- (irule LIST_EQ >> rw [EL_MAP] >>
      pairarg_tac >> gvs [] >>
      last_x_assum irule >>
      irule_at Any $ iffRL MEM_EL >>
      first_assum $ irule_at Any >> gvs [] >>
      rename1 ‘freevars e2’ >>
      last_x_assum $ qspecl_then [‘freevars e2’] assume_tac >>
      gvs [] >>
      strip_tac >> first_x_assum irule >>
      gvs [MEM_EL, EL_MAP] >> first_assum $ irule_at Any >> gvs [EL_MAP]) >>
  rename1 ‘Force e’ >> Cases_on ‘e’ >>
  gvs [replace_Force_def, freevars_def]
QED

Theorem replace_Force_COMM:
  ∀e expr1 expr2 v w. v ≠ w ∧ v ∉ freevars expr2 ∧ w ∉ freevars expr1 ⇒
             replace_Force expr1 v (replace_Force expr2 w e)
             = replace_Force expr2 w (replace_Force expr1 v e)
Proof
  Induct using freevars_ind >>
  gvs [replace_Force_def, freevars_def] >> rw [] >> gvs [replace_Force_def]
  >- (irule LIST_EQ >> rw [EL_MAP] >>
      last_x_assum irule >> gvs [EL_MEM])
  >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
      irule LIST_EQ >> rw [EL_MAP] >>
      pairarg_tac >> gvs [] >>
      last_x_assum irule >>
      irule_at Any $ iffRL MEM_EL >>
      first_assum $ irule_at Any >> gvs []) >>
  rename1 ‘Force e’ >> Cases_on ‘e’ >>
  gvs [replace_Force_def, freevars_def] >> rw [] >>
  gvs [replace_Force_def, replace_Force_ignore]
  >- (first_x_assum $ dxrule_then $ dxrule_then $ dxrule_then assume_tac >> gvs [replace_Force_def])
  >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
  >- (first_x_assum $ dxrule_then $ dxrule_then $ dxrule_then assume_tac >>
      gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, replace_Force_def] >>
      metis_tac [])
  >~[‘Let opt _ _’]
  >- (last_x_assum $ dxrule_all_then assume_tac >>
      Cases_on ‘opt’ >> gvs [replace_Force_def]
      >- metis_tac [] >>
      rw [replace_Force_def] >> gvs [replace_Force_def])
  >- (last_x_assum $ drule_all_then assume_tac >>
      rename1 ‘Force (replace_Force _ _ (Force e))’ >>
      Cases_on ‘e’ >> rw [replace_Force_def] >> gvs [replace_Force_def]
      >- (irule replace_Force_ignore >> gvs [freevars_def])
      >- (irule $ GSYM replace_Force_ignore >> gvs [freevars_def]))
QED

Theorem boundvars_replace_Force:
  ∀e expr n. boundvars (replace_Force expr n e) ⊆ boundvars e ∪ boundvars expr
Proof
  Induct using freevars_ind >> gvs [replace_Force_def] >>
  rw [] >> gvs [boundvars_def]
  >>~[‘BIGUNION _’]
  >- (rw [BIGUNION_SUBSET, MEM_MAP] >>
      last_x_assum $ drule_then assume_tac >>
      gvs [SUBSET_DEF] >> rw [] >> last_x_assum $ dxrule_then assume_tac >>
      gvs [MEM_MAP] >> disj1_tac >>
      rpt $ first_x_assum $ irule_at Any >> gvs [])
  >- (gvs [MEM_MAP, SUBSET_DEF] >> rw []
      >- (first_x_assum $ drule_then assume_tac >> gvs [])
      >- (rename1 ‘MEM y _’ >> PairCases_on ‘y’ >> gvs [] >>
          last_x_assum $ drule_all_then assume_tac >>
          gvs [] >> disj1_tac >> disj1_tac >> disj2_tac >>
          first_x_assum $ irule_at $ Pos last >> gvs []) >>
      rename1 ‘MEM y _’ >> PairCases_on ‘y’ >> gvs [] >>
      disj1_tac >> disj2_tac >>
      first_x_assum $ irule_at Any >> gvs [])
  >~[‘Force e’]
  >- (Cases_on ‘e’ >> gvs [replace_Force_def, boundvars_def] >>
      rw [] >> gvs [boundvars_def]) >>
  gvs [SUBSET_DEF] >> rw [] >>
  last_x_assum $ dxrule_then assume_tac >> gvs []
QED

Theorem boundvars_replace_Force2:
  ∀e expr n. boundvars e ⊆ boundvars (replace_Force expr n e)
Proof
  Induct using freevars_ind >> gvs [replace_Force_def] >>
  rw [] >> gvs [boundvars_def]
  >>~[‘BIGUNION _’]
  >- (rw [BIGUNION_SUBSET, MEM_MAP] >>
      last_x_assum $ drule_then assume_tac >>
      gvs [SUBSET_DEF] >> rw [] >> last_x_assum $ dxrule_then assume_tac >>
      gvs [MEM_MAP] >>
      rpt $ first_x_assum $ irule_at Any >> gvs [] >>
      irule_at Any EQ_REFL)
  >- (gvs [MEM_MAP, EXISTS_PROD, SUBSET_DEF] >> rw [] >>
      first_x_assum $ drule_all_then assume_tac >> gvs [] >>
      disj1_tac >> disj2_tac >> gvs [PULL_EXISTS] >>
      rpt $ first_x_assum $ irule_at Any)
  >~[‘Force e’]
  >- (Cases_on ‘e’ >> gvs [replace_Force_def, boundvars_def]) >>
  gvs [SUBSET_DEF] >> rw [] >>
  last_x_assum $ dxrule_then assume_tac >> gvs []
QED

Theorem freevars_replace_Force_SUBSET:
  ∀e expr n. freevars (replace_Force expr n e) ⊆ freevars e ∪ freevars expr
Proof
  Induct using freevars_ind >> gvs [replace_Force_def] >>
  rw [] >> gvs [freevars_def]
  >>~[‘BIGUNION _’]
  >- (rw [BIGUNION_SUBSET, MEM_MAP] >>
      last_x_assum $ drule_then assume_tac >>
      gvs [SUBSET_DEF] >> rw [] >> last_x_assum $ dxrule_then assume_tac >>
      gvs [MEM_MAP] >> disj1_tac >>
      rpt $ first_x_assum $ irule_at Any >> gvs [])
  >- (gvs [MEM_MAP, SUBSET_DEF] >> rw []
      >- (first_x_assum $ drule_then assume_tac >> gvs [FORALL_PROD])
      >- (rename1 ‘MEM y _’ >> PairCases_on ‘y’ >> gvs [] >>
          last_x_assum $ drule_all_then assume_tac >>
          gvs [FORALL_PROD] >> disj1_tac >> disj2_tac >>
          first_x_assum $ irule_at $ Pos last >> gvs []))
  >~[‘Force e’]
  >- (Cases_on ‘e’ >> gvs [replace_Force_def, freevars_def] >>
      rw [] >> gvs [freevars_def]) >>
  gvs [SUBSET_DEF] >> rw [] >>
  last_x_assum $ dxrule_then assume_tac >> gvs []
QED

Theorem freevars_replace_Force:
  ∀e expr n v. n ≠ v ∧ v ∈ freevars e ⇒ v ∈ freevars (replace_Force expr n e)
Proof
  Induct using freevars_ind >> gvs [replace_Force_def] >>
  rw [] >> gvs [freevars_def]
  >>~[‘MEM _ _’]
  >- (gvs [MEM_MAP, PULL_EXISTS] >>
      rpt $ first_assum $ irule_at Any)
  >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
      disj1_tac >> first_x_assum $ dxrule_all_then irule)
  >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
      disj2_tac >>
      gvs [MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
      rpt $ first_assum $ irule_at Any)
  >~[‘Force e’]
  >- (Cases_on ‘e’ >> gvs [replace_Force_def, freevars_def, MEM_MAP, PULL_EXISTS] >>
      last_x_assum irule >> gvs []
      >- rpt $ first_x_assum $ irule_at Any >>
      disj2_tac >> rpt $ first_x_assum $ irule_at Any)
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
  >~[‘Letrec (MAP _ g) (replace_Force _ _ y)’] >- (
    rename1 ‘subst ws (Letrec (MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) g) (replace_Force (Var v2) v1 y))’
    \\ qsuff_tac ‘subst ws (Letrec (MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) g) (replace_Force (Var v2) v1 y))
                  = Letrec (MAP (λ(v,e).(v,replace_Force (Var v2) v1 e))
                                (MAP (λ(v,e).(v, subst (FILTER (λ(v,e).¬MEM v (MAP FST g)) ws) e)) g))
                           (replace_Force (Var v2) v1 (subst (FILTER (λ(v,e). ¬MEM v (MAP FST g)) ws) y))’
    >- (rw [subst_def]
        \\ irule exp_rel_Letrec_Delay_Var
        \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EVERY_EL, EL_MAP]
        \\ rw [boundvars_subst]
        >- (last_x_assum $ drule_then assume_tac
            \\ pairarg_tac \\ gvs []
            \\ rename1 ‘ok_bind (subst _ x2)’ \\ Cases_on ‘x2’ \\ gvs [ok_bind_def, subst_def])
        >- (last_x_assum $ drule_then assume_tac
            \\ last_x_assum $ drule_then assume_tac
            \\ pairarg_tac \\ gvs []
            \\ rename1 ‘ok_bind (subst _ x2)’ \\ Cases_on ‘x2’ \\ gvs [ok_bind_def, subst_def])
        >- (rpt $ last_x_assum $ drule_then assume_tac
            \\ pairarg_tac \\ gvs [boundvars_subst])
        >- (gvs [MEM_MAP] \\ first_x_assum $ irule_at Any
            \\ gvs [subst_def]
            \\ CASE_TAC \\ gvs []
            \\ dxrule_then assume_tac ALOOKUP_MEM
            \\ gvs [MEM_FILTER])
        >- (first_x_assum $ irule
            \\ dxrule_then (qspecl_then [‘v_rel’, ‘λv. ¬MEM v (MAP FST g)’] assume_tac) LIST_FILTERED
            \\ gvs [LIST_REL_EL_EQN, EL_MAP])
        >- (rename1 ‘n < _’
            \\ rpt $ first_x_assum $ drule_then assume_tac
            \\ pairarg_tac \\ gvs []
            \\ pairarg_tac \\ gvs []
            \\ first_x_assum $ irule
            \\ dxrule_then (qspecl_then [‘v_rel’, ‘λv. ¬MEM v (MAP FST g)’] assume_tac) LIST_FILTERED
            \\ gvs [LIST_REL_EL_EQN, EL_MAP]))
    \\ rw [subst_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    >- (irule LIST_EQ
        \\ rw [EL_MAP] \\ pairarg_tac \\ gvs []
        \\ irule EQ_TRANS \\ irule_at Any subst_replace_Force
        \\ rw [subst_def, freevars_def]
        >- (gvs [EVERY_EL] \\ rpt $ first_x_assum $ drule_then assume_tac
            \\ gvs [EL_MAP])
        >- (strip_tac
            \\ gvs [MEM_MAP, EXISTS_PROD, MEM_FILTER, MEM_EL]
            \\ rename1 ‘(_, Delay _) = EL n2 f’
            \\ first_x_assum $ qspecl_then [‘SND (EL n2 g)’, ‘n2’] assume_tac
            \\ ‘LENGTH f = LENGTH g’ by metis_tac [LENGTH_MAP]
            \\ gvs []
            \\ first_x_assum irule
            \\ ‘∀i. i < LENGTH f ⇒ FST (EL i f) = FST (EL i g)’
              by (rw [] >>
                  ‘i < LENGTH f’ by gs [] >>
                  dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                  ‘i < LENGTH g’ by gs [] >>
                  dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                  rw [])
            \\ first_x_assum $ qspecl_then [‘n2’] assume_tac
            \\ gvs [FST_THM, SND_THM]
            \\ pairarg_tac \\ gs []
            \\ pairarg_tac \\ gs [])
        >- (CASE_TAC \\ gs []
            \\ dxrule_then assume_tac ALOOKUP_MEM \\ gs [MEM_FILTER]))
    \\ irule EQ_TRANS \\ irule_at Any subst_replace_Force
    \\ rw [freevars_def, subst_def]
    >- (strip_tac
        \\ gvs [MEM_MAP, EXISTS_PROD, MEM_FILTER, MEM_EL]
        \\ rename1 ‘(_, Delay _) = EL n2 f’
        \\ first_x_assum $ qspecl_then [‘SND (EL n2 g)’, ‘n2’] assume_tac
        \\ ‘LENGTH f = LENGTH g’ by metis_tac [LENGTH_MAP]
        \\ gvs []
        \\ first_x_assum irule
        \\ ‘∀i. i < LENGTH f ⇒ FST (EL i f) = FST (EL i g)’
          by (rw [] >>
              ‘i < LENGTH f’ by gs [] >>
              dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
              ‘i < LENGTH g’ by gs [] >>
              dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
              rw [])
        \\ first_x_assum $ qspecl_then [‘n2’] assume_tac
        \\ gvs [FST_THM, SND_THM]
        \\ pairarg_tac \\ gs []
        \\ pairarg_tac \\ gs [])
    >- (CASE_TAC \\ gs []
        \\ dxrule_then assume_tac ALOOKUP_MEM \\ gs [MEM_FILTER]))
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
  >~[‘Let (SOME v2) x1 (Let (SOME v1) (Delay (Var v2)) y1)’] >- (
    rw [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
    \\ rename1 ‘exp_rel y1 y2’
    \\ qspecl_then [‘y2’, ‘Var v2’, ‘v1’, ‘FILTER (λ(n,x). n ≠ v1) (FILTER (λ(n, x). n ≠ v2) ws)’]
                   assume_tac subst_replace_Force
    \\ gvs [MEM_MAP, MEM_FILTER, freevars_def, FORALL_PROD, subst_def, GSYM FILTER_REVERSE]
    \\ gvs [GEN_ALL ALOOKUP_FILTER]
    \\ irule exp_rel_Let_Delay_Var
    \\ rpt $ last_assum $ irule_at Any
    \\ dxrule_then (dxrule_then $ qspecl_then [‘λx. x ≠ v1 ∧ x ≠ v2’] assume_tac) LIST_FILTERED
    \\ gvs [FILTER_FILTER, LAMBDA_PROD, freevars_subst, boundvars_subst])
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
  >>~[‘Force (Value _)’]
  >- (rw [subst_def]
      \\ gs [exp_rel_Force_Value])
   >- (rw [subst_def]
       \\ irule exp_rel_Force_Recclosure_Delay_Var
       \\ gvs [LIST_REL_CONJ, SF ETA_ss])
  >~ [‘Force x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_Force])
  >~[‘MkTick x’] >- (
    rw [subst_def]
    \\ gs [exp_rel_MkTick])
QED

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars x = freevars y
Proof
  Induct using freevars_ind >> gvs [exp_rel_def, freevars_def, PULL_EXISTS]
  >- (rw [LIST_REL_EL_EQN] >>
      AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      rw [EL_MAP] >>
      last_x_assum irule >> gvs [EL_MEM])
  >- (rw [] >> rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rw [] >> rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rw [] >> rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rw [] >> rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rw []
      >- (rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [freevars_def]) >>
      rename1 ‘_ = freevars (Let (SOME s) x2 (Let (SOME v1) (Delay (Var s)) (replace_Force (Var s) v1 y2)))’ >>
      first_x_assum $ qspecl_then [‘Let (SOME v1) (Delay (Var s)) y2’] assume_tac >>
      gvs [exp_rel_def, PULL_EXISTS, freevars_def] >>
      last_x_assum $ dxrule_then assume_tac >>
      gvs [SET_EQ_SUBSET, SUBSET_DEF] >> rw [] >>
      rpt $ first_x_assum $ drule_then assume_tac >> gvs []
      >- (disj2_tac >> irule freevars_replace_Force >> gvs []) >>
      assume_tac freevars_replace_Force_SUBSET >> gvs [SUBSET_DEF] >>
      pop_assum $ dxrule_then assume_tac >> gvs [freevars_def])
  >- (rw [] >> last_assum $ drule_then assume_tac >>
      gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP, freevars_def,
           MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
      >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
          irule LIST_EQ >> rw [EL_MAP] >>
          pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
          last_x_assum irule >>
          first_x_assum $ drule_then assume_tac >>
          first_assum $ irule_at Any >> gvs [])
      \\ rename1 ‘exp_rel x y’
      \\ last_x_assum $ qspecl_then [‘y’] assume_tac
      \\ rw [SET_EQ_SUBSET, SUBSET_DEF]
      >- (disj1_tac \\ irule freevars_replace_Force \\ gvs [exp_rel_def, freevars_def]
          \\ strip_tac \\ gvs []
          \\ rename1 ‘(v1, _) = EL n2 f’
          \\ ‘v1 = EL n2 (MAP FST f)’ by (rw [EL_MAP] \\ Cases_on ‘EL n2 f’ \\ gvs [])
          \\ gvs [EL_MEM])
      >- (disj2_tac \\ gvs [MEM_MAP, PULL_EXISTS, MEM_EL]
          \\ first_assum $ irule_at $ Pos last
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
          \\ last_x_assum $ drule_then assume_tac \\ gs []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ irule freevars_replace_Force \\ gs []
          \\ strip_tac \\ gvs []
          \\ rename1 ‘(v1, _) = EL n2 f’
          \\ ‘v1 = EL n2 (MAP FST f)’ by (rw [EL_MAP] \\ Cases_on ‘EL n2 f’ \\ gvs [])
          \\ first_x_assum $ qspecl_then [‘n2’] assume_tac \\ gs [] \\ gs [EL_MAP])
      >- (assume_tac freevars_replace_Force_SUBSET
          \\ gvs [SUBSET_DEF]
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gvs [freevars_def, MEM_EL]
          \\ rename1 ‘EL n g’
          \\ first_x_assum $ qspecl_then [‘n’] assume_tac \\ gvs [EL_MAP])
      >- (disj2_tac \\ gvs [MEM_MAP, PULL_EXISTS, MEM_EL]
          \\ first_assum $ irule_at $ Pos last
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
          \\ assume_tac freevars_replace_Force_SUBSET \\ gs [SUBSET_DEF]
          \\ pop_assum $ dxrule_then assume_tac
          \\ rpt $ last_x_assum $ drule_then assume_tac
          \\ gvs [freevars_def]
          \\ first_x_assum $ dxrule_then assume_tac \\ gs []))
  >- (rw [] >> gvs [freevars_def])
QED

Theorem exp_rel_boundvars:
  ∀x y. exp_rel x y ⇒ boundvars x = boundvars y
Proof
  Induct using freevars_ind >> gvs [exp_rel_def, boundvars_def, PULL_EXISTS]
  >- (rw [LIST_REL_EL_EQN] >>
      AP_TERM_TAC >> AP_TERM_TAC >> irule LIST_EQ >>
      rw [EL_MAP] >>
      last_x_assum irule >> gvs [EL_MEM])
  >- (rw [] >> rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rw [] >> rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rw [] >> rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rw [] >> rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [])
  >- (rw []
      >- (rpt $ last_x_assum $ dxrule_then assume_tac >> gvs [boundvars_def]) >>
      rename1 ‘_ = boundvars (Let (SOME s) x2 (Let (SOME v1) (Delay (Var s)) (replace_Force (Var s) v1 y2)))’ >>
      first_x_assum $ qspecl_then [‘Let (SOME v1) (Delay (Var s)) y2’] assume_tac >>
      gvs [exp_rel_def, PULL_EXISTS, boundvars_def] >>
      last_x_assum $ dxrule_then assume_tac >>
      gvs [SET_EQ_SUBSET, SUBSET_DEF] >> rw [] >>
      rpt $ first_x_assum $ drule_then assume_tac >> gvs []
      >- (assume_tac boundvars_replace_Force2 >> gvs [SUBSET_DEF]) >>
      assume_tac boundvars_replace_Force >> gvs [SUBSET_DEF] >>
      pop_assum $ dxrule_then assume_tac >> gvs [boundvars_def])
  >- (rw [] >> last_assum $ drule_then assume_tac >>
      gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP, boundvars_def,
           MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
      >- (AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
          irule LIST_EQ >> rw [EL_MAP] >>
          pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
          last_x_assum irule >>
          first_x_assum $ drule_then assume_tac >>
          first_assum $ irule_at Any >> gvs [])
      \\ rename1 ‘exp_rel x y’
      \\ last_x_assum $ qspecl_then [‘y’] assume_tac
      \\ rw [SET_EQ_SUBSET, SUBSET_DEF]
      >- (assume_tac boundvars_replace_Force2 \\ gvs [SUBSET_DEF])
      >- (disj1_tac \\ disj2_tac \\ gvs [MEM_MAP, PULL_EXISTS, MEM_EL]
          \\ first_assum $ irule_at $ Pos last
          \\ last_x_assum $ drule_then assume_tac
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
          \\ last_x_assum $ drule_then assume_tac \\ gs []
          \\ first_x_assum $ dxrule_then assume_tac
          \\ assume_tac boundvars_replace_Force2
          \\ gvs [SUBSET_DEF])
      >- (assume_tac boundvars_replace_Force
          \\ gvs [SUBSET_DEF]
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gvs [boundvars_def])
      >- (disj1_tac \\ disj2_tac \\ gvs [MEM_MAP, PULL_EXISTS, MEM_EL]
          \\ first_assum $ irule_at $ Pos last
          \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
          \\ last_x_assum $ drule_then assume_tac \\ gs []
          \\ last_x_assum $ drule_then assume_tac \\ gs []
          \\ first_x_assum $ dxrule_then assume_tac \\ gs []
          \\ assume_tac boundvars_replace_Force \\ gs [SUBSET_DEF]
          \\ pop_assum $ dxrule_then assume_tac
          \\ gvs [boundvars_def]))
  >- (rw [] >> gvs [boundvars_def])
QED

Theorem exp_rel_replace_Force:
  ∀x y n v. exp_rel x y ∧ n ∉ (boundvars x) ⇒
                    exp_rel (replace_Force (Var n) v x) (replace_Force (Var n) v y)
Proof
  ‘(∀x y.
     exp_rel x y ⇒
     ∀n v.
       exp_rel x y ∧ n ∉ (boundvars x) ⇒
       exp_rel (replace_Force (Var n) v x) (replace_Force (Var n) v y)) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw [] >>
  ho_match_mp_tac exp_rel_strongind >> rw [] >>
  gvs [replace_Force_def, boundvars_def]
  >~[‘Prim _ _’]
  >- (irule exp_rel_Prim >>
      gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP] >>
      rw [] >> last_x_assum $ drule_then assume_tac >> gvs [] >>
      pop_assum irule >> gvs [] >>
      rename1 ‘exp_rel (EL n2 xs) _’ >>
      first_x_assum $ qspecl_then [‘boundvars (EL n2 xs)’] assume_tac >> gvs [] >>
      first_x_assum $ qspecl_then [‘n2’] assume_tac >> gvs [EL_MAP])
  >~[‘App _ _’]
  >- gvs [exp_rel_def]
  >~[‘Lam _ _’]
  >- (IF_CASES_TAC >> gvs [exp_rel_def])
  >~[‘Letrec (MAP _ (MAP _ _)) (replace_Force (Var n) v (replace_Force (Var v2) v1 y))’]
  >- (IF_CASES_TAC >> gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_CONJ] >>
      rw [exp_rel_def] >> disj2_tac >>
      rename1 ‘¬MEM _ (MAP FST g)’ >>
      Q.REFINE_EXISTS_TAC ‘MAP (λ(v2, e).(v2, replace_Force (Var n) v e)) g’ >>
      gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
      irule_at (Pos $ el 2) replace_Force_COMM >>
      conj_asm1_tac
      >- (strip_tac >>
          ‘MEM v1 (MAP FST f)’ by (gvs [MEM_MAP] >> first_x_assum $ irule_at Any >> gvs []) >>
          gvs []) >>
      conj_asm1_tac
      >- (strip_tac >> gvs [freevars_def]) >>
      conj_asm1_tac
      >- (‘MEM v1 (MAP FST f)’ by (gvs [MEM_MAP] >> first_x_assum $ irule_at Any >> gvs []) >>
          gvs [freevars_def] >>
          strip_tac >> gvs []) >>
      rw []
      >- (irule LIST_EQ >> gvs [EL_MAP] >>
          rw [] >> pairarg_tac >> gs [] >>
          irule replace_Force_COMM >> gvs [])
      >- (gvs [EVERY_EL, EL_MAP] >> rw [] >> last_x_assum $ dxrule_then assume_tac >>
          rename1 ‘SND p’ >>
          pairarg_tac >> Cases_on ‘SND p’ >> gvs [replace_Force_def, ok_bind_def] >>
          rw [ok_bind_def])
      >- (gvs [EVERY_EL, EL_MAP] >> rw [] >>
          last_x_assum $ drule_then assume_tac >>
          last_x_assum $ dxrule_then assume_tac >>
          rename1 ‘SND p’ >>
          pairarg_tac >> Cases_on ‘SND p’ >> gvs [replace_Force_def, ok_bind_def] >>
          rw [ok_bind_def])
      >-  (gvs [LIST_REL_EL_EQN, EL_MAP] >> rw [] >>
           last_x_assum $ drule_then assume_tac >>
           last_x_assum $ drule_then assume_tac >>
           pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
           first_x_assum irule >>
           rename1 ‘_ ∉ boundvars p2’ >>
           first_x_assum $ qspecl_then [‘boundvars p2’] assume_tac >> gvs [] >>
           strip_tac >> first_x_assum irule >>
           gvs [MEM_EL] >>
           first_assum $ irule_at Any >> gvs [EL_MAP])
      >- (gvs [EVERY_EL, EL_MAP] >> rw [] >>
          last_x_assum $ drule_then kall_tac >>
          last_x_assum $ drule_then assume_tac >>
          pairarg_tac >> gs [] >>
          strip_tac >> assume_tac boundvars_replace_Force >>
          gvs [SUBSET_DEF] >> first_x_assum $ dxrule_then assume_tac >>
          gvs [boundvars_def])
      >- (strip_tac >> assume_tac boundvars_replace_Force >>
          gvs [SUBSET_DEF] >> first_x_assum $ dxrule_then assume_tac >>
          gvs [boundvars_def])
      >- (rw [MEM_MAP] >>
          first_x_assum $ irule_at Any >>
          gvs [replace_Force_def]))
  >~[‘Letrec _ _’]
  >- (IF_CASES_TAC >> gs [] >>
      irule exp_rel_Letrec >>
      gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_CONJ,
           LIST_REL_EL_EQN, EL_MAP, EVERY_EL] >>
      rw [] >> rename1 ‘n2 < _’ >>
      rpt $ last_x_assum $ qspecl_then [‘n2’] assume_tac
      >- (rename1 ‘SND (_ p1)’ >>
          pairarg_tac >>
          Cases_on ‘SND p1’ >> gvs [ok_bind_def, replace_Force_def] >>
          rw [ok_bind_def])
      >- (rename1 ‘SND (_ p2)’ >>
          rename1 ‘exp_rel (SND p1) (SND p2)’ >>
          pairarg_tac >>
          Cases_on ‘SND p1’ >> gvs [exp_rel_def, ok_bind_def, replace_Force_def] >>
          rw [ok_bind_def])
      >- (pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
          first_x_assum irule >> gs [] >>
          rename1 ‘n ∉ boundvars e2’ >>
          first_x_assum $ qspecl_then [‘boundvars e2’] assume_tac >>
          strip_tac >> gvs [] >>
          first_x_assum irule >>
          gvs [MEM_EL] >>
          first_assum $ irule_at Any >> gvs [EL_MAP]))
  >~[‘Let _ _ (replace_Force _ _ (replace_Force _ _ _))’]
  >- (IF_CASES_TAC >> gvs []
      >- (irule exp_rel_Let_Delay_Var >> gvs []) >>
      IF_CASES_TAC >> gvs []
      >- (irule exp_rel_Let_Delay_Var >> gvs []) >>
      rw [exp_rel_def] >>
      disj2_tac >>
      irule_at Any replace_Force_COMM >>
      gvs [freevars_def] >>
      assume_tac freevars_replace_Force_SUBSET >>
      assume_tac boundvars_replace_Force >>
      rw [] >> strip_tac >>
      gvs [SUBSET_DEF] >>
      first_x_assum $ dxrule_then assume_tac >>
      gvs [freevars_def, boundvars_def])
  >~[‘Let opt _ _’]
  >- (Cases_on ‘opt’ >> gvs [replace_Force_def]
      >~[‘Seq _ _’]
      >- gvs [exp_rel_def, boundvars_def] >>
      IF_CASES_TAC >> gvs [] >>
      irule exp_rel_Let >> gvs [boundvars_def]) >>
  rw [exp_rel_def] >> gvs [] >>
  rename1 ‘exp_rel (Force x) _’ >>
  qpat_x_assum ‘exp_rel (Force x) _’ kall_tac >>
  first_x_assum $ dxrule_then assume_tac >>
  Cases_on ‘x’ >> gvs [exp_rel_def, replace_Force_def]
  >- rw [exp_rel_def] >>
  irule_at Any EQ_REFL >>
  gvs []
QED

Theorem exp_rel_subst_replace_Force:
  ∀x y v w n.
    exp_rel x y ∧ v_rel v w ⇒
    exp_rel (subst1 n (Thunk (INR (Value v))) x)
            (subst1 n (Thunk (INR (Value w))) (replace_Force (Value w) n y))
Proof
  ‘(∀x y.
      exp_rel x y ⇒
      ∀v w n. v_rel v w ⇒
              exp_rel (subst1 n (Thunk (INR (Value v))) x)
                      (subst1 n (Thunk (INR (Value w))) (replace_Force (Value w) n y))) ∧
   (∀v w. v_rel v w ⇒ T)’
    suffices_by rw []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
  \\ gvs [replace_Force_def, subst1_def, exp_rel_def, v_rel_def]
  >~[‘Var _’]
  >- (IF_CASES_TAC \\ gvs [exp_rel_def, v_rel_def])
  >~[‘LIST_REL exp_rel _ _’]
  >- gvs [LIST_REL_EL_EQN, EL_MAP]
  >~[‘Lam _ _’]
  >- (IF_CASES_TAC \\ gvs [exp_rel_def, v_rel_def, subst_def])
  >>~[‘MEM _ (MAP FST _)’]
  >- (IF_CASES_TAC \\ gs [subst_def]
      \\ irule exp_rel_Letrec
      \\ gvs [subst_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
              GSYM FST_THM, GSYM SND_THM, LIST_REL_CONJ, LIST_REL_EL_EQN]
      \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD, EL_MAP]
      \\ rw []
      >- (last_x_assum $ dxrule_then assume_tac
          \\ rename1 ‘ok_bind (subst1 _ _ expr)’
          \\ Cases_on ‘expr’ \\ gvs [ok_bind_def, subst_def])
      >- (last_x_assum $ dxrule_then assume_tac
          \\ rename1 ‘ok_bind (subst1 _ _ (replace_Force _ _ expr))’
          \\ Cases_on ‘expr’ \\ gvs [ok_bind_def, subst_def, replace_Force_def]
          \\ IF_CASES_TAC \\ gvs [ok_bind_def, subst_def])
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ dxrule_then $ dxrule_then assume_tac
      \\ pairarg_tac \\ gvs [] \\ pairarg_tac \\ gvs [])
  >- (IF_CASES_TAC
      \\ gs [subst_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
      >- (irule exp_rel_Letrec_Delay_Var
          \\ gvs [LIST_REL_CONJ, LIST_REL_EL_EQN])
      \\ rename1 ‘replace_Force (Value w) n (replace_Force (Var v2) v1 y)’
      \\ qspecl_then [‘y’, ‘Value w’, ‘Var v2’, ‘n’, ‘v1’] mp_tac replace_Force_COMM
      \\ impl_tac
      >- (gvs [freevars_def]
          \\ conj_tac \\ strip_tac \\ gs [] \\ first_x_assum irule
          \\ gvs [MEM_MAP, MEM_EL, PULL_EXISTS]
          \\ rename1 ‘MAP FST f = MAP FST g’
          \\ ‘LENGTH f = LENGTH g’ by metis_tac [LENGTH_MAP]
          \\ rename1 ‘(n, _) = EL n2 f’
          \\ qexists_tac ‘n2’
          \\ ‘EL n2 (MAP FST f) = EL n2 (MAP FST g)’ by gvs []
          \\ gvs [EL_MAP]
          \\ Cases_on ‘EL n2 f’ \\ gs [])
      \\ rw []
      \\ qspecl_then [‘replace_Force (Value w) n y’, ‘Var v2’, ‘v1’, ‘[(n, Thunk (INR (Value w)))]’]
                     mp_tac subst_replace_Force
      \\ impl_tac
      >- (gvs [freevars_def]
          \\ conj_tac \\ strip_tac \\ gs []
          >- (assume_tac boundvars_replace_Force
              \\ gvs [SUBSET_DEF]
              \\ first_x_assum $ dxrule_then assume_tac \\ gvs [boundvars_def])
          \\ first_x_assum irule
          \\ ‘MEM n (MAP FST f)’ suffices_by gvs []
          \\ gvs [MEM_MAP]
          \\ first_x_assum $ irule_at Any \\ gs [])
      \\ rw [subst_def] \\ gs []
      \\ qsuff_tac ‘MAP (λ(p1,p2).(p1, subst1 n (Thunk (INR (Value w)))
                                              (replace_Force (Value w) n (replace_Force (Var v2) v1 p2)))) g
                    = MAP (λ(p1, p2). (p1, replace_Force (Var v2) v1 p2))
                          (MAP (λ(p1,p2).(p1,subst1 n (Thunk (INR (Value w))) (replace_Force (Value w) n p2))) g)’
      >- (rw []
          \\ irule exp_rel_Letrec_Delay_Var
          \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, GSYM SND_THM,
                  LIST_REL_CONJ, LIST_REL_EL_EQN, EL_MAP]
          \\ rw []
          >- (assume_tac boundvars_replace_Force
              \\ gvs [boundvars_subst, SUBSET_DEF]
              \\ strip_tac \\ first_x_assum $ drule_then assume_tac
              \\ gvs [boundvars_def])
          >- (gvs [EVERY_EL, EL_MAP] \\ rw []
              \\ last_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ gs []
              \\ rename1 ‘ok_bind (subst _ expr)’
              \\ Cases_on ‘expr’ \\ gs [ok_bind_def, subst1_def] \\ rw [ok_bind_def])
          >- (gvs [EVERY_EL, EL_MAP] \\ rw []
              \\ last_x_assum $ drule_then assume_tac
              \\ last_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ gs []
              \\ rename1 ‘ok_bind (subst _ (replace_Force _ _ expr))’
              \\ Cases_on ‘expr’ \\ gs [ok_bind_def, replace_Force_def, subst1_def]
              \\ rw [ok_bind_def, subst1_def])
          >- (gvs [EVERY_EL, EL_MAP] \\ rw []
              \\ assume_tac boundvars_replace_Force
              \\ pairarg_tac \\ gvs [SUBSET_DEF, boundvars_subst]
              \\ strip_tac \\ first_x_assum $ dxrule_then assume_tac
              \\ gs [boundvars_def]
              \\ rpt $ last_x_assum $ drule_then assume_tac \\ gs [])
          >- (gvs [MEM_MAP]
              \\ first_x_assum $ irule_at $ Pos last
              \\ gvs [subst_def])
          >- (last_x_assum $ drule_then assume_tac
              \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
              \\ last_x_assum $ drule_then assume_tac \\ gs []))
      \\ irule LIST_EQ
      \\ rw [EL_MAP]
      \\ pairarg_tac \\ gs []
      \\ rename1 ‘replace_Force _ _ (replace_Force _ _ p2)’
      \\ qspecl_then [‘p2’, ‘Value w’, ‘Var v2’, ‘n’, ‘v1’] mp_tac replace_Force_COMM
      \\ impl_tac
      >- (gvs [freevars_def]
          \\ strip_tac \\ gs [] \\ first_x_assum irule
          \\ ‘MEM v1 (MAP FST f)’ suffices_by rw []
          \\ gvs [MEM_MAP]
          \\ first_x_assum $ irule_at Any \\ gs [])
      \\ rw []
      \\ qspecl_then [‘replace_Force (Value w) n p2’, ‘Var v2’, ‘v1’, ‘[(n, Thunk (INR (Value w)))]’]
                     mp_tac subst_replace_Force
      \\ impl_tac
      >- (gvs [freevars_def]
          \\ conj_tac \\ strip_tac \\ gs []
          >- (assume_tac boundvars_replace_Force
              \\ gvs [SUBSET_DEF, EVERY_EL]
              \\ first_x_assum $ dxrule_then assume_tac
              \\ rpt $ last_x_assum $ drule_then assume_tac
              \\ gvs [boundvars_def, EL_MAP])
          \\ ‘MEM n (MAP FST f)’ suffices_by gvs []
          \\ gvs [MEM_MAP]
          \\ first_x_assum $ irule_at Any \\ gs [])
      \\ rw [subst_def])
  >~[‘Let (SOME v1) (Delay (Var v2)) _’]
  >- (IF_CASES_TAC \\ gvs [subst_def]
      >- (disj2_tac \\ irule_at Any EQ_REFL \\ gvs [])
      \\ IF_CASES_TAC \\ gvs [subst_def, exp_rel_def, v_rel_def]
      >- (disj2_tac \\ irule_at Any EQ_REFL \\ gvs [])
      >- (disj2_tac \\ first_x_assum $ irule_at $ Pos last
          \\ first_assum $ irule_at Any
          \\ gvs [freevars_subst, boundvars_subst]
          \\ rename1 ‘replace_Force (Value w) n (replace_Force (Var v2) v1 y2)’
          \\ qspecl_then [‘y2’, ‘Value w’, ‘Var v2’, ‘n’, ‘v1’] assume_tac replace_Force_COMM
          \\ gvs [freevars_def]
          \\ qspecl_then [‘replace_Force (Value w) n y2’, ‘Var v2’, ‘v1’, ‘[(n, Thunk (INR (Value w)))]’]
                         assume_tac subst_replace_Force
          \\ conj_asm2_tac
          \\ gvs [freevars_def, subst_def]
          \\ assume_tac boundvars_replace_Force \\ strip_tac
          \\ gvs [SUBSET_DEF]
          \\ first_x_assum $ dxrule_then assume_tac
          \\ gvs [boundvars_def]))
  >~[‘Let opt x y’]
  >- (Cases_on ‘opt’ \\ gvs [replace_Force_def, subst_def, exp_rel_def]
      \\ IF_CASES_TAC \\ gvs [subst_def])
  >~[‘Force y’]
  >- (rename1 ‘exp_rel x y’
      \\ Cases_on ‘x’ \\ gvs [replace_Force_def, subst_def, exp_rel_def]
      >- (IF_CASES_TAC \\ gvs [subst_def, exp_rel_def])
      \\ first_x_assum irule
      \\ first_x_assum $ irule_at Any)
  >- (irule_at Any EQ_REFL
      \\ gvs [LIST_REL_CONJ, SF ETA_ss])
QED

Theorem APP_EQ:
  ∀f g x y. f = g ∧ x = y ⇒ f x = g y
Proof
  gvs []
QED

Theorem ALOOKUP_FUN:
  ∀l f n. MEM n (MAP FST l) ⇒ ALOOKUP (REVERSE (MAP (λ(n2, x). (n2, f n2)) l)) n = SOME (f n)
Proof
  Induct using SNOC_INDUCT >> gvs [FORALL_PROD, REVERSE_SNOC, MAP_SNOC] >>
  rw []
QED

Theorem exp_rel_subst_Recclosure:
  ∀f g x y v1 v2.
    MAP FST f = MAP FST g ∧ ALL_DISTINCT (MAP FST g) ∧ LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
    EVERY ok_bind (MAP SND f) ∧ EVERY ok_bind (MAP SND g) ∧
    MEM v2 (MAP FST g) ∧ MEM (v1, Delay (Var v2)) f ∧ exp_rel x y ∧
    EVERY (λe. v2 ∉ boundvars e) (MAP SND g) ∧ v1 ≠ v2 ∧ v2 ∉ boundvars y ⇒
    exp_rel (subst_funs f x)
            (subst_funs (MAP (λ(v, e). (v, replace_Force (Var v2) v1 e)) g) (replace_Force (Var v2) v1 y))
Proof
  qsuff_tac ‘(∀x y filter f g y v1 v2.
                exp_rel x y ∧
                     MAP FST f = MAP FST g ∧ ALL_DISTINCT (MAP FST g) ∧ LIST_REL exp_rel (MAP SND f) (MAP SND g) ∧
                     EVERY ok_bind (MAP SND f) ∧ EVERY ok_bind (MAP SND g) ∧ filter v2 ∧ filter v1 ∧
                     MEM v2 (MAP FST g) ∧ MEM (v1, Delay (Var v2)) f ∧ exp_rel x y ∧
                     EVERY (λe. v2 ∉ boundvars e) (MAP SND g) ∧ v1 ≠ v2 ∧ v2 ∉ boundvars y ⇒
                     exp_rel (subst (FILTER (λ(v,x). filter v) (MAP (λ(v,x). (v, Recclosure f v)) f)) x)
                             (subst (FILTER (λ(v,x). filter v)
                                     (MAP (λ(v,x). (v, Recclosure (MAP (λ(v, e). (v,
                                                                                  replace_Force (Var v2) v1 e))
                                                                   g) v))
                                      (MAP (λ(v, e). (v, replace_Force (Var v2) v1 e)) g)))
                              (replace_Force (Var v2) v1 y)))’
  >- (rw [subst_funs_def] >>
      last_x_assum $ drule_then $ qspecl_then [‘K T’] assume_tac >>
      gvs [GSYM LAMBDA_PROD, FILTER_T]) >>
  completeInduct_on ‘exp_size x’ >> rw [Once exp_rel_cases] >> gvs [replace_Force_def, subst_def]
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ rename1 ‘ALOOKUP _ s’
      \\ rename1 ‘replace_Force (Var v2) v1’
      \\ ‘OPTREL v_rel (ALOOKUP (REVERSE (MAP (λ(v,x).(v,Recclosure xs v)) xs)) s)
          (ALOOKUP (REVERSE (MAP (λ(v,x).(v,Recclosure (MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) ys) v))
                    (MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) ys))) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN]
            \\ ‘∀n. n < LENGTH ys ⇒ EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP]
            \\ rw [LAMBDA_PROD]
            \\ irule v_rel_Recclosure_Delay_Var
            \\ gvs [LIST_REL_EL_EQN, EL_MAP])
      \\ gvs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
      \\ IF_CASES_TAC \\ gvs [exp_rel_Var]
      \\ gvs [OPTREL_def, exp_rel_def])
  >~[‘Prim op _’]
  >- (irule exp_rel_Prim >>
      gvs [LIST_REL_EL_EQN, EL_MAP, exp_rel_def] >>
      rw [] >> last_x_assum irule >>
      gvs [EL_MAP, EL_MEM, boundvars_def, exp_size_def] >>
      conj_tac
      >- (rename1 ‘boundvars (EL n ys)’ >>
          first_x_assum $ qspecl_then [‘boundvars (EL n ys)’] assume_tac >> gvs [] >>
          strip_tac >> first_x_assum irule >>
          gvs [MEM_MAP, MEM_EL, PULL_EXISTS] >>
          first_x_assum $ irule_at Any >> gvs [])
      >- (assume_tac exp_size_lemma >> gs [] >>
          rename1 ‘EL n xs’ >>
          first_x_assum $ qspecl_then [‘EL n xs’, ‘xs’] mp_tac >>
          gvs [EL_MEM]))
  >~[‘If _ _ _’]
  >- (rw [exp_rel_def] >> last_x_assum irule >> gvs [boundvars_def, exp_size_def])
  >~[‘App _ _’]
  >- (rw [exp_rel_def] >> last_x_assum irule >> gvs [boundvars_def, exp_size_def])
  >~[‘Lam _ _’]
  >- (IF_CASES_TAC >> rw [exp_rel_def, subst_def, FILTER_FILTER, LAMBDA_PROD]
      >- (irule exp_rel_subst >>
          rename1 ‘MAP FST f = MAP FST g’ >>
          rename1 ‘_ ≠ s ∧ filter2 _’ >>
          qspecl_then [‘MAP (λ(v,x).(v, Recclosure f v)) f’,
                       ‘MAP ((λ(v,x).(v, Recclosure (MAP (λ(v,e).(v, replace_Force (Var v2) s e)) g) v)))
                        (MAP (λ(v,e).(v, replace_Force (Var v2) s e)) g)’,
                       ‘v_rel’, ‘λv. v ≠ s ∧ filter2 v’] mp_tac LIST_FILTERED >>
          impl_tac
          >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP] >>
              rw [] >>
              rename1 ‘n < _’ >>
              Cases_on ‘EL n f’ >> Cases_on ‘EL n g’ >>
              ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs []  >> gvs [EL_MAP] >>
              irule v_rel_Recclosure_Delay_Var >>
              gvs [LIST_REL_EL_EQN, EL_MAP]) >>
          gvs [])
      >- (rename1 ‘exp_rel (Lam _ x) _’ >>
          last_x_assum $ qspecl_then [‘exp_size x’] assume_tac >> gs [exp_size_def] >>
          first_x_assum $ qspecl_then [‘x’] assume_tac >> gs [] >>
          rename1 ‘_ ≠ s ∧ filter2 _’ >>
          last_x_assum $ qspecl_then [‘λv. v ≠ s ∧ filter2 v’] assume_tac >> gvs [] >>
          first_x_assum irule >>
          gvs [EL_MAP, boundvars_def]))
  >~[‘Letrec _ (replace_Force (Var v2) v1 (replace_Force (Var w2) w1 y))’]
  >- (IF_CASES_TAC
      >- (rw [exp_rel_def] >> disj2_tac >>
          gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, subst_def] >>
          rename1 ‘exp_rel (Letrec f2 x) (Letrec (MAP _ g2) (replace_Force _ _ y))’ >>
          Q.REFINE_EXISTS_TAC ‘MAP (λ(v,x). (v, subst l x)) g2’ >>
          gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, subst_def] >>
          irule_at Any LIST_EQ >> gs [LIST_REL_EL_EQN, EL_MAP] >>
          irule_at (Pos $ el 2) EQ_TRANS >> irule_at Any subst_replace_Force >>
          gvs [MAP_FST_FILTER, MEM_FILTER, freevars_def, boundvars_def] >>
          ‘MEM w1 (MAP FST f2)’ by (gvs [MEM_MAP] >> first_x_assum $ irule_at Any >> gs []) >>
          gs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER] >>
          irule_at (Pos hd) EQ_REFL >>
          qmatch_goalsub_abbrev_tac ‘boundvars (subst subst_l y)’ >>
          qexists_tac ‘subst_l’ >> rw [EVERY_MAP, LAMBDA_PROD, boundvars_subst]
          >- (pairarg_tac >> gs [] >>
              irule EQ_TRANS >> irule_at Any subst_replace_Force >>
              gvs [freevars_def, EVERY_EL, subst_def] >>
              unabbrev_all_tac >>
              gvs [GSYM FILTER_REVERSE, MAP_FST_FILTER, MEM_FILTER, ALOOKUP_FILTER] >>
              first_x_assum $ drule_then assume_tac >> gs [EL_MAP])
          >- (gvs [EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS] >> rw [] >>
              last_x_assum $ drule_then assume_tac >>
              rename1 ‘ok_bind (subst _ p2)’ >> Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
          >- (gvs [EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS] >> rw [] >>
              rename1 ‘MEM (p1, p2) g2’ >>
              rpt $ last_x_assum $ qspecl_then [‘p2’, ‘p1’] assume_tac >>
              Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
          >- (pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
              irule exp_rel_subst >>
              rename1 ‘FILTER _ (FILTER (λ(v,x). filter2 v) _)’ >>
              unabbrev_all_tac >> gs [FILTER_FILTER, LAMBDA_PROD] >>
              qspecl_then [‘MAP (λ(v,x).(v, Recclosure f v)) f’,
                           ‘MAP (λ(v,x).(v,Recclosure (MAP (λ(v,e).(v, replace_Force (Var v2) v1 e)) g) v)) g’,
                           ‘v_rel’, ‘λv. ¬MEM v (MAP FST g2) ∧ filter2 v’
                          ] mp_tac LIST_FILTERED >> impl_tac
              >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP] >>
                  rw [] >>
                  pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
                  rename1 ‘n2 < _’ >>
                  ‘EL n2 (MAP FST f) = EL n2 (MAP FST g)’ by gs [] >> gs [EL_MAP] >>
                  irule v_rel_Recclosure_Delay_Var >>
                  gvs [LIST_REL_EL_EQN, EL_MAP]) >>
              rw [] >>
              last_x_assum $ drule_then assume_tac >> gvs [])
          >- gvs [EVERY_MAP, LAMBDA_PROD]
          >- (rw [MEM_MAP] >> first_x_assum $ irule_at Any >>
              gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, MEM_MAP, FORALL_PROD] >>
              IF_CASES_TAC >> gs [] >>
              rename1 ‘¬MEM (FST y2, _) g2’ >> first_x_assum $ qspecl_then [‘SND y2’] assume_tac >>
              gvs [])
          >- (irule exp_rel_subst >> fs [] >>
              rename1 ‘FILTER _ (FILTER (λ(v,x). filter2 v) _)’ >>
              unabbrev_all_tac >> gs [FILTER_FILTER, LAMBDA_PROD] >>
              qspecl_then [‘MAP (λ(v,x).(v, Recclosure f v)) f’,
                           ‘MAP (λ(v,x).(v,Recclosure (MAP (λ(v,e).(v, replace_Force (Var v2) v1 e)) g) v)) g’,
                           ‘v_rel’, ‘λv. ¬MEM v (MAP FST g2) ∧ filter2 v’
                          ] assume_tac LIST_FILTERED >>
              fs [] >> first_x_assum irule >>
              gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP] >>
              rw [] >>
              rename1 ‘n < _’ >>
              Cases_on ‘EL n f’ >> Cases_on ‘EL n g’ >>
              ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gs [] >> gs [EL_MAP] >>
              irule v_rel_Recclosure_Delay_Var >>
              gvs [LIST_REL_EL_EQN, EL_MAP]))
      >- (rw [exp_rel_def] >> disj2_tac >>
          gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, subst_def] >>
          rename1 ‘exp_rel (Letrec f2 x) (Letrec (MAP _ g2) (replace_Force _ _ y))’ >>
          Q.REFINE_EXISTS_TAC ‘MAP (λ(v,x). (v, subst l (replace_Force (Var v2) v1 x))) g2’ >>
          gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, subst_def] >>
          qspecl_then [‘y’, ‘Var v2’, ‘Var w2’, ‘v1’, ‘w1’] mp_tac replace_Force_COMM >> impl_tac
          >- (gvs [freevars_def, boundvars_def] >>
              rpt $ conj_tac >> strip_tac >>
              gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
              ‘MEM w1 (MAP FST f2)’ by (gvs [MEM_MAP] >> first_x_assum $ irule_at Any >> gs []) >>
              gvs []) >>
          strip_tac >> gvs [] >>
          qmatch_goalsub_abbrev_tac ‘subst subst_l (replace_Force _ _ (replace_Force _ _ _))’ >>
          qexists_tac ‘subst_l’ >>
          qexists_tac ‘subst subst_l (replace_Force (Var v2) v1 y)’ >>
          qexists_tac ‘w1’ >> qexists_tac ‘w2’ >>
          rw [EVERY_MAP, LAMBDA_PROD, boundvars_subst]
          >- (irule LIST_EQ >> rw [EL_MAP] >>
              pairarg_tac >> gs [] >>
              irule EQ_TRANS >>
              irule_at (Pos hd) APP_EQ >>
              irule_at (Pos hd) EQ_REFL >>
              irule_at Any replace_Force_COMM >>
              gvs [freevars_def, boundvars_def] >>
              ‘MEM w1 (MAP FST f2)’ by (gvs [MEM_MAP] >> first_x_assum $ irule_at Any >> gs []) >>
              rpt $ conj_tac
              >- (strip_tac >> gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM])
              >- (strip_tac >> gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM])
              >- (strip_tac >> gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]) >>
              irule EQ_TRANS >> irule_at Any subst_replace_Force >>
              gvs [freevars_def, EVERY_EL, subst_def] >>
              rpt $ conj_tac
              >- (rename1 ‘n < _’ >>
                  rpt $ first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [EL_MAP] >>
                  assume_tac boundvars_replace_Force >>
                  strip_tac >> gs [SUBSET_DEF] >>
                  first_x_assum $ dxrule_then assume_tac >>
                  gvs [boundvars_def])
              >- (unabbrev_all_tac >> gvs [MAP_FST_FILTER, MEM_FILTER])
              >- (unabbrev_all_tac >>
                  gvs [GSYM FILTER_REVERSE, MAP_FST_FILTER, MEM_FILTER, ALOOKUP_FILTER] >>
                  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]))
          >- (irule EQ_TRANS >> irule_at (Pos hd) APP_EQ >>
              irule_at (Pos hd) EQ_REFL >> first_x_assum $ irule_at $ Pos hd >>
              irule EQ_TRANS >> irule_at Any subst_replace_Force >>
              gvs [freevars_def, boundvars_def] >>
              conj_tac
              >- (assume_tac boundvars_replace_Force >>
                  strip_tac >> gs [SUBSET_DEF] >>
                  first_x_assum $ dxrule_then assume_tac >>
                  gvs [boundvars_def]) >>
              ‘MEM w1 (MAP FST f2)’ by (gvs [MEM_MAP] >> first_x_assum $ irule_at Any >> gs []) >>
              conj_tac
              >- (unabbrev_all_tac >> gvs [MAP_FST_FILTER, MEM_FILTER])
              >- (unabbrev_all_tac >>
                  gvs [subst_def, GSYM FILTER_REVERSE, MAP_FST_FILTER, MEM_FILTER, ALOOKUP_FILTER] >>
                  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]))
          >- (gvs [EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS] >> rw [] >>
              last_x_assum $ drule_then assume_tac >>
              rename1 ‘ok_bind (subst _ p2)’ >> Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
          >- (gvs [EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS] >> rw [] >>
              rename1 ‘MEM (p1, p2) g2’ >>
              rpt $ last_x_assum $ qspecl_then [‘p2’, ‘p1’] assume_tac >>
              Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def, replace_Force_def] >>
              rw [subst_def, ok_bind_def])
          >- (gvs [LIST_REL_EL_EQN, EL_MAP] >> rw [] >>
              pairarg_tac >> gs [] >> pairarg_tac >> gs [FILTER_FILTER, LAMBDA_PROD] >>
              rename1 ‘n < _’ >>
              last_x_assum $ qspecl_then [‘exp_size (SND (EL n f2))’] mp_tac >> impl_tac
              >- (assume_tac exp_size_lemma >>
                  gvs [MEM_EL, PULL_EXISTS, exp_size_def] >>
                  first_x_assum $ qspecl_then [‘FST (EL n f2)’, ‘SND (EL n f2)’, ‘f2’, ‘n’] assume_tac >> gvs []) >>
              disch_then $ qspecl_then [‘SND (EL n f2)’] assume_tac >> fs [] >>
              rename1 ‘¬MEM _ (MAP FST _) ∧ filter2 _’ >>
              first_x_assum $ qspecl_then [‘λv. ¬MEM v (MAP FST g2) ∧ filter2 v’] assume_tac >> gs [] >>
              unabbrev_all_tac >> first_x_assum irule >>
              gvs [EL_MAP, EVERY_EL, boundvars_def] >>
              rpt $ first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [] >>
              first_x_assum $ qspecl_then [‘boundvars (replace_Force (Var w2) w1 (SND (EL n g2)))’] assume_tac >>
              gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
              strip_tac >> gvs [] >> first_x_assum irule
              >- (assume_tac boundvars_replace_Force2 >>
                  gvs [SUBSET_DEF])
              >- (gvs [MEM_EL] >> first_assum $ irule_at Any >>
                  gvs [EL_MAP]))
          >- (gvs [EVERY_MAP, LAMBDA_PROD, EVERY_MEM, FORALL_PROD] >>
              rw [] >> rpt $ first_x_assum $ drule_then assume_tac >>
              strip_tac >> assume_tac boundvars_replace_Force >>
              gvs [SUBSET_DEF] >>
              first_x_assum $ dxrule_then assume_tac >> gvs [boundvars_def])
          >- (strip_tac >> assume_tac boundvars_replace_Force >>
              gvs [SUBSET_DEF] >>
              first_x_assum $ dxrule_then assume_tac >> gvs [boundvars_def])
          >- (rw [MEM_MAP] >> first_x_assum $ irule_at Any >>
              gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, MEM_MAP, FORALL_PROD] >>
              IF_CASES_TAC >> gs [] >>
              rename1 ‘¬MEM (FST y2, _) g2’ >> first_x_assum $ qspecl_then [‘SND y2’] assume_tac >>
              gvs [])
          >- (last_x_assum $ qspecl_then [‘exp_size x’] assume_tac >> gs [exp_size_def] >>
              first_x_assum $ qspecl_then [‘x’] assume_tac >> fs [FILTER_FILTER, LAMBDA_PROD] >>
              rename1 ‘¬MEM _ (MAP FST _) ∧ filter2 _’ >>
              first_x_assum $ qspecl_then [‘λv. ¬MEM v (MAP FST g2) ∧ filter2 v’] assume_tac >> fs [] >>
              unabbrev_all_tac >> first_x_assum irule >>
              assume_tac boundvars_replace_Force2 >>
              gvs [boundvars_def, SUBSET_DEF, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
              strip_tac >> first_x_assum $ dxrule_then assume_tac >> gvs [])))
  >~[‘Letrec _ _’]
  >- (IF_CASES_TAC >> gvs [subst_def, FILTER_FILTER, LAMBDA_PROD] >>
      irule exp_rel_Letrec >>
      gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
      rw []
      >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
          pairarg_tac >> gs [] >>
          rename1 ‘ok_bind (subst _ p2)’ >>
          last_x_assum $ drule_then assume_tac >>
          Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
      >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
          pairarg_tac >> gs [] >>
          rename1 ‘ok_bind (subst _ p2)’ >>
          last_x_assum $ drule_then assume_tac >>
          Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
      >- (irule exp_rel_subst >> fs [] >>
          rename1 ‘exp_rel (Letrec f2 _) (Letrec g2 _)’ >>
          rename1 ‘MEM (_, Delay (Var _)) f’ >>
          rename1 ‘MAP FST f = MAP FST g’ >>
          rename1 ‘¬MEM _ (MAP FST _) ∧ filter2 _’ >>
          qspecl_then [‘MAP (λ(v,x).(v, Recclosure f v)) f’,
                       ‘MAP (λ(p1,p2). (p1,Recclosure (MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) g) p1)) g’,
                       ‘v_rel’, ‘λv. ¬MEM v (MAP FST g2) ∧ filter2 v’] assume_tac LIST_FILTERED >>
          gvs [] >> first_x_assum irule >>
          gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP] >>
          rw [] >> rename1 ‘n < _’ >>
          Cases_on ‘EL n f’ >> Cases_on ‘EL n g’ >>
          ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs [] >> gvs [EL_MAP] >>
          irule v_rel_Recclosure_Delay_Var >>
          gvs [LIST_REL_EL_EQN, EL_MAP])
      >- (gvs [LIST_REL_EL_EQN, EL_MAP] >> rw [] >>
          pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
          irule exp_rel_subst >>
          rename1 ‘exp_rel (Letrec f2 _) (Letrec g2 _)’ >>
          rename1 ‘¬MEM _ (MAP FST _) ∧ filter2 _’ >>
          qspecl_then [‘MAP (λ(v,x).(v, Recclosure f v)) f’,
                       ‘MAP ((λ(v,x).(v, Recclosure (MAP (λ(v,e).(v, replace_Force (Var v2) v1 e)) g) v))) g’,
                       ‘v_rel’, ‘λv. ¬MEM v (MAP FST g2) ∧ filter2 v’] mp_tac LIST_FILTERED >>
          impl_tac
          >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP] >>
              rw [] >>
              rename1 ‘n2 < LENGTH g’ >>
              Cases_on ‘EL n2 f’ >> Cases_on ‘EL n2 g’ >>
              ‘EL n2 (MAP FST f) = EL n2 (MAP FST g)’ by gvs []  >> gvs [EL_MAP] >>
              irule v_rel_Recclosure_Delay_Var >>
              gvs [LIST_REL_EL_EQN, EL_MAP]) >>
          first_x_assum $ drule_then assume_tac >>
          gvs [])
      >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
          pairarg_tac >> gs [] >>
          rename1 ‘ok_bind (subst _ p2)’ >>
          last_x_assum $ drule_then assume_tac >>
          Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def])
      >- (gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rw [] >>
          pairarg_tac >> gs [] >>
          rename1 ‘ok_bind (subst _ (replace_Force _ _ p2))’ >>
          last_x_assum $ drule_then assume_tac >>
          Cases_on ‘p2’ >> gvs [ok_bind_def, subst_def, replace_Force_def] >>
          rw [subst_def, ok_bind_def])
      >- (rename1 ‘exp_rel (Letrec f2 x) (Letrec g2 y)’ >>
          last_x_assum $ qspecl_then [‘exp_size x’] assume_tac >> gs [exp_size_def] >>
          first_x_assum $ qspecl_then [‘x’] assume_tac >> gs [] >>
          rename1 ‘¬MEM _ (MAP FST _) ∧ filter2 _’ >>
          first_x_assum $ qspecl_then [‘λv. ¬MEM v (MAP FST g2) ∧ filter2 v’] assume_tac >> gs [] >>
          first_x_assum irule >>
          gvs [boundvars_def])
      >- (gvs [LIST_REL_EL_EQN, EL_MAP] >> rw [] >>
          pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
          rename1 ‘exp_rel (Letrec f2 _) (Letrec g2 _)’ >>
          rename1 ‘EL n f2 = (ef1, ef2)’ >>
          last_x_assum $ qspecl_then [‘exp_size ef2’] mp_tac >> impl_tac
          >- (assume_tac exp_size_lemma >>
              gvs [MEM_EL, PULL_EXISTS, exp_size_def] >>
              first_x_assum $ qspecl_then [‘ef1’, ‘ef2’, ‘f2’, ‘n’] assume_tac >> gvs []) >>
          disch_then $ qspecl_then [‘ef2’] assume_tac >> fs [] >>
          rename1 ‘¬MEM _ (MAP FST _) ∧ filter2 _’ >>
          first_x_assum $ qspecl_then [‘λv. ¬MEM v (MAP FST g2) ∧ filter2 v’] assume_tac >> gs [] >>
          first_x_assum irule >>
          gvs [EL_MAP, boundvars_def] >>
          last_x_assum $ drule_then assume_tac >> gs [] >>
          rename1 ‘v2 ∉ boundvars eg2’ >>
          first_x_assum $ qspecl_then [‘boundvars eg2’] assume_tac >> gs [] >>
          strip_tac >> first_x_assum irule >>
          gvs [MEM_EL, EL_MAP] >>
          first_assum $ irule_at Any >>
          gvs [EL_MAP]))
  >~[‘Let (SOME _) _ (replace_Force (Var v2) v1 (replace_Force (Var w2) w1 y2))’]
  >- (rename1 ‘FILTER (λ(v,x). filter2 v) _’ >>
      gvs [GSYM FILTER_REVERSE, GEN_ALL ALOOKUP_FILTER, freevars_subst] >>
      IF_CASES_TAC >> gvs [subst_def, GSYM FILTER_REVERSE, GEN_ALL ALOOKUP_FILTER]
      >- (gvs [freevars_def, MEM_MAP, MEM_FILTER, FORALL_PROD, subst_def, FILTER_FILTER, GSYM FILTER_REVERSE] >>
          gvs [LAMBDA_PROD, PULL_EXISTS, EXISTS_PROD] >>
          qspecl_then [‘y2’, ‘Var v1’, ‘w1’, ‘(FILTER (λ(p1,p2). (p1 ≠ w1 ∧ p1 ≠ v1) ∧ filter2 p1)
                (MAP (λ(v,x). (v, Recclosure (MAP (λ(v,e). (v,replace_Force (Var (FST y)) v1 e)) g) v))
                 (MAP (λ(v,e). (v,replace_Force (Var (FST y)) v1 e)) g)))’] mp_tac subst_replace_Force >>
          impl_tac
          >- gvs [freevars_def, MEM_MAP, MEM_FILTER, FORALL_PROD] >>
          rw [subst_def, GSYM FILTER_REVERSE, GEN_ALL ALOOKUP_FILTER] >>
          irule exp_rel_Let_Delay_Var >>
          gvs [freevars_subst, boundvars_subst] >>
          irule_at (Pos last) exp_rel_subst >>
          qspecl_then [‘MAP (λ(v,x).(v, Recclosure f v)) f’,
                       ‘MAP ((λ(v,x).(v, Recclosure (MAP (λ(v,e).(v, replace_Force (Var (FST y)) v1 e)) g) v)))
                        (MAP (λ(v,e).(v, replace_Force (Var (FST y)) v1 e)) g)’,
                       ‘v_rel’, ‘λv. (v ≠ w1 ∧ v ≠ v1) ∧ filter2 v’] mp_tac LIST_FILTERED >>
          impl_tac
          >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP] >>
              rw [] >>
              rename1 ‘n < _’ >>
              Cases_on ‘EL n f’ >> Cases_on ‘EL n g’ >>
              ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs []  >> gvs [EL_MAP] >>
              irule v_rel_Recclosure_Delay_Var >>
              gvs [LIST_REL_EL_EQN, EL_MAP] >>
              gvs [MEM_MAP] >>
              irule_at Any EQ_REFL >> gvs []) >>
          rw [] >>
          last_x_assum irule >>
          gvs [exp_size_def, boundvars_def] >>
          qexists_tac ‘SND y’ >> gs []) >>
      IF_CASES_TAC >> gvs [subst_def, GSYM FILTER_REVERSE, GEN_ALL ALOOKUP_FILTER]
      >- (gvs [freevars_def, MEM_MAP, MEM_FILTER, FORALL_PROD, subst_def, FILTER_FILTER, GSYM FILTER_REVERSE] >>
          gvs [LAMBDA_PROD, PULL_EXISTS, EXISTS_PROD] >>
          qspecl_then [‘y2’, ‘Var w2’, ‘v1’, ‘FILTER (λ(p1,p2). (p1 ≠ v1 ∧ p1 ≠ w2) ∧ filter2 p1)
                (MAP (λ(v,x). (v, Recclosure (MAP (λ(v,e). (v,replace_Force (Var (FST y)) v1 e)) g) v))
                 (MAP (λ(v,e). (v,replace_Force (Var (FST y)) v1 e)) g))’] mp_tac subst_replace_Force >>
          impl_tac
          >- (gvs [freevars_def, MEM_MAP, MEM_FILTER, FORALL_PROD]) >>
          rw [subst_def, GSYM FILTER_REVERSE, GEN_ALL ALOOKUP_FILTER] >>
          irule exp_rel_Let_Delay_Var >>
          gvs [freevars_subst, boundvars_subst] >>
          irule_at (Pos last) exp_rel_subst >>
          qspecl_then [‘MAP (λ(v,x).(v, Recclosure f v)) f’,
                       ‘MAP ((λ(v,x).(v, Recclosure (MAP (λ(v,e).(v, replace_Force (Var (FST y)) v1 e)) g) v)))
                        (MAP (λ(v,e).(v, replace_Force (Var (FST y)) v1 e)) g)’,
                       ‘v_rel’, ‘λv. (v ≠ v1 ∧ v ≠ w2) ∧ filter2 v’] mp_tac LIST_FILTERED >>
          impl_tac
          >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP] >>
              rw [] >>
              rename1 ‘n < _’ >>
              Cases_on ‘EL n f’ >> Cases_on ‘EL n g’ >>
              ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs []  >> gvs [EL_MAP] >>
              irule v_rel_Recclosure_Delay_Var >>
              gvs [LIST_REL_EL_EQN, EL_MAP] >>
              gvs [MEM_MAP] >>
              irule_at Any EQ_REFL >> gvs []) >>
          rw [] >>
          last_x_assum irule >>
          gvs [exp_size_def, boundvars_def] >>
          qexists_tac ‘SND y’ >> gs []) >>
      gvs [freevars_def, MEM_MAP, MEM_FILTER, FORALL_PROD, subst_def, FILTER_FILTER, GSYM FILTER_REVERSE] >>
      gvs [LAMBDA_PROD, PULL_EXISTS, EXISTS_PROD] >>
      qspecl_then [‘y2’, ‘Var (FST y)’, ‘Var w2’, ‘v1’, ‘w1’] mp_tac replace_Force_COMM >> impl_tac
      >- gvs [freevars_def, boundvars_def] >>
      rw [] >>
      qspecl_then [‘replace_Force (Var (FST y)) v1 y2’, ‘Var w2’, ‘w1’,
              ‘FILTER (λ(p1,p2). (p1 ≠ w1 ∧ p1 ≠ w2) ∧ filter2 p1)
               (MAP (λ(v,x). (v, Recclosure (MAP (λ(v,e). (v,replace_Force (Var (FST y)) v1 e)) g) v))
                (MAP (λ(v,e). (v,replace_Force (Var (FST y)) v1 e)) g))’] mp_tac subst_replace_Force >>
      impl_tac
      >- (gvs [freevars_def, MEM_MAP, MEM_FILTER, FORALL_PROD] >>
          strip_tac >> assume_tac boundvars_replace_Force >>
          gvs [SUBSET_DEF] >>
          first_x_assum $ dxrule_then assume_tac >>
          gvs [boundvars_def]) >>
      rw [subst_def, GSYM FILTER_REVERSE, GEN_ALL ALOOKUP_FILTER] >>
      irule exp_rel_Let_Delay_Var >>
      gvs [freevars_subst, boundvars_subst] >>
      last_assum $ irule_at Any >>
      gvs [exp_size_def] >>
      qexists_tac ‘SND y’ >> gvs [boundvars_def] >>
      conj_tac
      >- (strip_tac >> assume_tac boundvars_replace_Force >>
          gs [SUBSET_DEF] >>
          first_x_assum $ dxrule_then assume_tac >>
          gvs [boundvars_def]) >>
      gvs [PULL_FORALL] >>
      rename1 ‘exp_rel y1 y2’ >>
      last_x_assum $ qspecl_then [‘y1’, ‘λv. (v ≠ w1 ∧ v ≠ w2) ∧ filter2 v’] assume_tac >> fs [] >>
      first_x_assum irule >>
      gvs [] >> conj_tac
      >- (strip_tac >> assume_tac boundvars_replace_Force2 >>
          gvs [SUBSET_DEF]) >>
      qexists_tac ‘SND y’ >> gs [])
  >~[‘replace_Force (Var v2) v1 (Let opt _ _)’]
  >- (rename1 ‘FILTER (λ(v,x). filter2 v) _’ >>
      Cases_on ‘opt’
      >~[‘Seq _ _’]
      >- (rw [subst_def, replace_Force_def, exp_rel_def] >>
          last_x_assum irule >> gvs [EL_MAP, boundvars_def, exp_size_def])
      >~[‘Let (SOME s) _ _’]
      >- (gvs [replace_Force_def, subst_def] >>
          IF_CASES_TAC >> gvs [subst_def, FILTER_FILTER, LAMBDA_PROD] >>
          irule exp_rel_Let >>
          last_assum $ irule_at $ Pos hd >> gvs [boundvars_def, exp_size_def] >>
          irule exp_rel_subst >> gvs [] >>
          rename1 ‘MAP FST f = MAP FST g’ >>
          qspecl_then [‘MAP (λ(v,x).(v, Recclosure f v)) f’,
                       ‘MAP ((λ(v,x).(v, Recclosure (MAP (λ(v,e).(v, replace_Force (Var v2) s e)) g) v)))
                        (MAP (λ(v,e).(v, replace_Force (Var v2) s e)) g)’,
                       ‘v_rel’, ‘λv. v ≠ s ∧ filter2 v’] mp_tac LIST_FILTERED >>
          impl_tac
          >- (gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP] >>
              rw [] >>
              rename1 ‘n < _’ >>
              Cases_on ‘EL n f’ >> Cases_on ‘EL n g’ >>
              ‘EL n (MAP FST f) = EL n (MAP FST g)’ by gvs []  >> gvs [EL_MAP] >>
              irule v_rel_Recclosure_Delay_Var >>
              gvs [LIST_REL_EL_EQN, EL_MAP]) >>
          gvs []))
  >~[‘Delay _’]
  >- (irule exp_rel_Delay >>
      last_x_assum irule >>
      gvs [exp_size_def, boundvars_def])
  >~[‘Box _’]
  >- (irule exp_rel_Box >>
      last_x_assum irule >>
      gvs [exp_size_def, boundvars_def])
  >~[‘replace_Force _ _ (Force y)’]
  >- (rename1 ‘exp_rel x y’ >>
      qpat_x_assum ‘exp_rel (Force _) (Force _)’ kall_tac >>
      gs [PULL_FORALL] >>
      last_x_assum $ qspecl_then [‘x’] assume_tac >> gs [exp_size_def] >>
      gvs [boundvars_def, exp_size_def] >>
      Cases_on ‘x’ >> gs [Once exp_rel_def, Once replace_Force_def, subst_def]
      >- (IF_CASES_TAC >> gvs [subst_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER, boundvars_def]
          >- (qspecl_then [‘f’, ‘Recclosure f’, ‘s’] mp_tac ALOOKUP_FUN >> impl_tac
              >- (gvs [MEM_MAP] >> first_x_assum $ irule_at Any >> gs []) >>
              rw [] >>
              qspecl_then [‘MAP (λ(v,e). (v,replace_Force (Var v2) s e)) g’,
                           ‘Recclosure (MAP (λ(v,e). (v,replace_Force (Var v2) s e)) g)’,
                           ‘v2’] mp_tac ALOOKUP_FUN >> impl_tac
              >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM] >>
              rw [] >>
              irule exp_rel_Force_Recclosure_Delay_Var >>
              gvs []) >>
          IF_CASES_TAC >> gs [exp_rel_def] >>
          Cases_on ‘MEM s (MAP FST f)’
          >- (qspecl_then [‘f’, ‘Recclosure f’, ‘s’] mp_tac ALOOKUP_FUN >> impl_tac
              >- (gvs [MEM_MAP] >> first_x_assum $ irule_at Any >> gs []) >>
              rw [] >>
              qspecl_then [‘MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) g’,
                           ‘Recclosure (MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) g)’,
                           ‘s’] mp_tac ALOOKUP_FUN >> impl_tac
              >- gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM] >>
              rw [exp_rel_def] >>
              irule v_rel_Recclosure_Delay_Var >>
              gvs []) >>
          qspecl_then [‘REVERSE (MAP (λ(v,x). (v,Recclosure f v)) f)’, ‘s’] assume_tac ALOOKUP_NONE >>
          qspecl_then [‘REVERSE (MAP (λ(v,x). (v, Recclosure (MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) g) v))
                        (MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) g))’, ‘s’] assume_tac ALOOKUP_NONE >>
          gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, MAP_REVERSE] >>
          rw [exp_rel_def])
      >>~[‘Letrec _ _’]
      >- (gvs [Once replace_Force_def, subst_def] >>
          irule exp_rel_Force >>
          first_x_assum irule >> gvs [exp_rel_def])
      >- (irule exp_rel_Force >>
          first_x_assum irule >> gvs [] >>
          irule exp_rel_Letrec_Delay_Var >> gvs [])
      >~[‘Let opt _ _’]
      >- (gvs [replace_Force_def, subst_def] >>
          irule exp_rel_Force >>
          first_x_assum irule >> gvs [exp_rel_def])
      >~[‘Let _ _ _’]
      >- (irule exp_rel_Force >>
          first_x_assum irule >> gvs [] >>
          irule exp_rel_Let_Delay_Var >>
          gvs [])
      >~[‘Force (Force _)’]
      >- (gvs [replace_Force_def, subst_def] >>
          irule exp_rel_Force >>
          first_x_assum irule >> gvs [] >>
          irule exp_rel_Force >> gvs [])
      >>~[‘Force (Value _)’]
      >- (gvs [replace_Force_def, subst_def] >>
          irule exp_rel_Force >>
          irule exp_rel_Force_Value >>
          gvs [])
      >- (gvs [replace_Force_def, subst_def] >>
          irule exp_rel_Force >>
          irule exp_rel_Force_Recclosure_Delay_Var >>
          gvs []) >>
      irule exp_rel_Force >>
      first_x_assum irule >> gvs [exp_rel_def] >>
      first_assum $ irule_at Any >> gvs [])
  >~[‘MkTick _’]
  >- (irule exp_rel_MkTick >>
      last_x_assum irule >>
      gvs [exp_size_def, boundvars_def])
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
  >~ [‘App f x’] >- (
    rw [exp_rel_def] \\ gs []
    \\ rename1 ‘exp_rel x y’ \\ rename1 ‘exp_rel f g’
    \\ gs [eval_to_def]
    \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac)) \\ gs []
    \\ Cases_on ‘eval_to k y’ \\ gs []
    >~[‘INL err’]
    >- (qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k) x’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k) x’ \\ gs []
    \\ rename1 ‘v_rel v1 w1’
    \\ first_x_assum (drule_then (qx_choose_then ‘jf’ assume_tac)) \\ gs []
    \\ Cases_on ‘eval_to k g = INL Diverge’ \\ gs []
    >- (Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
        >- (
         qexists_tac ‘0’
         \\ Cases_on ‘eval_to k y’ \\ gs []
         \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
         \\ ‘eval_to (j + k) x = eval_to k x’
           by (irule eval_to_mono \\ gs [])
         \\ gs [])
        \\ ‘∀j. eval_to (j + k) f = eval_to k f’
          by (strip_tac \\ irule eval_to_mono \\ gs [])
        \\ Cases_on ‘eval_to k f’ \\ gs [])
    \\ Cases_on ‘eval_to k g’ \\ gs []
    >~ [‘_ = INL err’]
    >- (Cases_on ‘err’ \\ gs []
        \\ qexists_tac ‘jf + j’
        \\ ‘eval_to (jf + j + k) x = eval_to (j + k) x’
          by (irule eval_to_mono \\ gs [])
        \\ ‘eval_to (jf + j + k) f = eval_to (jf + k) f’
          by (irule eval_to_mono \\ gs []
              \\ strip_tac \\ gs [])
        \\ Cases_on ‘eval_to (jf + k) f’ \\ gs [])
    \\ Cases_on ‘eval_to (jf + k) f’ \\ gs []
    \\ rename1 ‘v_rel v2 w2’
    \\ ‘∀i. eval_to (i + j + k) x = eval_to (j + k) x’
        by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ ‘∀i. eval_to (i + jf + k) f = eval_to (jf + k) f’
      by (strip_tac \\ irule eval_to_mono \\ gs [])
    \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
    \\ Cases_on ‘v2’ \\ gvs [dest_anyClosure_def, v_rel_def]
    >~[‘Closure s e’]
    >- (IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono \\ gs []
            \\ Cases_on ‘eval_to 0 f = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘jf’] assume_tac) eval_to_mono \\ gs [])
        \\ rename1 ‘eval_to (k - 1) (subst1 s w1 e2)’
        \\ rename1 ‘exp_rel e1 e2’
        \\ last_x_assum $ qspecl_then [‘subst1 s v1 e1’, ‘subst1 s w1 e2’] mp_tac
        \\ impl_tac
        >- (irule exp_rel_subst \\ gvs [LIST_REL_def])
        \\ disch_then $ qx_choose_then ‘js’ assume_tac
        \\ Cases_on ‘eval_to (k - 1) (subst1 s w1 e2) = INL Diverge’ \\ gs []
        >- (qexists_tac ‘0’
            \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
            \\ Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘jf + k’] assume_tac) eval_to_mono \\ gs []
            \\ Cases_on ‘eval_to (k - 1) (subst1 s v1 e1) = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘js + k - 1’] assume_tac) eval_to_mono \\ gs [])
        \\ qexists_tac ‘j + jf + js’
        \\ first_x_assum $ qspecl_then [‘j + js’] assume_tac
        \\ first_x_assum $ qspecl_then [‘jf + js’] assume_tac
        \\ gvs []
        \\ Cases_on ‘eval_to (js + k - 1) (subst1 s v1 e1) = INL Diverge’ \\ gs []
        >- (Cases_on ‘eval_to (k - 1) (subst1 s w1 e2)’ \\ gs [])
        \\ dxrule_then (qspecl_then [‘j + jf + js + k - 1’] assume_tac) eval_to_mono
        \\ gvs [])
    >>~[‘Recclosure g1 s’]
    >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
        \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
            (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
        \\ gs [OPTREL_def]
        >- (qexists_tac ‘j + jf’
            \\ first_x_assum $ qspecl_then [‘j’] assume_tac
            \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs [])
        \\ rename1 ‘exp_rel x0 y0’ \\ Cases_on ‘x0’ \\ gvs [exp_rel_def]
        >~[‘subst (MAP _ ys ++ [(s2, w1)]) e2’]
        >- (Cases_on ‘k = 0’ \\ gs []
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono \\ gs []
                \\ Cases_on ‘eval_to 0 f = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘jf’] assume_tac) eval_to_mono \\ gs [])
            \\ rename1 ‘exp_rel e1 e2’
            \\ last_x_assum $ qspecl_then [‘subst (MAP (λ(g, x). (g, Recclosure xs g)) xs ++ [(s2, v1)]) e1’,
                                           ‘subst (MAP (λ(g, x). (g, Recclosure ys g)) ys ++ [(s2, w1)]) e2’] mp_tac
            \\ impl_tac
            >- (irule exp_rel_subst
                \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM SND_THM, FST_THM]
                \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                \\ pairarg_tac \\ gvs [] \\ pairarg_tac \\ gvs []
                \\ gvs [v_rel_def]
                \\ gvs [LIST_REL_EL_EQN, EL_MAP, GSYM FST_THM]
                \\ ‘∀i. i < LENGTH ys ⇒ FST (EL i xs) = FST (EL i ys)’
                  by (rw [] >>
                      ‘i < LENGTH xs’ by gs [] >>
                      dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                      ‘i < LENGTH ys’ by gs [] >>
                      dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                      rw [])
                \\ first_x_assum $ dxrule_then assume_tac >> gvs [])
            \\ disch_then $ qx_choose_then ‘js’ assume_tac
            \\ Cases_on ‘eval_to (k-1) (subst (MAP (λ(g,x).(g,Recclosure ys g)) ys ++ [(s2,w1)]) e2) = INL Diverge’
            \\ gs []
            >- (qexists_tac ‘0’ \\ gs []
                \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
                \\ Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘jf + k’] assume_tac) eval_to_mono \\ gs []
                \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs ++ [(s2,v1)]) e1)
                             = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘js + k - 1’] assume_tac) eval_to_mono \\ gs [])
            \\ qexists_tac ‘j + jf + js’
            \\ first_x_assum $ qspecl_then [‘j + js’] assume_tac
            \\ first_x_assum $ qspecl_then [‘jf + js’] assume_tac
            \\ gvs []
            \\ Cases_on ‘eval_to (js + k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs ++ [(s2,v1)]) e1)
                         = INL Diverge’ \\ gs []
            >- (Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure ys g)) ys ++ [(s2,w1)]) e2)’ \\ gs [])
            \\ dxrule_then (qspecl_then [‘j + jf + js + k - 1’] assume_tac) eval_to_mono
            \\ gvs [])
        \\ qexists_tac ‘j + jf’
        \\ first_x_assum $ qspecl_then [‘j’] assume_tac
        \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs [])
    >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
        \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s)
            (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
          \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
        \\ gs [OPTREL_def, GSYM MAP_REVERSE, ALOOKUP_MAP]
        >- (qexists_tac ‘j + jf’
            \\ first_x_assum $ qspecl_then [‘j’] assume_tac
            \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs [])
        \\ rename1 ‘exp_rel x0 y0’ \\ Cases_on ‘x0’ \\ gvs [exp_rel_def, replace_Force_def]
        >~[‘Lam s2 y2’]
        >- (IF_CASES_TAC \\ gvs []
            \\ Cases_on ‘k = 0’ \\ gs []
            >>~[‘($= +++ v_rel) _ (INL Diverge)’]
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono \\ gs []
                \\ Cases_on ‘eval_to 0 f = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘jf’] assume_tac) eval_to_mono \\ gs [])
            >- (qexists_tac ‘0’
                \\ Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j’] assume_tac) eval_to_mono \\ gs []
                \\ Cases_on ‘eval_to 0 f = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘jf’] assume_tac) eval_to_mono \\ gs [])
            >~[‘subst _ (replace_Force (Var v2) v1 e2)’]
            >- (rename1 ‘exp_rel e1 e2’
                \\ last_x_assum $ qspecl_then [‘subst (MAP (λ(g, x). (g, Recclosure xs g)) xs ++ [(s2, v1')]) e1’,
                      ‘subst (MAP (λ(g, x). (g, Recclosure (MAP (λ(v,e).(v,replace_Force (Var v2) v1 e)) ys) g))
                              (MAP (λ(v,e).(v,replace_Force (Var v2) v1 e)) ys) ++ [(s2, w1)])
                                                (replace_Force (Var v2) v1 e2)’] mp_tac
                \\ impl_tac
                >- (gvs [subst_APPEND]
                    \\ dxrule_then assume_tac ALOOKUP_MEM
                    \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
                    \\ rename1 ‘replace_Force (Var (FST pair)) _ _’
                    \\ qspecl_then [‘e2’, ‘Var (FST pair)’, ‘v1’, ‘[(s2, w1)]’] mp_tac subst_replace_Force
                    \\ impl_tac
                    >- (first_x_assum $ dxrule_then assume_tac
                        \\ gvs [freevars_def, boundvars_def])
                    \\ rw [subst1_def]
                    >- (first_x_assum $ dxrule_then assume_tac
                        \\ gvs [boundvars_def])
                    \\ assume_tac exp_rel_subst_Recclosure \\ gs [subst_funs_def] \\ first_x_assum irule
                    \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, boundvars_subst]
                    \\ qexists_tac ‘pair’ \\ gvs [exp_rel_subst]
                    \\ first_x_assum $ dxrule_then assume_tac
                    \\ gvs [boundvars_def])
                \\ disch_then $ qx_choose_then ‘js’ assume_tac
                \\ qabbrev_tac ‘ys2 = MAP (λ(v,e). (v,replace_Force (Var v2) v1 e)) ys’
                \\ Cases_on ‘eval_to (k-1) (subst (MAP (λ(g,x).(g,Recclosure ys2 g)) ys2 ++ [(s2,w1)])
                                            (replace_Force (Var v2) v1 e2)) = INL Diverge’
                \\ gs []
                >- (qexists_tac ‘0’ \\ gs []
                    \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
                    \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
                    \\ Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
                    \\ dxrule_then (qspecl_then [‘jf + k’] assume_tac) eval_to_mono \\ gs []
                    \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs ++ [(s2,v1')]) e1)
                                 = INL Diverge’ \\ gs []
                    \\ dxrule_then (qspecl_then [‘js + k - 1’] assume_tac) eval_to_mono \\ gs [])
                \\ qexists_tac ‘j + jf + js’
                \\ first_x_assum $ qspecl_then [‘j + js’] assume_tac
                \\ first_x_assum $ qspecl_then [‘jf + js’] assume_tac
                \\ gvs []
                \\ Cases_on ‘eval_to (js + k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs ++ [(s2,v1')]) e1)
                             = INL Diverge’ \\ gs []
                >- (Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure ys2 g)) ys2 ++ [(s2,w1)])
                                               (replace_Force (Var v2) v1 e2))’
                    \\ gs [])
                \\ dxrule_then (qspecl_then [‘j + jf + js + k - 1’] assume_tac) eval_to_mono
                \\ gvs [])
            \\ rename1 ‘replace_Force (Var v2) vname’
            \\ rename1 ‘exp_rel e1 e2’
            \\ qabbrev_tac ‘ys2 = MAP (λ(v,e).(v,replace_Force (Var v2) vname e)) ys’
            \\ last_x_assum $ qspecl_then [‘subst (MAP (λ(g, x). (g, Recclosure xs g)) xs ++ [(vname, v1)]) e1’,
                      ‘subst (MAP (λ(g, x). (g, Recclosure ys2 g)) ys2 ++ [(vname, w1)]) e2’] mp_tac
            \\ impl_tac
            >- (irule exp_rel_subst
                \\ unabbrev_all_tac
                \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM SND_THM, GSYM FST_THM]
                \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
                \\ pairarg_tac \\ gvs [] \\ pairarg_tac \\ gvs []
                \\ rename1 ‘n < _’
                \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
                \\ irule v_rel_Recclosure_Delay_Var
                \\ gvs [LIST_REL_EL_EQN, EL_MAP])
            \\ disch_then $ qx_choose_then ‘js’ assume_tac
            \\ Cases_on ‘eval_to (k-1) (subst (MAP (λ(g,x).(g,Recclosure ys2 g)) ys2 ++ [(vname,w1)]) e2)
                         = INL Diverge’
            \\ gs []
            >- (qexists_tac ‘0’ \\ gs []
                \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘j + k’] assume_tac) eval_to_mono \\ gs []
                \\ Cases_on ‘eval_to k f = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘jf + k’] assume_tac) eval_to_mono \\ gs []
                \\ Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs ++ [(vname,v1)]) e1)
                             = INL Diverge’ \\ gs []
                \\ dxrule_then (qspecl_then [‘js + k - 1’] assume_tac) eval_to_mono \\ gs [])
            \\ qexists_tac ‘j + jf + js’
            \\ first_x_assum $ qspecl_then [‘j + js’] assume_tac
            \\ first_x_assum $ qspecl_then [‘jf + js’] assume_tac
            \\ gvs []
            \\ Cases_on ‘eval_to (js + k - 1) (subst (MAP (λ(g,x).(g,Recclosure xs g)) xs ++ [(vname,v1)]) e1)
                         = INL Diverge’ \\ gs []
            >- (Cases_on ‘eval_to (k - 1) (subst (MAP (λ(g,x).(g,Recclosure ys2 g)) ys2 ++ [(vname,w1)]) e2)’
                \\ gs [])
            \\ dxrule_then (qspecl_then [‘j + jf + js + k - 1’] assume_tac) eval_to_mono
            \\ gvs [])
        >>~[‘Let opt _ _’]
        >- (qexists_tac ‘j + jf’
            \\ first_x_assum $ qspecl_then [‘j’] assume_tac
            \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs []
            \\ Cases_on ‘opt’ \\ gvs [replace_Force_def]
            \\ IF_CASES_TAC \\ gvs [])
        >- (qexists_tac ‘j + jf’
            \\ first_x_assum $ qspecl_then [‘j’] assume_tac
            \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs []
            \\ IF_CASES_TAC \\ gvs [])
        >>~[‘Letrec _ (replace_Force (Var v2) vname1 _)’]
        >- (qexists_tac ‘j + jf’
            \\ first_x_assum $ qspecl_then [‘j’] assume_tac
            \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs []
            \\ IF_CASES_TAC \\ gvs [])
        >- (qexists_tac ‘j + jf’
            \\ first_x_assum $ qspecl_then [‘j’] assume_tac
            \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs []
            \\ IF_CASES_TAC \\ gvs [])
        >~[‘replace_Force _ _ (Force y2)’]
        >- (qexists_tac ‘j + jf’
            \\ first_x_assum $ qspecl_then [‘j’] assume_tac
            \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs []
            \\ Cases_on ‘y2’ \\ gvs [replace_Force_def]
            \\ IF_CASES_TAC \\ gvs [])
        \\ qexists_tac ‘j + jf’
        \\ first_x_assum $ qspecl_then [‘j’] assume_tac
        \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs [])
    \\ qexists_tac ‘j + jf’
    \\ first_x_assum $ qspecl_then [‘j’] assume_tac
    \\ first_x_assum $ qspecl_then [‘jf’] assume_tac \\ gvs [])
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
    >~[‘Delay (Var v1)’]
    >- (gvs [eval_to_def]
        \\ IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs [])
        \\ gvs [subst_def, eval_to_def]
        \\ last_assum $ qspecl_then [‘k - 2’] assume_tac
        \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac
        \\ last_x_assum kall_tac \\ last_x_assum kall_tac \\ gs []
        \\ rename1 ‘exp_rel x x2’
        \\ first_x_assum $ qspecl_then [‘x’, ‘x2’] assume_tac \\ gs []
        \\ rename1 ‘j + k - 1’
        \\ Cases_on ‘eval_to (k - 1) x2’
        >~[‘INL err’]
        >- (qexists_tac ‘j’ \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gvs [])
        \\ gvs []
        \\ CASE_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs []
            \\ Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j + k - 1’] assume_tac) eval_to_mono \\ gs []
            \\ Cases_on ‘eval_to (k - 1) x’ \\ gs [])
        \\ rename1 ‘replace_Force (Var v) w y2’
        \\ rename1 ‘_ = INR val2’
        \\ rename1 ‘exp_rel y y2’
        \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs []
        \\ rename1 ‘v_rel val1 val2’
        \\ first_x_assum $ qspecl_then [‘subst1 w (Thunk (INR (Value val1))) (subst1 v val1 y)’,
             ‘subst1 w (Thunk (INR (Value val2))) (subst1 v val2 (replace_Force (Var v) w y2))’] mp_tac
        \\ impl_tac
        >- (qspecl_then [‘y2’, ‘Var v’, ‘w’, ‘[(v, val2)]’] assume_tac subst_replace_Force
            \\ drule_then assume_tac exp_rel_freevars
            \\ gvs [subst1_notin_frees, subst_def, freevars_def]
            \\ gvs [freevars_def, subst_def]
            \\ gvs [exp_rel_subst_replace_Force])
        \\ disch_then $ qx_choose_then ‘j1’ assume_tac
        \\ Cases_on ‘eval_to (k − 2) (subst1 w (Thunk (INR (Value val2)))
                                      (subst1 v val2 (replace_Force (Var v) w y2))) = INL Diverge’
        >- (qexists_tac ‘0’ \\ gs []
            \\ Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j + k - 1’] assume_tac) eval_to_mono \\ gs []
            \\ Cases_on ‘eval_to (k - 2) (subst1 w (Thunk (INR (Value val1)))
                                          (subst1 v val1 y)) = INL Diverge’ \\ gs []
            \\ dxrule_then (qspecl_then [‘j1 + k - 2’] assume_tac) eval_to_mono \\ gs [])
        \\ qexists_tac ‘j + j1’
        \\ ‘eval_to (j + j1 + k - 1) x = eval_to (j + k - 1) x’
          by (irule eval_to_mono \\ gs [])
        \\ ‘eval_to (j + j1 + k - 2) (subst1 w (Thunk (INR (Value val1))) (subst1 v val1 y))
            = eval_to (j1 + k - 2) (subst1 w (Thunk (INR (Value val1))) (subst1 v val1 y))’
          by (irule eval_to_mono
              \\ gs [] \\ strip_tac
              \\ Cases_on ‘eval_to (k − 2) (subst1 w (Thunk (INR (Value val2)))
                                            (subst1 v val2 (replace_Force (Var v) w y2)))’ \\ gs [])
        \\ gvs [])
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
        \\ IF_CASES_TAC \\ gs []
        >- (qexists_tac ‘0’ \\ gs [])
        \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
        \\ first_x_assum irule
        \\ irule exp_rel_subst_Recclosure
        \\ gvs []))
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
    >~[‘Force (Value (Recclosure _ _))’]
    >- (once_rewrite_tac [eval_to_def] >>
        qexists_tac ‘1’ >> gvs [] >>
        rw [Once eval_to_def, dest_anyThunk_def] >>
        rename1 ‘MEM (v1, Delay (Var v2)) f’ >>
        qspecl_then [‘Delay (Var v2)’, ‘v1’, ‘REVERSE f’] assume_tac $ GEN_ALL ALOOKUP_ALL_DISTINCT_MEM >>
        gvs [MAP_REVERSE, ALL_DISTINCT_REVERSE, subst_funs_def, subst_def] >>
        qspecl_then [‘f’, ‘Recclosure f’, ‘v2’] assume_tac ALOOKUP_FUN >> gvs [eval_to_def] >>
        irule v_rel_Recclosure_Delay_Var >>
        gvs [])
    >~[‘Force (Value _)’]
    >- (once_rewrite_tac [eval_to_def]
        \\ qexists_tac ‘1’ \\ gvs []
        \\ simp [Once eval_to_def]
        \\ gvs [dest_anyThunk_def]
        \\ gvs [subst_funs_def, subst_empty, eval_to_def])
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
      >>~[‘Recclosure _ _’]
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL exp_rel
              (ALOOKUP (REVERSE xs) s)
              (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
          \\ gs [OPTREL_def]
          >- (qexists_tac ‘j’ \\ gvs [])
          \\ CASE_TAC \\ gs [exp_rel_def]
          >~[‘subst_funs ys e2’]
          >- (rename1 ‘exp_rel x0 (Delay e2)’
              \\ Cases_on ‘x0’ \\ gs [exp_rel_def]
              \\ rename1 ‘exp_rel e1 e2’
              \\ last_x_assum $ qspecl_then [‘subst_funs xs e1’, ‘subst_funs ys e2’] mp_tac
              \\ impl_tac
              >- (gvs [subst_funs_def] \\ irule exp_rel_subst
                  \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, LIST_REL_EL_EQN, EL_MAP]
                  \\ rw [] \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs [v_rel_def, LIST_REL_EL_EQN, EL_MAP]
                  \\ ‘∀i. i < LENGTH xs ⇒ FST (EL i xs) = FST (EL i ys)’
                    by (rw [] >>
                        ‘i < LENGTH xs’ by gs [] >>
                        dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                        ‘i < LENGTH ys’ by gs [] >>
                        dxrule_then (qspecl_then [‘FST’] assume_tac) $ GSYM EL_MAP >>
                        rw [])
                  \\ gs [] \\ first_x_assum $ dxrule_then assume_tac \\ gvs [])
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
          \\ rename1 ‘exp_rel x0 _’ \\ Cases_on ‘x0’ \\ gvs [exp_rel_def]
          \\ qexists_tac ‘j’ \\ gvs [])
      >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
          \\ ‘OPTREL exp_rel
              (ALOOKUP (REVERSE xs) s)
              (ALOOKUP (REVERSE ys) s)’
            by (irule LIST_REL_OPTREL
                \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
          \\ gs [OPTREL_def, GSYM MAP_REVERSE, ALOOKUP_MAP]
          >- (qexists_tac ‘j’ \\ gvs [])
          \\ rename1 ‘replace_Force (Var v2) v1 y0’
          \\ rename1 ‘exp_rel x0 y0’
          \\ Cases_on ‘x0’ \\ gs [exp_rel_def, replace_Force_def]
          >~[‘Lam s2 (replace_Force _ _ e2)’]
          >- (qexists_tac ‘j’
              \\ IF_CASES_TAC \\ gvs [])
          >>~[‘Letrec _ (replace_Force _ _ _)’]
          >- (qexists_tac ‘j’
              \\ IF_CASES_TAC \\ gvs [])
          >- (qexists_tac ‘j’
              \\ IF_CASES_TAC \\ gvs [])
          >>~[‘Let opt _ _’]
          >- (qexists_tac ‘j’
              \\ Cases_on ‘opt’ \\ gvs [replace_Force_def]
              \\ IF_CASES_TAC \\ gvs [])
          >- (qexists_tac ‘j’
              \\ IF_CASES_TAC \\ gvs [])
          >~[‘replace_Force _ _ (Force y)’]
          >- (qexists_tac ‘j’
              \\ Cases_on ‘y’ \\ gvs [replace_Force_def]
              \\ IF_CASES_TAC \\ gs [])
          >~[‘subst_funs (MAP _ ys) (replace_Force (Var v2) v1 e2)’]
          >- (rename1 ‘exp_rel e1 e2’
              \\ last_x_assum $ qspecl_then [‘subst_funs xs e1’,
                                             ‘subst_funs (MAP (λ(v,e). (v, replace_Force (Var v2) v1 e)) ys)
                                              (replace_Force (Var v2) v1 e2)’] mp_tac
              \\ impl_tac
              >- (irule exp_rel_subst_Recclosure
                  \\ gvs [EVERY_MEM]
                  \\ dxrule_then assume_tac ALOOKUP_MEM
                  \\ gvs [MEM_MAP, PULL_EXISTS]
                  \\ first_x_assum $ dxrule_then assume_tac
                  \\ gvs [boundvars_def])
              \\ disch_then $ qx_choose_then ‘j2’ assume_tac
              \\ Cases_on ‘eval_to (k - 1) (subst_funs (MAP (λ(v,e). (v, replace_Force (Var v2) v1 e)) ys)
                                              (replace_Force (Var v2) v1 e2)) = INL Diverge’ \\ gs []
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
                    \\ Cases_on ‘eval_to (k - 1) (subst_funs (MAP (λ(v,e). (v, replace_Force (Var v2) v1 e)) ys)
                                                  (replace_Force (Var v2) v1 e2))’ \\ gvs [])
              \\ gvs [])
          \\ qexists_tac ‘j’ \\ gvs [])
      >~[‘subst_funs [] y2’]
      >- (rename1 ‘exp_rel x2 y2’
          \\ last_x_assum $ qspecl_then [‘x2’, ‘y2’] assume_tac \\ gs [subst_funs_def]
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
    pop_assum mp_tac
    \\ simp [Once exp_rel_def]
    \\ rw []
    \\ gvs [eval_to_def]
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
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ first_x_assum $ qspec_then ‘0’ assume_tac \\ gs []
      \\ rename1 ‘exp_rel x y’
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
      \\ IF_CASES_TAC \\ gs []
      >- (
        qexists_tac ‘0’
        \\ gs [])
      \\ first_x_assum $ qspec_then ‘0’ assume_tac \\ gs []
      \\ rename1 ‘exp_rel x y’
      \\ last_x_assum $ qspecl_then [‘k - 1’] assume_tac \\ gvs []
      \\ first_x_assum (drule_then (qx_choose_then ‘j’ assume_tac))
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (k - 1) y’
      \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v w’
      \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [LIST_REL_EL_EQN, v_rel_def]
      \\ IF_CASES_TAC \\ gs []
      \\ rw [v_rel_def])
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
  \\ rename1 ‘_ (eval_to k x) _’
  \\ drule_all_then
     (qspec_then ‘k’ (qx_choose_then ‘m’ assume_tac)) exp_rel_eval_to
  \\ dxrule_then (qspecl_then [‘k + m’] assume_tac) eval_to_mono
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
  >- (rename1 ‘LIST_REL _ (MAP SND xs) (MAP SND ys)’
      \\ ‘OPTREL exp_rel (ALOOKUP (REVERSE xs) s) (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, EL_MAP, LIST_EQ_REWRITE])
      \\ gs [OPTREL_def, GSYM MAP_REVERSE, ALOOKUP_MAP]
      \\ qpat_x_assum ‘exp_rel x0 _’ mp_tac
      \\ rw [Once exp_rel_cases] \\ gs [replace_Force_def]
      >- (IF_CASES_TAC \\ gs []
          \\ first_x_assum irule
          \\ irule exp_rel_eval
          >- (irule exp_rel_subst
              \\ gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
              \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
              \\ pairarg_tac \\ gs [] \\ pairarg_tac \\ gs []
              \\ rename1 ‘n < _’
              \\ ‘EL n (MAP FST xs) = EL n (MAP FST ys)’ by gvs [] \\ gvs [EL_MAP]
              \\ irule v_rel_Recclosure_Delay_Var
              \\ gvs [LIST_REL_EL_EQN, EL_MAP])
          >- (gvs [subst_APPEND]
              \\ rename1 ‘subst1 n w2 (replace_Force (Var var) v1 y)’
              \\ drule_then assume_tac ALOOKUP_MEM
              \\ gvs [EVERY_MEM, MEM_MAP,  PULL_EXISTS]
              \\ first_assum $ dxrule_then assume_tac
              \\ gvs [boundvars_def]
              \\ rename1 ‘replace_Force (Var (FST pair))’
              \\ qspecl_then [‘y’, ‘Var (FST pair)’, ‘v1’, ‘[(n, w2)]’] assume_tac subst_replace_Force
              \\ gvs [freevars_def, subst_def]
              \\ assume_tac exp_rel_subst_Recclosure \\ gvs [subst_funs_def]
              \\ first_x_assum irule
              \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, boundvars_subst]
              \\ qexists_tac ‘pair’ \\ gs [exp_rel_subst]))
      >- (IF_CASES_TAC \\ gs [])
      >- (IF_CASES_TAC \\ gs [])
      >- (rename1 ‘Let opt _ _’
          \\ Cases_on ‘opt’ \\ gvs [replace_Force_def]
          \\ IF_CASES_TAC \\ gs [])
      >- (IF_CASES_TAC \\ gs [])
      >- (rename1 ‘Force y’ \\ Cases_on ‘y’ \\ gvs [replace_Force_def]
          \\ IF_CASES_TAC \\ gvs []))
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

Definition no_value_def:
  (no_value (Var n) = T) ∧
  (no_value (Force x) = no_value x) ∧
  (no_value (Prim op xs) = EVERY no_value xs) ∧
  (no_value (If x y z) = (no_value x ∧ no_value y ∧ no_value z)) ∧
  (no_value (App x y) = (no_value x ∧ no_value y)) ∧
  (no_value (Lam s x) = no_value x) ∧
  (no_value (Let opt x y) = (no_value x ∧ no_value y)) ∧
  (no_value (Box x) = no_value x) ∧
  (no_value (MkTick x) = no_value x) ∧
  (no_value (Letrec f x) = (no_value x ∧ EVERY no_value (MAP SND f) ∧ EVERY ok_bind (MAP SND f))) ∧
  (no_value (Value v) = F) ∧
  (no_value (Delay x) = no_value x)
Termination
  WF_REL_TAC ‘measure $ exp_size’ \\ rw [MEM_MAP, SND_THM]
  \\ assume_tac exp_size_lemma
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum $ dxrule_then assume_tac \\ gvs []
End

Theorem exp_rel_refl:
  ∀x. no_value x ⇒ exp_rel x x
Proof
  Induct using freevars_ind >> gvs [exp_rel_def, no_value_def, EVERY_CONJ] >>
  gvs [EVERY_EL, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN] >> rw [] >>
  disj1_tac >> rw [] >>
  last_x_assum irule >> gvs [] >>
  first_assum $ irule_at Any >>
  gvs [EL_MAP] >> irule_at Any PAIR
QED

Theorem no_value_replace_Force:
  ∀y x v. no_value x ∧ no_value y ⇒ no_value (replace_Force x v y)
Proof
  Induct using freevars_ind >> gvs [no_value_def, replace_Force_def] >> rw [no_value_def]
  >- gvs [EVERY_EL, MEM_EL, PULL_EXISTS, EL_MAP]
  >- (gvs [EVERY_EL, MEM_EL, PULL_EXISTS, EL_MAP] >> rw [] >>
      pairarg_tac >> gvs [] >>
      last_x_assum $ drule_then irule >>
      rpt $ last_x_assum $ drule_then assume_tac >> gvs [])
  >- (gvs [EVERY_EL, MEM_EL, PULL_EXISTS, EL_MAP] >> rw [] >>
      pairarg_tac >> gvs [] >>
      rpt $ last_x_assum $ drule_then assume_tac >>
      gvs [] >>
      rename1 ‘ok_bind (replace_Force _ _ e2)’ >>
      Cases_on ‘e2’ >> gvs [ok_bind_def, replace_Force_def] >>
      rw [ok_bind_def])
  >- (rename1 ‘replace_Force x v (Force y)’ >>
      last_x_assum $ qspecl_then [‘x’, ‘v’] assume_tac >> gs [] >>
      Cases_on ‘y’ >> rw [Once replace_Force_def, no_value_def])
QED

Theorem exp_rel_no_value:
  ∀x y. no_value x ∧ exp_rel x y ⇒ no_value y
Proof
  Induct using freevars_ind >> gvs [exp_rel_def, no_value_def, PULL_EXISTS]
  >- (gvs [EVERY_EL, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP] >> rw [] >>
      metis_tac [])
  >- (rw [] >> gvs [no_value_def] >>
      irule no_value_replace_Force >>
      rename1 ‘Let (SOME v1) (Delay (Var s)) y1’ >> rename1 ‘exp_rel y1 y2’ >>
      first_x_assum $ qspecl_then [‘Let (SOME v1) (Delay (Var s)) y2’] mp_tac >>
      impl_tac
      >- (irule exp_rel_Let >> gvs [exp_rel_def]) >>
      gvs [no_value_def])
  >- (rw [] >>
      gvs [no_value_def, EVERY_EL, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP, no_value_replace_Force] >>
      rw []
      >- (last_x_assum $ drule_then irule >>
          irule_at Any PAIR >> gvs [])
      >- (pairarg_tac >> gs [] >>
          irule no_value_replace_Force >> gs [no_value_def] >>
          last_x_assum irule >>
          rename1 ‘EL n2 g = (_, _)’ >> rpt $ first_x_assum $ qspecl_then [‘n2’] assume_tac >> gs [] >>
          irule_at Any PAIR >>
          rpt $ first_x_assum $ irule_at $ Pos last)
      >- (pairarg_tac >> gs [] >>
          rename1 ‘EL n2 g = (_, _)’ >> rpt $ first_x_assum $ qspecl_then [‘n2’] assume_tac >> gs [] >>
          Cases_on ‘SND (EL n2 g)’ >> gvs [replace_Force_def, ok_bind_def] >> rw [ok_bind_def]))
  >- (rw [] >> gvs [no_value_def])
QED

(* A relation included in the transitive closure of the relation before *)

Inductive full_exp_rel:
[~Var:]
  (∀n. full_exp_rel (Var n) (Var n)) ∧
[~Prim:]
  (∀op xs ys.
     LIST_REL full_exp_rel xs ys ⇒
       full_exp_rel (Prim op xs) (Prim op ys)) ∧
[~App:]
  (∀f g x y.
     full_exp_rel f g ∧
     full_exp_rel x y ⇒
       full_exp_rel (App f x) (App g y)) ∧
[~Lam:]
  (∀s x y.
     full_exp_rel x y ⇒
       full_exp_rel (Lam s x) (Lam s y)) ∧
[~Letrec:]
  (∀f g x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL full_exp_rel (MAP SND f) (MAP SND g) ∧
     full_exp_rel x y ⇒
     full_exp_rel (Letrec f x) (Letrec g y)) ∧
[~Letrec_Delay_Var:]
  (∀f g vL x y.
     MAP FST f = MAP FST g ∧
     EVERY ok_bind (MAP SND f) ∧
     EVERY ok_bind (MAP SND g) ∧
     LIST_REL full_exp_rel (MAP SND f) (MAP SND g) ∧
     ALL_DISTINCT (MAP FST f) ∧
     ALL_DISTINCT (MAP FST vL) ∧
     EVERY (λ(v1, v2). MEM v2 (MAP FST f) ∧ MEM (v1, Delay (Var v2)) f ∧
                       EVERY (λe. v2 ∉ boundvars e) (MAP SND g) ∧
                       v2 ∉ boundvars y ∧ v1 ≠ v2) vL ∧
     full_exp_rel x y ⇒
     full_exp_rel (Letrec f x)
             (Letrec (FOLDL (λl (v1, v2). MAP (λ(v,e). (v, replace_Force (Var v2) v1 e)) l) g vL)
              (FOLDL (λe (v1, v2). replace_Force (Var v2) v1 e) y vL))) ∧
[~Let:]
  (∀opt x1 y1 x2 y2.
     full_exp_rel x1 x2 ∧
     full_exp_rel y1 y2 ⇒
       full_exp_rel (Let opt x1 y1) (Let opt x2 y2)) ∧
[~Let_Delay_Var:]
  (∀v1 v2 x1 x2 y1 y2.
     v2 ∉ freevars y1 ∧ v2 ∉ boundvars y1 ∧ v1 ≠ v2 ∧
     full_exp_rel x1 x2 ∧ full_exp_rel y1 y2 ⇒
     full_exp_rel (Let (SOME v2) x1 (Let (SOME v1) (Delay (Var v2)) y1))
             (Let (SOME v2) x2 (Let (SOME v1) (Delay (Var v2)) (replace_Force (Var v2) v1 y2)))) ∧
[~If:]
  (∀x1 y1 z1 x2 y2 z2.
     full_exp_rel x1 x2 ∧
     full_exp_rel y1 y2 ∧
     full_exp_rel z1 z2 ⇒
       full_exp_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[~Delay:]
  (∀x y.
     full_exp_rel x y ⇒
       full_exp_rel (Delay x) (Delay y)) ∧
[~Box:]
  (∀x y.
     full_exp_rel x y ⇒
       full_exp_rel (Box x) (Box y)) ∧
[~Force:]
  (∀x y.
     full_exp_rel x y ⇒
     full_exp_rel (Force x) (Force y)) ∧
[~MkTick:]
  (∀x y. full_exp_rel x y ⇒ full_exp_rel (MkTick x) (MkTick y))
End

Theorem full_exp_rel_def =
  [“full_exp_rel (Var v) x”,
   “full_exp_rel (Value v) x”,
   “full_exp_rel (Prim op xs) x”,
   “full_exp_rel (App f x) y”,
   “full_exp_rel (Lam s x) y”,
   “full_exp_rel (Letrec f x) y”,
   “full_exp_rel (Let s x y) z”,
   “full_exp_rel (If x y z) w”,
   “full_exp_rel (Delay x) y”,
   “full_exp_rel (Box x) y”,
   “full_exp_rel (MkTick x) y”,
   “full_exp_rel (Force x) y”]
  |> map (SIMP_CONV (srw_ss()) [Once full_exp_rel_cases])
  |> LIST_CONJ;

Theorem full_exp_rel_Apps:
  ∀ys f e. full_exp_rel (Apps f ys) e ⇔
             ∃ys' f'. e = Apps f' ys' ∧ full_exp_rel f f' ∧ LIST_REL full_exp_rel ys ys'
Proof
  Induct \\ gvs [full_exp_rel_def]
  \\ rpt $ gen_tac \\ eq_tac \\ rw []
  >- (Q.REFINE_EXISTS_TAC ‘_::_’ \\ gvs []
      \\ irule_at (Pos hd) EQ_REFL
      \\ simp [])
  \\ simp []
  \\ irule_at (Pos hd) EQ_REFL \\ gvs []
QED

Theorem full_exp_rel_Lams:
  ∀vL x y. full_exp_rel (Lams vL x) y ⇔
             ∃y'. y = Lams vL y' ∧ full_exp_rel x y'
Proof
  Induct \\ gvs [full_exp_rel_def]
  \\ rpt $ gen_tac \\ eq_tac \\ rw []
  \\ metis_tac []
QED

Theorem full_exp_rel_IMP_no_value:
  ∀x y. full_exp_rel x y ⇒ no_value x
Proof
  Induct using freevars_ind >> gvs [full_exp_rel_def, no_value_def, PULL_EXISTS] >>
  rw [] >> gvs []
  >>~[‘Let _ _ _’]
  >- metis_tac []
  >- (first_x_assum irule >>
      irule_at Any full_exp_rel_Let >>
      gvs [full_exp_rel_def] >>
      first_x_assum $ irule_at Any)
  >>~[‘EVERY _ _’]
  >- (gvs [EVERY_EL, MEM_EL, LIST_REL_EL_EQN, PULL_EXISTS] >>
      rw [] >>
      last_x_assum $ drule_then irule >>
      last_x_assum $ drule_then $ irule_at Any)
  >- metis_tac []
  >- (gvs [EVERY_EL, MEM_EL, LIST_REL_EL_EQN, PULL_EXISTS, EL_MAP] >>
      rw [] >>
      last_x_assum $ drule_then irule >>
      last_x_assum $ drule_then $ irule_at Any >>
      irule_at Any PAIR)
  >- metis_tac []
  >- (gvs [EVERY_EL, MEM_EL, LIST_REL_EL_EQN, PULL_EXISTS, EL_MAP] >>
      rw [] >>
      last_x_assum $ drule_then irule >>
      last_x_assum $ drule_then $ irule_at Any >>
      irule_at Any PAIR) >>
  first_x_assum $ drule_then irule
QED

Theorem NRC_exp_rel_refl:
  ∀n. no_value x ⇒ NRC exp_rel n x x
Proof
  Induct >> rw [NRC] >>
  irule_at Any exp_rel_refl >> gvs []
QED

Theorem no_value_NRC_exp_rel:
  ∀n x y. no_value x ∧ NRC exp_rel n x y ⇒ no_value y
Proof
  Induct >> gvs [NRC] >> rw [] >>
  last_x_assum irule >> first_x_assum $ irule_at $ Pos last >>
  drule_all_then irule exp_rel_no_value
QED

Theorem rel_uses_Letrecs_exp_rel_trans:
  ∀xs ys x y. rel_uses_Letrecs exp_rel xs x ∧ exp_rel (Letrec xs x) (Letrec ys y) ⇒
              rel_uses_Letrecs exp_rel ys y
Proof
  gvs [exp_rel_def, rel_uses_Letrecs_def] >> rw [] >> gvs []
  >- (disj1_tac >> gvs [EVERY_EL, LIST_REL_EL_EQN, EL_MAP] >> rw [] >>
      first_x_assum $ drule_then assume_tac >>
      first_x_assum $ drule_then assume_tac >>
      first_x_assum $ drule_then assume_tac >>
      rename1 ‘exp_rel (SND (EL n ys)) (SND (EL n ys2))’ >>
      Cases_on ‘SND (EL n ys)’ >> gvs [ok_bind_def, exp_rel_def])
  >- (disj1_tac >> gvs [EVERY_EL, LIST_REL_EL_EQN, EL_MAP] >> rw [] >>
      rpt $ first_x_assum $ drule_then assume_tac
      >- (rename1 ‘exp_rel (SND (EL n xs)) _’ >>
          pairarg_tac >> gs [] >>
          Cases_on ‘SND (EL n xs)’ >>
          gvs [exp_rel_def, ok_bind_def, replace_Force_def] >>
          rw [ok_bind_def])
      >- (rename1 ‘SND (_ (EL n g))’ >>
          pairarg_tac >> gs [] >>
          Cases_on ‘SND (EL n g)’ >> gvs [ok_bind_def, replace_Force_def, exp_rel_def] >>
          qpat_x_assum ‘exp_rel _ (SND _)’ mp_tac >> IF_CASES_TAC >>
          gvs [exp_rel_def, ok_bind_def, PULL_EXISTS]))
QED

Theorem rel_uses_Letrecs_exp_rel:
  ∀xs x. EVERY ok_bind (MAP SND xs) ⇒ rel_uses_Letrecs exp_rel xs x
Proof
  rw [rel_uses_Letrecs_def] >>
  irule exp_rel_Letrec >>
  gvs [EVERY_EL, LIST_REL_EL_EQN, EL_MAP] >>
  rw [] >>
  rpt $ first_x_assum $ drule_then assume_tac >>
  rename1 ‘exp_rel x2 y2’ >>
  Cases_on ‘x2’ >> gvs [ok_bind_def, exp_rel_def]
QED

Theorem NRC_exp_rel_Letrec:
  ∀vL f x.
    EVERY no_value (MAP SND f) ∧ no_value x ∧
    EVERY ok_bind (MAP SND f) ∧
    EVERY (λ(v1,v2). MEM v2 (MAP FST f) ∧ MEM (v1,Delay (Var v2)) f ∧
                     EVERY (λe. v2 ∉ boundvars e) (MAP SND f) ∧ v2 ∉ boundvars x ∧
                     v1 ≠ v2) vL ∧
    ALL_DISTINCT (MAP FST f)
    ⇒ NRC exp_rel (LENGTH vL)
          (Letrec f x)
          (Letrec (FOLDL (λl (v1, v2). MAP (λ(v, e). (v, replace_Force (Var v2) v1 e)) l) f vL)
                  (FOLDL (λe (v1, v2). replace_Force (Var v2) v1 e) x vL))
Proof
  Induct >> gvs [NRC] >>
  PairCases >> rw [] >>
  last_x_assum $ irule_at Any >>
  irule_at Any exp_rel_Letrec_Delay_Var >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM, exp_rel_refl, LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >>
  rw []
  >- (pairarg_tac >> gs [] >> irule no_value_replace_Force >>
      last_x_assum $ dxrule_then assume_tac >>
      gvs [no_value_def])
  >- (irule no_value_replace_Force >> gvs [no_value_def])
  >- (pairarg_tac >>
      rpt $ last_x_assum $ drule_then assume_tac >> gs [] >>
      rename1 ‘ok_bind (replace_Force _ _ e)’ >>
      Cases_on ‘e’ >> gs [ok_bind_def, replace_Force_def] >>
      rw [ok_bind_def])
  >- (first_x_assum $ dxrule_then assume_tac >>
      pairarg_tac >> gs [] >> rw []
      >- (rw [MEM_MAP] >>
          first_x_assum $ irule_at Any >>
          gvs [replace_Force_def])
      >- (first_x_assum $ dxrule_then assume_tac >>
          pairarg_tac >> gvs [] >>
          strip_tac >>
          assume_tac boundvars_replace_Force >>
          gs [SUBSET_DEF] >>
          first_x_assum $ dxrule_then assume_tac >>
          gvs [boundvars_def])
      >- (strip_tac >>
          assume_tac boundvars_replace_Force >>
          gs [SUBSET_DEF] >>
          first_x_assum $ dxrule_then assume_tac >>
          gvs [boundvars_def]))
QED

Theorem NRC_exp_rel_Delay_Var:
  ∀n y v. NRC exp_rel n (Delay (Var v)) y ⇒ y = Delay (Var v)
Proof
  Induct >> gvs [NRC, exp_rel_def]
QED

Theorem NRC_exp_rel_replace_Force:
  ∀n x y v1 v2. NRC exp_rel n x y ∧
                v2 ∉ boundvars x ⇒
                NRC exp_rel n (replace_Force (Var v2) v1 x) (replace_Force (Var v2) v1 y)
Proof
  Induct >> rw [NRC] >>
  last_x_assum $ irule_at Any >>
  irule_at Any exp_rel_replace_Force >>
  rpt $ first_assum $ irule_at $ Pos hd >>
  dxrule_then assume_tac exp_rel_boundvars >>
  gvs []
QED

Theorem full_exp_rel_NRC_exp_rel:
  ∀x y. full_exp_rel x y ⇒ no_value x ∧ ∃n. NRC exp_rel n x y
Proof
  ho_match_mp_tac full_exp_rel_ind >> rw []
  >~[‘no_value (Var v)’] >- gvs [no_value_def]
  >~[‘no_value (Prim op xs)’]
  >- gvs [no_value_def, LIST_REL_CONJ, LIST_REL_EL_EQN, EL_MAP, EVERY_EL]
  >~[‘no_value (App f x)’] >- gvs [no_value_def]
  >~[‘no_value (Force x)’] >- gvs [no_value_def]
  >>~[‘no_value (Letrec f x)’]
  >- gvs [no_value_def, LIST_REL_CONJ, LIST_REL_EL_EQN, EL_MAP, EVERY_EL]
  >- gvs [no_value_def, LIST_REL_CONJ, LIST_REL_EL_EQN, EL_MAP, EVERY_EL]
  >~[‘no_value (Lam s x)’] >- gvs [no_value_def]
  >~[‘no_value (MkTick x)’] >- gvs [no_value_def]
  >~[‘no_value (Delay x)’] >- gvs [no_value_def]
  >~[‘no_value (Let (SOME _) x (Let (SOME _) _ y))’] >- gvs [no_value_def]
  >~[‘no_value (Let opt x y)’] >- gvs [no_value_def]
  >~[‘no_value (If x y z)’] >- gvs [no_value_def]
  >~[‘no_value (Box x)’] >- gvs [no_value_def]
  >~[‘Var _’]
  >- (qexists_tac ‘0’ >> gvs [exp_rel_Var, NRC])
  >~[‘App _ _’]
  >- (irule_at Any NRC_rel_App_MAX >>
      gvs [exp_rel_App, exp_rel_refl] >>
      metis_tac [])
  >~[‘Prim _ _’]
  >- (gvs [LIST_REL_CONJ] >>
      irule_at Any NRC_rel_Prim >>
      gvs [exp_rel_Prim] >>
      irule_at Any LIST_REL_NRC_MAX_1 >>
      gvs [LIST_REL_EL_EQN, EL_MAP, exp_rel_refl])
  >~[‘Lam _ _’]
  >- (irule_at Any NRC_rel_Lam >>
      gvs [exp_rel_Lam] >>
      first_x_assum $ irule_at Any)
  >~[‘Letrec _ (FOLDL _ _ _)’]
  >- (Q.REFINE_EXISTS_TAC ‘n1 + n2’ >>
      gvs [NRC_ADD_EQN, LIST_REL_CONJ] >>
      irule_at (Pos last) NRC_exp_rel_Letrec >> gvs [] >>
      drule_then (drule_then $ irule_at Any) no_value_NRC_exp_rel >>
      gs [GSYM PULL_EXISTS] >>
      conj_tac
      >- (gvs [EVERY_EL, LIST_REL_EL_EQN] >> rw [] >>
          first_x_assum $ drule_then assume_tac >>
          first_x_assum $ dxrule_then assume_tac >>
          irule no_value_NRC_exp_rel >>
          rpt $ first_x_assum $ irule_at Any) >>
      conj_tac
      >- (gvs [EVERY_EL] >> rw [] >>
          first_x_assum $ dxrule_then assume_tac >>
          pairarg_tac >> gvs [] >>
          gvs [MEM_EL, EL_MAP] >>
          rename1 ‘(v1, Delay (Var _)) = EL n2 f’ >>
          qexists_tac ‘n2’ >>
          gs [LIST_REL_EL_EQN, EL_MAP] >>
          rpt $ first_x_assum $ qspecl_then [‘n2’] assume_tac >> gs [SND_THM] >>
          pairarg_tac >> gs [] >> pairarg_tac >> gs [] >>
          ‘EL n2 (MAP FST f) = EL n2 (MAP FST g)’ by gs [] >> gvs [EL_MAP] >>
          drule_then irule $ GSYM NRC_exp_rel_Delay_Var) >>
      qspecl_then [‘f’, ‘x’] assume_tac rel_uses_Letrecs_exp_rel >> gs [] >>
      assume_tac rel_uses_Letrecs_exp_rel_trans >>
      dxrule_then (dxrule_then $ dxrule_then $ dxrule_then irule) NRC_rel_Letrec_MAX >>
      gvs [LIST_REL_EL_EQN, exp_rel_refl])
  >~[‘Letrec _ _’]
  >- (irule NRC_rel_Letrec_MAX >>
      gvs [LIST_REL_CONJ, LIST_REL_EL_EQN, exp_rel_refl] >> rw []
      >- drule_all_then irule rel_uses_Letrecs_exp_rel_trans
      >- gvs [rel_uses_Letrecs_exp_rel]
      >- first_x_assum $ irule_at Any)
  >~[‘Let _ _ (Let _ _ _)’]
  >- (Q.REFINE_EXISTS_TAC ‘SUC number’ >> gvs [NRC] >>
      irule_at Any exp_rel_Let_Delay_Var >>
      rpt $ irule_at Any exp_rel_refl >>
      gvs [] >>
      rpt $ irule_at Any NRC_rel_Let_MAX >>
      rpt $ irule_at Any NRC_refl >>
      gvs [exp_rel_Delay, exp_rel_Var, exp_rel_Let, exp_rel_refl] >>
      irule_at Any exp_rel_Let >>
      gvs [exp_rel_def] >>
      irule_at Any NRC_exp_rel_replace_Force >>
      irule_at Any exp_rel_replace_Force >>
      gvs [exp_rel_refl] >>
      rpt $ first_x_assum $ irule_at Any)
  >~[‘Let _ _ _’]
  >- (irule_at Any NRC_rel_Let_MAX >>
      gvs [exp_rel_Let, exp_rel_refl] >>
      rpt $ first_x_assum $ irule_at Any)
  >~[‘If _ _ _’]
  >- (irule_at Any NRC_rel_If_MAX >>
      gvs [exp_rel_If, exp_rel_refl] >>
      rpt $ first_x_assum $ irule_at Any)
  >~[‘Delay _’]
  >- (irule_at Any NRC_rel_Delay >>
      gvs [exp_rel_Delay, exp_rel_refl] >>
      first_x_assum $ irule_at Any)
  >~[‘Box _’]
  >- (irule_at Any NRC_rel_Box >>
      gvs [exp_rel_Box, exp_rel_refl] >>
      first_x_assum $ irule_at Any)
  >~[‘Force _’]
  >- (irule_at Any NRC_rel_Force >>
      gvs [exp_rel_Force, exp_rel_refl] >>
      first_x_assum $ irule_at Any)
  >~[‘MkTick _’]
  >- (irule_at Any NRC_rel_MkTick >>
      gvs [exp_rel_MkTick, exp_rel_refl] >>
      first_x_assum $ irule_at Any)
QED

Theorem full_delay_lam_semantics:
  full_exp_rel x y ∧
  closed x ⇒
    semantics x Done [] = semantics y Done []
Proof
  rw [] >>
  irule $ GEN_ALL NRC_semantics_full >> fs [] >>
  first_x_assum $ irule_at Any >>
  qexists_tac ‘exp_rel’ >>
  gvs [delay_lam_semantics, full_exp_rel_NRC_exp_rel, closed_def] >>
  rw [] >>
  metis_tac [exp_rel_freevars]
QED

(*
Let v1 = Delay (Lam s e1) in e2 -> Let v2 = Lam s e1 in Let v1 = Delay (Var v2) in e2

Let v2 = Lam s e1 in Let v1 = Delay (Var v2) in e2 ->
Let v2 = _ in Let v1 = _ in replace_Force (Var v2) v1 e2

let v1 = Lam s (Let (SOME s2) (Force s) e)
let v2 = Lam s2 e in Let v1 = Lam s (App v2 (Force s))

*)

val _ = export_theory ();
