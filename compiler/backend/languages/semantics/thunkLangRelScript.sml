open HolKernel Parse BasicProvers boolLib bossLib listTheory;
open thunkLangTheory thunkLang_primitivesTheory 
     thunkLangRel_primitivesTheory thunkLangRel_semanticsTheory;

val _ = new_theory "thunkLangRel";
val _ = numLib.prefer_num ();

Type inv = ``:state -> state -> bool``;
Type sigma = ``:(string # v) list``;

Definition rel_def:
  (val_rel (k : fuel) (Q : inv) (Constructor n vs) (Constructor n' vs') ⇔
    n = n'
    ∧ LIST_REL (val_rel k Q) vs vs') ∧
  (val_rel k Q (Monadic op es) (Monadic op' es') ⇔
    op = op'
    ∧ ∀i. i < k
      ⇒ LIST_REL (exp_rel i (Q, Q)) es es') ∧
  (val_rel k Q (Closure x e) (Closure x' e') ⇔
    ∀i v1 v2.
      i < k
      ⇒ val_rel i Q v1 v2
      ⇒ exp_rel i (Q, Q) (subst1 x v1 e) (subst1 x' v2 e')) ∧
  (val_rel k Q (Recclosure fs n) (Recclosure fs' n') ⇔
    ∀i e.
      i < k
      ⇒ ALOOKUP (REVERSE fs) n = SOME e
      ⇒ ∃e'. ALOOKUP (REVERSE fs') n' = SOME e'
        ∧ exp_rel i (Q, Q) (subst_funs fs e) (subst_funs fs' e')) ∧
  (val_rel k Q (Thunk e) (Thunk e') ⇔
    ∀i. i < k ⇒ exp_rel i (Q, Q) e e') ∧
  (val_rel k Q (Atom l) (Atom l') ⇔ l = l') ∧
  (val_rel k Q (DoTick v) (DoTick v') ⇔ val_rel k Q v v') ∧
  (val_rel k Q v1 v2 ⇔ F) ∧

  (res_rel (k : fuel) (Q : inv) OOT OOT ⇔ T) ∧
  (res_rel k Q Fail Fail ⇔ T) ∧
  (res_rel k Q (Ok v) (Ok v') ⇔ val_rel k Q v v') ∧
  (res_rel k Q r1 r2 ⇔ F) ∧

  (exp_rel (k : fuel) ((QL, QG) : inv # inv) (e1 : exp) (e2 : exp) ⇔
    ∀c1 t1 r1 s1.
      c1 ≤ k
      ⇒ eval_to' (state c1 t1) e1 = (r1, s1)
      ⇒ (∃c2 t2 r2 s2.
          eval_to' (state c2 t2) e2 = (r2, s2)
          ∧ QL (state c1 t1) (state c2 t2)
          ∧ res_rel (k - c1) QG r1 r2))
(*  (exp_rel (k : fuel) ((QL, QG) : inv # inv) (e1 : exp) (e2 : exp) ⇔
    ∀c1 t1 r1.
      c1 ≤ k
      ⇒ FST (eval_to' (state c1 t1) e1) = r1
      ⇒ (∃c2 t2 r2.
          FST (eval_to' (state c2 t2) e2) = r2
          ∧ QL (state c1 t1) (state c2 t2)
          ∧ res_rel (k - c1) QG r1 r2))*)
Termination
  WF_REL_TAC `inv_image ($< LEX $< LEX $<) (λx.
                case x of
                | INL (k, q, v1, v2) => (k, 0, v_size v1)
                | INR (INL (k, q, r1, r2)) => (k, 1, res_size v_size r1)
                | INR (INR (k, (ql, qg), e1, e2)) => (k, 2, exp_size e1))`
End

Definition var_rel_def:
  var_rel (k : fuel) (Q : inv) (sub1 : sigma) (sub2 : sigma)
          (x : string) (y : string) ⇔
    ∀v1. ALOOKUP sub1 x = SOME v1
         ⇒ ∃v2. ALOOKUP sub2 y = SOME v2
                ∧ val_rel k Q v1 v2
End

Definition subst_rel_def:
  subst_rel (k : fuel) (Q : inv) (S : string set)
            (sub1 : sigma) (sub2 : sigma) ⇔
    ∀x. x ∈ S ⇒ var_rel k Q sub1 sub2 x x
End

Definition top_rel_def:
  top_rel ((QL, QG) : inv # inv) (e1 : exp) (e2 : exp) ⇔
    ∀k sub1 sub2.
      subst_rel k QG (freevars e1) sub1 sub2
      ⇒ (freevars e1) ⊆ (set (MAP FST sub1))
      ⇒ exp_rel k (QL, QG) (subst sub1 e1) (subst sub2 e2)
End

Theorem rel_monotonic:
  (∀k Q v1 v2 j.
    val_rel k Q v1 v2
    ⇒ j ≤ k
    ⇒ val_rel j Q v1 v2) ∧
  (∀k Q r1 r2 j.
    res_rel k Q r1 r2
    ⇒ j ≤ k
    ⇒ res_rel j Q r1 r2) ∧
  (∀k Qs e1 e2 j.
    exp_rel k Qs e1 e2
    ⇒ j ≤ k
    ⇒ exp_rel j Qs e1 e2)
Proof
  ho_match_mp_tac rel_ind
  >> rw [rel_def]
  >- cheat
  >- (first_x_assum $ qspecl_then [`i`, `v1`, `v2`] assume_tac >> gvs [])
  >- (first_x_assum $ qspecl_then [`c1`, `t1`, `r1`, `s1`] assume_tac >> gvs []
      >> first_x_assum $ qspecl_then [`c1`, `t1`, `r1`, `s1`, `r2`] assume_tac >> gvs []
      >> qexistsl [`c2`, `t2`, `r2`, `s2`] >> gvs [])
QED

Theorem eval_to'_sub_thm:
  ∀s sm e s'.
    eval_to' s e = (OOT, s')
    ⇒ eval_to' (s - sm) e = (OOT, s' - sm)
Proof
  cheat
QED

Theorem OOT_thm:
  ∀t e r s'.
    eval_to' (state 0 t) e = (OOT, s')
Proof
  cheat
QED

Theorem constr_compat_thm:
  ∀(k : fuel) (QL : inv) (QG : inv)
   (*TODO ys1 ys2 values*)
   (ys1 : string list) (ys2 : string list)
   (x1 : string) (x2 : string) (sub1 : sigma)
   (sub2 : sigma) (C : string)
   (e1 : exp) (e2 : exp).
    QL (state 0 0) (state 0 0)
    ∧ (∀c1 t1 c2 t2.
        QL (state c1 t1) (state c2 t2) 
        ⇒ QL (state (c1 + 1) t1) (state (c2 + 1) t2))
    ∧ (LIST_REL (var_rel k QG sub1 sub2) ys1 ys2)
    ∧ (∀vs1 vs2.
        LIST_REL (val_rel k QG) vs1 vs2
        ⇒ exp_rel k (QL, QG) (subst1 x1 (Constructor C vs1) e1)
                             (subst1 x2 (Constructor C vs2) e2))
    ⇒ exp_rel k (QL, QG)
        (Let (SOME x1) (Value $ Constructor C []) e1)
        (Let (SOME x2) (Value $ Constructor C []) e2)
Proof
  rw [rel_def]
  >> first_x_assum $ qspecl_then [`[]`, `[]`] assume_tac >> gvs []
  >> qrefinel [`c2 + 2`, `t2`]
  >> gvs [AllCaseEqs(), eval_to'_def, check_state_def, fuel_def, trace_def]
  >- (first_x_assum $ qspecl_then [`0`, `t1`, `OOT`, `s1`] assume_tac >> gvs []
      >> qspecl_then [`t1`, `subst1 x1 (Constructor C []) e1`, `s1`] assume_tac OOT_thm
      >> gvs []
      >> Cases_on `r2` >> gvs [rel_def]
      >> qrefinel [`c2`, `t2`, `OOT`, `s2`] >> gvs [rel_def]
      >> cheat)
  >- (`c1 = 1` by gvs [] >> gvs []
      >> first_x_assum $ qspecl_then [`0`, `t1`, `OOT`, `s1`] assume_tac >> gvs []
      >> qspecl_then [`t1`, `subst1 x1 (Constructor C []) e1`, `s1`] assume_tac OOT_thm
      >> gvs []
      >> Cases_on `r2` >> gvs [rel_def]
      >> qexistsl [`c2`, `t2`, `OOT`, `s2`] >> gvs [rel_def]
      >> cheat)
  >- (first_x_assum $ qspecl_then [`c1 - 2`, `t1`, `r1`, `s1`] assume_tac >> gvs []
      >> qexistsl [`c2`, `t2`, `r2`, `s2`] >> gvs [rel_def]
      >> imp_res_tac rel_monotonic >> gvs []
      >> cheat)
QED

Theorem app_compat_thm:
  ∀(k : fuel) (QL : inv) (QG : inv)
   (f1 : exp) (f2 : exp) (x1 : exp) (x2 : exp).
   exp_rel k (QL, QG) f1 f2
   ∧ exp_rel k (QL, QG) x1 x2
   ⇒ exp_rel k (QL, QG) (App f1 x1) (App f2 x2)
Proof
  cheat
  (*rw [rel_def]
  >> gvs [eval_to'_def, check_state_def, fuel_def, trace_def]
  >> Cases_on `c1 = 0 ∨ t1 = 0` >> gvs []
  >- (qexistsl [`0`, `t1`, `OOT`] >> gvs [rel_def]
      >> cheat)
  >- (qexistsl [`c1`, `0`, `OOT`] >> gvs [rel_def]
      >> cheat)
  >- (Cases_on `eval_to' (state (c1 − 1) (t1 − 1)) x1` >> gvs []
      >> Cases_on `q` >> gvs []
      >- (
          Cases_on `eval_to' r f1` >> gvs []
          >> Cases_on `q` >> gvs []
          >- cheat
          >- (first_x_assum $ qspecl_then [`c1-1`,`t1-1`,`Ok a`,`r`] assume_tac >> gvs []
              >> Cases_on `r2` >> gvs [rel_def]
              >> first_x_assum $ qspecl_then [`r.c`,`r.t`,`Fail`,`r'`] assume_tac >> gvs []
              >> `r.c ≤ k` by cheat >> gvs []
              >> `state r.c r.t = r` by cheat >> gvs []
              >> Cases_on `r2` >> gvs [rel_def]
              >> qexistsl [`c2 + c2' + 1`, `t2 + t2' + 1`, `Fail`] >> gvs [rel_def]
              >> qspecl_then [`state c2 t2`, `state c2' t2'`, `x2`] assume_tac (cj 1 eval_to'_add_thm) >> gvs []
              >> qspecl_then [`state c2' t2'`, `s2`, `f2`] assume_tac (cj 1 eval_to'_add_thm) >> gvs []
              >> cheat)
          >- (last_x_assum $ qspecl_then [`r.c`,`r.t`,`OOT`,`r'`] assume_tac >> gvs []
              >> `r.c ≤ k` by cheat >> gvs []
              >> `state r.c r.t = r` by cheat >> gvs []
              >> Cases_on `r2` >> gvs [rel_def]
              >> first_x_assum $ qspecl_then [`c1-1+c2`,`t1-1+t2`,`Ok a`,`r`] assume_tac >> gvs []
              >> first_x_assum $ qspecl_then [`c1-1`,`t1-1`,`Ok a`,`r`] assume_tac >> gvs []
              >> Cases_on `r2` >> gvs [rel_def]
              >> qexistsl [`c2 + c2' + 1`, `t2 + t2' + 1`, `OOT`] >> gvs [rel_def]
              >> qspecl_then [`state c2 t2`, `state c2' t2'`, `x2`] assume_tac (cj 1 eval_to'_add_thm) >> gvs []
             )
         )
      >- (first_x_assum $ qspecl_then [`c1-1`,`t1-1`,`Fail`,`r`] assume_tac >> gvs []
          >> Cases_on `r2` >> gvs [rel_def]
          >> qexistsl [`c2 + 1`, `t2 + 1`, `Fail`] >> gvs [rel_def]
          >> cheat)
      >- (first_x_assum $ qspecl_then [`c1-1`,`t1-1`,`OOT`,`r`] assume_tac >> gvs []
          >> Cases_on `r2` >> gvs [rel_def]
          >> qexistsl [`c2 + 1`, `t2 + 1`, `OOT`] >> gvs [rel_def]
          >> cheat))*)
QED

val _ = export_theory()
