open HolKernel Parse boolLib bossLib listTheory;
open thunkLangTheory;

val _ = new_theory "thunkLangRel2";
val _ = numLib.prefer_num ();

Datatype:
  res = Ok 'a
      | OOT
End

Definition isok_def:
  (isok (Ok _) = T) ∧
  (isok _ = F)
End

Definition isoot_def:
  (isoot OOT = T) ∧
  (isoot _ = F)
End

Definition resok_def:
  resok (Ok v) = v
End

Type fuel = ``:num``;
Type trace = ``:num``;

Definition fuel_def:
  (fuel (e : exp) : fuel = 1)
End

Definition trace_def:
  (trace (App f x) : trace = 1) ∧
  (trace e = 0)
End

Definition dest_Closure'_def[simp]:
  (dest_Closure' (Closure s x) = SOME (s, x)) ∧
  (dest_Closure' _ = NONE)
End

Definition dest_Recclosure'_def[simp]:
  (dest_Recclosure' (Recclosure f n) = SOME (f, n)) ∧
  (dest_Recclosure' _ = NONE)
End

Definition dest_anyClosure'_def:
  dest_anyClosure' v =
    case dest_Closure' v of
    | SOME (s, x) => SOME (s, x, [])
    | NONE =>
        (case dest_Recclosure' v of
         | SOME (f, n) =>
            (case ALOOKUP (REVERSE f) n of
             | SOME (Lam s x) => SOME (s, x, MAP (λ(g, x). (g, Recclosure f g)) f)
             | _ => NONE)
         | NONE => NONE)
End

Definition dest_Thunk'_def[simp]:
  (dest_Thunk' (Thunk x) = SOME x) ∧
  (dest_Thunk' _ = NONE)
End

Definition dest_anyThunk'_def:
  dest_anyThunk' v =
    case dest_Thunk' v of
    | SOME w => SOME (w, [])
    | _ =>
        (case dest_Recclosure' v of
         | SOME (f, n) =>
            (case ALOOKUP (REVERSE f) n of
             | SOME (Delay x) => SOME (x, f)
             | _ => NONE)
         | NONE => NONE)
End

Definition dest_Constructor'_def[simp]:
  (dest_Constructor' (Constructor s vs) = SOME (s, vs)) ∧
  (dest_Constructor' _ = NONE)
End

Inductive bstep:
[bstep_value:]
  ∀(cin : fuel) (cout : trace) (v : v).
    bstep (Value v) cin (Ok v) cout
[bstep_app:]
  ∀(cin1 : fuel) (cin2 : fuel) (cout1 : trace) (cout2 : trace)
   (cin3 : fuel) (cout3 : trace) (x : exp) (f : exp) (xv : v) (fv : v)
   (n : vname) (body : exp) (binds : (vname # v) list) (r : v res).
    bstep_fuel x cin1 (Ok xv) cout1
    ∧ bstep_fuel f cin2 (Ok fv) cout2
    ∧ dest_anyClosure' fv = SOME (n, body, binds)
    ∧ bstep_fuel (subst (binds ++ [(n, xv)]) body) cin3 r cout3
    ⇒ bstep (App f x) (cin1 + cin2 + cin3) r (cout1 + cout2 + cout3)
[bstep_app_xOOT:]
  ∀(cin : fuel) (cout : fuel) (x : exp) (f : exp).
    bstep_fuel x cin OOT cout
    ⇒ bstep (App f x) cin OOT cout
[bstep_app_fOOT:]
  ∀(cin1 : fuel) (cout1 : trace) (cin2 : fuel) (cout2 : trace)
   (x : exp) (f : exp) (xv : v) (fv : v).
    bstep_fuel x cin1 (Ok xv) cout1
    ∧ bstep_fuel f cin2 OOT cout2
    ⇒ bstep (App f x) (cin1 + cin2) OOT (cout1 + cout2)
[bstep_lam:]
  ∀(cin : fuel) (cout : trace) (n : vname) (x : exp).
    bstep (Lam n x) cin (Ok (Closure n x)) cout
[bstep_let_NONE:]
  ∀(cin1 : fuel) (cout1 : trace) (cin2 : fuel) (cout2 : trace)
   (xv : v) (r : v res) (e1 : exp) (e2 : exp).
    bstep_fuel e1 cin1 (Ok xv) cout1
    ∧ bstep_fuel e2 cin2 r cout2 
    ⇒ bstep (Let NONE e1 e2) (cin1 + cin2) r (cout1 + cout2)
[bstep_let_NONE_OOT:]
  ∀(cin : fuel) (cout : trace) (e1 : exp) (e2 : exp).
    bstep_fuel e1 cin OOT cout
    ⇒ bstep (Let NONE e1 e2) cin OOT cout
[bstep_let_SOME:]
  ∀(cin1 : fuel) (cout1 : trace) (cin2 : fuel) (cout2 : trace)
   (xv : v) (n : vname) (e1 : exp) (e2 : exp) (r : v res).
    bstep_fuel e1 cin1 (Ok xv) cout1
    ∧ bstep_fuel (subst1 n xv e2) cin2 r cout2
    ⇒ bstep (Let (SOME n) e1 e2) (cin1 + cin2) r (cout1 + cout2)
[bstep_let_SOME_OOT:]
  ∀(cin : fuel) (cout : fuel) (n : vname) (e1 : exp) (e2 : exp).
    bstep_fuel e1 cin OOT cout
    ⇒ bstep (Let (SOME n) e1 e2) cin OOT cout
[bstep_if_true:]
  ∀(cin1 : fuel) (cout1 : trace) (cin2 : fuel) (cout2 : trace)
   (r : v res) (e1 : exp) (e2 : exp) (e3 : exp).
    bstep_fuel e1 cin1 (Ok (Constructor "True" [])) cout1
    ∧ bstep_fuel e2 cin2 r cout2
    ⇒ bstep (If e1 e2 e3) (cin1 + cin2) r (cout1 + cout2)
[bstep_if_false:]
  ∀(cin1 : fuel) (cout1 : trace) (cin2 : fuel) (cout2 : trace)
   (r : v res) (e1 : exp) (e2 : exp) (e3 : exp).
    bstep_fuel e1 cin1 (Ok (Constructor "False" [])) cout1
    ∧ bstep_fuel e3 cin2 r cout2
    ⇒ bstep (If e1 e2 e3) (cin1 + cin2) r (cout1 + cout2)
[bstep_if_OOT:]
  ∀(cin : fuel) (cout : trace) (e1 : exp) (e2 : exp) (e3 : exp).
    bstep_fuel e1 cin OOT cout
    ⇒ bstep (If e1 e2 e3) cin OOT cout
[bstep_letrec:]
  ∀(cin : fuel) (cout : fuel) (r : v res)
   (fs : (vname # exp) list) (x : exp).
    bstep_fuel (subst_funs fs x) cin r cout
    ⇒ bstep (Letrec fs x) cin r cout
[bstep_delay:]
  ∀(cin : fuel) (cout : trace) (e : exp).
    bstep (Delay e) cin (Ok (Thunk e)) cout
[bstep_force:]
  ∀(cin1 : fuel) (cout1 : trace) (cin2 : fuel) (cout2 : trace)
   (v : v) (y : exp) (binds : (vname # exp) list) (r : v res) (e : exp).
    bstep_fuel e cin1 (Ok v) cout1
    ∧ dest_anyThunk' v = SOME (y, binds)
    ∧ bstep_fuel (subst_funs binds y) cin2 r cout2
    ⇒ bstep (Force e) (cin1 + cin2) r (cout1 + cout2)
[bstep_force_OOT:]
  ∀(cin : fuel) (cout : trace) (e : exp).
    bstep_fuel e cin OOT cout
    ⇒ bstep (Force e) cin OOT cout
[bstep_mktick:]
  ∀(cin : fuel) (cout : trace) (v : v) (e : exp).
    bstep_fuel e cin (Ok v) cout
    ⇒ bstep (MkTick e) cin (Ok (DoTick v)) cout
[bstep_mktick_OOT:]
  ∀(cin : fuel) (cout : trace) (v : v) (e : exp).
    bstep_fuel e cin OOT cout
    ⇒ bstep (MkTick e) cin OOT cout
[bstep_monad:]
  ∀(cin : fuel) (cout : trace) (mop : mop) (es : exp list).
    bstep (Monad mop es) cin (Ok (Monadic mop es)) cout
[bstepf_OOT:]
  ∀(c : fuel) (e : exp).
    c < fuel e
    ⇒ bstep_fuel e c OOT 0
[bstepf_run:]
  ∀(cin : fuel) (cout : trace) (e : exp) (r : v res).
    bstep e cin r cout
    ⇒ bstep_fuel e (cin + (fuel e)) r (cout + (trace e))
End

Theorem bstep_add_lemma:
  (∀e cin r cout.
    bstep e cin r cout
    ⇒ ∀v. r = Ok v ⇒ ∀cin'. bstep e (cin + cin') r cout) ∧
  (∀e cin r cout.
    bstep_fuel e cin r cout
    ⇒ ∀v. r = Ok v ⇒ ∀cin'. bstep_fuel e (cin + cin') r cout)
Proof
  ho_match_mp_tac bstep_ind >> rw []
  >- rw [bstep_value]
  >- (ntac 2 (last_x_assum $ qspec_then `0` assume_tac >> gvs [])
      >> last_x_assum $ qspec_then `cin'3'` assume_tac >> gvs []
      >> imp_res_tac bstep_app >> gvs [])
  >- rw [bstep_lam]
  >- (last_x_assum $ qspec_then `0` assume_tac >> gvs []
      >> last_x_assum $ qspec_then `cin''` assume_tac >> gvs []
      >> imp_res_tac bstep_let_NONE >> gvs [])
  >- (last_x_assum $ qspec_then `0` assume_tac >> gvs []
      >> last_x_assum $ qspec_then `cin''` assume_tac >> gvs []
      >> imp_res_tac bstep_let_SOME >> gvs [])
  >- (last_x_assum $ qspec_then `0` assume_tac >> gvs []
      >> last_x_assum $ qspec_then `cin''` assume_tac >> gvs []
      >> imp_res_tac bstep_if_true >> gvs [])
  >- (last_x_assum $ qspec_then `0` assume_tac >> gvs []
      >> last_x_assum $ qspec_then `cin''` assume_tac >> gvs []
      >> imp_res_tac bstep_if_false >> gvs [])
  >- rw [bstep_letrec]
  >- rw [bstep_delay]
  >- (last_x_assum $ qspec_then `0` assume_tac >> gvs []
      >> last_x_assum $ qspec_then `cin''` assume_tac >> gvs []
      >> imp_res_tac bstep_force >> gvs [])
  >- rw [bstep_mktick]
  >- rw [bstep_monad]
  >- (last_x_assum $ qspec_then `cin'` assume_tac >> gvs []
      >> imp_res_tac bstepf_run >> gvs [])
QED

Theorem bstep_add_thm:
  ∀e cin v cout.
    bstep_fuel e cin (Ok v) cout
    ⇒ ∀cin'. bstep_fuel e (cin + cin') (Ok v) cout
Proof
  rw [bstep_add_lemma]
QED

Type inv = ``:(fuel # trace) -> (fuel # trace) -> bool``;
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
  (res_rel k Q (Ok v) (Ok v') ⇔ val_rel k Q v v') ∧
  (res_rel k Q r1 r2 ⇔ F) ∧

  (exp_rel (k : fuel) ((QL, QG) : inv # inv) (e1 : exp) (e2 : exp) ⇔
    ∀c1 t1 r1.
      c1 ≤ k
      ⇒ bstep_fuel e1 c1 r1 t1
      ⇒ (∃c2 t2 r2.
          bstep_fuel e2 c2 r2 t2
          ∧ QL (c1, t1) (c2, t2)
          ∧ res_rel (k - c1) QG r1 r2))
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
  >- (first_x_assum $ qspecl_then [`c1`, `t1`, `r1`] assume_tac >> gvs []
      >> first_x_assum $ qspecl_then [`c1`, `r1`, `t1`, `r2`] assume_tac >> gvs []
      >> qexistsl [`c2`, `t2`, `r2`] >> gvs [])
QED

Theorem app_compat_thm:
  ∀k QL QG e1 e2 f1 f2.
    exp_rel k (QL, QG) e1 e2
    ∧ exp_rel k (QL, QG) f1 f2
    ⇒ exp_rel k (QL, QG) (App f1 e1) (App f2 e2)
Proof
  cheat
  (*rw [rel_def]
  >> qpat_x_assum `bstep_fuel _ _ _ _` mp_tac
  >> once_rewrite_tac [Once bstep_cases]
  >> rw [fuel_def, trace_def]
  >- (qexistsl [`0`, `0`, `OOT`] >> rw []
      >- rw [Once bstep_cases, fuel_def, trace_def]
      >- cheat
      >- rw [rel_def])
  >- (qpat_x_assum `bstep _ _ _ _` mp_tac
      >> once_rewrite_tac [Once bstep_cases]
      >> rw []
      >- (
          rw [Once bstep_cases, fuel_def, trace_def]
          >> qrefinel [`c2 + 1`, `t2 + 1`] >> rw []
          >> rw [Once bstep_cases]
          >> first_x_assum $ qspecl_then [`cin2`, `cout2`, `Ok fv`] assume_tac
          >> gvs []
          >> Cases_on `r2` >> gvs [rel_def]
          >> first_x_assum $ qspecl_then [`cin1`, `cout1`, `Ok xv`] assume_tac
          >> gvs []
          >> Cases_on `r2` >> gvs [rel_def]
          >> qexistsl [`cin1 + cin2 + cin3`, `cout1 + cout2 + cout3`, `r1`]
          >> rw []
          >- (
              disj1_tac
              >> qrefinel [`c2'`, `c2`, `t2'`, `t2`, `cin3`, `cout3`,
                           `a'`, `a`, `n`, `body`, `binds`]
              >> rw []
             )
          >- ()
          >- ()
         )
      >- (rw [Once bstep_cases, fuel_def, trace_def]
          >> qrefinel [`c2 + 1`, `t2 + 1`, `OOT`] >> rw []
          >> rw [Once bstep_cases]
          >> last_x_assum $ qspecl_then [`cin`, `cout`, `OOT`] assume_tac >> gvs []
          >> Cases_on `r2` >> gvs [rel_def]
          >> qexistsl [`c2`, `t2`] >> rw []
          >> cheat)
      >- (rw [Once bstep_cases, fuel_def, trace_def]
          >> qrefinel [`c2 + 1`, `t2 + 1`, `OOT`] >> rw []
          >> rw [Once bstep_cases]
          >> first_x_assum $ qspecl_then [`cin2`, `cout2`, `OOT`] assume_tac
          >> gvs []
          >> Cases_on `r2` >> gvs [rel_def]
          >> first_x_assum $ qspecl_then [`cin1`, `cout1`, `Ok xv`] assume_tac
          >> gvs []
          >> Cases_on `r2` >> gvs [rel_def]
          >> qexistsl [`c2 + c2'`, `t2 + t2'`] >> rw []
          >- (ntac 2 disj2_tac
              >> qexistsl [`c2'`, `t2'`, `c2`, `t2`, `a`]
              >> rw [])
          >- cheat))*)
QED

Theorem constr_compat_thm:
  ∀(k : fuel) (QL : inv) (QG : inv)
   (*TODO ys1 ys2 values*)
   (ys1 : string list) (ys2 : string list)
   (x1 : string) (x2 : string) (sub1 : sigma)
   (sub2 : sigma) (C : string)
   (e1 : exp) (e2 : exp).
    QL (0, 0) (0, 0)
    ∧ (∀c1 t1 c2 t2.
        QL (c1, t1) (c2, t2) 
        ⇒ QL ((c1 + 1), t1) ((c2 + 1), t2))
    ∧ (LIST_REL (var_rel k QG sub1 sub2) ys1 ys2)
    ∧ (∀m vs1 vs2.
        m < k
        ⇒ LIST_REL (val_rel m QG) vs1 vs2
        ⇒ exp_rel m (QL, QG) (subst1 x1 (Constructor C vs1) e1)
                             (subst1 x2 (Constructor C vs2) e2))
    ⇒ exp_rel k (QL, QG)
        (Let (SOME x1) (Value $ Constructor C []) e1)
        (Let (SOME x2) (Value $ Constructor C []) e2)
Proof
  cheat
  (*rw [rel_def]
  >> qpat_x_assum `bstep_fuel _ _ _ _` mp_tac
  >> once_rewrite_tac [Once bstep_cases]
  >> rw [fuel_def, trace_def]
  >- (qexistsl [`0`, `0`, `OOT`]
      >> gvs [rel_def]
      >> rw [Once bstep_cases, fuel_def])
  >- (qpat_x_assum `bstep _ _ _ _` mp_tac
      >> once_rewrite_tac [Once bstep_cases]
      >> rw []
      >- (`xv = Constructor C []` by
            (qpat_x_assum `bstep_fuel _ _ (Ok _) _` mp_tac
             >> once_rewrite_tac [Once bstep_cases]
             >> rw [fuel_def, trace_def]
             >> qpat_x_assum `bstep _ _ (Ok _) _` mp_tac
             >> once_rewrite_tac [Once bstep_cases]
             >> rw [] >> gvs [])
          >> first_x_assum $ qspecl_then [`k - 1`, `[]`, `[]`] assume_tac
          >> gvs []
          >> first_x_assum $ qspecl_then [`cin2`, `cout2`, `r1`] assume_tac
          >> gvs []
          >> qexistsl [`c2 + cin1 + 1`, `t2 + cout1`, `r2`]
          >> rw []
          >- (rw [Once bstep_cases, fuel_def, trace_def]
              >> qexists `c2 + cin1` >> rw []
              >> rw [Once bstep_cases]
              >> disj1_tac
              >> qrefinel [`_`, `_`, `c2`, `t2`, `Constructor C []`]
              >> rw [])
          >- cheat
          >- (imp_res_tac rel_monotonic >> gvs []))
      >- (qpat_x_assum `bstep_fuel _ _ OOT _` mp_tac
          >> once_rewrite_tac [Once bstep_cases]
          >> rw [fuel_def, trace_def]
          >> qspecl_then [`cin`, `t1`, `Constructor C []`] assume_tac bstep_value
          >> gvs []
         )

      >- (qpat_x_assum `bstep_fuel _ _ (Ok _) _` mp_tac
          >> once_rewrite_tac [Once bstep_cases]
          >> rw [fuel_def, trace_def]
          >> qpat_x_assum `bstep _ _ _ _` mp_tac
          >> once_rewrite_tac [Once bstep_cases]
          >> rw []
          >> first_x_assum $ qspec_then `k - 1` assume_tac
          >> gvs []
          >> first_x_assum $ qspecl_then [`[]`, `[]`] assume_tac
          >> gvs []
          >> first_x_assum $ qspecl_then [`cin2`, `cout2`, `r1`] assume_tac
          >> gvs []
          >> qexistsl [`c2 + cin + 2`, `t2 + cout1`, `r2`]
          >> rpt conj_tac
          >- (rw [Once bstep_cases]
              >> rw [fuel_def, trace_def]
              >> qexists `c2 + cin + 1` >> rw []
              >> rw [Once bstep_cases]
              >> rw []
              >> disj1_tac
              >> qrefinel [`_`, `_`, `c2`, `t2`, `Constructor C []`]
              >> rw []
              >> rw [Once bstep_cases]
              >> rw [fuel_def, trace_def]
              >> rw [bstep_value])
          >- cheat
          >- cheat)
      >- (
          first_x_assum $ qspecl_then [`k - 1`, `[]`, `[]`] assume_tac
          >> gvs []
          >> first_x_assum $ qspecl_then [`cin`, `t1`, `OOT`] assume_tac
          >> gvs []
         )


     )*)
QED

val _ = export_theory()
