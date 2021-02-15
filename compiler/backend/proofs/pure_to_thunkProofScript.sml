(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)
open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     pure_evalTheory;

val _ = new_theory "pure_to_thunkProof";

(* TODO: Move to pure_to_thunk

   Some variables point to computations that have been
   suspended by a lambda on the thunkLang side. These variables
   need to be forced, and are thus tagged with ‘Suspended’.
 *)

Datatype:
  vmode = Raw | Suspended
End

Inductive exp_rel:
[exp_rel_Var_Suspended:]
  (∀ctxt n.
     ALOOKUP ctxt n = SOME Suspended ⇒
       exp_rel ctxt (Var n) (Force (Var n))) ∧
[exp_rel_Var_Raw:]
  (∀ctxt n.
     ALOOKUP ctxt n = SOME Raw ⇒
       exp_rel ctxt (Var n) (Var n)) ∧
[exp_rel_Lam:]
  (∀ctxt s (x: pure_exp$exp) (x': thunkLang_subst$exp).
     exp_rel ((s, Raw)::ctxt) x x' ⇒
       exp_rel ctxt (Lam s x) (Lam s x')) ∧
[exp_rel_App:]
  (∀ctxt x x' y y' s.
     exp_rel ctxt x x' ∧
     exp_rel ctxt y y' ∧
     s ∈ freevars y ⇒
       exp_rel ctxt (App x y) (App x' (Delay T (Lam s y')))) ∧
[exp_rel_If:]
  (∀ctxt xs x y z.
     LENGTH xs = 3 ∧
     exp_rel ctxt (EL 0 xs) x ∧
     exp_rel ctxt (EL 1 xs) y ∧
     exp_rel ctxt (EL 2 xs) z ⇒
       exp_rel ctxt (Prim If xs) (If x y z)) ∧
[exp_rel_Prim:]
  (∀ctxt op xs xs'.
     op ≠ If ∧
     LIST_REL (exp_rel ctxt) xs xs' ⇒
       exp_rel ctxt (Prim op xs) (Prim op xs')) ∧
[exp_rel_Letrec:]
  (∀ctxt f f' x x'.
     exp_rel ctxt (Letrec f x) (Letrec f' x'))
     (* FIXME This bit will involve more context-fiddling *)
End

(*
TypeBase.case_def_of “:pure_exp$exp”
|> CONJUNCTS
|> map (rand o funpow 5 rator o rand o rator o concl o SPEC_ALL)
|> map (fn t => SIMP_CONV (srw_ss()) [Once exp_rel_cases] “exp_rel ctxt ^t y”)
 *)

Theorem exp_rel_def[local]:
  (∀n.
     exp_rel ctxt (Var n) y ⇔
       (ALOOKUP ctxt n = SOME Suspended ∧
        y = Force (Var n)) ∨
       (ALOOKUP ctxt n = SOME Raw ∧
        y = Var n)) ∧
  (∀s x.
     exp_rel ctxt (Lam s x) y ⇔
       ∃z. y = Lam s z ∧
           exp_rel ((s, Raw)::ctxt) x z) ∧
  (∀op xs.
     exp_rel ctxt (Prim op xs) y ⇔
       (∃x1 x2 x3.
          y = If x1 x2 x3 ∧
          op = If ∧
          LENGTH xs = 3 ∧
          exp_rel ctxt (EL 0 xs) x1 ∧
          exp_rel ctxt (EL 1 xs) x2 ∧
          exp_rel ctxt (EL 2 xs) x3) ∨
       (∃xs'.
          y = Prim op xs' ∧
          op ≠ If ∧
          LIST_REL (exp_rel ctxt) xs xs')) ∧
  (∀f x.
     exp_rel ctxt (App f x) y ⇔
       ∃g z s.
         y = App g (Delay T (Lam s z)) ∧
         s ∈ freevars x ∧
         exp_rel ctxt f g ∧
         exp_rel ctxt x z)
Proof
  rw []
  \\ simp [Once exp_rel_cases]
  \\ eq_tac
  \\ rw [] \\ gs []
QED

Inductive thunk_rel:
  (∀ctxt x s y.
     exp_rel ctxt x y ⇒
       thunk_rel ctxt x (Thunk T (Closure s y))) ∧
  (∀ctxt x k y v.
    exp_rel ctxt x y ∧
    eval_to k y = INR v ⇒
      thunk_rel ctxt x (Thunk F v))
End

Theorem thunk_rel_def[local]:
  thunk_rel ctxt x (Thunk T e) =
    (∃s y.
       e = Closure s y ∧
       exp_rel ctxt x y) ∧
  thunk_rel ctxt x (Thunk F v) =
    (∃k y.
       exp_rel ctxt x y ∧
       eval_to k y = INR v)
Proof
  rw [] \\ simp [Once thunk_rel_cases]
QED

Definition v_rel_def:
  v_rel ctxt wh_Error (INL Type_error) = T ∧
  v_rel ctxt wh_Diverge (INL Diverge) = T ∧
  v_rel ctxt (wh_Closure s x) (INR (Closure t y)) =
    (s = t ∧ exp_rel ((s, Raw)::ctxt) x y) ∧
  v_rel ctxt (wh_Constructor s xs) (INR (Constructor t ys)) =
    (s = t ∧ LIST_REL (thunk_rel ctxt) xs ys) ∧
  v_rel ctxt _ _ = F
End

Theorem v_rel_rev[local]:
  v_rel ctxt x (INL Type_error) = (x = wh_Error) ∧
  v_rel ctxt x (INL Diverge) = (x = wh_Diverge) ∧
  v_rel ctxt x (INR (Closure s y)) =
    (∃b.
       x = wh_Closure s b ∧
       exp_rel ((s, Raw)::ctxt) b y) ∧
  v_rel ctxt x (INR (Constructor s ys)) =
    (∃xs.
       x = wh_Constructor s xs ∧
       LIST_REL (thunk_rel ctxt) xs ys)
Proof
  Cases_on ‘x’ \\ rw [v_rel_def, EQ_IMP_THM] \\ fs []
QED

(* Hmm
Theorem exp_rel_bind:
  exp_rel ctxt x y ∧
  thunk_rel ctxt z w ⇒
    exp_rel ctxt (bind s z x) (bind1 s w y)
Proof
  cheat
QED
 *)

Theorem exp_rel_eval_to:
  ∀k x res y ctxt.
    eval_wh_to k x = res ∧
    res ≠ wh_Error ∧
    exp_rel ctxt x y ⇒
      v_rel ctxt res (eval_to k y)
Proof
  ho_match_mp_tac eval_wh_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Var *)
    rw [eval_wh_to_def, eval_to_def])
  >- ((* Lam *)
    rw [eval_wh_to_def, exp_rel_def]
    \\ simp [eval_to_def, v_rel_def])
  >- ((* App *)
    strip_tac
    \\ rpt gen_tac
    \\ simp [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >- ((* pure sem diverges *)
      rw [exp_rel_def]
      \\ simp [eval_to_def]
      \\ IF_CASES_TAC \\ fs [v_rel_def]
      \\ ‘∃r. eval_to (k - 1) g = r’ by fs []
      \\ first_x_assum (drule_then assume_tac)
      \\ ‘eval_to k g = INL Diverge’
        by (Cases_on ‘eval_to k g’ \\ fs [v_rel_def]
            \\ rename1 ‘err = Diverge’
            \\ Cases_on ‘err’ \\ fs [v_rel_def])
      \\ ‘eval_to (k - 1) g = INL Diverge’ suffices_by rw [v_rel_def]
      \\ CCONTR_TAC
      \\ ‘k - 1 < k’ by fs []
      \\ drule_all_then assume_tac eval_to_subst_mono \\ gs [])
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x)’ \\ csimp []
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >- ((* pure sem diverges *)
      strip_tac
      \\ fs [exp_rel_def, eval_to_def, v_rel_def])
    \\ strip_tac
    \\ ‘eval_wh_to k x ≠ wh_Error’ by (strip_tac \\ fs [])
    \\ gvs [exp_rel_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ simp [eval_to_def]
    \\ Cases_on ‘eval_to (k - 1) g’ \\ fs []
    >- ((* thunk sem errors *)
      rename1 ‘INL err’
      \\ Cases_on ‘err’ \\ gs [v_rel_rev]
      >- ((* more errors *)
        ‘eval_to (k - 1) g ≠ INL Diverge’ by fs []
        \\ ‘k - 1 < k’ by fs []
        \\ drule_all_then assume_tac eval_to_subst_mono
        \\ gs [v_rel_rev])
      \\ cheat (* TODO mismatch between the two sides *))
    \\ cheat (* TODO *))
  >- ((* Letrec *)
    cheat (* TODO Not done *))
  >- ((* Prim *)
    cheat (* TODO Do later *))
QED

val _ = export_theory ();

