(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)
open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     pure_evalTheory thunkLang_primitivesTheory;

val _ = new_theory "pure_to_thunkProof";

(* TODO: Move to pure_to_thunk

   Some variables point to computations that have been
   suspended by a lambda on the thunkLang side. These variables
   need to be forced, and are thus tagged with ‘Suspended’.
 *)

Datatype:
  vmode = Raw | Suspended
End

Definition suspend_def:
  suspend v x = Delay T (Lam v x)
End

(*
  NOTES ON COMPILING PURELANG TO THUNKLANG:

  thunkLang_subst-pureLang simulation.

  As pureLang is lazy it allows non-functional value declarations that are
  mutually recursive, and lazy value declarations. All such computations are
  suspended behind a “Delay T (Closure «fresh_var»  «defn»)” thunkLang-side.
  We keep track of which variables are suspended and which are not using a
  context.

  * [Var]
    - ‘Suspended’ variables are forced thunkLang-side.
    - ‘Raw’ variables are evaluated as-is.
  * [Lam]
    - Lambdas are already lazy. The bound variable is treated as ‘Raw’.
  * [App]
    - The function argument is evaluated in the same way on both sides, but
      the function argument computation is suspended thunkLang-side by wrapping
      it in a “Delay T (Closure ...)”-thing (using a fresh variable).
  * [Prim]
    - ‘If’ receives special treatment because we need it to retain its laziness
      in thunkLang (Why isn't it possible to suspend the branches by wrapping
      them in ‘Delay’? Because the way the semantics is set up, a ‘Delay’
      produces a “Thunk” value that can only be dealt with by the semantics of
      ‘Force’. But if we wrap both branches with ‘Force’ then suspension is
      essentially a no-op).
    - Non-If prim-ops need to have the computation of their arguments
      suspended. All these operations should be treated as if they were
      n-ary ‘App’s. TODO we should accept both types of thunks here.
  * [Letrec]
    - TODO

  Various TODO:
    - Something looked fishy with the thunkLang substitution. I think could be
      helpful if it gets stuck with a Type_error when we substitute in non-
      closed expressions.
    - The clocks seem to be a bit off between the two semantics. I tried to
      line them up a bit already, but there might be some discrepancies still.
      I was able to avoid some cases by ignoring expressions that cause the
      pureLang semantics to get stuck with wh_Errors.
 *)

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
     s ∉ freevars y ⇒
       exp_rel ctxt (App x y) (App x' (suspend s y'))) ∧
[exp_rel_If:]
  (∀ctxt xs x y z.
     LENGTH xs = 3 ∧
     exp_rel ctxt (EL 0 xs) x ∧
     exp_rel ctxt (EL 1 xs) y ∧
     exp_rel ctxt (EL 2 xs) z ⇒
       exp_rel ctxt (Prim If xs) (If x y z)) ∧
[exp_rel_Prim:]
  (∀ctxt op ss xs ys.
     op ≠ If ∧
     LIST_REL (exp_rel ctxt) xs ys ∧
     LIST_REL (λs y. s ∉ freevars y) ss ys ⇒
       exp_rel ctxt (Prim op xs)
                    (Prim op (MAP2 suspend ss ys))) ∧
[exp_rel_Letrec:]
  (∀ctxt f f' x x'.
     exp_rel ctxt (Letrec f x) (Letrec f' x'))
     (* FIXME This bit will involve more context-fiddling *)
End

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
       (∃ss ys.
          op ≠ If ∧
          y = Prim op (MAP2 suspend ss ys) ∧
          LIST_REL (exp_rel ctxt) xs ys ∧
          LIST_REL (λs y. s ∉ freevars y) ss ys)) ∧
  (∀f x.
     exp_rel ctxt (App f x) y ⇔
       ∃g z s.
         y = App g (suspend s z) ∧
         s ∉ freevars x ∧
         exp_rel ctxt f g ∧
         exp_rel ctxt x z)
Proof
  rw []
  \\ simp [Once exp_rel_cases]
  \\ eq_tac
  \\ rw [] \\ gs []
  \\ irule_at Any EQ_REFL \\ fs []
QED

(*
  TODO: The name thunk_rel doesn't say much
 *)

Inductive thunk_rel:
[thunk_rel_Suspended:]
  (∀ctxt x s y.
     exp_rel ctxt x y ⇒
       thunk_rel ctxt x (Thunk T (Closure s y))) ∧
[thunk_rel_Raw:]
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

(*
  - v_rel seems to work (but it's a bit clunky with the INL/INR stuff)
  - thunk_rel seems to be OK (it fits with the Cons case at least)
 *)

Definition v_rel_def:
  v_rel ctxt wh_Error (INL Type_error) = T ∧
  v_rel ctxt wh_Diverge (INL Diverge) = T ∧
  v_rel ctxt (wh_Closure s x) (INR (Closure t y)) =
    (s = t ∧ exp_rel ((s, Raw)::ctxt) x y) ∧
  v_rel ctxt (wh_Constructor s xs) (INR (Constructor t ys)) =
    (s = t ∧ LIST_REL (thunk_rel ctxt) xs ys) ∧
  v_rel ctxt (wh_Atom a) (INR (Atom b)) = (a = b) ∧
  v_rel ctxt _ _ = F
End

Theorem v_rel_rev[local]:
  v_rel ctxt x (INL err) =
    ((x = wh_Error ∧ err = Type_error) ∨
     (x = wh_Diverge ∧ err = Diverge)) ∧
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
  \\ Cases_on ‘err’ \\ fs [v_rel_def]
QED

Theorem get_lits_map[local]:
  get_lits = map (λx. case x of Atom l => INR l | _ => INL Type_error)
Proof
  simp [FUN_EQ_THM]
  \\ Induct \\ simp [get_lits_def, map_def]
QED

Theorem exp_rel_eval_to:
  ∀k x res y ctxt.
    eval_wh_to k x = res ∧
    exp_rel ctxt x y ⇒
      v_rel ctxt res (eval_to k y)
Proof
  ho_match_mp_tac eval_wh_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Var *)
    rw [eval_wh_to_def, eval_to_def]
    \\ fs [exp_rel_def, v_rel_def, eval_to_def])
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
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to k g’ \\ fs [v_rel_def])
    \\ rw [exp_rel_def]
    \\ first_x_assum (drule_then assume_tac)
    \\ rw [suspend_def, eval_to_def]
    \\ Cases_on ‘eval_wh_to k x = wh_Error’ \\ fs []
    >- ((* pure sem errors *)
      simp [eval_to_def]
      \\ Cases_on ‘eval_to k g’ \\ fs [v_rel_def])
    \\ ‘∃res. eval_to k g = INR res’
      by (Cases_on ‘eval_to k g’ \\ fs []
          \\ rename1 ‘INL err’
          \\ Cases_on ‘err’ \\ fs [v_rel_rev])
    \\ simp []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x)’ \\ fs []
    >- ((* not a pureLang closure: thunk sem must also error *)
      Cases_on ‘eval_wh_to k x’ \\ Cases_on ‘res’ \\ gvs [v_rel_def]
      \\ simp [thunkLang_substTheory.dest_anyClosure_def,
               thunkLang_substTheory.dest_Closure_def,
               thunkLang_substTheory.dest_Recclosure_def,
               v_rel_def])
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ Cases_on ‘eval_wh_to k x’ \\ gvs [dest_wh_Closure_def]
    \\ Cases_on ‘res’ \\ gvs [dest_anyClosure_def,
                              thunkLang_substTheory.dest_Closure_def,
                              v_rel_def]
    \\ IF_CASES_TAC \\ fs [v_rel_def]
    \\ first_x_assum irule
    \\ simp [pure_expTheory.bind_def, FLOOKUP_UPDATE]
    \\ cheat
      (* TODO
           lemma about exp_rel and bound thunk stuff.
           we need for substitution to fail on both sides unless
           the expression (body) is closed.
       *))
  >- ((* Letrec *)
    cheat (* TODO Not done *))
  >- ((* Prim *)
    rename1 ‘Prim op xs’
    \\ rw [exp_rel_def]
    >- ((* If *)
      simp [eval_to_def, eval_wh_to_def]
      \\ IF_CASES_TAC \\ fs [v_rel_def]
      \\ gvs [LENGTH_EQ_NUM_compute]
      \\ fsrw_tac [boolSimps.DNF_ss] []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ rename1 ‘exp_rel ctxt y1 x1’
      \\ CASE_TAC \\ Cases_on ‘eval_to (k - 1) x1’ \\ fs [v_rel_def]
      \\ rename1 ‘INR res’ \\ Cases_on ‘res’ \\ gvs [v_rel_def]
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs [v_rel_def])
    >- ((* Non-If *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs [v_rel_def]
      \\ qmatch_goalsub_abbrev_tac ‘map f (MAP2 _ _ _)’
      \\ ‘∃res. map f (MAP2 suspend ss ys) = INR res’
        by (Cases_on ‘map f (MAP2 suspend ss ys)’ \\ fs []
            \\ gvs [map_INL, Abbr ‘f’, EL_MAP2, suspend_def, eval_to_def])
      \\ simp [do_prim_def, Abbr ‘f’, suspend_def]
      \\ drule map_INR
      \\ gvs [LIST_REL_EL_EQN, EL_MAP2, eval_to_def]
      \\ disch_then (assume_tac o GSYM)
      \\ drule_then assume_tac map_LENGTH \\ gvs []
      \\ Cases_on ‘op’ \\ fs []
      >- ((* Cons *)
        gvs [v_rel_def, LIST_REL_EL_EQN]
        \\ rw [] \\ gvs []
        \\ ‘MEM (EL n xs) xs’ by fs [EL_MEM]
        \\ last_x_assum (drule_all_then assume_tac)
        \\ last_x_assum (drule_all_then assume_tac) \\ fs []
        \\ fs [suspend_def, eval_to_def, thunk_rel_cases])
      >- ((* IsEq *)
        IF_CASES_TAC \\ gvs [v_rel_def, LENGTH_EQ_NUM_compute]
        \\ cheat (* TODO We have suspended computations on the RHS *))
      >- ((* Proj *)
        IF_CASES_TAC \\ gvs [v_rel_def, LENGTH_EQ_NUM_compute]
        \\ cheat (* TODO We have suspended computations on the RHS *))
      >- ((* AtomOp *)
        fs [eval_wh_to_def, CaseEq "option"]
        \\ cheat (* TODO We have suspended computations on the RHS *))
      >- ((* Lit *)
        IF_CASES_TAC \\ gvs [v_rel_def]
        \\ IF_CASES_TAC \\ gvs [v_rel_def])))
QED

val _ = export_theory ();

