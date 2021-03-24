(*
  This stage removes some unnecessary thunk allocations that are introduced by
  the pure_to_thunk stage of the compiler.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     thunkLang_primitivesTheory dep_rewrite;
open pure_miscTheory;

val _ = new_theory "thunk_subst_unthunk";

val _ = numLib.prefer_num ();

Inductive exp_rel:
[exp_rel_Var:]
  (∀v.
     exp_rel (Delay (Force (Var v))) (Var v)) ∧
[exp_rel_Value:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Value (Thunk (INR x))) (Value (Thunk (INR y)))) ∧
[exp_rel_Lam:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y)) ∧
[exp_rel_App:]
  (∀f x g y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f x) (App g y)) ∧
[exp_rel_If:]
  (∀x1 y1 z1 x2 y2 z2.
     LIST_REL exp_rel [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_Prim:]
  (∀op xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys)) ∧
[exp_rel_Let:]
  (∀x1 y1 x2 y2.
     exp_rel x1 x2 ∧
     exp_rel y1 y2 ⇒
       exp_rel (Let NONE x1 y1) (Let NONE x2 y2)) ∧
[exp_rel_Letrec:]
  (∀f x g y.
     LIST_REL (λ(f,x) (g,y). f = g ∧ exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y)) ∧
[exp_rel_Delay:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Delay x) (Delay y)) ∧
[exp_rel_Force:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Force x) (Force y))
End

Definition v_rel_def[simp]:
  v_rel (INL x: err + v) z =
    (∃y. z = INL y ∧ x = y) ∧
  v_rel (INR (Closure s x)) z =
    (∃y. z = INR (Closure s y) ∧ exp_rel x y) ∧
  v_rel (INR (Constructor s vs)) z =
    (∃ws. z = INR (Constructor s ws) ∧
          LIST_REL (λv w. ∃x y.
                 v = Thunk (INR x) ∧
                 w = Thunk (INR y) ∧
                 exp_rel x y) vs ws) ∧
  v_rel (INR (Atom x)) z =
    (z = INR (Atom x)) ∧
  v_rel (INR (Thunk (INR x))) z =
    (∃y. z = INR (Thunk (INR y)) ∧ exp_rel x y) ∧
  v_rel _ _ = F
End

Theorem v_rel_rev[simp]:
  (∀v x.
     v_rel v (INL x) = (v = INL x)) ∧
  (∀v s vs.
     v_rel v (INR (Constructor s vs)) =
       (∃ws. v = INR (Constructor s ws) ∧
             LIST_REL (λv w. ∃x y.
                    v = Thunk (INR x) ∧
                    w = Thunk (INR y) ∧
                    exp_rel x y) ws vs)) ∧
  (∀s y.
     v_rel v (INR (Closure s y)) =
       (∃x. v = INR (Closure s x) ∧
            exp_rel x y)) ∧
  (∀v a.
     v_rel v (INR (Atom a)) = (v = INR (Atom a))) ∧
  (∀v y.
     v_rel v (INR (Thunk y)) =
       (∃x z.
            v = INR (Thunk (INR x)) ∧
            y = INR z ∧
            exp_rel x z))
Proof
  rw [] \\ Cases_on ‘v’ \\ rw []
  >- (
    simp [EQ_SYM_EQ])
  \\ rename1 ‘INR z’
  \\ Cases_on ‘z’ \\ fs []
  \\ simp [EQ_SYM_EQ]
  \\ rename1 ‘Thunk z’ \\ Cases_on ‘z’ \\ fs []
QED

Theorem exp_size_lemma[local]:
  (∀x xs. MEM x xs ⇒ exp_size x ≤ exp4_size xs) ∧
  (∀x y xs. MEM (x,y) xs ⇒ exp_size y ≤ exp1_size xs)
Proof
  conj_tac
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
  \\ first_x_assum drule
  \\ simp []
QED

Theorem exp_ind_alt[local]:
  ∀P.
    (∀n. P (Var n)) ∧
    (∀op xs. (∀a. MEM a xs ⇒ P a) ⇒ P (Prim op xs)) ∧
    (∀x y z. P x ∧ P y ∧ P z ⇒ P (If x y z)) ∧
    (∀x y. P x ∧ (∀z. exp_size z ≤ exp_size y ⇒ P z) ⇒ P x ⇒ P (App x y)) ∧
    (∀s b. P b ⇒ P (Lam s b)) ∧
    (∀v x y. P x ∧ P y ⇒ P (Let v x y)) ∧
    (∀f x. (∀n x'. MEM (n,x') f ⇒ P x') ∧ P x ⇒ P (Letrec f x)) ∧
    (∀x. P x ⇒ P (Delay x)) ∧
    (∀x. P x ⇒ P (Box x)) ∧
    (∀x. P x ⇒ P (Force x)) ∧
    (∀v. P (Value v)) ⇒
      ∀v. P v
Proof
  gen_tac
  \\ strip_tac
  \\ gen_tac
  \\ completeInduct_on ‘exp_size v’ \\ rw []
  \\ fs [PULL_FORALL]
  \\ Cases_on ‘v’ \\ fs []
  \\ last_x_assum irule \\ rw []
  \\ first_x_assum irule
  \\ fs [exp_size_def]
  \\ imp_res_tac exp_size_lemma \\ fs []
QED

Theorem exp_rel_subst:
  ∀x y v w s.
    v_rel (INR v : err + v) (INR w) ∧
    exp_rel x y ⇒
      exp_rel (subst1 s v x) (subst1 s w y)
Proof
  ho_match_mp_tac exp_ind_alt \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_cases])
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ simp [subst1_def]
    \\ irule exp_rel_Prim
    \\ simp [EVERY2_MAP]
    \\ gvs [LIST_REL_EL_EQN] \\ rw []
    \\ first_x_assum irule \\ fs [EL_MEM])
  >- ((* If *)
    rw [Once exp_rel_cases]
    \\ simp [subst1_def]
    \\ irule exp_rel_If \\ fs [])
  >- ((* App *)
    rw [Once exp_rel_cases]
    \\ simp [subst1_def]
    \\ irule exp_rel_App \\ fs [])
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ gvs [subst1_def]
    \\ IF_CASES_TAC \\ gvs [exp_rel_Lam])
  >- ((* Let *)
    rw [Once exp_rel_cases]
    \\ simp [subst1_def]
    \\ irule exp_rel_Let \\ fs [])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ simp [subst1_def]
    \\ ‘MAP FST f = MAP FST g’
      by (fs [ELIM_UNCURRY, LIST_REL_CONJ]
          \\ irule LIST_EQ
          \\ gvs [LIST_REL_EL_EQN] \\ rw [EL_MAP])
    \\ IF_CASES_TAC \\ gs [exp_rel_Letrec]
    \\ irule exp_rel_Letrec
    \\ simp [EVERY2_MAP, LAMBDA_PROD]
    \\ gvs [LIST_REL_EL_EQN] \\ rw []
    \\ first_x_assum (drule_then assume_tac)
    \\ rpt (pairarg_tac \\ gvs [])
    \\ first_x_assum irule
    \\ rw [MEM_EL, Once EQ_SYM_EQ, SF SFY_ss])
  >- ((* Delay *)
    rw [Once exp_rel_cases]
    >- ((* Var *)
      simp [subst1_def]
      \\ IF_CASES_TAC \\ fs [exp_rel_Var]
      \\ cheat (* Ok if they are thunks... *))
    \\ simp [subst1_def]
    \\ irule exp_rel_Delay \\ fs [])
  >- ((* Box *)
    rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [subst1_def]
    \\ irule exp_rel_Force \\ fs [])
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [subst1_def]
    \\ irule exp_rel_Value \\ fs [])
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ∧
    closed x ⇒
      v_rel (eval_to k x) (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >- ((* Var *)
    fs [closed_def, freevars_def])
  >- ((* App *)
    rename1 ‘App x1 y1’
    \\ rw [Once exp_rel_cases]
    \\ rw [eval_to_def]
    \\ ‘closed x1 ∧ closed y1’ by fs [closed_def, freevars_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ Cases_on ‘eval_to k x1’ \\ Cases_on ‘eval_to k x2’ \\ fs []
    \\ Cases_on ‘eval_to k y1’ \\ Cases_on ‘eval_to k y2’ \\ fs []
    \\ rename1 ‘dest_anyClosure y’
    \\ Cases_on ‘dest_anyClosure y’ \\ fs []
    >- (
      rename1 ‘dest_anyClosure z’
      \\ Cases_on ‘y’ \\ Cases_on ‘z’ \\ fs [dest_anyClosure_def]
      \\ Cases_on ‘s’ \\ fs [])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘dest_anyClosure z’
    \\ Cases_on ‘y’ \\ Cases_on ‘z’ \\ gvs [dest_anyClosure_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ rename1 ‘v_rel (INR v1) (INR v2)’
    \\ rename1 ‘eval_to k x1 = INR (Closure s b1)’
    \\ rename1 ‘eval_to k x2 = INR (Closure s b2)’
    \\ ‘[(s,v1)] = [] ++ [(s,v1)]’ by fs [] \\ pop_assum SUBST1_TAC
    \\ ‘[(s,v2)] = [] ++ [(s,v2)]’ by fs [] \\ pop_assum SUBST1_TAC
    \\ first_x_assum irule \\ fs []
    \\ irule_at Any exp_rel_subst \\ fs []
    \\ fs [closed_def, freevars_def]
    \\ cheat (* substitution closed *))
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ rename1 ‘Let NONE x y’
    \\ ‘closed x ∧ closed y’ by fs [closed_def, freevars_def]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum (drule_then assume_tac)
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases])
  >- ((* If *)
    rw [Once exp_rel_cases]
    \\ rename1 ‘If x y z’
    \\ ‘closed x ∧ closed y ∧ closed z’ by fs [closed_def, freevars_def]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule \\ fs []
    \\ cheat (* TODO subst_funs theorem *))
  >- ((* Delay *)
    rw [Once exp_rel_cases] \\ fs [closed_def, freevars_def]
    \\ simp [eval_to_def])
  >- ((* Box *)
    rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ rename1 ‘exp_rel x y’
    \\ ‘closed x’ by fs [closed_def, freevars_def]
    \\ first_x_assum (drule_then assume_tac) \\ gs []
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ fs []
    \\ rename1 ‘dest_anyThunk z’
    \\ Cases_on ‘dest_anyThunk z’ \\ fs []
    >- (
      rename1 ‘dest_anyThunk zz’
      \\ Cases_on ‘z’ \\ Cases_on ‘zz’ \\ fs [dest_anyThunk_def])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘dest_anyThunk zz’
    \\ Cases_on ‘z’ \\ Cases_on ‘zz’ \\ gvs [dest_anyThunk_def]
    >- (
      rename1 ‘Thunk s’
      \\ Cases_on ‘s’ \\ fs [])
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ simp [subst_funs_def]
    \\ cheat (* should enforce closedness in v_rel *))
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ simp [eval_to_def]
    \\ Cases_on ‘op’ \\ fs []
    \\ cheat (* TODO this is just recursively applying whatever *))
QED

val _ = export_theory ();

