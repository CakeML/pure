(*
  This stage removes some unnecessary thunk allocations that are introduced by
  the pure_to_thunk stage of the compiler.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     thunkLang_primitivesTheory dep_rewrite;
open pure_miscTheory;

val _ = new_theory "thunk_subst_unthunkProof";

val _ = numLib.prefer_num ();

Theorem exp_size_lemma[local]:
  (∀x xs. MEM x xs ⇒ exp_size x ≤ exp4_size xs) ∧
  (∀x y xs. MEM (x,y) xs ⇒ exp_size y ≤ exp1_size xs) ∧
  (∀x xs. MEM x xs ⇒ v_size x < exp5_size xs)
Proof
  rpt conj_tac
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
    (∀v. P (Value v)) ∧
    (∀x. P (MkTick x)) ⇒
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

Theorem MAP_FST_FILTER[local]:
  MAP FST (FILTER (λ(a,b). P a) xs) = FILTER P (MAP FST xs)
Proof
  irule LIST_EQ
  \\ rw [EL_MAP, FILTER_MAP, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem LIST_TO_SET_FILTER_DIFF:
  set (FILTER P l) = set l DIFF {x | ¬P x}
Proof
  rw [LIST_TO_SET_FILTER, DIFF_DEF, INTER_DEF, EXTENSION, CONJ_COMM]
QED

(* TODO pure_misc? *)
Theorem LIST_REL_FILTER[local]:
  ∀xs ys.
    LIST_REL R xs ys ⇒
    MAP FST xs = MAP FST ys ⇒
      LIST_REL R (FILTER (λ(x,y). P x) xs)  (FILTER (λ(x,y). P x) ys)
Proof
  ho_match_mp_tac LIST_REL_ind \\ rw [] \\ fs [ELIM_UNCURRY]
QED

Theorem LIST_REL_EL_MONO:
  ∀xs ys.
    (∀n. n < LENGTH xs ∧ P (EL n xs) (EL n ys) ⇒ Q (EL n xs) (EL n ys)) ∧
    LIST_REL P xs ys ⇒
      LIST_REL Q xs ys
Proof
  once_rewrite_tac [CONJ_COMM]
  \\ once_rewrite_tac [GSYM AND_IMP_INTRO]
  \\ ho_match_mp_tac LIST_REL_ind \\ simp []
  \\ rw []
  >- (
    first_x_assum (qspec_then ‘0’ assume_tac)
    \\ fs [])
  \\ first_x_assum irule \\ rw []
  \\ first_x_assum (qspec_then ‘SUC n’ assume_tac) \\ fs []
QED

Theorem LIST_REL_OPTREL[local]:
  ∀xs ys.
    LIST_REL (λ(f,x) (g,y). f = g ∧ R x y) xs ys ⇒
      OPTREL R (ALOOKUP (REVERSE xs) k) (ALOOKUP (REVERSE ys) k)
Proof
  qsuff_tac ‘
    ∀xs ys.
      LIST_REL (λ(f,x) (g,y). f = g ∧ R x y) xs ys ⇒
        OPTREL R (ALOOKUP xs k) (ALOOKUP ys k)’
  >- rw []
  \\ ho_match_mp_tac LIST_REL_ind
  \\ simp [OPTREL_def]
  \\ Cases \\ Cases \\ rw []
QED

Theorem freevars_subst:
  ∀m x. freevars (subst m x) = freevars x DIFF set (MAP FST m)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ rw [subst_def]
  \\ simp [freevars_def]
  \\ fs [AC UNION_COMM UNION_ASSOC, UNION_DIFF_DISTRIBUTE]
  >- (
    CASE_TAC \\ fs [freevars_def, ALOOKUP_NONE, MAP_REVERSE]
    \\ drule ALOOKUP_SOME
    \\ simp [MAP_REVERSE])
  >- (
    rw [MAP_MAP_o, combinTheory.o_DEF, EXTENSION, EQ_IMP_THM]
    \\ gvs [MEM_MAP]
    \\ irule_at Any EQ_REFL
    \\ first_assum (irule_at Any) \\ fs []
    \\ rw [MEM_MAP])
  >- (
    simp [DIFF_COMM]
    \\ rw [EXTENSION, MEM_MAP, MEM_FILTER, EQ_IMP_THM]
    \\ gs [ELIM_UNCURRY, DISJ_EQ_IMP])
  >- (
    simp [UNION_DIFF_DISTRIBUTE, AC UNION_COMM UNION_ASSOC, DIFF_COMM]
    \\ AP_TERM_TAC
    \\ rw [EXTENSION, MEM_MAP, MEM_FILTER, EQ_IMP_THM]
    \\ gs [ELIM_UNCURRY, DISJ_EQ_IMP])
  >- (
    fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ fs [MAP_FST_FILTER]
    \\ fs [LIST_TO_SET_FILTER_DIFF]
    \\ fs [DIFF_COMM, UNION_DIFF_DISTRIBUTE, AC UNION_COMM UNION_ASSOC]
    \\ fs [GSYM DIFF_UNION]
    \\ AP_TERM_TAC
    \\ rw [EXTENSION, DISJ_EQ_IMP, EQ_IMP_THM]
    \\ gvs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [SF SFY_ss]
    \\ gvs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD])
QED

Theorem closed_subst:
  closed (subst m x) ⇔ freevars x ⊆ set (MAP FST m)
Proof
  rw [closed_def, freevars_subst, SUBSET_DIFF_EMPTY]
QED

(* TODO thunkLang props? *)
Theorem closed_simps[local,simp]:
  (∀f x. closed (App f x) ⇔ closed f ∧ closed x) ∧
  (∀s x y. closed (Let (SOME s) x y) ⇔ closed x ∧ freevars y ⊆ {s}) ∧
  (∀s x y. closed (Lam s x) ⇔ freevars x ⊆ {s}) ∧
  (∀x y. closed (Let NONE x y) ⇔ closed x ∧ closed y) ∧
  (∀x y z. closed (If x y z) ⇔ closed x ∧ closed y ∧ closed z) ∧
  (∀f x. closed (Letrec f x) ⇔
     BIGUNION (set (MAP (λ(f,x). freevars x) f)) ⊆ set (MAP FST f) ∧
     freevars x ⊆ set (MAP FST f)) ∧
  (∀op xs. closed (Prim op xs) ⇔ EVERY closed xs) ∧
  (∀x. closed (Force x) ⇔ closed x)  ∧
  (∀x. closed (Delay x) ⇔ closed x)  ∧
  (∀x. closed (Box x) ⇔ closed x)  ∧
  (∀v. closed (Value v) ⇔ T)  ∧
  (∀x. closed (MkTick x) ⇔ closed x) ∧
  (∀v. closed (Var v) ⇔ F)
Proof
  rw [closed_def, freevars_def]
  \\ simp [SUBSET_DIFF_EMPTY, AC CONJ_COMM CONJ_ASSOC]
  \\ rw [DISJ_EQ_IMP, EQ_IMP_THM]
  \\ fs [LIST_TO_SET_EQ_SING, EVERY_MAP, GSYM closed_def, SF ETA_ss]
  \\ Cases_on ‘xs’ \\ fs []
QED

Theorem ALOOKUP_SOME_REVERSE_EL[local]:
  ALOOKUP (REVERSE l) k = SOME v ⇒ ∃n. n < LENGTH l ∧ EL n l = (k, v)
Proof
  strip_tac
  \\ dxrule_then strip_assume_tac ALOOKUP_SOME_EL
  \\ gvs [EL_REVERSE]
  \\ qmatch_asmsub_abbrev_tac ‘EL m l’
  \\ first_assum (irule_at (Pos (el 2)))
  \\ gs [Abbr ‘m’]
QED

(*
 * This is used to prove that the input expressions always produce Recclosures
 * with bound names (used in a pure_to_thunk step). No part of the compiler
 * produces values, so exp_ok holds.
 *)

Inductive exp_ok:
[exp_ok_Var:]
  (∀v.
     exp_ok (Var v)) ∧
[exp_ok_Prim:]
  (∀op xs.
     EVERY exp_ok xs ⇒
       exp_ok (Prim op xs)) ∧
[exp_ok_App:]
  (∀f x.
     exp_ok f ∧
     exp_ok x ⇒
       exp_ok (App f x)) ∧
[exp_ok_Lam:]
  (∀s x.
     exp_ok x ⇒
       exp_ok (Lam s x)) ∧
[exp_ok_Letrec:]
  (∀f x.
     EVERY exp_ok (MAP SND f) ∧
     exp_ok x ⇒
       exp_ok (Letrec f x)) ∧
[exp_ok_Let:]
  (∀s x y.
     exp_ok x ∧
     exp_ok y ⇒
       exp_ok (Let s x y)) ∧
[exp_ok_If:]
  (∀x y z.
     exp_ok x ∧
     exp_ok y ∧
     exp_ok z ⇒
       exp_ok (If x y z)) ∧
[exp_ok_Delay:]
  (∀x.
     exp_ok x ⇒
       exp_ok (Delay x)) ∧
[exp_ok_Box:]
  (∀x.
     exp_ok x ⇒
       exp_ok (Box x)) ∧
[exp_ok_Force:]
  (∀x.
     exp_ok x ⇒
       exp_ok (Force x)) ∧
[exp_ok_Value:]
  (∀v.
     v_ok v ⇒
       exp_ok (Value v)) ∧
[exp_ok_MkTick:]
  (∀x.
     exp_ok x ⇒
       exp_ok (MkTick x)) ∧
[v_ok_DoTick:]
  (∀v.
     v_ok v ⇒
       v_ok (DoTick v)) ∧
[v_ok_Constructor:]
  (∀s vs.
     EVERY v_ok vs ⇒
       v_ok (Constructor s vs)) ∧
[v_ok_Closure:]
  (∀s x.
     exp_ok x ⇒ v_ok (Closure s x)) ∧
[v_ok_Recclosure:]
  (∀f n.
     MEM n (MAP FST f) ∧
     EVERY exp_ok (MAP SND f) ⇒
       v_ok (Recclosure f n)) ∧
[v_ok_Thunk_INL:]
  (∀v.
     v_ok v ⇒
       v_ok (Thunk (INL v))) ∧
[v_ok_Thunk_INR:]
  (∀x.
     exp_ok x ⇒
       v_ok (Thunk (INR x))) ∧
[v_ok_Atom:]
  (∀x.
     v_ok (Atom x))
End

Theorem exp_ok_def:
  (∀v. exp_ok (Var v)) ∧
  (∀op xs.
     exp_ok (Prim op xs) = EVERY exp_ok xs) ∧
  (∀f x.
     exp_ok (App f x) = (exp_ok f ∧ exp_ok x)) ∧
  (∀s x.
     exp_ok (Lam s x) = exp_ok x) /\
  (∀f x.
     exp_ok (Letrec f x) =
       (EVERY exp_ok (MAP SND f) ∧
        exp_ok x)) ∧
  (∀s x y.
     exp_ok (Let s x y) = (exp_ok x ∧ exp_ok y)) ∧
  (∀x y z.
     exp_ok (If x y z) = (exp_ok x ∧ exp_ok y ∧ exp_ok z)) ∧
  (∀x.
     exp_ok (Delay x) = exp_ok x) ∧
  (∀x.
     exp_ok (Box x) = exp_ok x) /\
  (∀x.
     exp_ok (Force x) = exp_ok x) ∧
  (∀v.
     exp_ok (Value v) = v_ok v) ∧
  (∀x.
     exp_ok (MkTick x) = exp_ok x)
Proof
  rw [] \\ rw [Once exp_ok_cases]
QED

Theorem v_ok_def:
  (∀s vs.
     v_ok (Constructor s vs) = EVERY v_ok vs) ∧
  (∀s x.
     v_ok (Closure s x) = exp_ok x) ∧
  (∀f n.
     v_ok (Recclosure f n) =
       (MEM n (MAP FST f) ∧
        EVERY exp_ok (MAP SND f))) ∧
  (∀v.
     v_ok (Thunk (INL v)) = v_ok v) ∧
  (∀x.
     v_ok (Thunk (INR x)) = exp_ok x) ∧
  (∀v.
     v_ok (DoTick v) = v_ok v) ∧
  (∀x.
     v_ok (Atom x))
Proof
  rw [] \\ rw [Once exp_ok_cases]
QED

Theorem exp_ok_subst:
  ∀xs x.
    EVERY v_ok (MAP SND xs) ∧
    exp_ok x ⇒
      exp_ok (subst xs x)
Proof
  ho_match_mp_tac subst_ind \\ rw [subst_def]
  \\ gs [exp_ok_def]
  >- ((* Var *)
    CASE_TAC  \\ gs [exp_ok_def]
    \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
    \\ gs [EVERY_EL]
    \\ first_x_assum (drule_then assume_tac)
    \\ gs [EL_MAP])
  >- ((* Prim *)
    rw [Once exp_ok_cases, EVERY_MAP]
    \\ gs [EVERY_MEM])
  >- ((* Lam *)
    gs [EVERY_MAP, EVERY_MEM, MEM_FILTER])
  >- ((* Let SOME *)
    gs [EVERY_MAP, EVERY_MEM, MEM_FILTER])
  >- ((* Letrec *)
    first_x_assum (irule_at Any)
    \\ gs [EVERY_MAP, LAMBDA_PROD, EVERY_FILTER]
    \\ irule_at Any EVERY_MONOTONIC
    \\ first_assum (irule_at Any)
    \\ simp [FORALL_PROD]
    \\ rw [EVERY_MEM, FORALL_PROD]
    \\ first_x_assum irule
    \\ simp [PULL_EXISTS]
    \\ first_assum (irule_at Any)
    \\ gs [EVERY_MEM, FORALL_PROD, SF SFY_ss])
QED

Theorem exp_ok_eval_to:
  ∀k x v.
    exp_ok x ∧
    eval_to k x = INR v ⇒
      v_ok v
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ qpat_x_assum ‘eval_to k _ = _’ mp_tac
  >- ((* Value *)
    gs [exp_ok_def, eval_to_def]
    \\ rw [] \\ gs [])
  >- ((* Var *)
    gs [eval_to_def])
  >- ((* App *)
    rename1 ‘App x y’
    \\ gs [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ gs []
    \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘dest_anyClosure vc’
    \\ Cases_on ‘dest_anyClosure vc’ \\ gs []
    \\ pairarg_tac \\ gvs []
    \\ IF_CASES_TAC \\ gs [] \\ rw []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ irule exp_ok_subst
    \\ Cases_on ‘vc’ \\ gvs [dest_anyClosure_def, exp_ok_def, v_ok_def]
    \\ gvs [CaseEqs ["option", "exp"], EVERY_MAP, LAMBDA_PROD]
    \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
    \\ gvs [EVERY_EL]
    \\ rw []
    >- (
      first_x_assum (drule_then assume_tac)
      \\ gs [ELIM_UNCURRY, Once exp_ok_cases])
    \\ first_assum (drule_then mp_tac)
    \\ simp_tac std_ss [ELIM_UNCURRY]
    \\ simp [v_ok_def]
    \\ gs [EVERY_MAP, EVERY_EL, MEM_MAP, PULL_EXISTS, MEM_EL]
    \\ strip_tac
    \\ irule_at Any EQ_REFL \\ gs [] \\ rw []
    \\ first_x_assum (drule_then assume_tac)
    \\ gs [ELIM_UNCURRY])
  >- ((* Lam *)
    gs [exp_ok_def, eval_to_def]
    \\ rw [] \\ gs [v_ok_def])
  >- ((* Let NONE *)
    rename1 ‘Let _ x y’
    \\ gs [exp_ok_def, eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ gs [])
  >- ((* Let SOME *)
    rename1 ‘Let _ x y’
    \\ gs [exp_ok_def, eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
    \\ rw []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ irule exp_ok_subst \\ gs [])
  >- ((* If *)
    rename1 ‘If x y z’
    \\ gs [exp_ok_def, eval_to_def]
    \\ IF_CASES_TAC \\ gs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [])
  >- ((* Letrec *)
    rename1 ‘Letrec f x’
    \\ gs [exp_ok_def, eval_to_def]
    \\ IF_CASES_TAC \\ gs [] \\ rw []
    \\ first_x_assum irule \\ gs [subst_funs_def]
    \\ irule exp_ok_subst
    \\ gs [EVERY_MAP, LAMBDA_PROD, EVERY_EL] \\ rw []
    \\ Cases_on ‘EL n f’ \\ gs [v_ok_def]
    \\ gs [EVERY_MAP, EVERY_EL, MEM_MAP, MEM_EL, EXISTS_PROD]
    \\ rw [Once EQ_SYM_EQ]
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Delay *)
    gs [exp_ok_def, eval_to_def]
    \\ rw [] \\ gs [v_ok_def])
  >- ((* Box *)
    gs [exp_ok_def, eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ gs []
    \\ rw [] \\ gs [v_ok_def])
  >- ((* Force *)
    gs [exp_ok_def]
    \\ simp [Once eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ gs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    >- (
      Cases_on ‘dest_anyThunk y’ \\ gs []
      \\ pairarg_tac \\ gvs []
      \\ BasicProvers.TOP_CASE_TAC \\ gs []
      >- (
        Cases_on ‘y’ \\ gvs [dest_anyThunk_def, CaseEqs ["option", "exp"],
                             v_ok_def]
        \\ rw [] \\ gs [])
      \\ IF_CASES_TAC \\ gs []
      \\ rw []
      \\ last_x_assum irule
      \\ first_assum (irule_at Any) \\ gs []
      \\ first_assum (irule_at Any) \\ gs []
      \\ gs [subst_funs_def]
      \\ irule exp_ok_subst
      \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, EVERY_MAP, v_ok_def]
      \\ Cases_on ‘y’ \\ gs [dest_anyThunk_def, v_ok_def]
      \\ gvs [CaseEqs ["option", "exp"], EVERY_MAP, EVERY_EL]
      \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gs []
      \\ rw [] \\ gs [EL_MAP, exp_ok_def, ELIM_UNCURRY, MEM_EL, PULL_EXISTS]
      \\ first_x_assum (drule_then assume_tac) \\ gvs [exp_ok_def]
      \\ gs [EVERY_EL, MEM_MAP, MEM_EL, EXISTS_PROD]
      \\ rw [Once EQ_SYM_EQ]
      \\ first_assum (irule_at Any)
      \\ rename1 ‘mm < LENGTH binds’
      \\ Cases_on ‘EL mm binds’ \\ gs [EL_MAP])
    \\ IF_CASES_TAC \\ gs []
    \\ rw []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any)
    \\ Cases_on ‘y’ \\ gvs [v_ok_def])
  >- ((* MkTick *)
    gs [exp_ok_def, eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ gs []
    \\ rw [] \\ gs [v_ok_def])
  >- ((* Prim *)
    gs [exp_ok_def, eval_to_def]
    \\ Cases_on ‘op’ \\ gs []
    >- (
      Cases_on ‘result_map (λx. eval_to k x) xs’ \\ gs []
      \\ rw [] \\ gs [v_ok_def]
      \\ gs [result_map_INR]
      \\ gs [EVERY_EL] \\ rw []
      \\ drule_then assume_tac map_INR
      \\ drule_then assume_tac map_LENGTH \\ gvs []
      \\ first_x_assum (drule_then assume_tac)
      \\ first_x_assum irule
      \\ first_assum (irule_at Any)
      \\ gs [EL_MEM])
    >- (
      IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
      \\ Cases_on ‘dest_Constructor y’ \\ gs []
      \\ pairarg_tac \\ gvs []
      \\ IF_CASES_TAC \\ gs []
      \\ rw [] \\ gs [v_ok_def])
    >- (
      IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ gs []
      \\ Cases_on ‘dest_Constructor y’ \\ gs []
      \\ pairarg_tac \\ gvs []
      \\ IF_CASES_TAC \\ gs []
      \\ Cases_on ‘y’ \\ gs [v_ok_def, EVERY_EL]
      \\ rw []
      \\ first_x_assum irule \\ gs [])
    >- (
      qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ Cases_on ‘result_map f xs’ \\ gs []
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gs []
      \\ rw [] \\ gs [v_ok_def]))
QED

(* --------------------------
   INVARIANT:
   --------------------------

   All variables should be substituted with something thunked.

   --------------------------
   EXPRESSING THE INVARIANT:
   --------------------------

   The invariant is satisfied by code that looks exactly as the code produced
   by the pure_to_thunk pass.

 *)

Inductive exp_inv:
[exp_inv_Var:]
  (∀v.
     exp_inv (Var v)) ∧
[exp_inv_Value:]
  (∀v.
     v_inv v ⇒
       exp_inv (Value v)) ∧
[exp_inv_App:]
  (∀f x.
     exp_inv f ∧
     exp_inv x ⇒
       exp_inv (App f (Delay x))) ∧
[exp_inv_Lam:]
  (∀s x.
     exp_inv x ⇒
       exp_inv (Lam s x)) ∧
[exp_inv_Letrec:]
  (∀f x.
     EVERY exp_inv (MAP SND f) ∧
     exp_inv x ⇒
       exp_inv (Letrec (MAP (λ(f,x). (f, Delay x)) f) x)) ∧
[exp_inv_Let:]
  (∀x y.
     exp_inv x ∧
     exp_inv y ⇒
       exp_inv (Let NONE x y)) ∧
[exp_inv_If:]
  (∀x y z.
     exp_inv x ∧
     exp_inv y ∧
     exp_inv z ⇒
       exp_inv (If x y z)) ∧
[exp_inv_Prim_Cons:]
  (∀nm xs.
     EVERY exp_inv xs ⇒
       exp_inv (Prim (Cons nm) (MAP Delay xs))) ∧
[exp_inv_Prim_Proj:]
  (∀s i xs.
     EVERY exp_inv xs ⇒
       exp_inv (Force (Prim (Proj s i) xs))) ∧
[exp_inv_Prim:]
  (∀op xs.
     (∀nm. op ≠ Cons nm) ∧
     (∀s i. op ≠ Proj s i) ∧
     EVERY exp_inv xs ⇒
       exp_inv (Prim op xs)) ∧
[exp_inv_Delay:]
  (∀x.
     exp_inv x ⇒
       exp_inv (Delay x)) ∧
[exp_inv_Force:]
  (∀x.
    exp_inv x ⇒
      exp_inv (Force x)) ∧
[v_inv_Atom:]
  (∀x.
     v_inv (Atom x)) ∧
[v_inv_Constructor:]
  (∀s vs.
     EVERY v_inv vs ⇒
       v_inv (Constructor s vs)) ∧
[v_inv_Closure:]
  (∀s x.
     exp_inv x ⇒
       v_inv (Closure s x)) ∧
[v_inv_Recclosure:]
  (∀f n.
     EVERY (λv. ∃x. v = Delay x ∧ exp_inv x) (MAP SND f) ⇒
       v_inv (Recclosure f n)) ∧
[v_inv_Thunk:]
  (∀x.
     exp_inv x ⇒
       v_inv (Thunk (INR x)))
End

Theorem exp_inv_def:
  (∀v.
     exp_inv (Var v) = T) ∧
  (∀v.
     exp_inv (Value v) = v_inv v) ∧
  (∀x.
     exp_inv (Box x) = F) ∧
  (∀f x.
     exp_inv (App f x) =
       (∃y. x = Delay y ∧
            exp_inv f ∧
            exp_inv y)) ∧
  (∀s x.
     exp_inv (Lam s x) =
       exp_inv x) ∧
  (∀s x y.
     exp_inv (Let s x y) =
       (s = NONE ∧
        exp_inv x ∧
        exp_inv y)) ∧
  (∀f x.
     exp_inv (Letrec f x) =
       (∃g. f = MAP (λ(fn,x). (fn,Delay x)) g ∧
            EVERY exp_inv (MAP SND g) ∧
            exp_inv x)) ∧
  (∀x y z.
     exp_inv (If x y z) =
       (exp_inv x ∧
        exp_inv y ∧
        exp_inv z)) ∧
  (∀nm xs.
     exp_inv (Prim (Cons nm) xs) =
       (∃ys. xs = MAP Delay ys ∧
             EVERY exp_inv ys)) ∧
  (∀op xs.
     (∀nm. op ≠ Cons nm) ⇒
     (∀s i. op ≠ Proj s i) ⇒
     exp_inv (Prim op xs) =
       EVERY exp_inv xs) ∧
  (∀s i xs.
     exp_inv (Force (Prim (Proj s i) xs)) =
       EVERY exp_inv xs) ∧
  (∀x.
     (∀s i xs. x ≠ Prim (Proj s i) xs) ⇒
     exp_inv (Force x) = exp_inv x) ∧
  (∀x.
     exp_inv (Delay x) =
       exp_inv x)
Proof
  rw [] \\ rw [Once exp_inv_cases]
  \\ rw [Once exp_inv_cases]
QED

Theorem v_inv_def[simp]:
  (∀s vs. v_inv (Constructor s vs) = EVERY v_inv vs) ∧
  (∀s x. v_inv (Closure s x) = exp_inv x) ∧
  (∀f n. v_inv (Recclosure f n) =
           EVERY (λv. ∃x. v = Delay x ∧ exp_inv x) (MAP SND f)) ∧
  (∀v. v_inv (Thunk (INL v)) = F) ∧
  (∀x. v_inv (Thunk (INR x)) = exp_inv x) ∧
  (∀x. v_inv (Atom x) = T)
Proof
  rw [] \\ rw [Once exp_inv_cases, AC CONJ_COMM CONJ_ASSOC]
QED

(* --------------------------
   COMPILATION:
   --------------------------

   We can replace all occurrences of (Delay (Force (Var v))) floating around
   in the middle of expressions with (Var v), but we can't touch those that sit
   at the top of bindings such as Letrecs, because Letrecs turn into
   Recclosures, and Recclosures that look like this are used as thunks. If we
   remove the Delay's sitting directly in a Letrec declaration then the
   resulting code will get stuck when it is forced somewhere. Otherwise, we
   expect that every variable will be replaced by a thunk.

 *)

Definition is_delay_def[simp]:
  is_delay (Delay x) = T ∧
  is_delay _ = F
End

Inductive exp_rel:
[exp_rel_Var:]
  (∀v.
     exp_rel (Delay (Force (Var v))) (MkTick (Var v))) ∧
[exp_rel_Value:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Delay (Force (Value v))) (MkTick (Value w))) ∧
[exp_rel_Value_Unchanged:]
  (∀v w.
     v_rel v w ⇒
       exp_rel (Value v) (Value w)) ∧
[exp_rel_Lam:]
  (∀s x y.
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
     LIST_REL (λ(f,x) (g,y).
                 f = g ∧
                 is_delay x ∧
                 is_delay y ∧
                 exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y)) ∧
[exp_rel_Delay:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Delay x) (Delay y)) ∧
[exp_rel_Force:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Force x) (Force y)) ∧
[v_rel_Closure:]
  (∀s x y.
     exp_rel x y ∧
     freevars x ⊆ {s} ⇒
       v_rel (Closure s x) (Closure s y)) ∧
[v_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 is_delay x ∧
                 is_delay y ∧
                 exp_rel x y ∧
                 freevars x ⊆ set (MAP FST f)) f g ⇒
       v_rel (Recclosure f n) (Recclosure g n)) ∧
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Thunk_Same:]
  (∀x y.
     exp_rel x y ∧
     closed x ⇒
       v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_Thunk_Changed:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INR (Force (Value v)))) (DoTick w)) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x))
End

Theorem v_rel_def[simp]:
  (∀s x z.
     v_rel (Closure s x) z =
       (∃y. z = Closure s y ∧
                exp_rel x y ∧
                freevars x ⊆ {s})) ∧
  (∀f n z.
     v_rel (Recclosure f n) z =
       (∃g. z = Recclosure g n ∧
            LIST_REL (λ(fn,x) (gn,y).
                        fn = gn ∧
                        is_delay x ∧
                        is_delay y ∧
                        exp_rel x y ∧
                        freevars x ⊆ set (MAP FST f)) f g)) ∧
  (∀s vs z.
     v_rel (Constructor s vs) z =
       (∃ws. z = Constructor s ws ∧
             LIST_REL v_rel vs ws)) ∧
  (∀x z.
     v_rel (Atom x) z = (z = Atom x))
Proof
  rw [] \\ rw [Once exp_rel_cases]
  \\ rw [EQ_SYM_EQ, AC CONJ_COMM CONJ_ASSOC, EQ_IMP_THM]
QED

Theorem v_rel_Thunk_def:
  v_rel (Thunk x) z =
    ((∃y w. z = Thunk (INR y) ∧
            x = INR w ∧
            exp_rel w y ∧
            closed w) ∨
     (∃v y. x = INR (Force (Value v)) ∧
            z = DoTick y ∧
            v_rel v y))
Proof
  rw [Once exp_rel_cases]
  \\ rw [EQ_SYM_EQ, AC CONJ_COMM CONJ_ASSOC, EQ_IMP_THM, SF SFY_ss]
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac \\ rw [Once exp_rel_cases]
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac \\ rw [Once exp_rel_cases]
QED

Theorem v_rel_Thunk_simps[simp]:
  (∀x s vs. ¬v_rel (Thunk x) (Constructor s vs)) ∧
  (∀x s y. ¬v_rel (Thunk x) (Closure s y)) ∧
  (∀x y. ¬v_rel (Thunk x) (Atom y)) ∧
  (∀x w. ¬v_rel (DoTick x) w)
Proof
  rpt conj_tac
  \\ Cases_on ‘x’ \\ rw [v_rel_Thunk_def]
  \\ rw [Once exp_rel_cases]
QED

Theorem v_rel_rev[simp]:
  (∀w.
     v_rel v (DoTick w) =
       (∃x. v = Thunk (INR (Force (Value x))) ∧
            v_rel x w)) ∧
  (∀s y.
     v_rel v (Closure s y) =
       (∃x. v = Closure s x ∧
            exp_rel x y ∧
            freevars x ⊆ {s})) ∧
  (∀g n.
     v_rel v (Recclosure g n) =
       ((∃f. v = Recclosure f n ∧
             LIST_REL (λ(fn,x) (gn,y).
                         fn = gn ∧
                         is_delay x ∧
                         is_delay y ∧
                         exp_rel x y ∧
                         freevars x ⊆ set (MAP FST f)) f g))) ∧
  (∀v s vs.
     v_rel v (Constructor s vs) =
       (∃ws. v = Constructor s ws ∧
             LIST_REL v_rel ws vs)) ∧
  (∀v s.
     v_rel v (Thunk s) =
      (∃x y.
         v = Thunk (INR x) ∧
         s = INR y ∧
         exp_rel x y ∧
         closed x)) ∧
  (∀v a.
     v_rel v (Atom a) = (v = Atom a))
Proof
  rw [] \\ Cases_on ‘v’ \\ simp []
  \\ rw [EQ_IMP_THM]
  \\ fs [v_rel_Thunk_def, SF SFY_ss]
QED

Theorem is_delay_subst[local,simp]:
  is_delay (subst ws x) = is_delay x
Proof
  Cases_on ‘x’ \\ rw [subst_def]
  >- (
    CASE_TAC \\ fs [])
  \\ rename1 ‘Let s’
  \\ Cases_on ‘s’ \\ rw [subst_def]
QED

Theorem exp_rel_subst:
  ∀vs x ws y.
    LIST_REL v_rel (MAP SND vs) (MAP SND ws) ∧
    MAP FST vs = MAP FST ws ∧
    exp_rel x y ⇒
      exp_rel (subst vs x) (subst ws y)
Proof
  ho_match_mp_tac subst_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Var *)
    rw [Once exp_rel_cases])
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Prim
    \\ simp [EVERY2_MAP]
    \\ gvs [LIST_REL_EL_EQN] \\ rw []
    \\ first_x_assum irule \\ fs [EL_MEM])
  >- ((* If *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_If \\ fs [])
  >- ((* App *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_App \\ fs [])
  >- ((* Lam *)
    rw [Once exp_rel_cases]
    \\ gvs [subst_def]
    \\ irule exp_rel_Lam
    \\ first_x_assum irule
    \\ fs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. x ≠ s’ \\ fs []
    \\ irule LIST_REL_FILTER \\ fs [])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Let \\ fs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ ‘MAP FST f = MAP FST g’
      by (fs [ELIM_UNCURRY, LIST_REL_CONJ]
          \\ irule LIST_EQ
          \\ gvs [LIST_REL_EL_EQN] \\ rw [EL_MAP])
    \\ irule exp_rel_Letrec
    \\ gvs [EVERY2_MAP, LAMBDA_PROD]
    \\ first_assum (irule_at Any)
    \\ gvs [MAP_FST_FILTER, EVERY2_MAP]
    \\ qabbrev_tac ‘P = λx. ¬MEM x (MAP FST g)’ \\ fs []
    \\ irule_at Any LIST_REL_FILTER \\ fs []
    \\ irule_at Any LIST_REL_EL_MONO
    \\ first_assum (irule_at Any) \\ rw []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ first_x_assum irule
    \\ simp [MAP_FST_FILTER]
    \\ gvs [MEM_EL, PULL_EXISTS]
    \\ rw [Once EQ_SYM_EQ]
    \\ first_assum (irule_at Any)
    \\ irule_at Any LIST_REL_FILTER \\ fs [])
  >- ((* Delay *)
    rw [Once exp_rel_cases] \\ simp [subst_def, exp_rel_Value, exp_rel_Delay,
                                     SF SFY_ss]
    \\ ‘OPTREL v_rel (ALOOKUP (REVERSE vs) v) (ALOOKUP (REVERSE ws) v)’
      suffices_by (rw [] \\ fs [subst_def, OPTREL_def, exp_rel_Var,
                                exp_rel_Value, SF SFY_ss])
    \\ irule LIST_REL_OPTREL
    \\ gvs [EVERY2_MAP, ELIM_UNCURRY, LIST_REL_CONJ]
    \\ pop_assum mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qid_spec_tac ‘ws’ \\ Induct_on ‘vs’ \\ Cases_on ‘ws’ \\ simp [])
  >- ((* Box *)
    rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ irule exp_rel_Force \\ fs [])
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ simp [subst_def]
    \\ rw [Once exp_rel_cases])
  >- ((* MkTick *)
    rw [Once exp_rel_cases])
QED

Theorem SUM_REL_def[simp] = quotient_sumTheory.SUM_REL_def;

Theorem exp_inv_subst:
  ∀xs x.
    EVERY v_inv (MAP SND xs) ∧
    exp_inv x ⇒
      exp_inv (subst xs x)
Proof
  qsuff_tac ‘
    (∀x. exp_inv x ⇒
       ∀xs. EVERY v_inv (MAP SND xs) ⇒
         exp_inv (subst xs x)) ∧
    (∀v. v_inv v ⇒ T)’
  >- rw []
  \\ ho_match_mp_tac exp_inv_strongind \\ rw []
  >- ((* Var *)
    simp [subst_def]
    \\ CASE_TAC \\ fs [exp_inv_def]
    \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
    \\ gs [EVERY_EL, EL_MAP]
    \\ first_x_assum (drule_then assume_tac) \\ gs [])
  >- ((* Value *)
    gvs [subst_def, exp_inv_def])
  >- ((* App *)
    gvs [subst_def, exp_inv_def])
  >- ((* Lam *)
    gvs [subst_def, exp_inv_def]
    \\ first_x_assum irule
    \\ gs [EVERY_MAP, EVERY_FILTER, EVERY_MEM, ELIM_UNCURRY, SF SFY_ss])
  >- ((* Letrec *)
    gs [subst_def, exp_inv_def]
    \\ gvs [EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
            EVERY_FILTER, GSYM FST_THM]
    \\ qpat_x_assum ‘∀xs. EVERY _ xs ⇒ _’ (irule_at Any)
    \\ gvs [EVERY_MEM, FORALL_PROD, subst_def, SF SFY_ss]
    \\ qmatch_goalsub_abbrev_tac ‘subst m’
    \\ qexists_tac ‘MAP (λ(n,x). (n,subst m x)) f’
    \\ gs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MEM_MAP, EXISTS_PROD,
           PULL_EXISTS, subst_def, exp_inv_def, SF SFY_ss]
    \\ qunabbrev_tac ‘m’
    \\ conj_tac
    >- (
      rw [MEM_FILTER]
      \\ first_x_assum (irule_at Any)
      \\ first_assum (irule_at Any))
    \\ rw []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ first_x_assum irule
    \\ rw [MEM_FILTER]
    \\ first_x_assum (irule_at Any)
    \\ first_assum (irule_at Any))
  >- ((* Let NONE *)
    gvs [subst_def, exp_inv_def])
  >- ((* If *)
    gvs [subst_def, exp_inv_def])
  >- ((* Prim Cons *)
      gs [subst_def, exp_inv_def, EVERY_MAP, EVERY_MEM, SF SFY_ss]
      \\ rename1 ‘subst ys’
      \\ qexists_tac ‘MAP (subst ys) xs’
      \\ rw [MAP_MAP_o, combinTheory.o_DEF, subst_def]
      \\ gvs [MEM_MAP, PULL_EXISTS, exp_inv_def, subst_def])
  >- ((* Prim Proj *)
    gs [subst_def]
    \\ irule exp_inv_Prim_Proj
    \\ gvs [EVERY_EL, EL_MAP])
  >- ((* Prim *)
    gvs [subst_def, exp_inv_def, EVERY_MAP, EVERY_MEM, SF SFY_ss])
  >- ((* Delay *)
    gvs [subst_def, exp_inv_def])
  >- ((* Force *)
    simp [subst_def]
    \\ irule exp_inv_Force \\ gs [])
QED

(* TODO fix IH instead: *)
Theorem dest_Tick_exists[simp,local]:
  (∃x. dest_Tick x = NONE) ∧
  (∀y. ∃x. dest_Tick x = SOME y)
Proof
  rw []
  >- (
    qexists_tac ‘Atom foo’
    \\ simp [])
  \\ qexists_tac ‘DoTick y’
  \\ simp []
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ∧
    exp_inv x ∧
    exp_ok x ∧
    closed x ⇒
      ($= +++ (λv w. v_rel v w ∧ v_inv v ∧ v_ok v))
        (eval_to k x)
        (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Value *)
    rw [Once exp_rel_cases]
    \\ gs [eval_to_def, exp_inv_def, exp_ok_def]
    \\ Cases_on ‘k'’
    )
  >- ((* App *)
    rename1 ‘App x1 y1’
    \\ rw [Once exp_rel_cases]
    \\ rw [eval_to_def] \\ gvs [exp_inv_def, exp_ok_def]
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ Cases_on ‘eval_to k x1’ \\ Cases_on ‘eval_to k g’ \\ gs []
    \\ qpat_x_assum ‘exp_rel (Delay _) _’ mp_tac
    \\ rw [Once exp_rel_cases] \\ gs [eval_to_def]
    \\ pop_assum mp_tac
    \\ rename1 ‘v_rel v1 v2’
    \\ strip_tac
    THEN (
      Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gvs [dest_anyClosure_def]
      >- ((* Thunk-Thunk *)
        IF_CASES_TAC \\ gs []
        \\ qmatch_goalsub_abbrev_tac ‘_ (eval_to _ (subst [s,w1] _))
                                        (eval_to _ (subst [s,w2] _))’
        \\ ‘[s,w1] = [] ++ [s,w1]’ by gs [] \\ pop_assum SUBST1_TAC
        \\ ‘[s,w2] = [] ++ [s,w2]’ by gs [] \\ pop_assum SUBST1_TAC
        \\ first_x_assum irule \\ simp []
        \\ simp [closed_subst]
        \\ irule_at Any exp_inv_subst
        \\ irule_at Any exp_ok_subst
        \\ irule_at Any exp_rel_subst \\ simp []
        \\ unabbrev_all_tac \\ gs [v_ok_def]
        \\ (irule_at Any v_rel_Thunk_Changed ORELSE
            irule_at Any v_rel_Thunk_Same))
      >- ((* Recclosure-Recclosure *)
        rename1 ‘LIST_REL _ xs ys’
        \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧
                            exp_rel _x _y)
                   (ALOOKUP (REVERSE xs) s)
                   (ALOOKUP (REVERSE ys) s)’
          by (irule LIST_REL_OPTREL
              \\ gs [LIST_REL_CONJ, ELIM_UNCURRY])
        \\ gs [OPTREL_def]
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [])))
  >- ((* Lam *)
    rw [Once exp_rel_cases, Once exp_inv_cases]
    \\ fs [exp_inv_def, eval_to_def, v_ok_def, exp_ok_def])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ gvs [exp_inv_def, exp_ok_def]
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ rw [eval_to_def]
    \\ first_x_assum (drule_all_then assume_tac)
    \\ first_x_assum (drule_all_then assume_tac)
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases])
  >- ((* If *)
    rw [Once exp_rel_cases] \\ fs [exp_inv_def, exp_ok_def]
    \\ rename1 ‘If x y z’
    \\ rw [eval_to_def] \\ gvs [exp_inv_def, exp_ok_def]
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs []
    \\ IF_CASES_TAC \\ gs [])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ rw [eval_to_def] \\ gvs [exp_inv_def, exp_ok_def]
    \\ first_x_assum (irule_at Any)
    \\ fs [subst_funs_def, closed_def, freevars_subst, freevars_def]
    \\ fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, SUBSET_DIFF_EMPTY,
           GSYM FST_THM]
    \\ irule_at Any exp_rel_subst
    \\ irule_at Any exp_ok_subst
    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
            GSYM FST_THM]
    \\ irule_at Any LIST_EQ
    \\ gvs [EL_MAP, freevars_def, MAP_MAP_o, combinTheory.o_DEF]
    \\ drule_then assume_tac LIST_REL_LENGTH \\ simp []
    \\ irule_at Any exp_inv_subst
    \\ simp [EVERY_MAP, LAMBDA_PROD, exp_inv_def]
    \\ gvs [EVERY_MEM, ELIM_UNCURRY, MEM_MAP, PULL_EXISTS, EL_MAP,
            LIST_REL_EL_EQN, freevars_def, BIGUNION_SUBSET, MEM_MAP,
            PULL_EXISTS, EL_MEM, MEM_MAP, SF SFY_ss, SF ETA_ss,
            v_ok_def]
    \\ rw []
    \\ gvs [MEM_EL, PULL_EXISTS]
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ gs [Once exp_rel_cases]
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Delay *)
    rw [Once exp_rel_cases] \\ gs [eval_to_def, exp_inv_def, exp_ok_def,
                                   v_ok_def, v_rel_Thunk_Same])
  >- ((* Box *)
    rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ CONV_TAC (PATH_CONV "lr" (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ CONV_TAC (PATH_CONV "r" (SIMP_CONV (srw_ss()) [Once eval_to_def]))
    \\ rename1 ‘exp_rel x y’
    \\ gs [exp_ok_def]
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘∃s i xs. x = Prim (Proj s i) xs’ \\ gvs [exp_inv_def]
    >- (
      qpat_x_assum ‘exp_rel _ y’ mp_tac
      \\ rw [Once exp_rel_cases]
      \\ CONV_TAC (PATH_CONV "lr" (SIMP_CONV (srw_ss()) [Once eval_to_def]))
      \\ CONV_TAC (PATH_CONV "r" (SIMP_CONV (srw_ss()) [Once eval_to_def]))
      \\ drule_then assume_tac LIST_REL_LENGTH
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘exp_rel x y’
      \\ last_assum (qspec_then ‘Atom foo’ mp_tac)
      \\ simp_tac std_ss [dest_Tick_def]
      \\ disch_then (qspec_then ‘[]’ mp_tac o CONV_RULE SWAP_FORALL_CONV)
      \\ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [subst_funs_def]))
      \\ gs [exp_ok_def]
      \\ disch_then (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v1 v2’
      \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gvs []
      \\ gvs [v_ok_def]
      \\ rename1 ‘LIST_REL _ f g’
      \\ drule_then assume_tac LIST_REL_LENGTH \\ gs []
      \\ IF_CASES_TAC \\ gvs []
      \\ gvs [LIST_REL_EL_EQN]
      \\ first_assum (drule_then assume_tac)
      \\ Cases_on ‘EL i f’ \\ Cases_on ‘EL i g’ \\ gvs [dest_anyThunk_def]
      >- ((* Recclosure-Recclosure *)
        rename1 ‘LIST_REL _ xs ys’
        \\ rename1 ‘ALOOKUP (REVERSE xs) s1’
        \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧
                            exp_rel _x _y)
                   (ALOOKUP (REVERSE xs) s1)
                   (ALOOKUP (REVERSE ys) s1)’
          by (irule LIST_REL_OPTREL
              \\ gs [LIST_REL_CONJ, ELIM_UNCURRY])
        \\ gs [OPTREL_def]
        \\ Cases_on ‘_x’ \\ gs [] \\ Cases_on ‘_y’ \\ gs []
        \\ ‘v_ok (Recclosure xs s1)’
          by (gs [EVERY_EL]
              \\ rpt (first_x_assum (drule_then assume_tac))
              \\ gs [v_ok_def])
        \\ gs [v_ok_def]
        \\ first_x_assum irule
        \\ simp [closed_subst, subst_funs_def]
        \\ irule_at Any exp_rel_subst
        \\ irule_at Any exp_inv_subst
        \\ irule_at Any exp_ok_subst
        \\ simp [EVERY2_MAP, EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF,
                 LAMBDA_PROD, v_ok_def, GSYM FST_THM]
        \\ irule_at Any LIST_EQ
        \\ gs [ELIM_UNCURRY, LIST_REL_CONJ]
        \\ irule_at Any LIST_REL_mono
        \\ first_assum (irule_at Any) \\ simp []
        \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
        \\ gvs [LIST_REL_EL_EQN, EVERY_EL, MEM_EL, PULL_EXISTS, EL_MAP,
                v_ok_def, EVERY_EL, Once exp_rel_cases, exp_ok_def, exp_inv_def,
                SF CONJ_ss]
        \\ rename1 ‘EL m ys’
        \\ Cases_on ‘xs = []’ \\ gs [] \\ rw []
        >- (
          first_assum (irule_at Any) \\ gs [])
        \\ rpt (first_x_assum (drule_then strip_assume_tac))
        \\ gvs [exp_ok_def, exp_inv_def, freevars_def, EVERY_EL, EL_MAP,
                v_ok_def, LIST_REL_EL_EQN, ELIM_UNCURRY]
        \\ rpt (first_x_assum (drule_then strip_assume_tac))
        \\ gvs [exp_ok_def, exp_inv_def, freevars_def])
      >- ((* Thunk-Thunk *)
        first_x_assum irule
        \\ gs [subst_funs_def, EVERY_EL]
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ gs [v_ok_def])
          (* DoTick *)
      \\ simp [subst_funs_def]
      \\ rename1 ‘v_rel v1 v2’
      \\ first_x_assum irule
      \\ gs [EVERY_EL, EL_MAP]
      \\ rpt (first_x_assum (drule_then strip_assume_tac))
      \\ gs [exp_inv_def, v_ok_def, exp_ok_def]
      \\ irule exp_rel_Force
      \\ irule exp_rel_Value_Unchanged
      \\ gs [])
    \\ Cases_on ‘eval_to k x’ \\ Cases_on ‘eval_to k y’ \\ gs []
    \\ rename1 ‘v_rel v1 v2’
    \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gvs [dest_anyThunk_def]
    >- ((* Recclosure-Recclosure *)
      rename1 ‘LIST_REL _ xs ys’
      \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧
                          exp_rel _x _y)
                 (ALOOKUP (REVERSE xs) s)
                 (ALOOKUP (REVERSE ys) s)’
        by (irule LIST_REL_OPTREL
            \\ gs [LIST_REL_CONJ, ELIM_UNCURRY])
      \\ gs [OPTREL_def]
      \\ Cases_on ‘_x’ \\ gs [] \\ Cases_on ‘_y’ \\ gs []
      \\ IF_CASES_TAC \\ gs []
      \\ first_x_assum irule
      \\ simp [closed_subst, subst_funs_def]
      \\ irule_at Any exp_rel_subst
      \\ irule_at Any exp_inv_subst
      \\ irule_at Any exp_ok_subst
      \\ simp [EVERY2_MAP, EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF,
               LAMBDA_PROD, v_ok_def, GSYM FST_THM]
      \\ irule_at Any LIST_EQ
      \\ gs [ELIM_UNCURRY, LIST_REL_CONJ]
      \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
      \\ gvs [LIST_REL_EL_EQN, EVERY_EL, MEM_EL, PULL_EXISTS, EL_MAP,
              v_ok_def, EVERY_EL, Once exp_rel_cases, exp_ok_def, exp_inv_def,
              SF CONJ_ss]
      \\ rw []
      >- (
        first_assum (irule_at Any) \\ gs [])
      \\ rpt (first_x_assum (drule_then strip_assume_tac))
      \\ gs [exp_ok_def, exp_inv_def, freevars_def])
    >- ((* Thunk-Thunk *)
      IF_CASES_TAC \\ gs []
      \\ first_x_assum irule
      \\ gs [subst_funs_def, EVERY_EL, v_ok_def])
    \\ IF_CASES_TAC \\ gs []
    \\ rename1 ‘v_rel v1 v2’
    \\ simp [subst_funs_def]
    \\ gs [exp_inv_def, v_ok_def]
    \\ simp [subst_funs_def]
    \\ first_x_assum irule
    \\ gs [EVERY_EL, EL_MAP]
    \\ rpt (first_x_assum (drule_then strip_assume_tac))
    \\ gs [exp_inv_def, v_ok_def, exp_ok_def]
    \\ irule exp_rel_Force
    \\ irule exp_rel_Value_Unchanged
    \\ gs [])
  >- ((* MkTick *)
    rw [Once exp_rel_cases])
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ gvs [exp_ok_def]
    \\ simp [eval_to_def]
    \\ Cases_on ‘op’ \\ gs [exp_inv_def, EVERY_EL, EL_MAP, LIST_REL_EL_EQN]
    >- ((* Cons *)
      gvs [result_map_def, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP, eval_to_def,
           PULL_EXISTS, MEM_EL]
      \\ IF_CASES_TAC \\ gs []
      >- (
        rpt (first_x_assum (drule_then assume_tac))
        \\ gs [exp_inv_def])
      \\ IF_CASES_TAC \\ gs []
      >- (
        rpt (first_x_assum (drule_then assume_tac))
        \\ gs [exp_inv_def])
      \\ gvs [EVERY2_MAP, EVERY_MAP, v_ok_def, LIST_REL_EL_EQN,
              EVERY_EL]
      \\ rw []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ Cases_on ‘eval_to k (EL n ys)’ \\ gs [exp_ok_def, exp_inv_def])
    >- ((* IsEq *)
      IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”, exp_inv_def]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum (drule_all_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) x’ \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v1 v2’
      \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gvs []
      \\ drule_then assume_tac LIST_REL_LENGTH
      \\ IF_CASES_TAC \\ gs [v_ok_def])
    >- ((* Proj *)
      gvs [Once exp_inv_cases])
    >- ((* AtomOp *)
      Cases_on ‘k = 0’ \\ gs []
      >- (
        simp [result_map_def, MEM_MAP]
        \\ gs [GSYM NOT_NULL_MEM, NULL_EQ]
        \\ Cases_on ‘xs = []’ \\ gs []
        >- (
          CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_ok_def])
        \\ ‘ys ≠ []’ by (strip_tac \\ gs [])
        \\ gs [])
      \\ qmatch_goalsub_abbrev_tac ‘result_map f ys’
      \\ qsuff_tac ‘result_map f xs = result_map f ys’
      >- (
        rw []
        \\ Cases_on ‘result_map f ys’ \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [v_ok_def])
      \\ Cases_on ‘result_map f xs’
      >- (
        Cases_on ‘result_map f ys’
        >- (
          gvs [result_map_def, CaseEq "bool", Abbr ‘f’, MEM_MAP, MEM_EL,
               PULL_EXISTS]
          \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
          >- (
            rpt (first_x_assum (drule_then assume_tac))
            \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
            \\ gs [CaseEqs ["sum", "v"]])
          \\ qpat_x_assum ‘n < LENGTH ys’ kall_tac
          \\ rename1 ‘m < LENGTH ys’
          \\ rpt (first_x_assum (drule_then assume_tac))
          \\ Cases_on ‘eval_to (k - 1) (EL m ys)’
          \\ gvs [CaseEqs ["sum", "v"]])
        \\ gvs [result_map_def, CaseEq "bool", Abbr ‘f’, MEM_MAP, MEM_EL,
                PULL_EXISTS]
        \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        >- (
          rpt (first_x_assum (drule_then assume_tac))
          \\ Cases_on ‘eval_to (k - 1) (EL n ys)’
          \\ gs [CaseEqs ["sum", "v"]])
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ Cases_on ‘eval_to (k - 1) (EL n ys)’
        \\ gvs [CaseEqs ["sum", "v"], v_rel_Thunk_def])
      \\ Cases_on ‘result_map f ys’ \\ gs []
      >- (
        gvs [result_map_def, CaseEq "bool", Abbr ‘f’, MEM_MAP, MEM_EL,
             PULL_EXISTS]
        \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        >- (
          rpt (first_x_assum (drule_then assume_tac))
          \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
          \\ gs [CaseEqs ["sum", "v"]])
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ Cases_on ‘eval_to (k - 1) (EL n xs)’
        \\ gvs [CaseEqs ["sum", "v"], v_rel_Thunk_def])
      \\ irule_at Any LIST_EQ
      \\ gvs [result_map_def, MEM_EL, CaseEq "bool", EL_MAP]
      \\ fs [Once (DECIDE “A ⇒ ¬B ⇔ B ⇒ ¬A”)] \\ rw []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ gs [EL_MAP]
      \\ Cases_on ‘∃err. f (EL x ys) = INL err’ \\ gs []
      >- (
        Cases_on ‘err’ \\ gs [])
      \\ Cases_on ‘∃err. f (EL x xs) = INL err’ \\ gs []
      >- (
        Cases_on ‘err’ \\ gs [])
      \\ Cases_on ‘f (EL x ys)’ \\ Cases_on ‘f (EL x xs)’ \\ gs []
      \\ gs [Abbr ‘f’, PULL_EXISTS, CaseEqs ["sum", "v"]]
      \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs []))
QED

val _ = export_theory ();

