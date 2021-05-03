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
     exp_ok (Value v) = v_ok v)
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
    gs [exp_ok_def, eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ gs []
    \\ Cases_on ‘dest_anyThunk y’ \\ gs []
    \\ pairarg_tac \\ gvs []
    \\ BasicProvers.TOP_CASE_TAC \\ gs []
    >- (
      rw []
      \\ Cases_on ‘y’ \\ gvs [dest_anyThunk_def, CaseEqs ["option", "exp"],
                              v_ok_def])
    \\ IF_CASES_TAC \\ gs [] \\ rw []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any)
    \\ gs [subst_funs_def]
    \\ irule exp_ok_subst
    \\ Cases_on ‘y’ \\ gs [dest_anyThunk_def, v_ok_def]
    \\ gvs [CaseEqs ["option", "exp"]]
    \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
    \\ gvs [EVERY_EL]
    \\ (rw []
        >- (
          first_x_assum (drule_then assume_tac)
          \\ gs [EL_MAP, exp_ok_def])
        \\ simp [EL_MAP, ELIM_UNCURRY]
        \\ irule v_ok_Recclosure
        \\ gs [EVERY_EL, MEM_MAP, MEM_EL, EXISTS_PROD]
        \\ rw [Once EQ_SYM_EQ]
        \\ first_assum (irule_at Any)
        \\ rename1 ‘mm < LENGTH binds’
        \\ Cases_on ‘EL mm binds’ \\ gs []))
  >- ((* Prim *)
    gs [exp_ok_def, eval_to_def]
    \\ Cases_on ‘op’ \\ gs []
    >- (
      Cases_on ‘map (λx. eval_to k x) xs’ \\ gs []
      \\ rw [] \\ gs [v_ok_def]
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
      qmatch_goalsub_abbrev_tac ‘map f xs’
      \\ Cases_on ‘map f xs’ \\ gs []
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
     thunk_inv v ⇒
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
  (∀op xs. (* TODO *)
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
       v_inv (Thunk (INR x))) ∧
[thunk_inv_Thunk:]
  (∀x.
     exp_inv x ⇒
       thunk_inv (Thunk (INR x))) ∧
[thunk_inv_Recclosure:]
  (∀f n.
     EVERY (λv. ∃x. v = Delay x ∧ exp_inv x) (MAP SND f) ⇒
       thunk_inv (Recclosure f n))
End

Theorem exp_inv_def:
  (∀v.
     exp_inv (Var v) = T) ∧
  (∀v.
     exp_inv (Value v) = thunk_inv v) ∧
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
  rw [] \\ rw [Once exp_inv_cases]
QED

Theorem thunk_inv_def[simp]:
  (∀f n.
     thunk_inv (Recclosure f n) =
       (EVERY (λv. ∃x. v = Delay x ∧ exp_inv x) (MAP SND f))) ∧
  (∀t. thunk_inv (Thunk t) = (∃x. t = INR x ∧ exp_inv x)) ∧
  (∀s vs. ¬thunk_inv (Constructor s vs)) ∧
  (∀s x. ¬thunk_inv (Closure s x)) ∧
  (∀x. ¬thunk_inv (Atom x))
Proof
  rw [] \\ rw [Once exp_inv_cases, SF DNF_ss]
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

Definition is_thunky_def[simp]:
  is_thunky (Thunk (INR x)) = T ∧
  is_thunky (Recclosure f n) = EVERY (λx. ∃y. x = Delay y) (MAP SND f) ∧
  is_thunky _ = F
End

Definition is_delay_def[simp]:
  is_delay (Delay x) = T ∧
  is_delay _ = F
End

Inductive exp_rel:
[exp_rel_Var:]
  (∀v.
     exp_rel (Delay (Force (Var v))) (Var v)) ∧
[exp_rel_Value:]
  (∀n v w.
     thunk_rel n v w ⇒
       exp_rel (Delay (Force (Value v))) (Value w)) ∧
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
     LIST_REL (λv w. ∃n. thunk_rel n v w) vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Thunk_Same:]
  (∀x y.
     exp_rel x y ∧
     closed x ⇒
       v_rel (Thunk (INR x)) (Thunk (INR y))) ∧
[v_rel_Thunk_Changed:]
  (∀n v w.
     thunk_rel n v w ⇒
       v_rel (Thunk (INR (Force (Value v)))) w) ∧
[v_rel_Atom:]
  (∀x.
     v_rel (Atom x) (Atom x)) ∧
[thunk_rel_Thunk_Changed:]
  (∀n v w.
     thunk_rel n v w ∧
     is_thunky w ⇒
       thunk_rel (SUC n) (Thunk (INR (Force (Value v)))) w) ∧
[thunk_rel_Thunk_Same:]
  (∀x y.
     exp_rel x y ∧
     closed x ⇒
       thunk_rel 0 (Thunk (INR x)) (Thunk (INR y))) ∧
[thunk_rel_Recclosure:]
  (∀f g n.
     LIST_REL (λ(fn,x) (gn,y).
                 fn = gn ∧
                 is_delay x ∧
                 is_delay y ∧
                 exp_rel x y ∧
                 freevars x ⊆ set (MAP FST f)) f g ∧
     is_thunky (Recclosure g n) ⇒
       thunk_rel 0 (Recclosure f n) (Recclosure g n))
End

Theorem thunk_rel_is_thunky:
  ∀n v w. thunk_rel n v w ⇒ is_thunky v ∧ is_thunky w
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ T) ∧
    (∀v w. v_rel v w ⇒ T) ∧
    (∀n v w. thunk_rel n v w ⇒ is_thunky v ∧ is_thunky w)’
  >- rw []
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
  \\ gvs [LIST_REL_EL_EQN, EVERY_MAP, EVERY_EL, ELIM_UNCURRY] \\ rw []
  \\ first_x_assum (drule_then strip_assume_tac)
  \\ first_x_assum (drule_then strip_assume_tac)
  \\ gvs [Once exp_rel_cases]
QED

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
             LIST_REL (λv w. ∃n. thunk_rel n v w) vs ws)) ∧
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
            (∀v. w ≠ Force (Value v)) ∧
            exp_rel w y ∧
            closed w) ∨
     (∃n v. x = INR (Force (Value v)) ∧
            thunk_rel n v z ∧
            is_thunky z))
Proof
  rw [Once exp_rel_cases]
  \\ rw [EQ_SYM_EQ, AC CONJ_COMM CONJ_ASSOC, EQ_IMP_THM]
  \\ rw [thunk_rel_is_thunky, SF SFY_ss, DISJ_EQ_IMP]
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac \\ rw [Once exp_rel_cases]
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac \\ rw [Once exp_rel_cases]
QED

Theorem v_rel_Thunk_simps[simp]:
  (∀x s vs. ¬v_rel (Thunk x) (Constructor s vs)) ∧
  (∀x s y. ¬v_rel (Thunk x) (Closure s y)) ∧
  (∀x y. ¬v_rel (Thunk x) (Atom y))
Proof
  rpt conj_tac
  \\ Cases_on ‘x’ \\ rw [v_rel_Thunk_def]
  \\ Cases_on ‘v’ \\ rw [Once exp_rel_cases]
QED

Theorem v_rel_rev[simp]:
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
                         freevars x ⊆ set (MAP FST f)) f g) ∨
        (∃k w. v = Thunk (INR (Force (Value w))) ∧
               thunk_rel k w (Recclosure g n) ∧
               is_thunky (Recclosure g n)))) ∧
  (∀v s vs.
     v_rel v (Constructor s vs) =
       (∃ws. v = Constructor s ws ∧
             LIST_REL (λv w. ∃n. thunk_rel n v w) ws vs)) ∧
  (∀v a.
     v_rel v (Atom a) = (v = Atom a))
Proof
  rw [] \\ Cases_on ‘v’ \\ simp []
  \\ rw [EQ_IMP_THM]
  \\ fs [v_rel_Thunk_def, SF SFY_ss]
QED

Theorem thunk_rel_def:
  thunk_rel k v w ⇔
    ((∃x y.
        k = 0 ∧
        v = Thunk (INR x) ∧
        w = Thunk (INR y) ∧
        (∀v. x ≠ Force (Value v)) ∧
        closed x ∧
        exp_rel x y) ∨
     (∃j u.
        k = SUC j ∧
        v = Thunk (INR (Force (Value u))) ∧
        thunk_rel j u w) ∨
     (∃f g n.
        k = 0 ∧
        v = Recclosure f n ∧
        w = Recclosure g n ∧
        is_thunky w ∧
        LIST_REL (λ(fn,x) (gn,y).
                    fn = gn ∧
                    is_delay x ∧
                    is_delay y ∧
                    exp_rel x y ∧
                    freevars x ⊆ set (MAP FST f)) f g))
Proof
  rw [Once exp_rel_cases]
  \\ rw [EQ_IMP_THM] \\ rw [DISJ_EQ_IMP]
  \\ gs [thunk_rel_is_thunky, SF SFY_ss]
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac \\ rw [Once exp_rel_cases]
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac \\ rw [Once exp_rel_cases]
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
    LIST_REL (λv w. ∃n. thunk_rel n v w) (MAP SND vs) (MAP SND ws) ∧
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
    \\ ‘OPTREL (λv w. ∃n. thunk_rel n v w)
               (ALOOKUP (REVERSE vs) v)
               (ALOOKUP (REVERSE ws) v)’
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
    rw [Once exp_rel_cases])
QED

Theorem SUM_REL_def[simp] = quotient_sumTheory.SUM_REL_def;

Theorem exp_inv_subst:
  ∀xs x.
    EVERY thunk_inv (MAP SND xs) ∧
    exp_inv x ⇒
      exp_inv (subst xs x)
Proof
  qsuff_tac ‘
    (∀x. exp_inv x ⇒
       ∀xs. EVERY thunk_inv (MAP SND xs) ⇒
         exp_inv (subst xs x)) ∧
    (∀v. v_inv v ⇒ T) ∧
    (∀v. thunk_inv v ⇒ T)’
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

Theorem result_rel_mono_left[local]:
  ($= +++ (λv w. v_rel v w ∧ v_inv v ∧ v_ok v))
    (eval_to k x)
    (eval_to j y) ∧
  eval_to k x ≠ INL Diverge ⇒
    ($= +++ (λv w. v_rel v w ∧ v_inv v ∧ v_ok v))
      (eval_to (k + i) x)
      (eval_to j y)
Proof
  rpt strip_tac
  \\ drule_then (qspec_then ‘k + i’ assume_tac) eval_to_subst_mono \\ gs []
  \\ Cases_on ‘i = 0’ \\ gs []
QED

Theorem result_rel_mono_right[local]:
  ($= +++ (λv w. v_rel v w ∧ v_inv v ∧ v_ok v))
    (eval_to k x)
    (eval_to j y) ∧
  eval_to j y ≠ INL Diverge ⇒
    ($= +++ (λv w. v_rel v w ∧ v_inv v ∧ v_ok v))
      (eval_to (i + k) x)
      (eval_to j y)
Proof
  rpt strip_tac
  \\ ‘eval_to k x ≠ INL Diverge’
    by (strip_tac
        \\ Cases_on ‘eval_to j y’
        \\ gs [])
  \\ drule_then (qspec_then ‘i + k’ assume_tac) eval_to_subst_mono \\ gs []
  \\ Cases_on ‘i = 0’ \\ gs []
QED

Theorem eval_to_mono[local]:
  eval_to k x ≠ INL Diverge ∧ k ≤ j ⇒ eval_to j x = eval_to k x
Proof
  rw []
  \\ Cases_on ‘k = j’ \\ gs [arithmeticTheory.LESS_OR_EQ]
  \\ irule eval_to_subst_mono
  \\ fs []
QED

Theorem result_rel_Diverge_left[local]:
  ($= +++ (λv w. v_rel v w ∧ v_inv v ∧ v_ok v))
    (eval_to k x)
    (eval_to j y) ∧
  j ≤ k ∧
  eval_to k x = INL Diverge ⇒
    eval_to j y = INL Diverge
Proof
  rw [] \\ CCONTR_TAC
  \\ drule_all_then assume_tac eval_to_mono
  \\ Cases_on ‘eval_to j y’ \\ gs []
QED

Theorem eval_to_Diverge[local]:
  eval_to k x = INL Diverge ⇒
    ∀j. j ≤ k ⇒ eval_to j x = INL Diverge
Proof
  rw [] \\ CCONTR_TAC
  \\ drule_all_then assume_tac eval_to_mono \\ gs []
QED

Theorem exp_rel_exp_ok:
  exp_rel x y ⇒ exp_ok x ⇒ exp_ok y
Proof
  qsuff_tac ‘
    (∀x y. exp_rel x y ⇒ exp_ok x ⇒ exp_ok y) ∧
    (∀v w. v_rel v w ⇒ v_ok v ⇒ v_ok w) ∧
    (∀n v w. thunk_rel n v w ⇒ v_ok v ⇒ v_ok w)’
  >- rw [SF SFY_ss]
  \\ ho_match_mp_tac exp_rel_strongind \\ rw []
  \\ gs [exp_ok_def, v_ok_def]
  \\ gs [LIST_REL_EL_EQN, EVERY_EL, EL_MAP, ELIM_UNCURRY]
  \\ gvs [MEM_EL, EL_MAP]
  >- (
    first_assum (irule_at Any)
    \\ gs [EL_MAP])
  >- (
    rw []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ first_x_assum (drule_then strip_assume_tac))
  >- (
    first_assum (irule_at Any)
    \\ gs [EL_MAP])
QED

Theorem thunk_rel_final:
  (∀n u g s.
     thunk_rel n u (Recclosure g s) ⇒
       ∃f. thunk_rel 0 (Recclosure f s) (Recclosure g s)) ∧
  (∀n u y.
     thunk_rel n u (Thunk (INR y)) ⇒
       ∃x. thunk_rel 0 (Thunk (INR x)) (Thunk (INR y)))
Proof
  conj_tac \\ Induct \\ rw []
  \\ ((gvs [Once thunk_rel_def]
       \\ gvs [Once thunk_rel_def]
       \\ first_assum (irule_at Any)
       \\ gs []
       \\ NO_TAC) ORELSE
      (gvs [Once thunk_rel_def]
       \\ first_x_assum (irule_at Any)
       \\ first_x_assum (irule_at Any)))
QED

Theorem exp_rel_eval_to:
  ∀k x y.
    exp_rel x y ∧
    exp_inv x ∧
    exp_ok x ∧
    closed x ⇒
      ∃j. ($= +++ (λv w. v_rel v w ∧ v_inv v ∧ v_ok v))
            (eval_to (k + j) x)
            (eval_to k y)
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ qpat_x_assum ‘exp_rel _ _’ mp_tac
  >- ((* Value *)
    rw [Once exp_rel_cases])
  >- ((* App *)
    rename1 ‘App x1 y1’
    \\ rw [Once exp_rel_cases]
    \\ rw [eval_to_def] \\ gvs [exp_inv_def, exp_ok_def]
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ map_every rename1 [
      ‘exp_rel x1 x2’,
      ‘exp_rel (Delay y) y2’,
      ‘eval_to (j1 + k) (Delay y)’,
      ‘eval_to (j2 + k) x1’]
    \\ Cases_on ‘eval_to k x2 = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j2’
      \\ Cases_on ‘eval_to (k + j2) x1’ \\ gs [])
    \\ ‘eval_to (j2 + k) x1 ≠ INL Diverge’
      by (strip_tac
          \\ drule_then assume_tac result_rel_Diverge_left
          \\ gs [])
    \\ drule_then (qspec_then ‘j1’ assume_tac) result_rel_mono_left \\ gs []
    \\ ‘eval_to (j1 + k) (Delay y) ≠ INL Diverge’ by fs [eval_to_def]
    \\ qpat_x_assum ‘_ (eval_to (j1 + k) (Delay _)) _’ assume_tac
    \\ dxrule_then (qspec_then ‘j2’ assume_tac) result_rel_mono_left \\ gs []
    \\ ‘∀j. eval_to (j + j2 + k) x1 = eval_to (j2 + k) x1’
      by (strip_tac
          \\ irule eval_to_mono \\ gs [])
    \\ Cases_on ‘eval_to (j1 + j2 + k) x1’ \\ Cases_on ‘eval_to k x2’ \\ gvs []
    >- (
      qexists_tac ‘j1 + j2’
      \\ simp [])
    \\ Cases_on ‘eval_to (j1 + j2 + k) (Delay y)’
    \\ Cases_on ‘eval_to k y2’ \\ gvs []
    >- (
      gs [eval_to_def])
    \\ rename1 ‘eval_to _ x1 = INR v1’
    \\ rename1 ‘eval_to _ x2 = INR v2’
    \\ Cases_on ‘k = 0’ \\ gs []
    >- (
      Cases_on ‘dest_anyClosure v2’ \\ gs []
      >- (
        qexists_tac ‘j2’ \\ simp [eval_to_def]
        \\ reverse (Cases_on ‘v1’) \\ Cases_on ‘v2’ \\ gvs [dest_anyClosure_def]
        >- (
          gs [CaseEqs ["option", "exp"]])
        \\  qmatch_asmsub_abbrev_tac ‘LIST_REL _ f g’
        \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                   (ALOOKUP (REVERSE f) s) (ALOOKUP (REVERSE g) s)’
          suffices_by (rw [] \\ gs [OPTREL_def]
                       \\ qpat_x_assum `exp_rel _x _` mp_tac
                       \\ rw [Once exp_rel_cases] \\ gs [])
        \\ irule LIST_REL_OPTREL \\ gs []
        \\ irule LIST_REL_mono
        \\ first_assum (irule_at Any)
        \\ simp [ELIM_UNCURRY])
      \\ pairarg_tac \\ gvs []
      \\ qexists_tac ‘0’
      \\ Cases_on ‘eval_to 0 x1 = INL Diverge’ \\ gs []
      \\ drule_then (qspec_then ‘j2’ (assume_tac o GSYM)) eval_to_mono
      \\ gs [eval_to_def]
      \\ reverse (Cases_on ‘v1’) \\ Cases_on ‘v2’ \\ gs [dest_anyClosure_def]
      >- (
        gs [CaseEqs ["option", "exp"], EVERY_EL]
        \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
        \\ first_x_assum (drule_then strip_assume_tac) \\ gs [EL_MAP])
      \\ qmatch_asmsub_abbrev_tac ‘LIST_REL _ f g’ \\ gvs []
      \\ rename1 ‘ALOOKUP (REVERSE g) s1’
      \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                 (ALOOKUP (REVERSE f) s1) (ALOOKUP (REVERSE g) s1)’
        suffices_by (rw [] \\ gs [OPTREL_def]
                     \\ qpat_x_assum `exp_rel _x _` mp_tac
                     \\ rw [Once exp_rel_cases] \\ gs [])
      \\ irule LIST_REL_OPTREL \\ gs []
      \\ irule LIST_REL_mono
      \\ first_assum (irule_at Any)
      \\ simp [ELIM_UNCURRY])
    \\ simp [eval_to_def]
    \\ Cases_on ‘dest_anyClosure v2’ \\ gs []
    >- (
      Q.REFINE_EXISTS_TAC ‘j + j2’ \\ simp []
      \\ reverse (Cases_on ‘v1’) \\ Cases_on ‘v2’ \\ gvs [dest_anyClosure_def]
      >- (
        gs [CaseEqs ["option", "exp"], EVERY_EL])
      \\ qmatch_asmsub_abbrev_tac ‘LIST_REL _ f g’ \\ gvs []
      \\ rename1 ‘ALOOKUP (REVERSE g) s1’
      \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                 (ALOOKUP (REVERSE f) s1) (ALOOKUP (REVERSE g) s1)’
        suffices_by (rw [] \\ gs [OPTREL_def]
                     \\ qpat_x_assum `exp_rel _x _` mp_tac
                     \\ rw [Once exp_rel_cases] \\ gs [])
      \\ irule LIST_REL_OPTREL \\ gs []
      \\ irule LIST_REL_mono
      \\ first_assum (irule_at Any)
      \\ simp [ELIM_UNCURRY])
    \\ pairarg_tac \\ gvs []
    \\ Cases_on ‘dest_anyClosure v1’ \\ gs []
    >- (
      reverse (Cases_on ‘v1’) \\ Cases_on ‘v2’ \\ gvs [dest_anyClosure_def]
      >- (
        gs [CaseEqs ["option", "exp"], EVERY_EL]
        \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
        \\ gs [EL_MAP]
        \\ first_x_assum (drule_then strip_assume_tac) \\ gs [])
      \\ qmatch_asmsub_abbrev_tac ‘LIST_REL _ f g’ \\ gvs []
      \\ rename1 ‘ALOOKUP (REVERSE g) s1’
      \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                 (ALOOKUP (REVERSE f) s1) (ALOOKUP (REVERSE g) s1)’
        suffices_by (rw [] \\ gs [OPTREL_def]
                     \\ qpat_x_assum `exp_rel _x _` mp_tac
                     \\ rw [Once exp_rel_cases] \\ gs [])
      \\ irule LIST_REL_OPTREL \\ gs []
      \\ irule LIST_REL_mono
      \\ first_assum (irule_at Any)
      \\ simp [ELIM_UNCURRY])
    \\ rename1 ‘dest_anyClosure v1 = INR vv’
    \\ PairCases_on ‘vv’
    \\ qmatch_goalsub_abbrev_tac ‘eval_to (k - 1) (subst binds1 body1)’
    \\ qabbrev_tac ‘binds2 = vv2 ++ [vv0,Thunk (INR y)]’
    \\ qabbrev_tac ‘body2 = vv1’
    \\ ‘exp_rel (subst binds2 body2) (subst binds1 body1) ∧
        exp_inv (subst binds2 body2) ∧
        exp_ok (subst binds2 body2) ∧
        closed (subst binds2 body2)’
      by (unabbrev_all_tac
          \\ irule_at Any exp_rel_subst
          \\ irule_at Any exp_inv_subst
          \\ irule_at Any exp_ok_subst
          \\ gvs [closed_subst, eval_to_def]
          \\ Cases_on ‘v1’ \\ Cases_on ‘v2’
          \\ gvs [dest_anyClosure_def, v_rel_Thunk_def, v_ok_def]
          >- (
            irule_at Any thunk_rel_Thunk_Same \\ gs [])
          >- (
            irule_at Any thunk_rel_Thunk_Changed \\ gs []
            \\ first_assum (irule_at Any))
          \\ qmatch_asmsub_abbrev_tac ‘LIST_REL _ f g’ \\ gvs []
          \\ rename1 ‘ALOOKUP (REVERSE g) s1’
          \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                  (ALOOKUP (REVERSE f) s1) (ALOOKUP (REVERSE g) s1)’
            suffices_by (rw [] \\ gs [OPTREL_def]
                         \\ qpat_x_assum `exp_rel _x _` mp_tac
                         \\ rw [Once exp_rel_cases] \\ gs [])
          \\ irule LIST_REL_OPTREL \\ gs []
          \\ irule LIST_REL_mono
          \\ first_assum (irule_at Any)
          \\ simp [ELIM_UNCURRY])
    \\ unabbrev_all_tac
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ qmatch_asmsub_abbrev_tac ‘_ (eval_to _ e1) (eval_to _ e2)’
    \\ Cases_on ‘eval_to (j + k - 1) e1 = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (j + k) x1 = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘j’ \\ simp [])
      \\ ‘eval_to (j + k) x1 = eval_to (j2 + k) x1’
        by (drule_then (qspec_then ‘j + k + j2’ assume_tac) eval_to_mono
            \\ gs [])
      \\ qexists_tac ‘j’ \\ simp [])
    \\ drule_then (qspec_then ‘j2’ assume_tac) result_rel_mono_left
    \\ qexists_tac ‘j2 + j’ \\ gs [])
  >- ((* Lam *)
    rw [Once exp_rel_cases, Once exp_inv_cases]
    \\ fs [exp_inv_def, eval_to_def, v_ok_def, exp_ok_def])
  >- ((* Let NONE *)
    rw [Once exp_rel_cases]
    \\ gvs [exp_inv_def, exp_ok_def]
    \\ rename1 ‘exp_rel x1 x2’
    \\ rename1 ‘exp_rel y1 y2’
    \\ rw [eval_to_def]
    >- ((* k = 0 *)
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ rename1 ‘eval_to (j1 + k - 1) x1’
    \\ rename1 ‘eval_to (j2 + k - 1) y1’
    \\ Cases_on ‘eval_to (k - 1) x2 = INL Diverge’ \\ fs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs [])
    \\ ‘eval_to (j1 + k - 1) x1 ≠ INL Diverge’
      by (strip_tac
          \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
    \\ ‘∀j. eval_to (j + j1 + k - 1) x1 = eval_to (j1 + k - 1) x1’
      by (strip_tac
          \\ drule_then (qspec_then ‘j + j1 + k - 1’ assume_tac) eval_to_mono
          \\ gs [])
    \\ Cases_on ‘eval_to (j1 + k - 1) x1’ \\ gs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs [])
    \\ Cases_on ‘eval_to (k - 1) x2’ \\ gs []
    \\ Cases_on ‘eval_to (j2 + k - 1) y1 = INL Diverge’ \\ gs []
    >- (
      qexists_tac ‘j2’
      \\ Cases_on ‘eval_to (j2 + k - 1) x1’ \\ gs []
      \\ Cases_on ‘eval_to (j2 + k - 1) x1 = INL Diverge’ \\ gs []
      \\ ‘eval_to (j2 + k - 1) x1 ≠ INL Diverge’ by fs []
      \\ drule_then (qspec_then ‘j2 + (j1 + k) - 1’ assume_tac) eval_to_mono
      \\ gs [])
    \\ Q.REFINE_EXISTS_TAC ‘j + j1’ \\ simp []
    \\ drule_then (qspec_then ‘j1’ assume_tac) result_rel_mono_left
    \\ qexists_tac ‘j2’ \\ gs [])
  >- ((* Let SOME *)
    rw [Once exp_rel_cases])
  >- ((* If *)
    rw [Once exp_rel_cases] \\ fs [exp_inv_def, exp_ok_def]
    \\ rename1 ‘If x y z’
    \\ rw [eval_to_def] \\ gvs [exp_inv_def, exp_ok_def]
    >- ((* k = 0 *)
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ map_every rename1 [
      ‘eval_to (j1 + k - 1) x’,
      ‘eval_to (j2 + k - 1) y’,
      ‘eval_to (j3 + k - 1) z’]
    \\ Cases_on ‘eval_to (k - 1) x2 = INL Diverge’ \\ fs []
    >- (
      qexists_tac ‘j1’
      \\ Cases_on ‘eval_to (j1 + k - 1) x’ \\ gs [])
    \\ Cases_on ‘eval_to (k - 1) x2 = INL Type_error’ \\ fs []
    >- (
      qexists_tac ‘j1’ \\ simp []
      \\ Cases_on ‘eval_to (j1 + k - 1) x’ \\ gs [])
    \\ ‘∃res. eval_to (k - 1) x2 = INR res’
      by (Cases_on ‘eval_to (k - 1) x2’ \\ fs []
          \\ rename1 ‘eval_to (k - 1) x2 = INL err’
          \\ Cases_on ‘err’ \\ gs [])
    \\ ‘eval_to (j1 + k - 1) x ≠ INL Diverge’
      by (strip_tac \\ gs [])
    \\ qpat_x_assum ‘_ (eval_to _ x) (eval_to _ x2)’ assume_tac
    \\ drule_then assume_tac result_rel_mono_left \\ gs []
    \\ ‘∃res. eval_to (j1 + k - 1) x = INR res’
      by (pop_assum (qspec_then ‘0’ assume_tac)
          \\ Cases_on ‘eval_to (j1 + k - 1) x’ \\ gs [])
    \\ IF_CASES_TAC \\ gvs []
    >- ((* First branch taken *)
      Cases_on ‘eval_to (k - 1) y2 = INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (j2 + k - 1) y’ \\ gs []
        \\ Cases_on ‘eval_to (j2 + k - 1) x = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘j2’ \\ simp [])
        \\ ‘eval_to (j2 + k - 1) x = eval_to (j1 + k - 1) x’
          by (drule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono
              \\ ‘eval_to (j1 + k - 1) x ≠ INL Diverge’ by fs []
              \\ drule_then (qspec_then ‘j2 + k - 1’ assume_tac) eval_to_mono
              \\ Cases_on ‘j1 < j2’ \\ gs [])
        \\ qexists_tac ‘j2’ \\ simp [])
      \\ ‘eval_to (j2 + k - 1) y ≠ INL Diverge’
        by (strip_tac
            \\ Cases_on ‘eval_to (k - 1) y2’ \\ gs [])
      \\ qpat_x_assum ‘_ (_ _ y) (_ _ y2)’ assume_tac
      \\ drule_all_then (qspec_then ‘j1’ assume_tac) result_rel_mono_left
      \\ first_x_assum (qspec_then ‘j2’ assume_tac)
      \\ qexists_tac ‘j1 + j2’
      \\ Cases_on ‘eval_to (j1 + j2 + k - 1) x’ \\ gs [])
    \\ reverse IF_CASES_TAC \\ gvs []
    >- (
      qexists_tac ‘j1’ \\ simp []
      \\ IF_CASES_TAC \\ gs []
      \\ IF_CASES_TAC \\ gs [])
        (* Second branch taken *)
    \\ Cases_on ‘eval_to (k - 1) z2 = INL Diverge’ \\ gs []
    >- (
      Cases_on ‘eval_to (j3 + k - 1) z’ \\ gs []
      \\ Cases_on ‘eval_to (j3 + k - 1) x = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘j3’ \\ simp [])
      \\ ‘eval_to (j3 + k - 1) x = eval_to (j1 + k - 1) x’
        by (drule_then (qspec_then ‘j1 + k - 1’ assume_tac) eval_to_mono
            \\ ‘eval_to (j1 + k - 1) x ≠ INL Diverge’ by fs []
            \\ drule_then (qspec_then ‘j3 + k - 1’ assume_tac) eval_to_mono
            \\ Cases_on ‘j1 < j3’ \\ gs [])
      \\ qexists_tac ‘j3’ \\ simp [])
    \\ ‘eval_to (j3 + k - 1) z ≠ INL Diverge’
      by (strip_tac
          \\ Cases_on ‘eval_to (k - 1) z2’ \\ gs [])
    \\ qpat_x_assum ‘_ (_ _ z) (_ _ z2)’ assume_tac
    \\ drule_all_then (qspec_then ‘j1’ assume_tac) result_rel_mono_left
    \\ first_x_assum (qspec_then ‘j3’ assume_tac)
    \\ qexists_tac ‘j1 + j3’
    \\ Cases_on ‘eval_to (j1 + j3 + k - 1) x’ \\ gs [])
  >- ((* Letrec *)
    rw [Once exp_rel_cases]
    \\ rw [eval_to_def] \\ gvs [exp_inv_def, exp_ok_def]
    >- ((* k = 0 *)
      qexists_tac ‘0’
      \\ simp [])
    \\ first_x_assum (irule_at Any)
    \\ fs [subst_funs_def, closed_def, freevars_subst, freevars_def]
    \\ fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, SUBSET_DIFF_EMPTY,
           GSYM FST_THM]
    \\ irule_at Any exp_rel_subst
    \\ irule_at Any exp_ok_subst
    \\ gvs [MAP_MAP_o, combinTheory.o_DEF, EVERY2_MAP, LAMBDA_PROD,
            GSYM FST_THM]
    \\ irule_at Any LIST_EQ
    \\ simp [Once thunk_rel_def]
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
    rw [Once exp_rel_cases] \\ gvs [exp_inv_def, eval_to_def, v_rel_Thunk_Same,
                                    v_rel_Thunk_Changed, SF SFY_ss, v_ok_def,
                                    exp_ok_def])
  >- ((* Box *)
    rw [Once exp_rel_cases])
  >- ((* Force *)
    rw [Once exp_rel_cases]
    \\ rw [eval_to_def] \\ gs [exp_ok_def]
    \\ Cases_on ‘∃s i xs. x = Prim (Proj s i) xs’ \\ gvs [exp_inv_def]
    >- ((* Prim Proj *)
      qpat_x_assum ‘exp_rel (Prim _ _) _’ mp_tac
      \\ rw [Once exp_rel_cases]
      \\ gs [Once exp_inv_cases]
      \\ simp [eval_to_def]
      \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      >- ((* k = 0 *)
        qexists_tac ‘0’
        \\ simp [])
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”, exp_inv_def]
      \\ gs [exp_ok_def]
      \\ rename1 ‘exp_rel x y’
      \\ first_assum (qspec_then ‘[]’ mp_tac o CONV_RULE SWAP_FORALL_CONV)
      \\ simp_tac list_ss [subst_funs_def, subst_empty]
      \\ disch_then (drule_all_then (qx_choose_then ‘j’ assume_tac))
      \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      >- (
        qexists_tac ‘j’
        \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs [])
      \\ Cases_on ‘eval_to (j + k - 1) x’ \\ gs []
      \\ rename1 ‘v_rel v1 v2’
      \\ Cases_on ‘dest_Constructor v1’ \\ gs []
      >- (
        qexists_tac ‘j’
        \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs [v_rel_Thunk_def])
      \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs [LIST_REL_EL_EQN, v_rel_Thunk_def]
      \\ reverse IF_CASES_TAC \\ gvs []
      >- (
        qexists_tac ‘j’ \\ gs []
        \\ IF_CASES_TAC \\ gs [])
      \\ rename1 ‘LENGTH f = LENGTH g’
      \\ first_x_assum (drule_then (qx_choose_then ‘n’ assume_tac))
      \\ drule_all_then assume_tac exp_rel_exp_ok
      \\ drule_all_then assume_tac exp_ok_eval_to
      \\ gs [EVERY_EL]
      \\ rpt (first_x_assum (drule_all_then assume_tac)) \\ gvs []
      \\ ‘∀m. eval_to (m + j + k - 1) x = eval_to (j + k - 1) x’
        by (strip_tac \\ irule eval_to_mono \\ simp [])
      \\ Cases_on ‘dest_anyThunk (EL i f)’ \\ gs []
      >- (
        gs [Once thunk_rel_def, dest_anyThunk_def]
        \\ rename1 ‘LIST_REL _ f1 g1’
        \\ rename1 ‘ALOOKUP (REVERSE g1) n1’
        \\ gs [v_ok_def]
        \\ ‘MEM n1 (MAP FST f1)’
          by (gvs [EVERY_EL]
              \\ first_x_assum (drule_then assume_tac)
              \\ first_x_assum (drule_then assume_tac)
              \\ gs [v_ok_def])
        \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                   (ALOOKUP (REVERSE f1) n1)
                   (ALOOKUP (REVERSE g1) n1)’
          suffices_by (rw []
                       \\ gs [OPTREL_def, ALOOKUP_NONE, MAP_REVERSE]
                       \\ CASE_TAC \\ gs [CaseEq "exp"])
        \\ irule LIST_REL_OPTREL \\ gs []
        \\ irule LIST_REL_mono
        \\ first_assum (irule_at Any)
        \\ rw [ELIM_UNCURRY])
      \\ Cases_on ‘∃g1 n1. EL i g = Recclosure g1 n1’ \\ gs []
      >- (
        ‘MEM n1 (MAP FST g1)’
          by (gvs [EVERY_EL, v_ok_def]
              \\ first_x_assum (drule_then assume_tac)
              \\ first_x_assum (drule_then assume_tac)
              \\ gs [v_ok_def])
        \\ simp [dest_anyThunk_def]
        \\ Cases_on ‘ALOOKUP (REVERSE g1) n1’ \\ gs [ALOOKUP_NONE, MAP_REVERSE]
        \\ rename1 ‘ALOOKUP (REVERSE g1) n1 = SOME v1’
        \\ ‘∃x1. v1 = Delay x1’
          by (drule_then (qx_choose_then ‘f1’ mp_tac)
                (CONJUNCT1 thunk_rel_final)
              \\ rw [Once thunk_rel_def]
              \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
              \\ gvs [EVERY_EL, EL_MAP]
              \\ first_x_assum (drule_then strip_assume_tac) \\ gs [])
        \\ gvs [GSYM subst_funs_def]
        \\ Cases_on ‘∃f1 m1. EL i f = Recclosure f1 m1’ \\ gs []
        >- ((* Recclosure-Recclosure *)
          gvs [Once thunk_rel_def]
          \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                     (ALOOKUP (REVERSE f1) m1)
                     (ALOOKUP (REVERSE g1) m1)’
            by (irule LIST_REL_OPTREL \\ gs []
                \\ irule LIST_REL_mono
                \\ first_assum (irule_at Any)
                \\ rw [ELIM_UNCURRY])
          \\ gs [OPTREL_def]
          \\ Cases_on ‘eval_to (k - 1) (subst_funs g1 x1) = INL Diverge’
          >- (
            Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
            >- (
              qexists_tac ‘0’
              \\ simp [])
            \\ ‘∀m. eval_to (m + k - 1) x = eval_to (j + k - 1) x’
              by (rw []
                  \\ drule_then (qspec_then ‘m + k - 1’ assume_tac) eval_to_mono
                  \\ drule_then (qspec_then ‘j + k - 1’ assume_tac) eval_to_mono
                  \\ gs [])
            \\ simp []
            \\ CASE_TAC \\ gs []
            \\ ‘INL Diverge = eval_to (k - 1) (subst_funs g1 x1)’ by fs []
            \\ pop_assum SUBST1_TAC
            \\ first_x_assum (irule_at Any)
            \\ rw [subst_funs_def]
            >- (
              simp [closed_subst]
              \\ gvs [Once exp_rel_cases, LIST_REL_EL_EQN, ELIM_UNCURRY,
                      MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
              \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gvs []
              \\ first_x_assum (drule_then strip_assume_tac)
              \\ gs [freevars_def])
            >- (
              irule_at Any exp_inv_subst
              \\ gvs [Once exp_rel_cases, LIST_REL_EL_EQN, ELIM_UNCURRY,
                      MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP, thunk_inv_def,
                      EVERY_EL]
              \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gvs []
              \\ first_x_assum (drule_then strip_assume_tac)
              \\ gs [])
            >- (
              irule_at Any exp_ok_subst
              \\ gvs [Once exp_rel_cases, LIST_REL_EL_EQN, ELIM_UNCURRY,
                      MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP, v_ok_def,
                      EVERY_EL]
              \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gvs []
              \\ rw []
              \\ last_x_assum (drule_then assume_tac)
              \\ gs [v_ok_def, EVERY_EL, EL_MAP]
              \\ first_x_assum (drule_then assume_tac)
              \\ gvs [exp_ok_def]
              \\ qpat_x_assum ‘∀m. n < LENGTH g1 ⇒ _ ∧ _’
                (drule_then assume_tac)
              \\ gs []
              \\ pop_assum (SUBST1_TAC o SYM)
              \\ irule MEM_MAP_f
              \\ gs [MEM_EL]
              \\ irule_at Any EQ_REFL \\ gs [])
            >- (
              irule_at Any exp_rel_subst
              \\ gvs [Once exp_rel_cases, LIST_REL_EL_EQN, ELIM_UNCURRY,
                      MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP, EVERY_EL,
                      GSYM FST_THM, SF ETA_ss]
              \\ irule_at Any LIST_EQ
              \\ rw [EL_MAP, Once thunk_rel_def, EVERY_EL, LIST_REL_EL_EQN,
                     ELIM_UNCURRY]))
          \\ Q.REFINE_EXISTS_TAC ‘m + j’ \\ simp []
          \\ CASE_TAC \\ gs []
          \\ ‘exp_rel (subst_funs f1 e) (subst_funs g1 x1) ∧
              exp_inv (subst_funs f1 e) ∧
              exp_ok (subst_funs f1 e) ∧
              closed (subst_funs f1 e)’
            by (simp [subst_funs_def, closed_subst] \\ rw []
                >- (
                  irule_at Any exp_rel_subst
                  \\ gvs [Once exp_rel_cases, LIST_REL_EL_EQN, ELIM_UNCURRY,
                          MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP, EVERY_EL,
                          GSYM FST_THM, SF ETA_ss]
                  \\ irule_at Any LIST_EQ
                  \\ rw [EL_MAP, Once thunk_rel_def, EVERY_EL, LIST_REL_EL_EQN,
                         ELIM_UNCURRY])
                >- (
                  irule_at Any exp_inv_subst
                  \\ gvs [Once exp_rel_cases, LIST_REL_EL_EQN, ELIM_UNCURRY,
                          MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP, thunk_inv_def,
                          EVERY_EL]
                  \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gvs []
                  \\ first_x_assum (drule_then strip_assume_tac)
                  \\ gs [])
                >- (
                  irule_at Any exp_ok_subst
                  \\ qpat_x_assum ‘exp_rel (Delay _) _’ mp_tac
                  \\ gvs [Once exp_rel_cases, LIST_REL_EL_EQN, ELIM_UNCURRY,
                          MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP, v_ok_def,
                          EVERY_EL]
                  \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gvs []
                  \\ rw []
                  \\ last_x_assum (drule_then assume_tac)
                  \\ gs [v_ok_def, EVERY_EL, EL_MAP]
                  \\ first_x_assum (drule_then assume_tac)
                  \\ gvs [exp_ok_def]
                  \\ qpat_x_assum ‘∀m. n < LENGTH g1 ⇒ _ ∧ _’
                    (drule_then assume_tac)
                  \\ gs []
                  \\ pop_assum (SUBST1_TAC o SYM)
                  \\ irule MEM_MAP_f
                  \\ gs [MEM_EL]
                  \\ irule_at Any EQ_REFL \\ gs [])
                >- (
                  gvs [Once exp_rel_cases, LIST_REL_EL_EQN, ELIM_UNCURRY,
                          MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
                  \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL \\ gvs []
                  \\ first_x_assum (drule_then strip_assume_tac)
                  \\ gs [freevars_def]))
            \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
            \\ drule_then (qspec_then ‘j’ assume_tac) result_rel_mono_right
            \\ qexists_tac ‘j1’ \\ gs [])
            (* lhs is thunk *)
          \\ gvs [Once thunk_rel_def]
          \\ rename1 ‘thunk_rel n u _’
          \\ last_x_assum assume_tac
          \\ gvs [exp_inv_def, dest_anyThunk_def, v_ok_def, EVERY_EL]
          \\ Cases_on ‘eval_to (k - 1) (subst_funs g1 x1) = INL Diverge’
          >- (
            Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
            >- (
              qexists_tac ‘0’
              \\ simp [])
            \\ ‘∀m. eval_to (m + k - 1) x = eval_to (j + k - 1) x’
              by (rw []
                  \\ drule_then (qspec_then ‘m + k - 1’ assume_tac) eval_to_mono
                  \\ drule_then (qspec_then ‘j + k - 1’ assume_tac) eval_to_mono
                  \\ gs [])
            \\ simp [Once subst_funs_def]
          \\ ‘v_ok u’
            by (gs [EVERY_EL, v_ok_def]
                \\ last_x_assum (drule_then strip_assume_tac)
                \\ gs [v_ok_def, exp_ok_def])
          \\ pop_assum mp_tac
          \\ qpat_x_assum ‘thunk_inv _’ mp_tac
          \\ qpat_x_assum ‘thunk_rel _ _ _’ mp_tac
          \\ ntac 4 (last_x_assum kall_tac)
          \\ last_x_assum assume_tac
          \\ ntac 12 (last_x_assum kall_tac)
          \\ qid_spec_tac ‘u’
          \\ qid_spec_tac ‘n’
          \\ Induct
          >- (
            rw [Once thunk_rel_def]
            \\ gs [v_ok_def, thunk_inv_def, eval_to_def, dest_anyThunk_def]
            \\ CASE_TAC \\ gs [ALOOKUP_NONE, MAP_REVERSE]
            \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
            \\ gvs [EVERY_EL, EL_MAP]
            \\ first_x_assum (drule_then strip_assume_tac)
            \\ first_x_assum (drule_then strip_assume_tac)
            \\ gs []
            \\ Cases_on ‘k ≤ 1’ \\ gs []
            >- (
              qexists_tac ‘0’
              \\ simp [])
            \\ Q.REFINE_EXISTS_TAC ‘m + 1’ \\ simp []
            \\ once_rewrite_tac [arithmeticTheory.ADD_COMM]
            \\ qpat_x_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
            \\ last_x_assum (irule_at Any)
            \\ cheat)
          \\ rw [Once thunk_rel_def]
          \\ rw [eval_to_def, dest_anyThunk_def]
          \\ Cases_on ‘k ≤ 1’ \\ gs []
          >- (
            qexists_tac ‘0’
            \\ simp [])
          \\ simp [Once subst_funs_def]
          \\ Q.REFINE_EXISTS_TAC ‘m + 1’
          \\ simp []
          \\ once_rewrite_tac [arithmeticTheory.ADD_COMM]
          \\ first_x_assum (irule_at Any)
          \\ gs [thunk_inv_def, v_ok_def, exp_inv_def, exp_ok_def])
        \\ Q.REFINE_EXISTS_TAC ‘m + j’
        \\ simp [Once subst_funs_def]
        \\ ‘v_ok u’
          by (gs [EVERY_EL, v_ok_def]
              \\ last_x_assum (drule_then strip_assume_tac)
              \\ gs [v_ok_def, exp_ok_def])
        \\ pop_assum mp_tac
        \\ qpat_x_assum ‘thunk_inv _’ mp_tac
        \\ qpat_x_assum ‘thunk_rel _ _ _’ mp_tac
        \\ ntac 4 (last_x_assum kall_tac)
        \\ last_x_assum assume_tac
        \\ ntac 12 (last_x_assum kall_tac)
        \\ qid_spec_tac ‘u’
        \\ qid_spec_tac ‘n’
        \\ Induct
        >- (
          rw [Once thunk_rel_def]
          \\ gs [v_ok_def, thunk_inv_def, eval_to_def, dest_anyThunk_def]
          \\ CASE_TAC \\ gs [ALOOKUP_NONE, MAP_REVERSE]
          \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
          \\ gvs [EVERY_EL, EL_MAP]
          \\ first_x_assum (drule_then strip_assume_tac)
          \\ first_x_assum (drule_then strip_assume_tac)
          \\ gs []
          \\ Q.REFINE_EXISTS_TAC ‘m + 1’ \\ simp []
          \\ rename1 ‘subst_funs f1 y1’
          \\ ‘exp_rel (subst_funs f1 y1) (subst_funs g1 x1) ∧
              exp_inv (subst_funs f1 y1) ∧
              exp_ok (subst_funs f1 y1) ∧
              closed (subst_funs f1 y1)’
            by cheat
          \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
          \\ drule_then (qspec_then ‘j’ assume_tac) result_rel_mono_right
          \\ qexists_tac ‘j1’ \\ gs [])
        \\ rw [Once thunk_rel_def]
        \\ rw [eval_to_def, dest_anyThunk_def]
        \\ Q.REFINE_EXISTS_TAC ‘m + 1’
        \\ simp [Once subst_funs_def]
        \\ gs [thunk_inv_def, v_ok_def, exp_inv_def, exp_ok_def])
      \\ Cases_on ‘∃x1. EL i g = Thunk (INR x1)’ \\ gs []
      >- (
        simp [dest_anyThunk_def]
        \\ last_x_assum
          (qspec_then ‘[]’ assume_tac o CONV_RULE SWAP_FORALL_CONV)
        \\ gvs [subst_funs_def, Once thunk_rel_def]
        >- ((* lhs is the same thunk *)
          Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
          >- (
            Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
            >- (
              qexists_tac ‘0’
              \\ simp [])
            \\ ‘∀m. eval_to (m + k - 1) x = eval_to (j + k - 1) x’
              by (rw []
                  \\ drule_then (qspec_then ‘m + k - 1’ assume_tac) eval_to_mono
                  \\ drule_then (qspec_then ‘j + k - 1’ assume_tac) eval_to_mono
                  \\ gs [])
            \\ simp []
            \\ qpat_x_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
            \\ first_x_assum (irule_at Any)
            \\ gs [v_ok_def, EVERY_EL]
            \\ first_x_assum (drule_then assume_tac)
            \\ first_x_assum (drule_then assume_tac)
            \\ gs [v_ok_def])
          \\ Q.REFINE_EXISTS_TAC ‘m + j’ \\ simp []
          \\ rename1 ‘exp_rel x0 x1’
          \\ ‘exp_ok x0’
            by (gs [v_ok_def, EVERY_EL]
                \\ last_x_assum (drule_then assume_tac)
                \\ gs [v_ok_def])
          \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
          \\ drule_then (qspec_then ‘j’ assume_tac) result_rel_mono_right
          \\ qexists_tac ‘j1’ \\ gs [])
            (* lhs is another thunk *)
          \\ rename1 ‘thunk_rel n u _’
          \\ gvs [exp_inv_def, dest_anyThunk_def, v_ok_def, EVERY_EL]
          \\ Cases_on ‘eval_to (k - 1) x1 = INL Diverge’
          >- (
            Cases_on ‘eval_to (k - 1) x = INL Diverge’ \\ gs []
            >- (
              qexists_tac ‘0’
              \\ simp [])
            \\ ‘∀m. eval_to (m + k - 1) x = eval_to (j + k - 1) x’
              by (rw []
                  \\ drule_then (qspec_then ‘m + k - 1’ assume_tac) eval_to_mono
                  \\ drule_then (qspec_then ‘j + k - 1’ assume_tac) eval_to_mono
                  \\ gs [])
            \\ simp [Once subst_funs_def]
          \\ ‘v_ok u’
            by (gs [EVERY_EL, v_ok_def]
                \\ last_x_assum (drule_then strip_assume_tac)
                \\ gs [v_ok_def, exp_ok_def])
          \\ pop_assum mp_tac
          \\ qpat_x_assum ‘thunk_inv _’ mp_tac
          \\ qpat_x_assum ‘thunk_rel _ _ _’ mp_tac
          \\ ntac 4 (last_x_assum kall_tac)
          \\ last_x_assum assume_tac
          \\ ntac 10 (last_x_assum kall_tac)
          \\ qid_spec_tac ‘u’
          \\ qid_spec_tac ‘n’
          \\ Induct
          >- (
            rw [Once thunk_rel_def]
            \\ gs [v_ok_def, thunk_inv_def, eval_to_def, dest_anyThunk_def]
            \\ Cases_on ‘k ≤ 1’ \\ gs []
            >- (
              qexists_tac ‘0’
              \\ simp [])
            \\ Q.REFINE_EXISTS_TAC ‘m + 1’ \\ simp [subst_funs_def]
            \\ once_rewrite_tac [arithmeticTheory.ADD_COMM]
            \\ qpat_x_assum ‘_ = INL Diverge’ (SUBST1_TAC o SYM)
            \\ last_x_assum (irule_at Any) \\ gs [])
          \\ rw [Once thunk_rel_def]
          \\ rw [eval_to_def, dest_anyThunk_def]
          \\ Cases_on ‘k ≤ 1’ \\ gs []
          >- (
            qexists_tac ‘0’
            \\ simp [])
          \\ simp [Once subst_funs_def]
          \\ Q.REFINE_EXISTS_TAC ‘m + 1’ \\ simp []
          \\ once_rewrite_tac [arithmeticTheory.ADD_COMM]
          \\ first_x_assum (irule_at Any)
          \\ gs [thunk_inv_def, v_ok_def, exp_inv_def, exp_ok_def])
        \\ Q.REFINE_EXISTS_TAC ‘m + j’
        \\ simp [Once subst_funs_def]
        \\ ‘v_ok u’
          by (gs [EVERY_EL, v_ok_def]
              \\ last_x_assum (drule_then strip_assume_tac)
              \\ gs [v_ok_def, exp_ok_def])
        \\ pop_assum mp_tac
        \\ qpat_x_assum ‘thunk_inv _’ mp_tac
        \\ qpat_x_assum ‘thunk_rel _ _ _’ mp_tac
        \\ ntac 4 (last_x_assum kall_tac)
        \\ last_x_assum assume_tac
        \\ ntac 10 (last_x_assum kall_tac)
        \\ qid_spec_tac ‘u’
        \\ qid_spec_tac ‘n’
        \\ Induct
        >- (
          rw [Once thunk_rel_def]
          \\ gs [v_ok_def, thunk_inv_def, eval_to_def, dest_anyThunk_def]
          \\ Q.REFINE_EXISTS_TAC ‘m + 1’ \\ simp [subst_funs_def]
          \\ first_x_assum (drule_all_then (qx_choose_then ‘j1’ assume_tac))
          \\ drule_then (qspec_then ‘j’ assume_tac) result_rel_mono_right
          \\ qexists_tac ‘j1’ \\ gs [])
        \\ rw [Once thunk_rel_def]
        \\ rw [eval_to_def, dest_anyThunk_def]
        \\ Q.REFINE_EXISTS_TAC ‘m + 1’
        \\ simp [Once subst_funs_def]
        \\ gs [thunk_inv_def, v_ok_def, exp_inv_def, exp_ok_def])
      \\ ‘F’ suffices_by rw []
      \\ drule_then strip_assume_tac thunk_rel_is_thunky
      \\ Cases_on ‘EL i f’ \\ Cases_on ‘EL i g’ \\ gs [dest_anyThunk_def]
      \\ rename1 ‘ss ≠ INR _’
      \\ Cases_on ‘ss’ \\ gs [])
    \\ rename1 ‘exp_rel x y’
    \\ first_x_assum (drule_then assume_tac) \\ gs []
    \\ Cases_on ‘eval_to k y’ \\ fs []
    >- (
      qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k) x’ \\ gs [])
    \\ Cases_on ‘eval_to (j + k) x’ \\ gs []
    \\ rename1 ‘v_rel v1 v2’
    \\ Cases_on ‘∃z. v2 = Thunk (INR z)’ \\ gvs []
    >- ((* rhs is thunk *)
      Cases_on ‘v1’ \\ gs []
      \\ rename1 ‘v_rel (Thunk s1) _’ \\ Cases_on ‘s1’ \\ gs []
      \\ gvs [v_rel_Thunk_def, v_ok_def]
      >- ((* Thunk - Thunk *)
        Cases_on ‘k = 0’ \\ gs []
        >- (
          qexists_tac ‘0’
          \\ Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
          >- (
            simp [dest_anyThunk_def])
          \\ ‘eval_to 0 x = eval_to j x’
            by (once_rewrite_tac [EQ_SYM_EQ]
                \\ irule eval_to_mono
                \\ simp [])
          \\ simp [dest_anyThunk_def])
        \\ first_x_assum
          (qspec_then ‘[]’ assume_tac o CONV_RULE SWAP_FORALL_CONV)
        \\ gs [subst_funs_def]
        \\ first_x_assum (drule_all_then strip_assume_tac)
        \\ rename1 ‘_ (eval_to (j1 + k - 1) z1)’
        \\ Cases_on ‘eval_to (j1 + k - 1) z1 = INL Diverge’ \\ gs []
        >- (
          Cases_on ‘eval_to (j1 + k) x = INL Diverge’ \\ gs []
          >- (
            qexists_tac ‘j1’
            \\ simp [dest_anyThunk_def])
          \\ ‘eval_to (j1 + k) x = eval_to (j + k) x’
            by (drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
                \\ ‘eval_to (j + k) x ≠ INL Diverge’ by fs []
                \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
                \\ Cases_on ‘j ≤ j1’ \\ gs [])
          \\ qexists_tac ‘j1’
          \\ simp [dest_anyThunk_def])
        \\ drule_all_then (qspec_then ‘j’ assume_tac) result_rel_mono_left
        \\ ‘eval_to (j1 + j + k) x = eval_to (j + k) x’
          by (irule eval_to_mono
              \\ simp [])
        \\ qexists_tac ‘j1 + j’
        \\ gs [dest_anyThunk_def])
      \\ Cases_on ‘k = 0’ \\ simp []
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
        >- (
          simp [dest_anyThunk_def])
        \\ ‘eval_to 0 x = eval_to j x’
          by (once_rewrite_tac [EQ_SYM_EQ]
              \\ irule eval_to_mono
              \\ simp [])
        \\ simp [dest_anyThunk_def])
      \\ ‘∀m. eval_to (m + j + k) x = eval_to (j + k) x’
        by (strip_tac
            \\ irule eval_to_mono
            \\ simp [])
      \\ first_x_assum (qspec_then ‘[]’ assume_tac o CONV_RULE SWAP_FORALL_CONV)
      \\ gs [dest_anyThunk_def, subst_funs_def]
      \\ Cases_on ‘eval_to (k - 1) z = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
        \\ ‘eval_to k x = eval_to (j + k) x’
          by (once_rewrite_tac [EQ_SYM_EQ]
              \\ irule eval_to_mono
              \\ simp [])
        \\ gs [exp_inv_def]
        \\ ntac 5 (last_x_assum kall_tac)
        \\ gs [exp_ok_def]
        \\ map_every (fn tm => qpat_x_assum tm kall_tac) [
          ‘eval_to k y = _’,
          ‘eval_to (j + k) x = _’,
          ‘∀m. eval_to _ _ = _’,
          ‘eval_to k x = _’ ]
        \\ qpat_x_assum ‘v_ok v’ mp_tac
        \\ qpat_x_assum ‘thunk_rel _ _ _’ mp_tac
        \\ qpat_x_assum  ‘thunk_inv v’ mp_tac
        \\ qid_spec_tac ‘v’
        \\ Induct_on ‘n’
        >- (
          rw [Once thunk_rel_def]
          \\ gs [exp_inv_def, v_ok_def]
          \\ first_x_assum (drule_all_then strip_assume_tac)
          \\ gs [eval_to_def, dest_anyThunk_def, subst_funs_def]
          \\ IF_CASES_TAC \\ gs []
          \\ rename1 ‘eval_to (j + k - 1) x’
          \\ Cases_on ‘eval_to (k - 2) x = INL Diverge’ \\ gs []
          \\ drule_then (qspec_then ‘k - 2 + j + 1’ assume_tac) eval_to_mono
          \\ gs [])
        \\ rw [Once thunk_rel_def]
        \\ fs [thunk_inv_def, exp_inv_def, v_ok_def, exp_ok_def]
        \\ first_x_assum (drule_all_then assume_tac)
        \\ simp [eval_to_def, dest_anyThunk_def]
        \\ IF_CASES_TAC \\ gs [subst_funs_def]
        \\ Cases_on ‘eval_to (k - 2) (Force (Value u)) = INL Diverge’ \\ gs []
        \\ drule_then (qspec_then ‘k - 1’ assume_tac) eval_to_mono \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘m + j’
      \\ gs [exp_inv_def, exp_ok_def]
      \\ ntac 5 (last_x_assum kall_tac)
      \\ map_every (fn tm => qpat_x_assum tm kall_tac) [
        ‘eval_to k y = _’,
        ‘eval_to (j + k) x = _’,
        ‘∀m. eval_to _ _ = _’ ]
      \\ qpat_x_assum ‘v_ok v’ mp_tac
      \\ qpat_x_assum ‘thunk_rel _ _ _’ mp_tac
      \\ qpat_x_assum ‘thunk_inv v’ mp_tac
      \\ qid_spec_tac ‘v’
      \\ Induct_on ‘n’
      >- (
        rw [Once thunk_rel_def]
        \\ gs [exp_inv_def, v_ok_def, exp_ok_def]
        \\ first_x_assum (drule_all_then strip_assume_tac)
        \\ gs [eval_to_def, dest_anyThunk_def, subst_funs_def]
        \\ rename1 ‘eval_to (j1 + k - 1) x’
        \\ qexists_tac ‘j1 + 1’ \\ gs []
        \\ ‘eval_to (j1 + k - 1) x ≠ INL Diverge’
          by (strip_tac
              \\ Cases_on ‘eval_to (k - 1) z’ \\ gs [])
        \\ dxrule_then (qspec_then ‘j’ assume_tac) result_rel_mono_left
        \\ gs [])
      \\ rw [Once thunk_rel_def]
      \\ fs [thunk_inv_def, exp_inv_def, exp_ok_def, v_ok_def]
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ simp [eval_to_def, dest_anyThunk_def]
      \\ qexists_tac ‘m + 1’ \\ gs [subst_funs_def])
    \\ Cases_on ‘∃g n. v2 = Recclosure g n’ \\ gvs []
    >- ((* Recclosure - Recclosure *)
      rename1 ‘LIST_REL _ f g’
      \\ Cases_on ‘dest_anyThunk (Recclosure g n)’ \\ gs []
      >- (
        qexists_tac ‘j’
        \\ gs [dest_anyThunk_def]
        \\ rename1 ‘ALOOKUP (REVERSE f) s’
        \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                   (ALOOKUP (REVERSE f) s) (ALOOKUP (REVERSE g) s)’
          suffices_by (rw [] \\ gs [OPTREL_def]
                       \\ qpat_x_assum `exp_rel _x _` mp_tac
                       \\ rw [Once exp_rel_cases] \\ gs [])
        \\ irule LIST_REL_OPTREL \\ gs []
        \\ irule LIST_REL_mono
        \\ first_assum (irule_at Any)
        \\ simp [ELIM_UNCURRY])
      \\ Cases_on ‘k = 0’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
        >- (
          gvs [dest_anyThunk_def, CaseEqs ["option", "exp"]])
        \\ ‘eval_to 0 x = eval_to j x’
          by (once_rewrite_tac [EQ_SYM_EQ]
              \\ irule eval_to_mono
              \\ simp [])
        \\ gs []
        \\ pairarg_tac \\ gvs [dest_anyThunk_def, CaseEqs ["option", "exp"]]
        \\ qmatch_asmsub_rename_tac ‘ALOOKUP (REVERSE g) s’
        >- (
          ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                     (ALOOKUP (REVERSE f) s) (ALOOKUP (REVERSE g) s)’
            suffices_by (rw [] \\ gs [OPTREL_def]
                         \\ qpat_x_assum `exp_rel _x _` mp_tac
                         \\ rw [Once exp_rel_cases] \\ gs [])
          \\ irule LIST_REL_OPTREL \\ gs []
          \\ irule LIST_REL_mono
          \\ first_assum (irule_at Any)
          \\ simp [ELIM_UNCURRY])
        \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
        \\ gvs [EVERY_EL, LIST_REL_EL_EQN]
        \\ first_x_assum (drule_then strip_assume_tac)
        \\ gs [ELIM_UNCURRY])
      \\ reverse (gvs [dest_anyThunk_def, CaseEqs ["option", "exp"]])
      >- (
        drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
        \\ gvs [LIST_REL_EL_EQN]
        \\ first_x_assum (drule_then strip_assume_tac)
        \\ gvs [ELIM_UNCURRY])
      \\ qmatch_asmsub_rename_tac ‘ALOOKUP (REVERSE g) s’
      \\ ‘OPTREL (λ_x _y. is_delay _x ∧ is_delay _y ∧ exp_rel _x _y)
                 (ALOOKUP (REVERSE f) s) (ALOOKUP (REVERSE g) s)’
        by (irule LIST_REL_OPTREL \\ gs []
            \\ irule LIST_REL_mono
            \\ first_assum (irule_at Any)
            \\ simp [ELIM_UNCURRY])
      \\ gs [OPTREL_def]
      \\ ‘∀m. eval_to (m + j + k) x = eval_to (j + k) x’
        by (strip_tac
            \\ irule eval_to_mono \\ simp [])
      \\ Cases_on ‘_x’ \\ gs []
      \\ rename1 ‘exp_rel (Delay x1) (Delay x2)’
      \\ ‘exp_rel (subst_funs f x1) (subst_funs g x2) ∧
          exp_inv (subst_funs f x1) ∧
          exp_ok (subst_funs f x1) ∧
          closed (subst_funs f x1)’
        by (simp [subst_funs_def, closed_subst]
            \\ irule_at Any exp_rel_subst
            \\ irule_at Any exp_inv_subst
            \\ irule_at Any exp_ok_subst
            \\ simp [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                     GSYM FST_THM]
            \\ simp [Once thunk_rel_def, EVERY_EL, EL_MAP]
            \\ irule_at Any LIST_EQ
            \\ irule_at Any LIST_REL_mono
            \\ first_assum (irule_at Any)
            \\ gvs [LIST_REL_EL_EQN, ELIM_UNCURRY, Once exp_rel_cases,
                    EVERY_EL, EL_MAP, SF SFY_ss] \\ rw []
            >- (
              first_x_assum (drule_then strip_assume_tac)
              \\ Cases_on ‘SND (EL n g)’ \\ gs [])
            >- (
              drule_all_then assume_tac exp_ok_eval_to
              \\ gs [v_ok_def, exp_ok_def, MEM_MAP, EXISTS_PROD, EL_MEM]
              \\ rw [MEM_EL]
              \\ first_assum (irule_at Any)
              \\ Cases_on ‘EL n f’ \\ gs []
              \\ first_x_assum drule \\ gs [])
            \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
            \\ gvs [LIST_REL_EL_EQN, EVERY_EL]
            \\ rpt (first_x_assum (drule_then strip_assume_tac))
            \\ gvs [EL_MAP, freevars_def, v_ok_def, EVERY_EL, EL_MAP]
            \\ last_x_assum (drule_then assume_tac)
            \\ gs [exp_ok_def])
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ rename1 ‘_ (eval_to (j1 + k - 1) (subst_funs f x1))’
      \\ Cases_on ‘eval_to (j1 + k - 1) (subst_funs f x1) =
                   INL Diverge’ \\ gs []
      >- (
        Cases_on ‘eval_to (j1 + k) x = INL Diverge’ \\ gs []
        >- (
          qexists_tac ‘j1’
          \\ simp [dest_anyThunk_def])
        \\ ‘eval_to (j1 + k) x = eval_to (j + k) x’
          by (drule_then (qspec_then ‘j + k’ assume_tac) eval_to_mono
              \\ ‘eval_to (j + k) x ≠ INL Diverge’ by fs []
              \\ drule_then (qspec_then ‘j1 + k’ assume_tac) eval_to_mono
              \\ Cases_on ‘j ≤ j1’ \\ gs [])
        \\ qexists_tac ‘j1’
        \\ simp [dest_anyThunk_def])
      \\ drule_all_then (qspec_then ‘j’ assume_tac) result_rel_mono_left
      \\ ‘eval_to (j1 + j + k) x = eval_to (j + k) x’
        by (irule eval_to_mono
            \\ simp [])
      \\ qexists_tac ‘j1 + j’
      \\ gs [dest_anyThunk_def])
    >- ((* rhs is recclosure *)
      Cases_on ‘dest_anyThunk (Recclosure g n)’ \\ gs []
      >- (
        ‘F’ suffices_by rw []
        \\ drule_all_then assume_tac exp_rel_exp_ok
        \\ drule_all_then assume_tac exp_ok_eval_to
        \\ ‘MEM n (MAP FST g)’ by gs [v_ok_def]
        \\ Cases_on ‘ALOOKUP (REVERSE g) n’ \\ gs []
        >- (
          gs [ALOOKUP_NONE, MAP_REVERSE])
        \\ ‘∃f. thunk_rel 0 (Recclosure f n) (Recclosure g n)’
          by (qpat_x_assum ‘thunk_rel _ _ _’ mp_tac
              \\ rename1 ‘thunk_rel i w _’
              \\ map_every qid_spec_tac [‘n’, ‘g’, ‘w’, ‘i’]
              \\ Induct \\ rw []
              >- (
                gs [Once thunk_rel_def]
                \\ rw [Once thunk_rel_def]
                \\ first_assum (irule_at Any))
              \\ rw []
              \\ pop_assum mp_tac
              \\ rw [Once thunk_rel_def]
              \\ first_x_assum (drule_then (irule_at Any)))
        \\ gs [Once thunk_rel_def]
        \\ drule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
        \\ gvs [LIST_REL_EL_EQN]
        \\ first_x_assum (drule_then assume_tac)
        \\ gvs [ELIM_UNCURRY, dest_anyThunk_def, CaseEq "exp"])
      \\ pairarg_tac \\ gvs []
      \\ CASE_TAC \\ gs []
      >- (
        gs [dest_anyThunk_def, CaseEqs ["option", "exp"]])
      \\ Cases_on ‘k = 0’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to 0 x = INL Diverge’ \\ gs []
        \\ ‘eval_to 0 x = eval_to j x’
          by (once_rewrite_tac [EQ_SYM_EQ]
              \\ irule eval_to_mono
              \\ simp [])
        \\ gvs [dest_anyThunk_def, CaseEqs ["option", "exp"]])
      \\ ‘∀m. eval_to (m + j + k) x = eval_to (j + k) x’
        by (strip_tac
            \\ irule eval_to_mono
            \\ simp [])
      \\ rename1 ‘INR (INR x2, g1)’
      \\ Cases_on ‘eval_to (k - 1) (subst_funs g1 x2) = INL Diverge’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘eval_to k x = INL Diverge’ \\ gs []
        \\ ‘eval_to k x = eval_to (j + k) x’
          by (once_rewrite_tac [EQ_SYM_EQ]
              \\ irule eval_to_mono
              \\ simp [])
        \\ gs [exp_inv_def]
        \\ last_x_assum assume_tac
        \\ ntac 5 (last_x_assum kall_tac)
        \\ gs [v_ok_def, exp_ok_def]
        \\ map_every (fn tm => qpat_x_assum tm kall_tac) [
            ‘eval_to k y = _’,
            ‘eval_to (j + k) x = _’,
            ‘∀m. eval_to _ _ = _’,
            ‘eval_to k x = _’ ]
        \\ qpat_x_assum ‘v_ok w’ mp_tac
        \\ qpat_x_assum ‘thunk_rel _ _ _’ mp_tac
        \\ qpat_x_assum ‘thunk_inv _’ mp_tac
        \\ rename1 ‘thunk_rel m w’
        \\ qid_spec_tac ‘w’
        \\ Induct_on ‘m’
        >- (
          rw [Once thunk_rel_def]
          \\ gs [exp_inv_def]
          \\ ‘OPTREL (λ_x _y. exp_rel _x _y ∧ is_delay _x ∧ is_delay _y)
                     (ALOOKUP (REVERSE f) n)
                     (ALOOKUP (REVERSE g) n)’
            by (irule LIST_REL_OPTREL \\ gs []
                \\ irule LIST_REL_mono
                \\ first_assum (irule_at Any)
                \\ simp [ELIM_UNCURRY])
          \\ gs [dest_anyThunk_def]
          \\ simp [Once subst_funs_def, eval_to_def, dest_anyThunk_def]
          \\ gvs [OPTREL_def, CaseEq "exp"]
          \\ CASE_TAC \\ gs []
          \\ IF_CASES_TAC \\ gs []
          \\ rename1 ‘exp_rel (Delay x1) (Delay x2)’
          \\ ‘exp_rel (subst_funs f x1) (subst_funs g x2) ∧
              exp_inv (subst_funs f x1) ∧
              exp_ok (subst_funs f x1) ∧
              closed (subst_funs f x1)’
            by (simp [subst_funs_def, closed_subst, MAP_MAP_o, LAMBDA_PROD,
                      combinTheory.o_DEF, GSYM FST_THM]
                \\ irule_at Any exp_rel_subst
                \\ irule_at Any exp_inv_subst
                \\ irule_at Any exp_ok_subst
                \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                         EVERY2_MAP, EVERY_MAP, EVERY_MEM, FORALL_PROD,
                         Once thunk_rel_def, GSYM FST_THM]
                \\ irule_at Any LIST_REL_mono
                \\ first_assum (irule_at Any)
                \\ simp [ELIM_UNCURRY]
                \\ irule_at Any LIST_EQ
                \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
                \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY]
                \\ first_x_assum (drule_then strip_assume_tac)
                \\ qpat_x_assum ‘exp_rel (Delay x1) _’ mp_tac
                \\ rw [Once exp_rel_cases] \\ gs [freevars_def]
                >- (
                  gs [v_ok_def, MEM_MAP, EXISTS_PROD, SF SFY_ss])
                \\ gvs [EVERY_EL, EVERY_MAP, v_ok_def]
                \\ first_x_assum (drule_then strip_assume_tac)
                \\ first_x_assum (drule_then strip_assume_tac)
                \\ gs [exp_ok_def])
          \\ first_x_assum (drule_all_then strip_assume_tac)
          \\ rename1 ‘eval_to (j + k - 1) (subst_funs f x1)’
          \\ Cases_on ‘eval_to (k - 2) (subst_funs f x1) = INL Diverge’ \\ gs []
          \\ drule_then (qspec_then ‘k - 2 + j + 1’ assume_tac) eval_to_mono
          \\ gs [])
        \\ rw [Once thunk_rel_def]
        \\ fs [thunk_inv_def, exp_inv_def, v_ok_def, exp_ok_def]
        \\ first_x_assum (drule_all_then assume_tac)
        \\ simp [dest_anyThunk_def, subst_funs_def]
        \\ simp [eval_to_def]
        \\ pop_assum mp_tac
        \\ gs [eval_to_def, dest_anyThunk_def]
        \\ gs [subst_funs_def]
        \\ IF_CASES_TAC \\ gs []
        \\ Cases_on ‘eval_to (k - 2) (Force (Value u)) = INL Diverge’ \\ gs []
        \\ drule_then (qspec_then ‘k - 1’ assume_tac) eval_to_mono \\ gs [])
      \\ Q.REFINE_EXISTS_TAC ‘m + j’
      \\ gs [exp_inv_def]
      \\ last_x_assum assume_tac
      \\ ntac 5 (last_x_assum kall_tac)
      \\ gs [v_ok_def, exp_ok_def]
      \\ map_every (fn tm => qpat_x_assum tm kall_tac) [
          ‘eval_to k y = _’,
          ‘eval_to (j + k) x = _’,
          ‘∀m. eval_to _ _ = _’ ]
      \\ qpat_x_assum ‘v_ok w’ mp_tac
      \\ qpat_x_assum ‘thunk_rel _ _ _’ mp_tac
      \\ qpat_x_assum ‘thunk_inv v’ mp_tac
      \\ rename1 ‘thunk_rel m w’
      \\ qid_spec_tac ‘w’
      \\ Induct_on ‘m’
      >- (
        rw [Once thunk_rel_def]
        \\ gs [exp_inv_def]
        \\ ‘OPTREL (λ_x _y. exp_rel _x _y ∧ is_delay _x ∧ is_delay _y)
                   (ALOOKUP (REVERSE f) n)
                   (ALOOKUP (REVERSE g) n)’
          by (irule LIST_REL_OPTREL \\ gs []
              \\ irule LIST_REL_mono
              \\ first_assum (irule_at Any)
              \\ simp [ELIM_UNCURRY])
        \\ gs [dest_anyThunk_def]
        \\ simp [Once subst_funs_def, eval_to_def, dest_anyThunk_def]
        \\ gvs [OPTREL_def, CaseEq "exp"]
        \\ CASE_TAC \\ gs []
        \\ rename1 ‘exp_rel (Delay x1) (Delay x2)’
        \\ ‘exp_rel (subst_funs f x1) (subst_funs g x2) ∧
            exp_inv (subst_funs f x1) ∧
            exp_ok (subst_funs f x1) ∧
            closed (subst_funs f x1)’
          by (simp [subst_funs_def, closed_subst, MAP_MAP_o, LAMBDA_PROD,
                    combinTheory.o_DEF, GSYM FST_THM]
              \\ irule_at Any exp_rel_subst
              \\ irule_at Any exp_inv_subst
              \\ irule_at Any exp_ok_subst
              \\ simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
                       EVERY2_MAP, EVERY_MAP, EVERY_MEM, FORALL_PROD,
                       Once thunk_rel_def, GSYM FST_THM]
              \\ irule_at Any LIST_REL_mono
              \\ first_assum (irule_at Any)
              \\ simp [ELIM_UNCURRY]
              \\ irule_at Any LIST_EQ
              \\ dxrule_then strip_assume_tac ALOOKUP_SOME_REVERSE_EL
              \\ gvs [LIST_REL_EL_EQN, EL_MAP, ELIM_UNCURRY] \\ rw []
              >- (
                gs [v_ok_def, MEM_MAP, EXISTS_PROD, SF SFY_ss])
              \\ first_x_assum (drule_then strip_assume_tac)
              \\ qpat_x_assum ‘exp_rel (Delay x1) _’ mp_tac
              \\ rw [Once exp_rel_cases] \\ gs [freevars_def]
              \\ gvs [v_ok_def, EVERY_EL, EVERY_MAP, MEM_MAP, EXISTS_PROD,
                      SF SFY_ss]
              \\ rw []
              \\ first_x_assum (drule_then strip_assume_tac) \\ gs [exp_ok_def]
              \\ first_x_assum (drule_then strip_assume_tac) \\ gs [])
        \\ first_x_assum (drule_all_then strip_assume_tac)
        \\ rename1 ‘eval_to (j1 + k - 1) (subst_funs f x1)’
        \\ qexists_tac ‘j1 + 1’ \\ simp []
        \\ ‘eval_to (j1 + k - 1) (subst_funs f x1) ≠ INL Diverge’
          by (strip_tac
              \\ Cases_on ‘eval_to (k - 1) (subst_funs g x2)’ \\ gs [])
        \\ dxrule_then (qspec_then ‘j’ assume_tac) result_rel_mono_left
        \\ gs [])
      \\ rw [Once thunk_rel_def]
      \\ fs [thunk_inv_def, exp_inv_def, exp_ok_def, v_ok_def]
      \\ first_x_assum (drule_all_then (qx_choose_then ‘m1’ assume_tac))
      \\ simp [dest_anyThunk_def, subst_funs_def]
      \\ simp [eval_to_def]
      \\ pop_assum mp_tac
      \\ rw [eval_to_def, dest_anyThunk_def]
      \\ gs [subst_funs_def]
      \\ qexists_tac ‘m1 + 1’ \\ simp [])
    \\ Cases_on ‘dest_anyThunk v2’ \\ gs []
    >- (
      qexists_tac ‘j’
      \\ gs [dest_anyThunk_def]
      \\ Cases_on ‘v2’ \\ gs [])
    \\ Cases_on ‘v2’ \\ gvs [dest_anyThunk_def]
    \\ Cases_on ‘v1’ \\ gvs [v_rel_Thunk_def]
    \\ rename1 ‘ss ≠ INR _’
    \\ Cases_on ‘ss’ \\ gs [])
  >- ((* Prim *)
    rw [Once exp_rel_cases]
    \\ gvs [exp_inv_def, eval_to_def, MEM_EL, PULL_EXISTS, LIST_REL_EL_EQN]
    \\ ‘∀n. n < LENGTH xs ⇒ closed (EL n xs)’
      by gvs [closed_def, freevars_def, LIST_TO_SET_EQ_SING, EVERY_MAP,
              EVERY_EL]
    \\ Cases_on ‘op’ \\ gs [exp_ok_def]
    >- ((* Cons *)
      gvs [exp_inv_def, EL_MAP, map_MAP, combinTheory.o_DEF]
      \\ simp [eval_to_def]
      \\ rename1 ‘LENGTH xs = LENGTH ys’
      \\ Cases_on ‘map (λx. INR (Thunk (INR x)): err + v) xs’ \\ gs []
      >- (
        gs [map_INL])
      \\ rename1 ‘map _ xs = INR vs’ \\ gs []
      \\ Cases_on ‘map (λx. eval_to k x) ys’ \\ gs []
      >- (
        drule_then assume_tac map_LENGTH
        \\ dxrule_then assume_tac map_INR \\ gs []
        \\ gs [map_INL]
        \\ rpt (first_x_assum (drule_all_then assume_tac))
        \\ gvs [Once exp_rel_cases, eval_to_def])
      \\ imp_res_tac map_LENGTH
      \\ dxrule_then assume_tac map_INR \\ gs []
      \\ dxrule_then assume_tac map_INR \\ gs []
      \\ gs [v_ok_def, EVERY_MAP, exp_ok_def, SF ETA_ss]
      \\ gs [LIST_REL_EL_EQN, EVERY_EL] \\ rw []
      \\ rpt (first_x_assum (drule_all_then strip_assume_tac))
      \\ gs [eval_to_def]
      \\ qpat_x_assum ‘_ = EL n vs’ (assume_tac o SYM)
      \\ gs [v_rel_Thunk_def]
      >- (
        rw [Once exp_rel_cases])
      >- (
        qpat_x_assum ‘exp_rel _ (EL n ys)’ mp_tac
        \\ rw [Once exp_rel_cases] \\ gvs []
        \\ irule_at Any thunk_rel_Thunk_Changed \\ gs []
        \\ first_assum (irule_at Any))
      \\ first_x_assum drule
      \\ rw [EQ_SYM_EQ] \\ gs [v_ok_def])
    >- ((* IsEq *)
      IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      >- ((* k = 0 *)
        qexists_tac ‘0’
        \\ simp [])
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “n < 1 ⇔ n = 0”, exp_inv_def]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ qexists_tac ‘j’
      \\ Cases_on ‘eval_to (j + k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) y’ \\ gs []
      \\ rename1 ‘v_rel v1 v2’
      \\ Cases_on ‘dest_Constructor v1’ \\ fs []
      >- (
        Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs [v_rel_Thunk_def])
      \\ pairarg_tac \\ gvs []
      \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs [LIST_REL_EL_EQN, v_rel_Thunk_def]
      \\ IF_CASES_TAC \\ gs [v_ok_def])
    >- ((* Proj *)
      gvs [Once exp_inv_cases])
    >- ((* AtomOp *)
      Cases_on ‘k = 0’ \\ gs []
      >- (
        qexists_tac ‘0’
        \\ Cases_on ‘xs = []’ \\ gs []
        >- (
          simp [map_def]
          \\ CASE_TAC \\ gs []
          \\ CASE_TAC \\ gs [v_ok_def])
        \\ ‘ys ≠ []’ by (strip_tac \\ gs [])
        \\ simp [GSYM (SIMP_CONV (srw_ss()) [combinTheory.K_DEF]
                                            “K (INL Diverge)”),
                 map_K_INL])
      \\ cheat (* TODO map again *)))
QED

val _ = export_theory ();

