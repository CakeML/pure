(*
  Some useful theorems about the thunkLang_subst syntax and semantics.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     thunkLang_primitivesTheory;
open pure_miscTheory;

val _ = new_theory "thunk_substProps";

val _ = numLib.prefer_num ();

Theorem exp_size_lemma:
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

Theorem exp_ind:
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

(* TODO move to pure_misc? *)
Theorem LIST_REL_FILTER:
  ∀xs ys.
    LIST_REL R xs ys ⇒
    MAP FST xs = MAP FST ys ⇒
      LIST_REL R (FILTER (λ(x,y). P x) xs)  (FILTER (λ(x,y). P x) ys)
Proof
  ho_match_mp_tac LIST_REL_ind \\ rw [] \\ fs [ELIM_UNCURRY]
QED

(* TODO move to pure_misc? *)
Theorem LIST_REL_OPTREL:
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

(* TODO pure_misc? *)
Theorem MAP_FST_FILTER:
  MAP FST (FILTER (λ(a,b). P a) xs) = FILTER P (MAP FST xs)
Proof
  irule LIST_EQ
  \\ rw [EL_MAP, FILTER_MAP, combinTheory.o_DEF, LAMBDA_PROD]
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

Theorem LIST_TO_SET_FILTER_DIFF[local]:
  set (FILTER P l) = set l DIFF {x | ¬P x}
Proof
  rw [LIST_TO_SET_FILTER, DIFF_DEF, INTER_DEF, EXTENSION, CONJ_COMM]
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

Theorem closed_simps[simp]:
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

(* TODO pure_misc? *)
Theorem ALOOKUP_SOME_REVERSE_EL:
  ALOOKUP (REVERSE l) k = SOME v ⇒ ∃n. n < LENGTH l ∧ EL n l = (k, v)
Proof
  strip_tac
  \\ dxrule_then strip_assume_tac ALOOKUP_SOME_EL
  \\ gvs [EL_REVERSE]
  \\ qmatch_asmsub_abbrev_tac ‘EL m l’
  \\ first_assum (irule_at (Pos (el 2)))
  \\ gs [Abbr ‘m’]
QED

val _ = export_theory ();

