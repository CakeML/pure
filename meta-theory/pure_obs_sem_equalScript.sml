(*
   This file proves that bisimilar (≃) expressions lead to equal (=)
   observational semantics:

       ∀x y. x ≃ y ⇒ semantics x [] = semantics y []

*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite io_treeTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_exp_relTheory pure_semanticsTheory;

val _ = new_theory "pure_obs_sem_equal";

Triviality eval_wh_Cons:
  wh_Constructor n es = eval_wh x ∧ x ≃ y ⇒
  ∃es1. eval_wh y = wh_Constructor n es1 ∧ LIST_REL (≃) es es1
Proof
  fs [Once app_bisimilarity_iff]
  \\ Cases_on ‘eval_wh x’ \\ fs []
  \\ rw [] \\ gvs []
  \\ cheat
QED

Theorem next_lemma[local]:
  ∀a res1.
    next a res1 ⇒
    ∀x xs y ys.
      a = (eval_wh x,xs) ∧ x ≃ y ∧ LIST_REL (≃) xs ys ⇒
      ∃res2. next (eval_wh y,ys) res2 ∧
             (res1 ≠ res2 ⇒
                ∃a new1 new2. res1 = Act a new1 ∧
                              res2 = Act a new2 ∧
                              LIST_REL (≃) new1 new2)
Proof
  ho_match_mp_tac next_ind \\ rw [] \\ fs [PULL_EXISTS]
  THEN1
   (qsuff_tac ‘∃e1. eval_wh y = wh_Constructor "Act" [e1] ∧ eval_wh e1 = wh_Atom a’
    THEN1 (rw [] \\ simp [Once next_cases] \\ strip_tac \\ gvs [])
    \\ drule_all eval_wh_Cons \\ rw [] \\ fs []
    \\ fs [Once app_bisimilarity_iff])
  THEN1
   (qsuff_tac ‘∃m1 f1. eval_wh y = wh_Constructor "Bind" [m1;f1] ∧
                       m ≃ m1 ∧ f ≃ f1’
    THEN1 (rw [] \\ simp [Once next_cases]
           \\ first_x_assum irule \\ fs []
           \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ cheat)
  THEN1
   (qsuff_tac ‘eval_wh y = wh_Diverge’
    THEN1 (simp [Once next_cases])
    \\ cheat)
  \\ cheat
QED

Theorem next_lemma_alt[local] =
  next_lemma |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO];

Theorem next_det:
  ∀x1 r1 r2. next x1 r1 ∧ next x1 r2 ==> r1 = r2
Proof
  qsuff_tac ‘∀x1 r1. next x1 r1 ⇒ ∀r2. next x1 r2 ==> r1 = r2’
  THEN1 (rw [] \\ res_tac \\ fs [])
  \\ ho_match_mp_tac next_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once next_cases] \\ strip_tac \\ gvs []
QED

Theorem symmetric_LIST_REL:
  ∀xs ys R. symmetric R ∧ LIST_REL R xs ys ⇒ LIST_REL R ys xs
Proof
  Induct \\ fs [PULL_EXISTS] \\ rw [symmetric_def]
QED

Theorem bisimilarity_IMP_semantics_eq:
  ∀x y. x ≃ y ⇒ semantics x [] = semantics y []
Proof
  cheat (*
  qsuff_tac ‘∀x y xs ys. x ≃ y ∧ LIST_REL (≃) xs ys ⇒
                         semantics x xs = semantics y ys’
  THEN1 (rw [] \\ first_x_assum match_mp_tac)
  \\ fs [io_el_eqv] \\ fs [PULL_FORALL] \\ rpt gen_tac
  \\ EVERY (map qid_spec_tac [‘ys’,‘xs’,‘y’,‘x’])
  \\ completeInduct_on ‘LENGTH path’ \\ rw [] \\ fs [PULL_FORALL]
  \\ fs [semantics_def]
  \\ once_rewrite_tac [interp_def]
  \\ qsuff_tac ‘
    next_action (eval_wh x,xs) = next_action (eval_wh y,ys) ∨
    ∃a new1 new2.
      next_action (eval_wh x,xs) = Act a new1 ∧
      next_action (eval_wh y,ys) = Act a new2 ∧
      LIST_REL (≃) new1 new2’
  THEN1
   (strip_tac \\ fs []
    \\ Cases_on ‘path’ \\ fs [io_el_def]
    \\ ‘wh_Constructor "Ret" [Lit h] = eval_wh (Ret (Lit h))’ by fs [eval_wh_Cons]
    \\ fs [] \\ first_x_assum irule \\ fs []
    \\ match_mp_tac reflexive_app_bisimilarity \\ fs [])
  \\ qpat_x_assum ‘∀x. _’ kall_tac
  \\ fs [next_action_def]
  \\ Cases_on ‘∃res. next (eval_wh x,xs) res’ \\ fs []
  THEN1
   (drule_all next_lemma_alt \\ strip_tac
    \\ ‘∀r. next (eval_wh x,xs) r ⇔ r = res’ by metis_tac [next_det]
    \\ ‘∀r. next (eval_wh y,ys) r ⇔ r = res2’ by metis_tac [next_det]
    \\ fs [] \\ metis_tac [])
  \\ Cases_on ‘∃res. next (eval_wh y,ys) res’ \\ fs []
  \\ drule next_lemma_alt
  \\ disch_then (qspecl_then [‘x’,‘xs’] mp_tac)
  \\ reverse impl_tac THEN1 (rw [] \\ fs [])
  \\ assume_tac symmetric_app_bisimilarity
  \\ drule_all symmetric_LIST_REL \\ fs []
  \\ fs [symmetric_def] *)
QED

val _ = export_theory();
