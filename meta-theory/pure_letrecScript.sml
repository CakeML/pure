(*
   Proof of an equivalence for Letrec
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory pure_congruenceTheory;

val _ = new_theory "pure_letrec";

Inductive letrec_binds:
  (* swap *)
  (∀b1 b2 x y.
    letrec_binds b1 b2 x y ⇒
    letrec_binds b1 b2 (Letrec b1 x) (Letrec b2 y)) ∧
  (* cases below are just recursion *)
  (∀b1 b2 n.
    letrec_binds b1 b2 (Var n) (Var n))
  ∧
  (∀b1 b2 n x y.
    letrec_binds b1 b2 x y ⇒
    letrec_binds b1 b2 (Lam n x) (Lam n y))
  ∧
  (∀b1 b2 f g x y.
    letrec_binds b1 b2 f g ∧ letrec_binds b1 b2 x y ⇒
    letrec_binds b1 b2 (App f x) (App g y))
  ∧
  (∀b1 b2 n xs ys.
    LIST_REL (letrec_binds b1 b2) xs ys ⇒
    letrec_binds b1 b2 (Prim n xs) (Prim n ys))
  ∧
  (∀b1 b2  xs ys x y.
    LIST_REL (letrec_binds b1 b2) (MAP SND xs) (MAP SND ys) ∧
    MAP FST xs = MAP FST ys ∧ letrec_binds b1 b2 x y ⇒
    letrec_binds b1 b2 (Letrec xs x) (Letrec ys y))
End

Theorem exp_eq_Letrec_change_lemma[local]:
  ∀binds1 binds2 e b.
    ALL_DISTINCT (MAP FST binds1) ∧
    MAP FST binds1 = MAP FST binds2 ∧
    LIST_REL (λ(v1, e1) (v2, e2).
      v1 = v2 ∧ (Letrec binds1 e1 ≃ Letrec binds1 e2) b) binds1 binds2 ∧
    LIST_REL (λ(v1, e1) (v2, e2).
      v1 = v2 ∧ (Letrec binds2 e1 ≃ Letrec binds2 e2) b) binds1 binds2
    ⇒
    (Letrec binds1 e ≃ Letrec binds2 e) b
Proof
  cheat
QED

Triviality FST_LAM:
  FST = λ(p1,p2). p1
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Triviality LIST_REL_MAP_CONG:
  ∀xs ys R Q f.
    (∀x y. R x y ∧ MEM x xs ∧ MEM y ys ⇒ Q (f x) (f y)) ∧ LIST_REL R xs ys ⇒
    LIST_REL Q (MAP f xs) (MAP f ys)
Proof
  Induct \\ fs [PULL_EXISTS] \\ metis_tac []
QED

Theorem exp_eq_Letrec_change:
  ∀binds1 binds2 e b.
    ALL_DISTINCT (MAP FST binds1) ∧
    MAP FST binds1 = MAP FST binds2 ∧
    LIST_REL (λ(v1, e1) (v2, e2).
      v1 = v2 ∧ (Letrec binds1 e1 ≅? Letrec binds1 e2) b) binds1 binds2 ∧
    LIST_REL (λ(v1, e1) (v2, e2).
      v1 = v2 ∧ (Letrec binds2 e1 ≅? Letrec binds2 e2) b) binds1 binds2
    ⇒
    (Letrec binds1 e ≅? Letrec binds2 e) b
Proof
  rw [exp_eq_def,bind_def] \\ rw [] \\ fs [subst_def]
  \\ irule exp_eq_Letrec_change_lemma
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,GSYM FST_LAM]
  \\ conj_tac
  >-
   (irule LIST_REL_MAP_CONG \\ fs []
    \\ last_x_assum $ irule_at Any \\ fs [FORALL_PROD]
    \\ rpt strip_tac
    \\ first_x_assum $ qspec_then ‘f’ mp_tac
    \\ asm_rewrite_tac []
    \\ disch_then irule
    \\ fs [SUBSET_DEF] \\ rw [] \\ fs [SF DNF_ss]
    \\ gvs [MEM_MAP,PULL_EXISTS,FORALL_PROD,UNCURRY]
    \\ res_tac
    \\ PairCases_on ‘y’ \\ fs []
    \\ res_tac)
  >-
   (irule LIST_REL_MAP_CONG \\ fs []
    \\ first_x_assum $ irule_at Any \\ fs [FORALL_PROD]
    \\ rpt strip_tac
    \\ first_x_assum $ qspec_then ‘f’ mp_tac
    \\ asm_rewrite_tac []
    \\ disch_then irule
    \\ fs [SUBSET_DEF] \\ rw [] \\ fs [SF DNF_ss]
    \\ gvs [MEM_MAP,PULL_EXISTS,FORALL_PROD,UNCURRY]
    \\ res_tac
    \\ PairCases_on ‘y’ \\ fs []
    \\ res_tac)
QED

val _ = export_theory();
