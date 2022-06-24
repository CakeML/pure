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
[~swap:]
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

Theorem letrec_binds_refl:
  ∀x. letrec_binds b1 b2 x x
Proof
  ho_match_mp_tac freevars_ind
  \\ rw [] \\ simp [Once letrec_binds_cases]
  >- (Induct_on ‘es’ \\ fs [])
  \\ disj2_tac
  \\ Induct_on ‘lcs’ \\ fs [FORALL_PROD,SF DNF_ss]
  \\ rw [] \\ res_tac \\ fs []
QED

Triviality LIST_REL_opp:
  ∀xs ys. LIST_REL R xs ys ⇒ LIST_REL (λx y. R y x) ys xs
Proof
  Induct \\ fs [PULL_EXISTS]
QED

Theorem letrec_binds_opp:
  letrec_binds binds2 binds1 = (λx y. letrec_binds binds1 binds2 y x)
Proof
  qsuff_tac ‘∀b2 b1 x y. letrec_binds b2 b1 x y ⇒ letrec_binds b1 b2 y x’
  >- (rw [FUN_EQ_THM] \\ eq_tac \\ fs [])
  \\ ho_match_mp_tac letrec_binds_ind \\ rw []
  \\ simp [Once letrec_binds_cases]
  \\ imp_res_tac LIST_REL_opp \\ fs [SF ETA_ss]
QED

Theorem eval_forward_letrec_binds:
  ALL_DISTINCT (MAP FST binds2) ∧
  MAP FST binds1 = MAP FST binds2 ∧
  EVERY (λe. freevars e ⊆ set (MAP FST binds1)) (MAP SND binds1) ∧
  EVERY (λe. freevars e ⊆ set (MAP FST binds2)) (MAP SND binds2) ∧
  LIST_REL
     (λ(v1,e1) (v2,e2). v1 = v2 ∧ (Letrec binds2 e1 ≃ Letrec binds2 e2) b)
     binds1 binds2 ⇒
  eval_forward b (letrec_binds binds1 binds2)
Proof
  rpt strip_tac
  \\ fs [eval_forward_def]
  \\ ho_match_mp_tac eval_wh_to_ind
  \\ rpt strip_tac
  >~ [‘letrec_binds _ _ (Var v)’] >- fs [eval_wh_to_def]
  >~ [‘letrec_binds _ _ (Lam v x)’] >-
   (fs [eval_wh_to_def]
    \\ qpat_x_assum ‘letrec_binds _ _ _ _’ mp_tac
    \\ simp [Once letrec_binds_cases] \\ strip_tac \\ gvs []
    \\ fs [eval_wh_Lam] \\ rw []
    \\ cheat)
  >~ [‘letrec_binds _ _ (App e1 e2y)’] >- cheat
  >~ [‘letrec_binds _ _ (Prim p xs)’] >- cheat
  >~ [‘letrec_binds _ _ (Letrec bs x)’]
  \\ qpat_x_assum ‘letrec_binds _ _ _ _’ mp_tac
  \\ simp [Once letrec_binds_cases]
  \\ reverse strip_tac \\ gvs []
  >- cheat (* boring case *)
  \\ rw [eval_wh_to_def] \\ gvs []
  \\ rename [‘letrec_binds b1 b2’]
  \\ fs [eval_wh_Letrec]
  \\ last_x_assum irule \\ fs []
  \\ conj_tac >-
   (fs [subst_funs_def] \\ irule IMP_closed_bind
    \\ fs [SUBSET_DEF,FDOM_FUPDATE_LIST,MAP_MAP_o,
           combinTheory.o_DEF,UNCURRY,SF ETA_ss])
  \\ ‘(Letrec b2 y ≃ subst_funs b2 y) b’ by
   (irule eval_IMP_app_bisimilarity
    \\ fs [eval_Letrec] \\ cheat)
  \\ ‘∀e. (e ≃ e2) b ⇔ (e ≃ subst_funs b2 y) b’ by
    metis_tac [app_bisimilarity_trans,app_bisimilarity_sym]
  \\ fs []
  \\ simp [subst_funs_def,bind_def]
  \\ reverse IF_CASES_TAC >- cheat
  \\ reverse IF_CASES_TAC >- cheat
  \\ qexists_tac ‘subst (FEMPTY |++ MAP (λ(g,x). (g,Letrec b2 x)) b1) y’
  \\ cheat
QED

Theorem exp_eq_Letrec_change_lemma[local]:
  ∀binds1 binds2 e b.
    ALL_DISTINCT (MAP FST binds1) ∧
    MAP FST binds1 = MAP FST binds2 ∧
    closed (Letrec binds1 e) ∧ closed (Letrec binds2 e) ∧
    LIST_REL (λ(v1, e1) (v2, e2).
      v1 = v2 ∧ (Letrec binds1 e1 ≃ Letrec binds1 e2) b) binds1 binds2 ∧
    LIST_REL (λ(v1, e1) (v2, e2).
      v1 = v2 ∧ (Letrec binds2 e1 ≃ Letrec binds2 e2) b) binds1 binds2
    ⇒
    (Letrec binds1 e ≃ Letrec binds2 e) b
Proof
  rw [] \\ irule eval_forward_imp_bisim \\ fs []
  \\ qexists_tac ‘letrec_binds binds1 binds2’
  \\ conj_tac
  >- (irule letrec_binds_swap \\ fs [letrec_binds_refl])
  \\ fs [GSYM letrec_binds_opp]
  \\ irule_at Any eval_forward_letrec_binds
  \\ irule_at Any eval_forward_letrec_binds
  \\ fs []
  \\ pop_assum kall_tac
  \\ drule LIST_REL_opp \\ fs []
  \\ fs [UNCURRY,LAMBDA_PROD]
  \\ match_mp_tac LIST_REL_mono
  \\ fs [FORALL_PROD]
  \\ metis_tac [app_bisimilarity_sym]
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
  rw [exp_eq_def]
  \\ ‘closed (bind f (Letrec binds1 e)) ∧
      closed (bind f (Letrec binds2 e))’ by
   (rw [] \\ irule pure_exp_lemmasTheory.IMP_closed_bind \\ fs [])
  \\ rw [bind_def] \\ fs [subst_def,bind_def] \\ fs [SF SFY_ss]
  \\ irule exp_eq_Letrec_change_lemma
  \\ gs [MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,GSYM FST_LAM]
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
