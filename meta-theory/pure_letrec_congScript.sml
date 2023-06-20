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

val _ = new_theory "pure_letrec_cong";

Inductive letrec_binds:
[~swap:]
  (∀b1 b2 x y.
    MAP FST b1 = MAP FST b2 ∧
    EVERY (λe. freevars e ⊆ set (MAP FST b1)) (MAP SND b1) ∧
    EVERY (λe. freevars e ⊆ set (MAP FST b2)) (MAP SND b2) ∧
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

Triviality LIST_REL_opp: (* TODO: move *)
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

Theorem letrec_binds_freevars:
  ∀b1 b2 x y. letrec_binds b1 b2 x y ⇒ freevars x = freevars y
Proof
  Induct_on ‘letrec_binds’ \\ rw [] \\ gvs []
  >- (fs [EXTENSION,EVERY_MEM,MEM_MAP,PULL_EXISTS,EXISTS_PROD,FORALL_PROD,SUBSET_DEF]
      \\ metis_tac [])
  >- (pop_assum mp_tac
      \\ qid_spec_tac ‘xs’
      \\ qid_spec_tac ‘ys’
      \\ Induct \\ Cases_on ‘xs’ \\ fs [])
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘xs’
  \\ qid_spec_tac ‘ys’
  \\ Induct \\ fs []
  \\ fs [PULL_EXISTS]
  \\ strip_tac \\ Cases \\ fs []
  \\ strip_tac \\ res_tac \\ fs [UNCURRY]
  \\ gvs [EXTENSION]
  \\ metis_tac []
QED

Theorem subst_exp_eq:
  ∀y m1 m2 b.
    FDOM m1 = FDOM m2 ∧
    (∀k v1 v2. FLOOKUP m1 k = SOME v1 ∧ FLOOKUP m2 k = SOME v2 ⇒ (v1 ≃ v2) b) ⇒
    (subst m1 y ≅? subst m2 y) b
Proof
  ho_match_mp_tac freevars_ind \\ rw []
  >-
   (fs [subst_def] \\ rpt CASE_TAC
    \\ fs [exp_eq_refl]
    \\ res_tac \\ fs [app_bisimilarity_eq]
    \\ gvs [FLOOKUP_DEF])
  >-
   (fs [subst_def,SF ETA_ss]
    \\ irule exp_eq_Prim_cong
    \\ last_x_assum mp_tac
    \\ qid_spec_tac ‘es’ \\ Induct
    \\ fs [SF DNF_ss]
    \\ metis_tac [])
  >-
   (fs [subst_def,SF ETA_ss]
    \\ irule exp_eq_App_cong
    \\ metis_tac [])
  >-
   (fs [subst_def,SF ETA_ss]
    \\ irule exp_eq_Lam_cong
    \\ last_x_assum irule
    \\ fs [DOMSUB_FLOOKUP_THM,AllCaseEqs()]
    \\ rw [] \\ res_tac \\ fs [])
  \\ fs [subst_def,SF ETA_ss]
  \\ irule exp_eq_Letrec_cong
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
  \\ first_x_assum $ irule_at Any
  \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF]
  \\ rw [] \\ res_tac \\ fs []
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘m2’
  \\ qid_spec_tac ‘m1’
  \\ qid_spec_tac ‘lcs’
  \\ Induct
  \\ fs [SF DNF_ss,FORALL_PROD]
  \\ rw []
  >-
   (pop_assum kall_tac
    \\ first_x_assum irule
    \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF]
    \\ metis_tac [])
  \\ rewrite_tac [GSYM finite_mapTheory.FDIFF_FDOMSUB_INSERT]
  \\ first_x_assum irule
  \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF]
  \\ fs [DOMSUB_FLOOKUP_THM,AllCaseEqs()]
  \\ metis_tac []
QED

Triviality MAP_ID: (* TODO: move *)
  ∀xs f. (MAP f xs = xs) ⇔ ∀x. MEM x xs ⇒ f x = x
Proof
  Induct \\ fs [] \\ metis_tac []
QED

Theorem subst_letrec_binds:
  ∀b1 b2 x y m1 m2.
    letrec_binds b1 b2 x y ∧
    FDOM m1 = FDOM m2 ∧
    (∀k v1 v2.
      FLOOKUP m1 k = SOME v1 ∧ FLOOKUP m2 k = SOME v2 ⇒
      letrec_binds b1 b2 v1 v2) ⇒
    letrec_binds b1 b2 (subst m1 x) (subst m2 y)
Proof
  Induct_on ‘letrec_binds’ \\ rw []
  >-
   (fs [subst_def]
    \\ simp [Once letrec_binds_cases]
    \\ disj1_tac
    \\ fs [MAP_ID,FORALL_PROD]
    \\ reverse (rw [])
    >-
     (last_x_assum irule \\ fs [FDOM_FDIFF,EXTENSION,SUBSET_DEF]
      \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF]
      \\ rw [] \\ res_tac \\ fs []
      \\ metis_tac [])
    \\ irule pure_exp_lemmasTheory.subst_ignore
    \\ CCONTR_TAC \\ gvs [IN_DISJOINT,EVERY_MEM,SUBSET_DEF]
    \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS] \\ metis_tac [])
  >-
   (fs [subst_def] \\ rpt CASE_TAC \\ fs [letrec_binds_refl]
    \\ res_tac \\ fs [] \\ gvs [FLOOKUP_DEF])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_binds_cases]
    \\ last_x_assum irule \\ fs []
    \\ fs [DOMSUB_FLOOKUP_THM,AllCaseEqs()]
    \\ rw [] \\ res_tac \\ fs [SUBSET_DEF])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_binds_cases]
    \\ rpt $ last_x_assum $ irule_at Any \\ fs [])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_binds_cases,SF ETA_ss]
    \\ last_x_assum mp_tac \\ fs []
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ rw [] \\ metis_tac [])
  >-
   (fs [subst_def]
    \\ simp [Once letrec_binds_cases] \\ disj2_tac
    \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
    \\ reverse conj_tac
    >-
     (last_x_assum irule
      \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF,SUBSET_DEF]
      \\ rw [] \\ res_tac \\ fs [])
    \\ last_x_assum mp_tac
    \\ last_x_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘m2’
    \\ qid_spec_tac ‘m1’
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ fs [PULL_EXISTS]
    \\ strip_tac \\ Cases \\ fs []
    \\ rw []
    >-
     (first_x_assum irule
      \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF,SUBSET_DEF]
      \\ rw [] \\ res_tac \\ fs [])
    \\ rewrite_tac [GSYM finite_mapTheory.FDIFF_FDOMSUB_INSERT]
    \\ first_x_assum irule
    \\ fs [FDOM_FDIFF,EXTENSION,FLOOKUP_FDIFF]
    \\ fs [DOMSUB_FLOOKUP_THM,AllCaseEqs(),SUBSET_DEF]
    \\ rw [] \\ res_tac \\ fs [])
QED

Triviality FDOM_UPDATES_EQ:
  ∀b1. FDOM (FEMPTY |++ MAP (λ(g,x). (g,Letrec b2 x)) b1) = set (MAP FST b1)
Proof
  fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
QED

Triviality FORALL_FRANGE: (* TODO: move *)
  (∀v. v ∈ FRANGE m ⇒ P v) ⇔ ∀k v. FLOOKUP m k = SOME v ⇒ P v
Proof
  fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS]
QED

Triviality MEM_IMP_EQ: (* TODO: move *)
  ∀b1 k p1 p2.
    MEM (k,p1) b1 ∧ MEM (k,p2) b1 ∧ ALL_DISTINCT (MAP FST b1) ⇒ p1 = p2
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ fs [MEM_MAP,EXISTS_PROD]
  \\ res_tac \\ fs []
QED

Triviality EVERY_FLOOKUP_closed_lemma:
  EVERY (λe. freevars e ⊆ set (MAP FST ys)) (MAP SND ys) ⇒
  (∀n v.
     FLOOKUP (FEMPTY |++ MAP (λ(g,x). (g,Letrec ys x)) ys) n = SOME v ⇒
     closed v)
Proof
  fs [alistTheory.flookup_fupdate_list,AllCaseEqs()]
  \\ rw [] \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP,EXISTS_PROD,EVERY_MEM,PULL_EXISTS]
  \\ res_tac \\ fs []
QED

Triviality FORALL_FRANGE: (* TODO: move *)
  (∀x. x IN FRANGE v ⇒ p x) ⇔ ∀k x. FLOOKUP v k = SOME x ⇒ p x
Proof
  fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS]
QED

Theorem ALOOKUP_REVERSE_LIST_REL:
  ∀bs ys.
    LIST_REL p (MAP SND bs) (MAP SND ys) ∧
    MAP FST ys = MAP FST bs ∧
    ALOOKUP (REVERSE (MAP (λ(g,x). (g,f x)) bs)) k' = SOME v1 ∧
    ALOOKUP (REVERSE (MAP (λ(g,x). (g,h x)) ys)) k' = SOME v2 ⇒
    ∃x y. p x y ∧ v1 = f x ∧ v2 = h y ∧ MEM x (MAP SND bs) ∧ MEM y (MAP SND ys)
Proof
  Induct using SNOC_INDUCT \\ fs [PULL_EXISTS]
  \\ Cases \\ Cases using SNOC_CASES
  \\ gvs [GSYM REVERSE_APPEND,MAP_SNOC,LIST_REL_SNOC,REVERSE_SNOC]
  \\ rename [‘SND hh’] \\ PairCases_on ‘hh’ \\ fs []
  \\ fs [AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
  \\ metis_tac []
QED

Theorem MEM_LIST_REL: (* TODO: move *)
  ∀xs ys P y. LIST_REL P xs ys ∧ MEM y ys ⇒ ∃x. MEM x xs ∧ P x y
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ metis_tac []
QED

Theorem MEM_LIST_REL1: (* TODO: move *)
  ∀xs ys P x. LIST_REL P xs ys ∧ MEM x xs ⇒ ∃y. MEM y ys ∧ P x y
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ metis_tac []
QED

Theorem LIST_REL_COMP: (* TODO: move *)
  ∀xs ys zs.
    LIST_REL f xs ys ∧ LIST_REL g ys zs ⇒
    LIST_REL (λx z. ∃y. f x y ∧ g y z) xs zs
Proof
  Induct \\ fs [PULL_EXISTS]
  \\ metis_tac []
QED

Triviality eval_wh_Constructor_NIL_bisim =
  eval_wh_Constructor_bisim |> Q.GEN ‘xs’ |> Q.SPEC ‘[]’ |> SIMP_RULE (srw_ss()) [];

Triviality LIST_REL_IMP_MAP_EQ: (* TODO: move *)
  ∀xs ys P f g.
    (∀x y. MEM x xs ∧ MEM y ys ∧ P x y ⇒ f x = g y) ⇒
    LIST_REL P xs ys ⇒ MAP g ys = MAP f xs
Proof
  Induct \\ fs [PULL_EXISTS,SF DNF_ss] \\ metis_tac []
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
    \\ ‘eval_wh (Lam v y) = wh_Closure v y’ by fs [eval_wh_Lam]
    \\ drule_all eval_wh_Closure_bisim
    \\ strip_tac \\ fs []
    \\ rw [] \\ first_x_assum drule
    \\ disch_then $ irule_at Any
    \\ irule_at Any subst_letrec_binds
    \\ fs [FLOOKUP_UPDATE])
  >~ [‘letrec_binds _ _ (App e1 e2y)’] >-
   (fs [eval_wh_to_def]
    \\ qpat_x_assum ‘letrec_binds _ _ _ _’ mp_tac
    \\ simp [Once letrec_binds_cases] \\ strip_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k e1)’ \\ fs []
    >-
     (first_x_assum drule
      \\ imp_res_tac letrec_binds_freevars
      \\ ‘(g ≃ g) b ∧ closed g’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule_all
      \\ rw [] \\ fs []
      \\ ‘eval_wh g ≠ wh_Diverge ∧ dest_wh_Closure (eval_wh g) = NONE’ by
        (every_case_tac \\ fs [])
      \\ irule eval_wh_Error_bisim
      \\ first_x_assum $ irule_at Any
      \\ fs [eval_wh_App])
    \\ PairCases_on ‘x’ \\ fs []
    \\ rw [] \\ gvs []
    \\ Cases_on ‘eval_wh_to k e1’ \\ gvs [dest_wh_Closure_def]
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac letrec_binds_freevars
    \\ ‘(g ≃ g) b ∧ closed g’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule_all
    \\ strip_tac \\ fs []
    \\ rename [‘eval_wh g = wh_Closure v1 e1’]
    \\ first_x_assum $ qspec_then ‘e2y’ mp_tac
    \\ imp_res_tac letrec_binds_freevars
    \\ ‘closed y’ by fs [closed_def]
    \\ disch_then drule_all \\ strip_tac \\ gvs []
    \\ fs [bind_def,FLOOKUP_DEF]
    \\ first_x_assum drule
    \\ disch_then irule
    \\ irule_at Any IMP_closed_subst
    \\ fs [FRANGE_DEF]
    \\ irule_at Any pure_eval_lemmasTheory.eval_wh_Closure_closed
    \\ drule eval_wh_to_IMP_eval_wh \\ fs [] \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos last \\ fs []
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ irule_at Any IMP_closed_subst
    \\ fs [FRANGE_DEF]
    \\ irule_at Any pure_eval_lemmasTheory.eval_wh_Closure_closed
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ fs [eval_wh_App,bind_def,FLOOKUP_DEF])
  >~ [‘letrec_binds _ _ (Letrec bs x)’] >-
   (qpat_x_assum ‘letrec_binds _ _ _ _’ mp_tac
    \\ simp [Once letrec_binds_cases]
    \\ reverse strip_tac \\ gvs []
    >-
     (rw [eval_wh_to_def] \\ gvs [] \\ first_x_assum irule
      \\ rename [‘(Letrec ys y ≃ e2) b’]
      \\ irule_at Any app_bisimilarity_trans
      \\ first_x_assum $ irule_at $ Pos $ el 2
      \\ qexists_tac ‘subst_funs ys y’
      \\ irule_at Any eval_wh_IMP_app_bisimilarity
      \\ simp [eval_wh_Letrec] \\ gvs []
      \\ fs [subst_funs_def,bind_def]
      \\ ‘MAP FST ys = MAP FST bs’ by fs [] \\ fs []
      \\ drule EVERY_FLOOKUP_closed_lemma \\ strip_tac
      \\ ‘EVERY (λe. freevars e ⊆ set (MAP FST ys)) (MAP SND ys)’ by
        (fs [EVERY_MEM] \\ rw []
         \\ drule_all MEM_LIST_REL \\ rw []
         \\ imp_res_tac letrec_binds_freevars \\ fs []
         \\ res_tac  \\ gvs [] \\ metis_tac [])
      \\ imp_res_tac letrec_binds_freevars \\ fs []
      \\ drule EVERY_FLOOKUP_closed_lemma  \\ strip_tac
      \\ asm_rewrite_tac []
      \\ rpt $ irule_at Any IMP_closed_subst
      \\ gvs [] \\ irule_at Any subst_letrec_binds \\ gs [FORALL_FRANGE]
      \\ asm_rewrite_tac []
      \\ fs [FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,SF ETA_ss]
      \\ fs [alistTheory.flookup_fupdate_list,AllCaseEqs()]
      \\ rpt strip_tac
      \\ drule_all ALOOKUP_REVERSE_LIST_REL \\ strip_tac \\ gvs []
      \\ simp [Once letrec_binds_cases] \\ disj2_tac \\ fs [])
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
       \\ imp_res_tac letrec_binds_freevars
       \\ fs [eval_Letrec]
       \\ rw [subst_funs_def,bind_def]
       \\ rpt $ irule_at Any IMP_closed_subst
       \\ fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
       \\ fs [FORALL_FRANGE,alistTheory.flookup_fupdate_list,AllCaseEqs()]
       \\ rw []
       \\ imp_res_tac ALOOKUP_MEM
       \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
       \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,EVERY_MEM])
    \\ ‘∀e. (e ≃ e2) b ⇔ (e ≃ subst_funs b2 y) b’ by
      metis_tac [app_bisimilarity_trans,app_bisimilarity_sym]
    \\ fs []
    \\ simp [subst_funs_def,bind_def]
    \\ reverse IF_CASES_TAC >-
     (fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
      \\ gvs [AllCaseEqs()]
      \\ imp_res_tac ALOOKUP_MEM
      \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
      \\ gvs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,EVERY_MEM]
      \\ res_tac \\ fs [])
    \\ reverse IF_CASES_TAC >-
     (fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
      \\ gvs [AllCaseEqs()]
      \\ imp_res_tac ALOOKUP_MEM
      \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
      \\ gvs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,EVERY_MEM]
      \\ res_tac \\ fs [])
    \\ qexists_tac ‘subst (FEMPTY |++ MAP (λ(g,x). (g,Letrec b2 x)) b1) y’
    \\ simp [app_bisimilarity_eq]
    \\ rpt $ irule_at Any IMP_closed_subst
    \\ irule_at Any subst_letrec_binds
    \\ irule_at Any subst_exp_eq
    \\ imp_res_tac letrec_binds_freevars
    \\ fs [FDOM_UPDATES_EQ,PULL_EXISTS,alistTheory.flookup_fupdate_list]
    \\ fs [FORALL_FRANGE,alistTheory.flookup_fupdate_list,AllCaseEqs()]
    \\ rw []
    \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
    \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS,EVERY_MEM]
    \\ res_tac \\ gvs []
    >-
     (rename [‘(ll _ ≃ _) _’]
      \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
      \\ qpat_x_assum ‘MEM _ b2’ mp_tac
      \\ qpat_x_assum ‘MEM _ b1’ mp_tac
      \\ last_x_assum mp_tac
      \\ last_x_assum mp_tac
      \\ rename [‘MEM (kk,p_2) b2 ⇒ MEM (kk,p_1) b1 ⇒ _’]
      \\ qid_spec_tac ‘p_1’
      \\ qid_spec_tac ‘p_2’
      \\ qid_spec_tac ‘b1’
      \\ qid_spec_tac ‘b2’
      \\ Induct \\ fs [PULL_EXISTS,FORALL_PROD,SF DNF_ss]
      \\ rw []
      >- (fs [MEM_MAP,EXISTS_PROD] \\ gvs [])
      \\ first_x_assum irule \\ fs []
      \\ ‘MEM kk (MAP FST b2')’ by (simp_tac std_ss [MEM_MAP,EXISTS_PROD] \\ metis_tac [])
      \\ gvs [] \\ metis_tac [])
    \\ ‘p_2 = p_2'’ by metis_tac [MEM_IMP_EQ]
    \\ rw []
    \\ irule letrec_binds_swap
    \\ fs []
    \\ res_tac \\ fs [letrec_binds_refl]
    \\ fs [EVERY_MEM,EXISTS_PROD,MEM_MAP])
  >~ [‘letrec_binds _ _ (Prim p xs)’]
  \\ qpat_x_assum ‘letrec_binds _ _ _ _’ mp_tac
  \\ simp [Once letrec_binds_cases]
  \\ reverse strip_tac \\ gvs []
  \\ Cases_on ‘p’ \\ fs []
  >~ [‘Cons s xs’] >-
   (rw [eval_wh_to_def]
    \\ ‘eval_wh (Cons s ys) = wh_Constructor s ys’ by fs [eval_wh_Cons]
    \\ drule_all eval_wh_Constructor_bisim \\ strip_tac \\ fs []
    \\ drule_then drule LIST_REL_COMP
    \\ match_mp_tac LIST_REL_mono \\ fs [])
  >~ [‘If’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw []
      \\ drule_at Any eval_wh_Error_bisim
      \\ fs [eval_wh_Prim,AllCaseEqs()]
      \\ disch_then irule
      \\ imp_res_tac LIST_REL_LENGTH
      \\ Cases_on ‘ys’ \\ fs []
      \\ rpt (Cases_on ‘t’ \\ fs [] \\ Cases_on ‘t'’ \\ fs []))
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ IF_CASES_TAC \\ fs [SF DNF_ss]
    \\ reverse (Cases_on ‘∃s. eval_wh_to (k − 1) h = wh_Constructor s []’ \\ fs [])
    >-
     (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw []
      \\ irule eval_wh_Error_bisim
      \\ last_x_assum $ irule_at Any
      \\ qpat_x_assum ‘letrec_binds binds1 binds2 h y’ assume_tac
      \\ first_x_assum drule
      \\ imp_res_tac letrec_binds_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH
      \\ fs [eval_wh_If]
      \\ rw [] \\ gvs [])
    \\ qpat_x_assum ‘letrec_binds binds1 binds2 h y’ assume_tac
    \\ first_assum drule
    \\ imp_res_tac letrec_binds_freevars
    \\ ‘(y ≃ y) b ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ reverse (rw []) \\ fs []
    >-
     (irule eval_wh_Error_bisim
      \\ last_x_assum $ irule_at Any
      \\ fs [eval_wh_If])
    \\ rename [‘eval_wh_to (k − 1) h2’]
    \\ qpat_x_assum ‘letrec_binds binds1 binds2 h2 _’ assume_tac
    \\ first_x_assum drule
    \\ disch_then irule \\ fs []
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at Any \\ fs []
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ fs [closed_def,eval_wh_If])
  >~ [‘Seq’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw []
      \\ drule_at Any eval_wh_Error_bisim
      \\ fs [eval_wh_Prim,AllCaseEqs()]
      \\ disch_then irule
      \\ imp_res_tac LIST_REL_LENGTH
      \\ Cases_on ‘ys’ \\ fs []
      \\ rpt (Cases_on ‘t’ \\ fs [] \\ Cases_on ‘t'’ \\ fs []))
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘k=0’ \\ fs [SF DNF_ss]
    \\ Cases_on ‘eval_wh_to (k − 1) h = wh_Diverge’ \\ fs []
    \\ Cases_on ‘eval_wh_to (k − 1) h = wh_Error’ \\ gvs []
    >-
     (rw [] \\ qpat_x_assum ‘letrec_binds binds1 binds2 h y’ assume_tac
      \\ first_x_assum drule
      \\ imp_res_tac letrec_binds_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ irule eval_wh_Error_bisim
      \\ first_x_assum $ irule_at $ Pos $ last
      \\ fs [eval_wh_Seq])
    \\ imp_res_tac letrec_binds_freevars
    \\ first_assum irule \\ fs []
    \\ first_x_assum $ irule_at $ Pos last
    \\ irule app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos last \\ fs []
    \\ irule eval_wh_IMP_app_bisimilarity
    \\ fs [closed_def,eval_wh_Seq,AllCaseEqs()]
    \\ qsuff_tac ‘eval_wh y ≠ wh_Error ∧ eval_wh y ≠ wh_Diverge’
    \\ fs []
    \\ first_x_assum drule
    \\ ‘(y ≃ y) b ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ Cases_on ‘eval_wh_to (k − 1) h’ \\ fs [])
  >~ [‘IsEq cname arity onoff’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw []
      \\ drule_at Any eval_wh_Error_bisim
      \\ fs [eval_wh_Prim,AllCaseEqs()]
      \\ disch_then irule
      \\ imp_res_tac LIST_REL_LENGTH
      \\ Cases_on ‘ys’ \\ fs []
      \\ rpt (Cases_on ‘t’ \\ fs [] \\ Cases_on ‘t'’ \\ fs []))
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘k=0’ \\ fs [SF DNF_ss]
    \\ reverse (Cases_on ‘∃s xs. eval_wh_to (k − 1) h = wh_Constructor s xs ∧
                   ~is_eq_fail onoff s ∧ (s = cname ⇒ arity = LENGTH xs)’ \\ fs [])
    >-
     (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw []
      \\ irule eval_wh_Error_bisim
      \\ last_x_assum $ irule_at Any
      \\ qpat_x_assum ‘letrec_binds binds1 binds2 h y’ assume_tac
      \\ first_x_assum drule
      \\ imp_res_tac letrec_binds_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH
      \\ fs [eval_wh_Prim])
    \\ IF_CASES_TAC \\ gvs []
    \\ first_assum drule
    \\ imp_res_tac letrec_binds_freevars
    \\ ‘(y ≃ y) b ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ irule eval_wh_Constructor_NIL_bisim
    \\ first_x_assum $ irule_at $ Pos last
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [eval_wh_IsEq])
  >~ [‘Proj cname i’] >-
   (fs [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw []
      \\ drule_at Any eval_wh_Error_bisim
      \\ fs [eval_wh_Prim,AllCaseEqs()]
      \\ disch_then irule
      \\ imp_res_tac LIST_REL_LENGTH
      \\ Cases_on ‘ys’ \\ fs []
      \\ Cases_on ‘t’ \\ fs [])
    \\ fs [] \\ gvs [LENGTH_EQ_NUM_compute]
    \\ Cases_on ‘k=0’ \\ fs [SF DNF_ss]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ reverse (Cases_on ‘∃s xs. eval_wh_to (k − 1) h = wh_Constructor s xs ∧
                                 s = cname ∧ i < LENGTH xs’ \\ fs [])
    >-
     (Cases_on ‘eval_wh_to (k − 1) h’ \\ gvs [] \\ rw []
      \\ irule eval_wh_Error_bisim
      \\ last_x_assum $ irule_at Any
      \\ qpat_x_assum ‘letrec_binds binds1 binds2 h y’ assume_tac
      \\ first_x_assum drule
      \\ imp_res_tac letrec_binds_freevars
      \\ ‘(y ≃ y) T ∧ closed y’ by
       (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
        \\ fs [closed_def])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ imp_res_tac LIST_REL_LENGTH
      \\ fs [eval_wh_Prim] \\ rw [] \\ fs [])
    \\ first_assum irule \\ fs []
    \\ last_x_assum drule \\ fs []
    \\ imp_res_tac letrec_binds_freevars
    \\ ‘(y ≃ y) b ∧ closed y’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def])
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ fs [LIST_REL_EL_EQN]
    \\ gvs []
    \\ pop_assum drule \\ strip_tac
    \\ first_x_assum $ irule_at $ Pos last
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos hd \\ fs []
    \\ irule_at Any app_bisimilarity_trans
    \\ first_x_assum $ irule_at $ Pos $ el 2 \\ fs []
    \\ irule_at Any eval_wh_IMP_app_bisimilarity
    \\ fs [eval_wh_Proj]
    \\ dxrule eval_wh_freevars_SUBSET
    \\ dxrule eval_wh_to_freevars_SUBSET
    \\ fs [PULL_EXISTS,MEM_MAP,closed_def,EXTENSION]
    \\ fs [MEM_EL]
    \\ metis_tac [])
  >~ [‘AtomOp a’] >-
   (fs [eval_wh_to_def]
    \\ Cases_on ‘get_atoms (MAP (if k = 0 then K wh_Diverge else
                                   (λa. eval_wh_to (k − 1) a)) xs)’ \\ fs []
    \\ Cases_on ‘x’ \\ fs []
    >-
     (rw []
      \\ fs [get_atoms_def,AllCaseEqs(),EXISTS_MEM]
      \\ gvs [MEM_MAP]
      \\ Cases_on ‘k=0’ \\ gvs [error_Atom_def]
      \\ first_x_assum drule
      \\ drule_all MEM_LIST_REL1 \\ strip_tac
      \\ disch_then drule
      \\ rename [‘letrec_binds binds1 binds2 x y’]
      \\ imp_res_tac letrec_binds_freevars
      \\ ‘(y ≃ y) T ∧ closed y ∧ closed x’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
      \\ disch_then drule \\ fs [] \\ strip_tac
      \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ gvs [error_Atom_def]
      \\ irule eval_wh_Error_bisim
      \\ last_x_assum $ irule_at Any
      \\ fs [eval_wh_Prim,get_atoms_def]
      \\ qsuff_tac ‘EXISTS error_Atom (MAP eval_wh ys)’ >- fs []
      \\ fs [EXISTS_MEM,MEM_MAP,PULL_EXISTS]
      \\ first_x_assum $ irule_at Any
      \\ fs [])
    \\ rename [‘eval_op a atoms’]
    \\ qsuff_tac ‘get_atoms (MAP eval_wh ys) = SOME (SOME atoms)’
    >-
     (rw []
      \\ Cases_on ‘eval_op a atoms’ \\ fs []
      >-
       (rw [] \\ irule eval_wh_Error_bisim
        \\ last_x_assum $ irule_at Any
        \\ gvs [eval_wh_Prim])
      \\ Cases_on ‘x’ \\ fs []
      >-
       (rw [] \\ irule eval_wh_Atom_bisim
        \\ last_x_assum $ irule_at Any
        \\ gvs [eval_wh_Prim])
      \\ Cases_on ‘y’ \\ fs []
      \\ rw [] \\ irule eval_wh_Constructor_NIL_bisim
      \\ last_x_assum $ irule_at Any
      \\ gvs [eval_wh_Prim])
    \\ fs [get_atoms_def,AllCaseEqs()]
    \\ gvs []
    \\ Cases_on ‘xs = []’ >- gvs []
    \\ Cases_on ‘k = 0’ >- (Cases_on ‘xs’ \\ fs [])
    \\ gvs [MEM_MAP]
    \\ rw []
    >-
     (fs [EVERY_MEM,MEM_MAP] \\ rw []
      \\ drule_all MEM_LIST_REL \\ rw []
      \\ first_x_assum $ drule_then drule
      \\ res_tac
      \\ imp_res_tac letrec_binds_freevars
      \\ ‘(y ≃ y) b ∧ closed y’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def])
      \\ disch_then drule_all
      \\ rw [] \\ fs [PULL_EXISTS]
      \\ first_x_assum drule \\ strip_tac
      \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs []
      \\ res_tac \\ fs [])
    >-
     (CCONTR_TAC \\ fs []
      \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
      \\ drule_all MEM_LIST_REL \\ strip_tac
      \\ ‘closed x ∧ ¬error_Atom (eval_wh_to (k − 1) x)’ by (res_tac \\ fs [])
      \\ ‘eval_wh_to (k − 1) x ≠ wh_Diverge’ by (CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
      \\ first_x_assum $ drule_then drule
      \\ imp_res_tac letrec_binds_freevars
      \\ ‘(y ≃ y) b ∧ closed y ∧ closed x’ by
        (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
         \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
      \\ disch_then drule \\ fs []
      \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs [])
    \\ AP_TERM_TAC
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ match_mp_tac LIST_REL_IMP_MAP_EQ
    \\ rw []
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ ‘closed x ∧ ¬error_Atom (eval_wh_to (k − 1) x)’ by (res_tac \\ fs [])
    \\ ‘eval_wh_to (k − 1) x ≠ wh_Diverge’ by (CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
    \\ first_x_assum $ drule_then drule
    \\ imp_res_tac letrec_binds_freevars
    \\ ‘(y ≃ y) b ∧ closed y ∧ closed x’ by
      (irule_at Any pure_exp_relTheory.reflexive_app_bisimilarity
       \\ fs [closed_def,EVERY_MEM] \\ res_tac \\ fs [])
    \\ disch_then drule \\ fs []
    \\ Cases_on ‘eval_wh_to (k − 1) x’ \\ fs [])
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
  \\ simp [letrec_binds_refl]
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

Triviality FST_LAM: (* TODO: move *)
  FST = λ(p1,p2). p1
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Triviality LIST_REL_MAP_CONG: (* TODO: move *)
  ∀xs ys R Q f.
    (∀x y. R x y ∧ MEM x xs ∧ MEM y ys ⇒ Q (f x) (f y)) ∧ LIST_REL R xs ys ⇒
    LIST_REL Q (MAP f xs) (MAP f ys)
Proof
  Induct \\ fs [PULL_EXISTS] \\ metis_tac []
QED

Triviality LIST_REL_IMP_same_keys:
  ∀binds1 binds2.
    LIST_REL (λ(v1,e1) (v2,e2). v1 = v2) binds1 binds2 ⇒
    MAP FST binds1 = MAP FST binds2
Proof
  Induct \\ fs [PULL_EXISTS,FORALL_PROD]
QED

Theorem exp_eq_Letrec_change:
  ∀binds1 binds2 e b.
    ALL_DISTINCT (MAP FST binds1) ∧
    LIST_REL (λ(v1, e1) (v2, e2).
      v1 = v2 ∧ (Letrec binds1 e1 ≅? Letrec binds1 e2) b) binds1 binds2 ∧
    LIST_REL (λ(v1, e1) (v2, e2).
      v1 = v2 ∧ (Letrec binds2 e1 ≅? Letrec binds2 e2) b) binds1 binds2
    ⇒
    (Letrec binds1 e ≅? Letrec binds2 e) b
Proof
  rw [exp_eq_def]
  \\ ‘MAP FST binds1 = MAP FST binds2’ by
   (irule LIST_REL_IMP_same_keys
    \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs [FORALL_PROD])
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
