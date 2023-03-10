(*
   Theorem that help prove inlining correct
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     combinTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory pure_congruenceTheory
     pure_letrec_seqTheory;

val _ = new_theory "pure_inline";

(*

semantics level proof (capturing idea):

  |- subst_rel f x rhs rhs' ==>
     (Let f x rhs) ~ (Let f x rhs')

implementation level proof:

  |- subst_rel f (exp_of x) (exp_of r) (exp_of (inline f x r))

*)

Inductive subst_rel:
[~refl:]
  (∀v x t.
    subst_rel v x t t) ∧
[~Var:]
  (∀v x.
    subst_rel v x (Var v) x) ∧
[~Prim:]
  (∀v x p xs ys.
    LIST_REL (subst_rel v x) xs ys ⇒
    subst_rel v x (Prim p xs) (Prim p ys)) ∧
[~App:]
  (∀v x t1 t2 u1 u2.
    subst_rel v x t1 u1 ∧
    subst_rel v x t2 u2 ⇒
    subst_rel v x (App t1 t2) (App u1 u2)) ∧
[~Lam:]
  (∀v x t u w.
    subst_rel v x t u ∧ v ≠ w ∧ w ∉ freevars x ⇒
    subst_rel v x (Lam w t) (Lam w u)) ∧
[~Letrec:]
  (∀v x t u xs ys.
    LIST_REL (λ(n,t1) (m,u1). n = m ∧ subst_rel v x t1 u1 ∧ n ∉ freevars x) xs ys ∧
    subst_rel v x t u ∧
    ~MEM v (MAP FST xs) ⇒
    subst_rel v x (Letrec xs t) (Letrec ys u))
End

Theorem FLOOKUP_closed_FRANGE_closed:
  ∀f. (
    (∀n v. FLOOKUP f n = SOME v ⇒ closed v) ⇔
      (∀v. v ∈ FRANGE f ⇒ closed v)
  )
Proof
  rw []
  \\ simp [FRANGE_FLOOKUP]
  \\ rw [EQ_IMP_THM]
  \\ first_x_assum irule
  \\ qexists ‘n’
  \\ rw []
QED

Theorem subst1_notin:
  ∀w e e1. w ∉ freevars e ⇒
    subst1 w e1 e = e
Proof
  rw []
  \\ qspecl_then [‘FEMPTY |+ (w, e1)’, ‘e’, ‘w’] assume_tac subst_fdomsub
  \\ fs []
QED

Theorem Let_Var3:
  w ∉ freevars e ⇒
    (Let w e (Var w) ≅? Let w e e) b
Proof
  rw []
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [subst_def,eval_wh_Seq] \\ rw [] \\ fs []
  \\ fs [eval_wh_App,eval_wh_Lam,bind1_def]
  \\ rw [subst1_def]
  \\ AP_TERM_TAC
  \\ sg ‘∀v. v ∈ FRANGE (f \\ w) ⇒ closed v’
  >- (
    simp [GSYM FLOOKUP_closed_FRANGE_closed]
    \\ simp [DOMSUB_FLOOKUP_THM]
    \\ rw []
    \\ res_tac
  )
  \\ qsuff_tac ‘w ∉ freevars (subst (f \\ w) e)’
  >- (
    rw []
    \\ irule EQ_TRANS
    \\ irule_at (Pos last) $ GSYM subst1_notin
    \\ simp [subst_fdomsub]
  )
  \\ qsuff_tac ‘closed (subst (f \\ w) e)’
  >- (
    rw []
    \\ fs [closed_def]
  )
  \\ gvs [GSYM subst_fdomsub]
QED

(* //TODO(kπ) move *)
Theorem exp_eq_subst_IMP_exp_eq:
  (∀f. (∀n v. FLOOKUP f n = SOME v ⇒ closed v) ∧
       freevars x ⊆ FDOM f ∧ freevars y ⊆ FDOM f ⇒
       (subst f x ≅? subst f y) b) ⇒
    (x ≅? y) b
Proof
  rw []
  \\ irule (iffRL exp_eq_open_bisimilarity_freevars)
  \\ simp [open_bisimilarity_def]
  \\ rw []
  \\ first_x_assum (qspecl_then [‘f’] assume_tac)
  \\ gs []
  \\ simp [bind_def]
  \\ rw []
  \\ reverse (qsuff_tac ‘(subst f x ≅? subst f y) b’)
  >- (
    simp []
    \\ first_x_assum irule
    \\ rw []
    \\ first_x_assum irule
    \\ qexists ‘n’
    \\ rw []
  )
  \\ rw []
  \\ irule (iffLR (GSYM app_bisimilarity_eq))
  \\ rw []
  \\ rw []
  \\ irule IMP_closed_subst
  \\ rw []
  \\ gvs [FLOOKUP_closed_FRANGE_closed]
QED

Theorem Let_Lam:
  v ≠ w ∧ w ∉ freevars x ⇒
    (Let v x (Lam w t) ≅? Lam w (Let v x t)) b
Proof
  rw []
  \\ irule exp_eq_subst_IMP_exp_eq
  \\ rw [subst_def]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ conj_asm1_tac
  >- (
    irule IMP_closed_subst
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
  )
  \\ rw [subst_def]
  \\ rw [exp_eq_Lam_removed]
  \\ simp [exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ rw []
  >- (
    irule IMP_closed_subst
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
    \\ simp [DOMSUB_FAPPLY_NEQ]
    \\ fs [SUBSET_DEF]
  )
  \\ simp [DOMSUB_FUPDATE_NEQ]
  \\ simp [exp_eq_refl]
  \\ reverse $ qsuff_tac
    ‘(subst (f \\ w \\ v) t = subst (f \\ v \\ w) t)
      ∧ (subst (f \\ w) x = subst f x)’
  >- (
    rw []
    >- (
      rw []
      \\ simp [DOMSUB_COMMUTES]
    )
    \\ irule (GSYM subst_fdomsub)
    \\ rw []
  )
  \\ rw []
  \\ rw [exp_eq_refl]
QED

Theorem FST_intro:
  (λ(p1,p2). p1) = FST
Proof
  simp [FUN_EQ_THM,FORALL_PROD]
QED

Theorem Let_Letrec:
  v ∉ freevars x ∧ EVERY (λ(n,u). n ∉ freevars x) xs ∧
  ¬MEM v (MAP FST xs) ∧
  DISJOINT (freevars x) (set (MAP FST xs)) ⇒
    (Let v x (Letrec xs e) ≅? Letrec (MAP (λ(n,t). (n, Let v x t)) xs) (Let v x e)) b
Proof
  rw []
  \\ irule exp_eq_subst_IMP_exp_eq
  \\ rw []
  \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro]
  \\ simp [subst_def]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ conj_asm1_tac
  >- (
    irule IMP_closed_subst
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
  )
  \\ rw [subst_def]
  \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro]
  \\ irule exp_eq_Letrec_cong
  \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro]
  \\ reverse $ conj_tac
  >- (
    simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any beta_equality
    \\ conj_asm1_tac
    >- (
      irule IMP_closed_subst
      \\ fs [FDOM_FDIFF,SUBSET_DEF,IN_DISJOINT]
      \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]

      \\ fs [FDIFF_def,DRESTRICT_DEF]
      \\ metis_tac []
    )
    \\ DEP_REWRITE_TAC [subst_subst_FUNION]
    \\ conj_tac
    >- (
      fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
      \\ fs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
    )
    \\ qmatch_goalsub_abbrev_tac ‘(subst f1 e ≅? subst f2 e) b’
    \\ qsuff_tac ‘f1 = f2’
    >- (simp [exp_eq_refl])
    \\ unabbrev_all_tac
    \\ rpt MK_COMB_TAC \\ fs []
    \\ simp [FLOOKUP_EXT,FUN_EQ_THM,FLOOKUP_FDIFF,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
    \\ rw []
    \\ fs []
    \\ irule subst_FDIFF'
    \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
    \\ rw []
    \\ res_tac
  )
  \\ simp [LIST_REL_MAP_MAP]
  \\ fs [EVERY_MEM,FORALL_PROD]
  \\ rw []
  \\ res_tac
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ conj_tac
  >- (
    fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
    \\ fs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
  )
  \\ simp [Once exp_eq_sym]
  \\ rw [subst_def]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ conj_asm1_tac
  >- (
    irule IMP_closed_subst
    \\ fs [FDOM_FDIFF,SUBSET_DEF,IN_DISJOINT]
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]

    \\ fs [FDIFF_def,DRESTRICT_DEF]
    \\ metis_tac []
  )
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ conj_tac
  >- (
    fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
    \\ fs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
  )
  \\ qmatch_goalsub_abbrev_tac ‘(subst f1 p_2 ≅? subst f2 p_2) b’
  \\ qsuff_tac ‘f1 = f2’
  >- (simp [exp_eq_refl])
  \\ unabbrev_all_tac
  \\ rpt MK_COMB_TAC \\ fs []
  \\ simp [FLOOKUP_EXT,FUN_EQ_THM,FLOOKUP_FDIFF,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
  \\ rw []
  \\ fs []
  \\ irule subst_FDIFF'
  \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
  \\ rw []
  \\ res_tac
QED

Theorem LIST_REL_swap:
  ∀xs ys. LIST_REL R xs ys = LIST_REL (λx y. R y x) ys xs
Proof
  Induct \\ fs []
QED

Theorem subst_rel_IMP_exp_eq:
  ∀v x t u.
    v ∉ freevars x ∧
    subst_rel v x t u ⇒
    (Let v x t ≅? Let v x u) b
Proof
  Induct_on ‘subst_rel’
  \\ rpt strip_tac
  >- rw [exp_eq_refl]
  >- rw [Let_Var3]
  >- (
    rw []
    \\ gvs []
    \\ irule exp_eq_trans
    \\ irule_at Any Let_Prim
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Let_Prim
    \\ irule exp_eq_Prim_cong
    \\ simp [LIST_REL_MAP]
    \\ gvs [LIST_REL_EL_EQN]
    \\ simp [Once exp_eq_sym]
  )
  >- (
    rw []
    \\ gvs []
    \\ qsuff_tac
      ‘(App (Let v x t) (Let v x t') ≅? App (Let v x u) (Let v x u'))b’
    >- (
      rw []
      \\ qspecl_then [‘v’, ‘x’, ‘t’, ‘t'’, ‘b’] assume_tac Let_App
      \\ qspecl_then [‘v’, ‘x’, ‘u’, ‘u'’, ‘b’] assume_tac Let_App
      \\ qsuff_tac
        ‘(Let v x (App t t') ≅? App (Let v x u) (Let v x u')) b’
      >- (
        rw []
        \\ qspecl_then [‘Let v x (App t t')’, ‘App (Let v x u) (Let v x u')’, ‘Let v x (App u u')’, ‘b’] assume_tac exp_eq_trans
        \\ gvs [exp_eq_sym]
      )
      \\ qspecl_then [‘Let v x (App t t')’, ‘App (Let v x t) (Let v x t')’, ‘App (Let v x u) (Let v x u')’, ‘b’] assume_tac exp_eq_trans
      \\ gvs [exp_eq_sym]
    )
    \\ irule exp_eq_App_cong
    \\ conj_tac
    >- rw []
    \\ rw []
  )
  >- (
    rw []
    \\ gvs []
    \\ ‘(Lam w (Let v x u) ≅? Let v x (Lam w u)) b’ by (simp [Let_Lam, exp_eq_sym])
    \\ ‘(Let v x (Lam w t) ≅? Lam w (Let v x t)) b’ by (simp [Let_Lam, exp_eq_sym])
    \\ qsuff_tac ‘(Lam w (Let v x t) ≅? Lam w (Let v x u)) b’
    >- (
      rw []
      \\ irule exp_eq_trans
      \\ qexists ‘Lam w (Let v x t)’
      \\ rw []
      \\ irule exp_eq_trans
      \\ qexists ‘Lam w (Let v x u)’
      \\ rw []
    )
    \\ simp [exp_eq_Lam_removed]
  )
  \\ rw []
  \\ gvs []
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Letrec
  \\ rw []
  >- (
    rw []
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw []
    \\ qspecl_then [‘xs’, ‘ys’, ‘(λ(n,t') (m,u'). n ∉ freevars x)’, ‘(p_1,p_2)’] assume_tac LIST_REL_MEM_IMP
    \\ gvs []
    \\ first_x_assum mp_tac
    \\ reverse $ impl_tac
    >- (
      rw []
      \\ Cases_on ‘y’
      \\ gvs []
    )
    \\ fs [LIST_REL_EVERY_ZIP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw []
    \\ first_x_assum (qspecl_then [‘p_1'’, ‘p_2'’, ‘p_1''’, ‘p_2''’] assume_tac)
    \\ rw []
  )
  >- (
    rw []
    \\ simp [Once DISJOINT_SYM]
    \\ simp [DISJOINT_ALT]
    \\ rw []
    \\ fs [MEM_MAP]
    \\ Cases_on ‘y’
    \\ qspecl_then [‘xs’, ‘ys’, ‘(λ(n,t') (m,u'). n ∉ freevars x)’, ‘(q,r)’] assume_tac LIST_REL_MEM_IMP
    \\ simp [FST]
    \\ fs [LIST_REL_EVERY_ZIP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ gvs []
    \\ first_x_assum mp_tac
    \\ reverse $ impl_tac
    >- (
      rw []
      \\ Cases_on ‘y’
      \\ gvs []
    )
    \\ rw []
    \\ first_x_assum (qspecl_then [‘p_1’, ‘p_2’, ‘p_1'’, ‘p_2'’] assume_tac)
    \\ gvs []
  )
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Letrec
  \\ rw []
  >- (
    rw []
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw []
    \\ fs [Once LIST_REL_swap]
    \\ qspecl_then [‘ys’, ‘xs’, ‘(λ(n,t') (m,u'). n ∉ freevars x)’, ‘(p_1,p_2)’] assume_tac LIST_REL_MEM_IMP
    \\ gvs []
    \\ first_x_assum mp_tac
    \\ reverse $ impl_tac
    >- (
      rw []
      \\ Cases_on ‘y’
      \\ gvs []
    )
    \\ fs [LIST_REL_EVERY_ZIP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw []
    \\ first_x_assum (qspecl_then [‘p_1'’, ‘p_2'’, ‘p_1''’, ‘p_2''’] assume_tac)
    \\ gvs []
  )
  >- (
    rw []
    \\ qsuff_tac ‘MAP FST xs = MAP FST ys’
    >- (
      rw []
      \\ gvs []
    )
    \\ simp [MAP_EQ_EVERY2]
    \\ fs [LIST_REL_EVERY_ZIP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw []
    \\ first_x_assum (qspecl_then [‘p_1’, ‘p_2’, ‘p_1'’, ‘p_2'’] assume_tac)
    \\ gvs []
  )
  >- (
    rw []
    \\ simp [Once DISJOINT_SYM]
    \\ simp [DISJOINT_ALT]
    \\ rw []
    \\ fs [MEM_MAP]
    \\ Cases_on ‘y’
    \\ fs [Once LIST_REL_swap]
    \\ qspecl_then [‘ys’, ‘xs’, ‘(λ(n,t') (m,u'). n ∉ freevars x)’, ‘(q,r)’] assume_tac LIST_REL_MEM_IMP
    \\ simp [FST]
    \\ fs [LIST_REL_EVERY_ZIP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ gvs []
    \\ first_x_assum mp_tac
    \\ reverse $ impl_tac
    >- (
      rw []
      \\ Cases_on ‘y’
      \\ gvs []
    )
    \\ rw []
    \\ first_x_assum (qspecl_then [‘p_1’, ‘p_2’, ‘p_1'’, ‘p_2'’] assume_tac)
    \\ gvs []
  )
  \\ irule exp_eq_Letrec_cong
  \\ rw []
  >- (
    rw []
    \\ simp [Once EQ_SYM_EQ]
    \\ simp [MAP_EQ_EVERY2]
    \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro]
    \\ simp [LIST_REL_MAP]
    \\ fs [LIST_REL_EVERY_ZIP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw []
    \\ first_x_assum (qspecl_then [‘p_1’, ‘p_2’, ‘p_1'’, ‘p_2'’] assume_tac)
    \\ gvs []
  )
  >- (
    rw []
    \\ simp [LIST_REL_MAP]
    \\ simp [Once LIST_REL_swap]
    \\ fs [LIST_REL_EVERY_ZIP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw []
    \\ first_x_assum (qspecl_then [‘p_1’, ‘p_2’, ‘p_1'’, ‘p_2'’] assume_tac)
    \\ gvs []
    \\ simp [Once exp_eq_sym]
  )
  \\ rw [exp_eq_sym]
QED

(*

TODO:
 - remember to add a simplifying pass after inlining (particularly to simplify Case)

*)

val _ = export_theory();
