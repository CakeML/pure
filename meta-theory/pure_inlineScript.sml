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
  ∀f. (∀n v. FLOOKUP f n = SOME v ⇒ closed v) ⇔
      (∀v. v ∈ FRANGE f ⇒ closed v)
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
  ∀v x xs e.
    EVERY (λ(n,u). n ∉ freevars x) xs ∧
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
    >- simp [exp_eq_refl]
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

Theorem subst_rel_IMP_exp_eq_specialized:
  ∀v x t u.
    v ∉ freevars x ∧
    subst_rel v x t u ⇒
    Let v x t ≅ Let v x u
Proof
  simp [subst_rel_IMP_exp_eq]
QED

Inductive deep_subst_rel:
[~Let:]
  (∀v x y y'.
    subst_rel v x y y' ∧
    v ∉ freevars x ⇒
    deep_subst_rel (Let v x y) (Let v x y')) ∧
(* Boilerplate: *)
[~refl:]
  (∀t.
    deep_subst_rel t t) ∧
[~Prim:]
  (∀p xs ys.
    LIST_REL (deep_subst_rel) xs ys ⇒
    deep_subst_rel (Prim p xs) (Prim p ys)) ∧
[~App:]
  (∀t1 t2 u1 u2.
    deep_subst_rel t1 u1 ∧
    deep_subst_rel t2 u2 ⇒
    deep_subst_rel (App t1 t2) (App u1 u2)) ∧
[~Lam:]
  (∀t u w.
    deep_subst_rel t u  ⇒
    deep_subst_rel (Lam w t) (Lam w u)) ∧
[~Letrec:]
  (∀t u xs ys.
    LIST_REL (λ(n,t1) (m,u1). n = m ∧ deep_subst_rel t1 u1) xs ys ∧
    deep_subst_rel t u  ⇒
    deep_subst_rel (Letrec xs t) (Letrec ys u))
End

Theorem deep_subst_rel_IMP_exp_eq:
  ∀t u.
    deep_subst_rel t u ⇒
    (t ≅? u) b
Proof
  Induct_on ‘deep_subst_rel’
  \\ rpt strip_tac
  >- (
    rw []
    \\ irule subst_rel_IMP_exp_eq
    \\ rw []
  )
  >- rw [exp_eq_refl]
  >- (
    rw []
    \\ irule exp_eq_Prim_cong
    \\ fs [LIST_REL_EVERY_ZIP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ gvs []
  )
  >- (
    irule exp_eq_App_cong
    \\ rw []
  )
  >- simp [exp_eq_Lam_removed]
  >- (
    irule exp_eq_Letrec_cong
    \\ rw []
    >- (
      simp [MAP_EQ_EVERY2]
      \\ fs [LAMBDA_PROD,FST_intro]
      \\ fs [LIST_REL_EVERY_ZIP]
      \\ fs [EVERY_MEM,FORALL_PROD]
      \\ rw []
      \\ first_x_assum (qspecl_then [‘p_1’, ‘p_2’, ‘p_1'’, ‘p_2'’] assume_tac)
      \\ gvs []
    )
    \\ simp [LIST_REL_MAP]
    \\ fs [LAMBDA_PROD,FST_intro]
    \\ fs [LIST_REL_EVERY_ZIP]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ rw []
    \\ first_x_assum (qspecl_then [‘p_1’, ‘p_2’, ‘p_1'’, ‘p_2'’] assume_tac)
    \\ gvs []
  )
QED

Theorem deep_subst_rel_IMP_exp_eq_specialized:
  ∀t u. deep_subst_rel t u ⇒ t ≅ u
Proof
  simp [deep_subst_rel_IMP_exp_eq]
QED

Theorem x_equiv_IMP_weak:
  ∀b. (x ≅? y) T ⇒ (x ≅? y) b
Proof
  Cases \\ fs []
  \\ cheat
QED

Datatype:
  rhs = Exp exp | Rec exp
End

Definition list_lookup_def:
  list_lookup v [] = NONE ∧
  list_lookup v ((v', x)::rest) =
    if v = v' then SOME (x, rest) else
      case list_lookup v rest of
      | NONE => NONE
      | SOME (y,ys) => SOME (y,(v', x)::ys)
End

Inductive no_shadowing:
[~Var:]
  (∀v. no_shadowing (Var v)) ∧
[~Prim:]
  (∀l p.
     EVERY no_shadowing l ⇒
     no_shadowing (Prim p l)) ∧
[~App:]
  (∀x y.
     no_shadowing x ∧ no_shadowing y ∧
     DISJOINT (boundvars x) (boundvars y) ⇒
     no_shadowing (App x y)) ∧
[~Lam:]
  (∀v x.
     no_shadowing x ∧ v ∉ boundvars x ⇒
     no_shadowing (Lam v x)) ∧
[~Letrec:]
  (∀l x.
     EVERY (λ(v,e).
              no_shadowing e ∧
              DISJOINT (set (MAP FST l)) (boundvars e)) l ∧
     no_shadowing x ∧ DISJOINT (set (MAP FST l)) (boundvars x) ⇒
     no_shadowing (Letrec l x))
End

Theorem no_shadowing_simp[simp] =
  map (SIMP_CONV (srw_ss()) [Once no_shadowing_cases])
    [“no_shadowing (Var v)”,
     “no_shadowing (Prim p l)”,
     “no_shadowing (App x y)”,
     “no_shadowing (Lam v x)”] |> LIST_CONJ;

Definition TAKE_WHILE_def:
  (TAKE_WHILE P [] = []) ∧
  (TAKE_WHILE P (h::t) = if P h then h::(TAKE_WHILE P t) else [])
End

Definition vars_of_def:
  vars_of [] = {} ∧
  vars_of ((v,Exp e)::rest) = v INSERT boundvars e ∪ vars_of rest ∧
  vars_of ((v,Rec e)::rest) = v INSERT boundvars e ∪ vars_of rest
End

Definition freevars_of_def:
  freevars_of [] = {} ∧
  freevars_of ((v,Exp e)::rest) = freevars e ∪ freevars_of rest ∧
  freevars_of ((v,Rec e)::rest) = freevars e ∪ freevars_of rest
End

Inductive list_subst_rel:
[~refl:]
  (∀l t.
    list_subst_rel l t t) ∧
[~Let:]
  (∀l v x y.
    list_subst_rel l x x' ∧
    list_subst_rel (l ++ [(v,Exp x)]) y y' ⇒
    list_subst_rel l (Let v x y) (Let v x' y')) ∧
[~LetrecInline:]
  (∀v l t x y.
    MEM (v, Rec t) l ∧
    list_subst_rel l x y ⇒
    list_subst_rel l x (Letrec [(v,t)] y)) ∧
[~Var:]
  (∀v x x1 x2 l.
    MEM (v, Exp x) l ∧
    x ≅ x1 ∧
    no_shadowing x1 ∧
    DISJOINT (boundvars x1) (freevars x1) ∧
    DISJOINT (boundvars x1) (vars_of l) ∧
    DISJOINT (boundvars x1) (freevars_of l) ∧
    list_subst_rel l x1 x2 ⇒
    list_subst_rel l (Var v) x2) ∧
[~VarSimp:]
  (∀v x l.
    MEM (v, Exp x) l ⇒
    list_subst_rel l (Var v) x) ∧
[~Prim:]
  (∀l p xs ys.
    LIST_REL (list_subst_rel l) xs ys ⇒
    list_subst_rel l (Prim p xs) (Prim p ys)) ∧
[~App:]
  (∀l t1 t2 u1 u2.
    list_subst_rel l t1 u1 ∧
    list_subst_rel l t2 u2 ⇒
    list_subst_rel l (App t1 t2) (App u1 u2)) ∧
[~Lam:]
  (∀l t u w.
    list_subst_rel l t u ⇒
    list_subst_rel l (Lam w t) (Lam w u)) ∧
[~Letrec:]
  (∀l t u xs ys.
    LIST_REL (λ(n,t1) (m,u1). n = m ∧ list_subst_rel l t1 u1) xs ys ∧
    list_subst_rel l t u ⇒
    list_subst_rel l (Letrec xs t) (Letrec ys u)) ∧
[~LetrecIntro:]
  (∀l t u v x.
    list_subst_rel l x y ∧
    list_subst_rel (l ++ [(v,Rec x)]) t u ⇒
    list_subst_rel l (Letrec [(v, x)] t) (Letrec [(v, y)] u))
End

Definition Binds_def[simp]:
  Binds [] e = e ∧
  Binds ((v,Exp x)::xs) e = Let v x (Binds xs e) ∧
  Binds ((v,Rec x)::xs) e = Letrec [(v,x)] (Binds xs e)
End

Theorem Binds_snoc:
  ∀xs. Binds (xs ++ [(v,Exp x)]) y = Binds xs (Let v x y)
Proof
  Induct \\ fs []
  \\ PairCases \\ Cases_on ‘h1’ \\ fs []
QED

Definition bind_ok_def:
  (bind_ok xs (v,Exp x) ⇔
    v ∉ freevars x ∧ (* for copying *)
    v ∉ boundvars x ∧
    DISJOINT (boundvars x) (set (MAP FST xs)) ∧ (* thm assumption *)
    DISJOINT (boundvars x) (vars_of (FILTER (λ(w,_). w ≠ v) xs)) ∧ (* thm assumption *)
    DISJOINT (boundvars x) (freevars x) ∧ (* thm assumption *)
    no_shadowing x) ∧
  (bind_ok xs (v,Rec x) ⇔ T)
End

Definition bind_ok_rec_def:
  (bind_ok_rec [] = T) ∧
  (bind_ok_rec ((v,Exp x)::rest) =
    (DISJOINT (freevars x) (set (MAP FST rest)) ∧ (* for pushing down bindings *)
    bind_ok_rec rest)) ∧
  (bind_ok_rec ((v,Rec x)::rest) =
    (DISJOINT (freevars x) (set (MAP FST rest)) ∧ (* for pushing down bindings *)
    bind_ok_rec rest))
End

Definition binds_ok_def:
  binds_ok xs ⇔
    ALL_DISTINCT (MAP FST xs) ∧
    EVERY (bind_ok xs) xs ∧
    bind_ok_rec xs
End

Theorem bind_ok_rec_APPEND:
  bind_ok_rec (ys ++ xs) ⇒ bind_ok_rec xs
Proof
  rw []
  \\ Induct_on `ys` \\ rw []
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  >- fs [bind_ok_rec_def]
  \\ fs [bind_ok_rec_def]
QED

Theorem vars_of_MEM_not_in:
  MEM (q,Exp e) xs ∧ v ∉ vars_of xs ⇒
  v ∉ boundvars e
Proof
  rw []
  \\ Induct_on `xs` \\ rw []
  >- fs [vars_of_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ fs [vars_of_def]
QED

Theorem vars_of_DISJOINT_MAP_FST:
  DISJOINT s (vars_of xs) ⇒ DISJOINT s (set (MAP FST xs))
Proof
  rw []
  \\ Induct_on `xs` \\ reverse $ rw [vars_of_def]
  >- (
    Cases_on `h` \\ Cases_on `r` \\ fs [vars_of_def]
  )
  \\ Cases_on `h` \\ Cases_on `r` \\ fs [vars_of_def]
  >- (
    last_x_assum irule
    \\ fs [DISJOINT_SYM]
  )
  \\ last_x_assum irule
  \\ fs [DISJOINT_SYM]
QED

Theorem vars_of_MEM_DISJOINT:
  MEM (q,Exp e) xs ∧ DISJOINT s (vars_of xs) ⇒
  DISJOINT s (boundvars e)
Proof
  rw []
  \\ Induct_on `xs` \\ rw []
  >- fs [vars_of_def,DISJOINT_SYM]
  \\ Cases_on `h` \\ Cases_on `r` \\ fs [vars_of_def,DISJOINT_SYM]
QED

Theorem vars_of_append:
  ∀xs ys. vars_of (xs ++ ys) = vars_of xs ∪ vars_of ys
Proof
  rw []
  \\ Induct_on ‘xs’ \\ rw []
  >- fs [vars_of_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  >- (
    fs [vars_of_def]
    \\ fs [UNION_ASSOC]
    \\ fs [INSERT_UNION_EQ]
  )
  \\ fs [vars_of_def]
  \\ fs [UNION_ASSOC]
  \\ fs [INSERT_UNION_EQ]
QED

Theorem freevars_of_append:
  ∀xs ys. freevars_of (xs ++ ys) = freevars_of xs ∪ freevars_of ys
Proof
  rw []
  \\ Induct_on ‘xs’ \\ rw []
  >- fs [freevars_of_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  >- (
    fs [freevars_of_def]
    \\ fs [UNION_ASSOC]
  )
  \\ fs [freevars_of_def]
  \\ fs [UNION_ASSOC]
QED

Theorem vars_of_DISJOINT_FILTER:
  ∀xs ys. DISJOINT s (vars_of ys) ⇒
    DISJOINT s (vars_of (FILTER P ys))
Proof
  rw []
  \\ Induct_on ‘ys’ \\ reverse $ rw []
  >- (
    last_x_assum irule
    \\ qsuff_tac `DISJOINT s (vars_of ([h] ++ ys))`
    >- fs [vars_of_append, vars_of_def, DISJOINT_SYM]
    \\ fs [Once APPEND]
  )
  \\ sg `DISJOINT s (vars_of ([h] ++ ys))`
  >- simp [Once APPEND]
  \\ qsuff_tac `DISJOINT s (vars_of ([h] ++ FILTER P ys))`
  >- simp [Once APPEND]
  \\ fs [vars_of_append]
  \\ simp [Once DISJOINT_SYM]
  \\ last_x_assum irule
  \\ fs [DISJOINT_SYM]
QED

Theorem bind_ok_EVERY_append:
  EVERY (bind_ok xs) xs ∧
  v ∉ vars_of xs ∧
  DISJOINT (boundvars x) (vars_of xs) ⇒
  EVERY (bind_ok (xs ++ [(v,Exp x)])) xs
Proof
  rw []
  \\ fs [EVERY_MEM]
  \\ rw []
  \\ first_assum $ qspec_then `e` assume_tac
  \\ Cases_on `e` \\ Cases_on `r` \\ rw []
  \\ fs [bind_ok_def,vars_of_def]
  \\ gvs []
  \\ fs [vars_of_append]
  \\ fs [DISJOINT_SYM]
  \\ fs [vars_of_def]
  \\ irule_at Any vars_of_MEM_not_in
  \\ qexists `xs` \\ qexists `q`
  \\ simp []
  \\ fs [FILTER_APPEND, vars_of_append]
  \\ once_rewrite_tac [DISJOINT_SYM]
  \\ simp []
  \\ Cases_on `v = q`
  >- simp [vars_of_def]
  \\ simp [vars_of_def]
  \\ once_rewrite_tac [DISJOINT_SYM]
  \\ irule_at Any vars_of_MEM_DISJOINT
  \\ qexists `xs` \\ qexists `q`
  \\ simp []
  \\ irule vars_of_MEM_not_in
  \\ qexists `q` \\ qexists `xs`
  \\ simp []
QED

Theorem bind_ok_rec_Exp_append:
  bind_ok_rec xs ∧
  v ∉ freevars_of xs ∧
  DISJOINT (boundvars x) (freevars_of xs) ∧
  no_shadowing x ⇒
    bind_ok_rec (xs ++ [(v,Exp x)])
Proof
  rw []
  \\ Induct_on `xs` \\ rw []
  >- fs [bind_ok_rec_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  >- (
    fs [bind_ok_rec_def]
    \\ fs [DISJOINT_SYM]
    \\ fs [freevars_of_def]
    \\ last_x_assum $ irule
    \\ fs [DISJOINT_SYM]
  )
  \\ fs [bind_ok_rec_def]
  \\ fs [DISJOINT_SYM]
  \\ fs [freevars_of_def]
  \\ last_x_assum $ irule
  \\ fs [DISJOINT_SYM]
QED

Theorem Binds_Lam:
  v ∉ set (MAP FST xs) ⇒
  (Binds xs (Lam v x) ≅? Lam v (Binds xs x)) b
Proof
  cheat (* false as stated: what is v is a free var in xs *)
QED

Theorem Binds_App:
  ∀xs x y. (Binds xs (App x y) ≅? App (Binds xs x) (Binds xs y)) b
Proof
  Induct \\ fs [Binds_def,exp_eq_refl]
  \\ PairCases \\ Cases_on ‘h1’ \\ fs [Binds_def]
  \\ rw []
  >-
   (irule exp_eq_trans
    \\ irule_at Any pure_congruenceTheory.Let_App
    \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ irule_at Any pure_congruenceTheory.Letrec_App
  \\ irule exp_eq_Letrec_cong \\ fs [exp_eq_refl]
QED

Theorem Binds_Let:
  v ∉ set (MAP FST xs) ⇒
  (Binds xs (Let v x y) ≅? Let v (Binds xs x) (Binds xs y)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any Binds_App
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl,Binds_Lam]
QED

Theorem exp_eq_Let_cong:
  (e1 ≅? e2) b ∧ (bod1 ≅? bod2) b ⇒
  (Let v e1 bod1 ≅? Let v e2 bod2) b
Proof
  simp[exp_eq_App_cong, exp_eq_Lam_cong]
QED

Theorem Binds_cong:
  (x ≅? y) b ⇒ (Binds xs x ≅? Binds xs y) b
Proof
  rw []
  \\ Induct_on `xs`
  >- rw [Binds_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  >- (
    irule exp_eq_Let_cong
    \\ rw [exp_eq_refl]
  )
  \\ irule exp_eq_Letrec_cong
  \\ rw [MAP,exp_eq_refl]
QED

Theorem not_in_vars_of_imp:
  v ∉ vars_of xs ⇒ ¬MEM v (MAP FST xs)
Proof
  rw []
  \\ Induct_on `xs`
  >- rw [vars_of_def,MAP]
  \\ Cases_on `h` \\ Cases_on `r`
  >- rw [vars_of_def,MAP]
  >- rw [vars_of_def,MAP]
QED

Theorem Binds_append:
  ∀xs ys e. Binds (xs ++ ys) e = Binds xs (Binds ys e)
Proof
  rw []
  \\ Induct_on `xs`
  >- rw [Binds_def]
  \\ Cases_on `h` \\ Cases_on `r`
  >- rw [Binds_def]
  >- rw [Binds_def]
QED

Theorem Let_ignore:
  ∀v t e. v ∉ freevars e ⇒ (Let v t e ≅? e) b
Proof
  rw []
  \\ irule exp_eq_subst_IMP_exp_eq
  \\ rw []
  \\ simp [subst_def]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ conj_asm1_tac
  >- (
    irule IMP_closed_subst
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
  )
  \\ sg ‘v ∉ freevars (subst (f \\ v) e)’
  >- (
    sg ‘(∀w. w ∈ FRANGE (f \\ v) ⇒ closed w)’
    >- (
      simp [FRANGE_FLOOKUP]
      \\ rw [EQ_IMP_THM]
      \\ first_x_assum irule
      \\ qexists ‘k’
      \\ rw []
      \\ fs [DOMSUB_FLOOKUP_THM]
    )
    \\ simp [freevars_subst]
  )
  \\ simp [subst1_notin]
  \\ simp [GSYM subst_fdomsub]
  \\ simp [exp_eq_refl]
QED

Theorem Letrec1_ignore:
  ∀v t e. v ∉ freevars e ⇒ (Letrec [(v, t)] e ≅? e) b
Proof
  rw []
  \\ irule pure_exp_relTheory.eval_wh_IMP_exp_eq
  \\ rw [] \\ gvs [subst_def,eval_wh_Letrec,subst_funs_def,bind_def]
  \\ gvs [FUPDATE_LIST,FLOOKUP_UPDATE]
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ conj_tac
  >- fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,FDIFF_def,DRESTRICT_DEF]
  \\ reverse IF_CASES_TAC >- gvs [SUBSET_DEF]
  \\ AP_TERM_TAC
  \\ irule EQ_TRANS
  \\ irule_at Any subst1_ignore
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ conj_tac
  >- fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,FDIFF_def,DRESTRICT_DEF]
  \\ gvs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ irule subst_FDIFF'
  \\ gvs []
QED

Theorem Let_Letrec1:
  ∀v t w u e.
  v ≠ w ∧ v ∉ freevars u ∧ w ∉ freevars t ⇒
    (Let w u (Letrec [(v, t)] e) ≅? Letrec [(v, t)] (Let w u e)) b
Proof
  rw []
  \\ qspecl_then [‘w’, ‘u’, ‘[(v, t)]’, ‘e’] assume_tac Let_Letrec
  \\ fs [MAP]
  \\ gvs []
  \\ irule exp_eq_trans
  \\ first_x_assum $ irule_at Any
  \\ irule exp_eq_Letrec_cong
  \\ rw [exp_eq_refl,MAP]
  \\ irule Let_ignore
  \\ rw []
QED

Theorem Letrec1_Let:
  ∀v t w u e.
  v ≠ w ∧ v ∉ freevars u ∧ w ∉ freevars t ⇒
    (Letrec [(v, t)] (Let w u e) ≅? Let w u (Letrec [(v, t)] e)) b
Proof
  rw []
  \\ simp [Once exp_eq_sym]
  \\ irule Let_Letrec1
  \\ rw []
QED

Theorem Letrec_Letrec:
  ∀v t w u e.
  v ≠ w ∧ v ∉ freevars u ∧ w ∉ freevars t ⇒
    (Letrec [(v, t)] (Letrec [(w, u)] e) ≅? Letrec [(w, u)] (Letrec [(v, t)] e)) b
Proof
  cheat
QED

Theorem Let_Let:
  ∀v t w u e.
  v ≠ w ∧ v ∉ freevars u ∧ w ∉ freevars t ⇒
    (Let v t (Let w u e) ≅? Let w u (Let v t e)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any Let_App
  \\ irule exp_eq_App_cong
  \\ rw []
  >- (
    irule Let_ignore
    \\ rw []
  )
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Lam
  \\ rw []
  \\ irule exp_eq_refl
QED

Theorem set_DIFF_DELETE_EMPTY:
  a ⊆ b ∧
  x ∉ a ⇒
  a DIFF (b DELETE x) = ∅
Proof
  fs [EXTENSION,SUBSET_DEF] \\ metis_tac []
QED

Theorem Binds_copy:
  ∀e x.
    bind_ok [] e ⇒
    (Binds [e] x ≅? Binds [e; e] x) b
Proof
  rw []
  \\ Induct_on `e` \\ rw [] \\ Induct_on `p_2` \\ rw []
  >- (
    fs [binds_ok_def,bind_ok_def]
    \\ irule exp_eq_subst_IMP_exp_eq
    \\ rw []
    \\ simp [subst_def]
    \\ irule exp_eq_trans
    \\ irule_at Any beta_equality
    \\ conj_asm1_tac
    >- (
      irule IMP_closed_subst
      \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
    )
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any beta_equality
    \\ rw []
    \\ simp [subst1_def]
    \\ irule exp_eq_trans
    \\ irule_at Any beta_equality
    \\ rw []
    >- (
      irule IMP_closed_subst
      \\ rw []
      \\ sg ‘(∀w. w ∈ FRANGE (f \\ p_1) ⇒ closed w)’
      >- (
        simp [FRANGE_FLOOKUP]
        \\ rw [EQ_IMP_THM]
        \\ first_x_assum irule
        \\ qexists ‘k’
        \\ rw []
        \\ fs [DOMSUB_FLOOKUP_THM]
      )
      \\ fs [freevars_subst]
      \\ fs [set_DIFF_DELETE_EMPTY]
    )
    \\ sg ‘(∀w. w ∈ FRANGE (f \\ p_1) ⇒ closed w)’
    >- (
      simp [FRANGE_FLOOKUP]
      \\ rw [EQ_IMP_THM]
      \\ first_x_assum irule
      \\ qexists ‘k’
      \\ rw []
      \\ fs [DOMSUB_FLOOKUP_THM]
    )
    \\ qsuff_tac `(subst1 p_1 (subst f e) (subst (f \\ p_1) e)) = (subst f e)`
    >- rw [exp_eq_refl]
    \\ qsuff_tac `p_1 ∉ freevars (subst (f \\ p_1) e)`
    >- (
      rw []
      \\ simp [subst1_notin]
      \\ simp [subst_fdomsub]
    )
    \\ simp [freevars_subst]
  )
  \\ fs [binds_ok_def,bind_ok_def]
  \\ irule exp_eq_subst_IMP_exp_eq
  \\ rw []
  \\ simp [subst_def]
  \\ simp [FDIFF_FDIFF]
  \\ simp [Once exp_eq_sym]
  \\ qsuff_tac `p_1 ∉ freevars (Letrec [(p_1,subst (FDIFF f {p_1}) e)] (subst (FDIFF f {p_1}) x))`
  >- (
    rw []
    \\ irule Letrec1_ignore
    \\ rw []
  )
  \\ simp [freevars_def]
QED

Theorem bind_ok_sublist:
  ∀x xs ys e. bind_ok (ys ++ x::xs) e ⇒ bind_ok (ys ++ xs) e
Proof
  rw []
  \\ Cases_on `e` \\ Cases_on `r` \\ rw [] \\ fs [bind_ok_def]
  \\ fs [FILTER_APPEND, vars_of_append]
  \\ fs [DISJOINT_SYM]
  \\ Cases_on `x` \\ Cases_on `r` \\ rw []
  >- (
    Cases_on `q' = q`
    >- gvs []
    \\ gvs []
    \\ fs [vars_of_def, DISJOINT_SYM]
  )
  \\ Cases_on `q' = q`
  >- gvs []
  \\ gvs []
  \\ fs [vars_of_def, DISJOINT_SYM]
QED

Theorem Let_Let_copy:
  ∀v w x y e.
    v ≠ w ∧
    w ∉ freevars x ∧
    v ∉ freevars x ⇒
    (Let v x (Let v x (Let w y e)) ≅? Let v x (Let w y (Let v x e))) b
Proof
  rw []
  \\ irule exp_eq_subst_IMP_exp_eq
  \\ rw []
  \\ simp [Once subst_def]
  \\ simp [Once subst_def]
  \\ simp [Once exp_eq_sym]
  \\ simp [Once subst_def]
  \\ simp [Once subst_def]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ conj_asm1_tac
  >- (
    irule IMP_closed_subst
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
  )
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ conj_asm1_tac
  >- (
    irule IMP_closed_subst
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
  )
  \\ simp [Once exp_eq_sym]
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ conj_tac
  >- (
    fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
    \\ fs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
  )
  \\ simp [FUNION_FUPDATE_2]
  \\ simp [subst_def]
  \\ simp [DOMSUB_FUPDATE_THM]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Let
  \\ rw []
  >- (
    fs [FLOOKUP_closed_FRANGE_closed]
    \\ sg `(∀n. n ∈ FRANGE (f \\ w |+ (v,subst f x)) ⇒ closed n)`
    >- (
      rw []
      >- simp []
      \\ first_assum $ qspec_then `n` assume_tac
      \\ fs [FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM]
      \\ first_x_assum irule
      \\ qexists ‘k’
      \\ simp []
    )
    \\ simp [freevars_subst]
  )
  >- (
    fs [FLOOKUP_closed_FRANGE_closed]
    \\ sg `(∀n. n ∈ FRANGE (f |+ (v,subst f x)) ⇒ closed n)`
    >- (
      rw []
      >- simp []
      \\ first_assum $ qspec_then `n` assume_tac
      \\ fs [FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM]
      \\ first_x_assum irule
      \\ qexists ‘k’
      \\ simp []
    )
    \\ simp [freevars_subst]
  )
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ rw []
  >- (
    irule IMP_closed_subst
    \\ rw []
    >- simp []
    >- (
      fs [FLOOKUP_closed_FRANGE_closed]
      \\ first_assum $ qspec_then `v'` assume_tac
      \\ fs [FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM]
      \\ first_x_assum irule
      \\ qexists `k`
      \\ rw []
    )
    \\ qsuff_tac `freevars x DELETE w ⊆ FDOM f DELETE w`
    >- (
      rw []
      \\ gvs [DELETE_NON_ELEMENT]
    )
    \\ fs [SUBSET_DELETE_BOTH]
  )
  \\ simp [subst_def]
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ rw []
  >- (
    irule IMP_closed_subst
    \\ rw []
    >- simp []
    \\ fs [FLOOKUP_closed_FRANGE_closed]
    \\ first_assum $ qspec_then `v'` assume_tac
    \\ fs [FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM]
    \\ first_x_assum irule
    \\ qexists `k`
    \\ rw []
  )
  \\ simp [subst_def]
  \\ irule exp_eq_Let_cong
  \\ rw []
  >- (
    qsuff_tac `subst (f |+ (v,subst f x)) x = subst (f \\ w |+ (v,subst f x)) x`
    >- simp [DOMSUB_COMMUTES, exp_eq_refl]
    \\ qsuff_tac `subst (f |+ (v,subst f x)) x = subst ((f |+ (v,subst f x)) \\ w) x`
    >- simp [DOMSUB_FUPDATE_NEQ]
    \\ simp [subst_fdomsub]
  )
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ conj_tac
  >- (
    rw []
    >- (
      fs [FLOOKUP_closed_FRANGE_closed]
      \\ first_assum $ qspec_then `v'` assume_tac
      \\ fs [FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM]
      \\ first_x_assum irule
      \\ qexists `k`
      \\ rw []
    )
    >- simp []
    >- (
      fs [FLOOKUP_closed_FRANGE_closed]
      \\ first_assum $ qspec_then `v'` assume_tac
      \\ fs [FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM]
      \\ first_x_assum irule
      \\ qexists `k`
      \\ rw []
    )
  )
  \\ simp [FUNION_FUPDATE_2, DOMSUB_FUPDATE_THM]
  \\ qsuff_tac `subst (f |+ (v,subst f x)) x = subst f x`
  >- rw [exp_eq_refl]
  \\ qspecl_then [`(f |+ (v,subst f x))`, `x`, `v`] assume_tac subst_fdomsub
  \\ gvs []
  \\ qspecl_then [`f`, `x`, `v`] assume_tac subst_fdomsub
  \\ gvs []
QED

Theorem Let_Letrec1_copy:
  ∀v w x y e.
    v ≠ w ∧
    w ∉ freevars x ∧
    v ∉ freevars x ⇒
    (Let v x (Let v x (Letrec [(w, y)] e)) ≅? Let v x (Letrec [(w, y)] (Let v x e))) b
Proof
  rw []
  \\ irule exp_eq_subst_IMP_exp_eq
  \\ rw []
  \\ simp [Once subst_def]
  \\ simp [Once subst_def]
  \\ simp [Once exp_eq_sym]
  \\ simp [Once subst_def]
  \\ simp [Once subst_def]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ conj_asm1_tac
  >- (
    irule IMP_closed_subst
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
  )
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ conj_asm1_tac
  >- (
    irule IMP_closed_subst
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
  )
  \\ simp [Once exp_eq_sym]
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ conj_tac
  >- (
    fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
    \\ fs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
  )
  \\ simp [FUNION_FUPDATE_2]
  \\ simp [subst_def]
  \\ simp [DOMSUB_FUPDATE_THM]
  \\ cheat
QED

Theorem Binds_MEM:
  ∀xs e x.
    MEM e xs ∧ binds_ok xs ⇒
    (Binds xs x ≅? Binds (xs ++ [e]) x) b
Proof
  qsuff_tac
    ‘∀xs ys e x. MEM e xs ∧ ALL_DISTINCT (MAP FST xs) ∧ EVERY (bind_ok (ys ++ xs)) xs ∧ bind_ok_rec xs ⇒
      (Binds xs x ≅? Binds (xs ++ [e]) x) b’
  >- (
    fs [binds_ok_def] \\ metis_tac [APPEND]
  )
  \\ Induct \\ fs []
  \\ reverse $ rw []
  >- (
    sg ‘EVERY (bind_ok ((ys ++ [h]) ++ xs)) xs’
    >- asm_rewrite_tac [GSYM APPEND_ASSOC,APPEND]
    \\ sg `bind_ok_rec ([h] ++ xs)`
    >- simp [APPEND]
    \\ sg `bind_ok_rec xs`
    >- (
      irule bind_ok_rec_APPEND
      \\ qexists `[h]`
      \\ simp []
    )
    \\ last_x_assum $ drule_all
    \\ qspec_then ‘[h]’ assume_tac Binds_append
    \\ first_assum $ qspec_then ‘xs’ mp_tac
    \\ first_x_assum $ qspec_then ‘xs++[e]’ mp_tac
    \\ fs []
    \\ rw []
    \\ irule Binds_cong
    \\ simp []
  )
  \\ last_x_assum kall_tac
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘ys’
  \\ Induct_on ‘xs’
  >- (
    fs []
    \\ rw []
    \\ irule Binds_copy
    \\ Induct_on `e` \\ Induct_on `p_2`
    \\ rw [] \\ fs [binds_ok_def,bind_ok_def,vars_of_def]
  )
  \\ rw []
  \\ first_x_assum $ qspec_then ‘ys’ assume_tac
  \\ gvs []
  \\ sg ‘bind_ok (ys ++ e::xs) e’
  >- (
    sg ‘bind_ok (ys ++ [e] ++ xs) e’
    >- (
      irule bind_ok_sublist
      \\ qexists ‘h’
      \\ asm_rewrite_tac [GSYM APPEND_ASSOC,APPEND]
    )
    \\ asm_rewrite_tac [Once CONS_APPEND, APPEND_ASSOC]
  )
  \\ gvs []
  \\ sg ‘EVERY (bind_ok (ys ++ e::xs)) xs’
  >- (
    sg ‘EVERY (bind_ok (ys ++ [e] ++ xs)) xs’
    >- (
      fs [EVERY_MEM]
      \\ rw []
      \\ irule bind_ok_sublist
      \\ qexists ‘h’
      \\ asm_rewrite_tac [GSYM APPEND_ASSOC,APPEND]
      \\ first_x_assum $ irule
      \\ rw []
    )
    \\ asm_rewrite_tac [Once CONS_APPEND, APPEND_ASSOC]
  )
  \\ gvs []
  \\ irule exp_eq_trans
  \\ qexists `Binds (e::e::h::xs) x`
  \\ rw []
  >- (
    sg `(Binds [e; e] (Binds (h::xs) x) ≅? Binds (e::e::h::xs) x) b`
    >- simp [GSYM Binds_append, exp_eq_refl]
    \\ sg `(Binds [e] (Binds (h::xs) x) ≅? Binds [e; e] (Binds (h::xs) x)) b`
    >- (
      irule Binds_copy
      \\ Cases_on ‘e’ \\ Cases_on ‘r’ \\ fs [bind_ok_def, vars_of_def]
    )
    \\ gvs [GSYM Binds_append]
  )
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ qexists `Binds (e::e::h::(xs ++ [e])) x`
  \\ rw []
  >- (
    sg `(Binds [e; e] (Binds (h::(xs ++ [e])) x) ≅? Binds (e::e::h::(xs ++ [e])) x) b`
    >- simp [GSYM Binds_append, exp_eq_refl]
    \\ sg `(Binds [e] (Binds (h::(xs ++ [e])) x) ≅? Binds [e; e] (Binds (h::(xs ++ [e])) x)) b`
    >- (
      irule Binds_copy
      \\ Cases_on ‘e’ \\ Cases_on ‘r’ \\ fs [bind_ok_def, vars_of_def]
    )
    \\ gvs [GSYM Binds_append]
  )
  \\ simp [Once exp_eq_sym]
  \\ Cases_on ‘e’ \\ Cases_on ‘r’ \\ Cases_on ‘h’ \\ Cases_on ‘r’ \\ rw []
  >- (
    irule exp_eq_trans
    \\ irule_at Any Let_Let_copy
    \\ fs [bind_ok_def]
    \\ rw []
    >- fs [bind_ok_rec_def]
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Let_Let_copy
    \\ rw []
    >- fs [bind_ok_rec_def]
    \\ irule exp_eq_Let_cong
    \\ simp [exp_eq_refl]
    \\ irule exp_eq_Let_cong
    \\ simp [exp_eq_refl]
    \\ simp [Once exp_eq_sym]
    \\ last_x_assum $ irule
    \\ fs [bind_ok_rec_def]
  )
  >- (
    cheat
  )
  >- (
    cheat
  )
  \\ cheat
QED

Theorem list_subst_rel_IMP_exp_eq_lemma:
  ∀xs x y.
    list_subst_rel xs x y ∧ binds_ok xs ∧
    DISJOINT (boundvars x) (vars_of xs) ∧ (* v ∉ boundvars e (where e ∈ MAP SND xs), this is required for DISJOINT (boundvars x) (set (MAP FST xs)) in bind_ok *)
    DISJOINT (boundvars x) (freevars x) ∧ (* v ∉ freevars x *)
    DISJOINT (boundvars x) (freevars_of xs) ∧ (* v ∉ freevars e (where (_, e) ∈ xs) *)
    no_shadowing x ⇒
    (Binds xs x ≅? Binds xs y) b
Proof
  Induct_on ‘list_subst_rel’
  \\ rpt strip_tac \\ fs [exp_eq_refl]
  >~ [‘Var’] >- (
    rw []
    \\ fs [binds_ok_def,EVERY_MEM,bind_ok_def]
    \\ res_tac
    \\ fs [bind_ok_def]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_MEM
    \\ first_assum $ irule_at $ Pos hd
    \\ fs [EVERY_MEM,binds_ok_def]
    \\ fs [Binds_append]
    \\ sg `(Let v x (Var v) ≅? x) b`
    >- irule Let_Var
    \\ sg `(Binds xs (Let v x (Var v)) ≅? Binds xs x) b`
    >- (
      irule Binds_cong
      \\ simp []
    )
    \\ irule exp_eq_trans
    \\ pop_assum $ irule_at Any
    \\ irule exp_eq_trans
    \\ irule_at (Pos hd) Binds_cong
    \\ drule_then (qspec_then `b` assume_tac) x_equiv_IMP_weak
    \\ pop_assum $ irule_at $ Pos hd
    \\ fs []
  )
  >~ [‘Var’] >- (
    rw []
    \\ fs [binds_ok_def,EVERY_MEM,bind_ok_def]
    \\ res_tac
    \\ fs [bind_ok_def]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_MEM
    \\ first_assum $ irule_at $ Pos hd
    \\ fs [EVERY_MEM,binds_ok_def]
    \\ fs [Binds_append]
    \\ irule Binds_cong
    \\ irule Let_Var
  )
  >~ [‘Let _ _ _’] >- (
    fs [Binds_snoc]
    \\ irule exp_eq_trans
    \\ last_x_assum $ irule_at Any
    \\ conj_tac
    >- (
      fs [binds_ok_def,bind_ok_def]
      \\ fs [ALL_DISTINCT_APPEND]
      \\ fs [DISJOINT_SYM]
      \\ fs [not_in_vars_of_imp]
      \\ fs [vars_of_DISJOINT_MAP_FST]
      \\ fs [FILTER_APPEND]
      \\ fs [vars_of_DISJOINT_FILTER]
      \\ fs [bind_ok_EVERY_append]
      \\ fs [bind_ok_rec_def]
      \\ fs [bind_ok_rec_Exp_append]
    )
    \\ conj_tac
    >- (
      simp [vars_of_append,vars_of_def,DISJOINT_SYM]
      \\ fs [DISJOINT_SYM]
    )
    \\ conj_tac
    >- (
      fs [IN_DISJOINT]
      \\ rw []
      \\ metis_tac []
    )
    \\ conj_tac
    >- (
      fs [freevars_of_append, freevars_of_def]
      \\ fs [DISJOINT_SYM]
    )
    \\ irule_at Any exp_eq_trans
    \\ irule_at Any Binds_Let
    \\ irule_at Any exp_eq_trans
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule_at (Pos $ el 2) Binds_Let
    \\ irule_at Any exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ once_rewrite_tac [exp_eq_sym]
    \\ last_x_assum $ irule_at $ Pos hd
    \\ fs [binds_ok_def,ALL_DISTINCT_APPEND,SF CONJ_ss,bind_ok_def]
    \\ once_rewrite_tac [DISJOINT_SYM] \\ fs [vars_of_append,vars_of_def]
    \\ once_rewrite_tac [DISJOINT_SYM] \\ fs []
    \\ fs [IN_DISJOINT,not_in_vars_of_imp]
  )
  >- (
    irule exp_eq_trans
    \\ last_x_assum $ irule_at Any
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_MEM
    \\ last_x_assum $ irule_at $ Pos hd
    \\ gvs []
    \\ simp [Binds_append,exp_eq_refl]
  )
  >~ [‘App’] >-
   cheat
  >~ [‘Prim’] >-
   cheat
  >~ [‘Lam’] >-
   cheat
  >- (
    cheat
  )
  \\ rename [‘Letrec’]
  \\ cheat
QED

Theorem list_subst_rel_IMP_exp_eq_lemma_specialized:
  ∀xs x y.
    list_subst_rel xs x y ∧ binds_ok xs ∧
    DISJOINT (boundvars x) (vars_of xs) ∧ no_shadowing x ∧
    DISJOINT (boundvars x) (freevars x) ∧
    DISJOINT (boundvars x) (freevars_of xs) ⇒
    Binds xs x ≅ Binds xs y
Proof
  rw []
  \\ irule list_subst_rel_IMP_exp_eq_lemma
  \\ simp []
QED

Theorem list_subst_rel_IMP_exp_eq:
  list_subst_rel [] x y ∧ no_shadowing x ∧ closed x ⇒
  (x ≅? y) b
Proof
  rw [] \\ drule list_subst_rel_IMP_exp_eq_lemma
  \\ fs [binds_ok_def,vars_of_def,freevars_of_def,closed_def,bind_ok_rec_def]
QED

(*

Need to prove:

  list_subst_rel l x z ==>
  ?n y. NRC n deep_subst_rel x y /\ expand_subst_rel l y z

where

  expand_subst_rel [] x y = (x = y) /\
  expand_subst_rel ((v,b)::l) x y = ?z. subst_rel v b x z /\ expand_subst_rel l z y

  NRC 0 R x y = (x = y) /\
  NRC (SUC n) R x y = ?z. R x z /\ NRC n R z y

in order to prove:

  list_subst_rel [] x y ==> x ~=~ y

*)

(*

TODO:
 - remember to add a simplifying pass after inlining (particularly to simplify Case)
 - also would be nice to check dead code elimination too (+unused lambda abstraction elimination?)
*)

val _ = export_theory();
