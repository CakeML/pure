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
  (∀v x x' l.
    MEM (v, Exp x) l ∧ list_subst_rel (FILTER (λ(w,_). w ≠ v) l) x x' ⇒
    list_subst_rel l (Var v) x') ∧
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

Definition vars_of_def:
  vars_of [] = {} ∧
  vars_of ((v,Exp e)::rest) = v INSERT boundvars e ∪ vars_of rest ∧
  vars_of ((v,Rec e)::rest) = v INSERT boundvars e ∪ vars_of rest
End

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

Theorem vars_of_MEM_not_in:
  MEM (q,Exp e) xs ∧ v ∉ vars_of xs ⇒
  v ∉ boundvars e
Proof
  rw []
  \\ Induct_on `xs` \\ rw []
  >- fs [vars_of_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ fs [vars_of_def]
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
  >- simp [vars_of_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ fs [vars_of_def, UNION_ASSOC]
  >- cheat
  \\ cheat
QED

Theorem vars_of_append_FILTER:
  ∀xs ys. vars_of (FILTER P (xs ++ ys)) = vars_of (FILTER P xs) ∪ vars_of (FILTER P ys)
Proof
  cheat
QED

Theorem vars_of_DISJOINT_FILTER:
  ∀xs ys. DISJOINT s (vars_of ys) ⇒
  DISJOINT s (vars_of (FILTER P ys))
Proof
  cheat
QED

Theorem Binds_Lam:
  v ∉ set (MAP FST xs) ⇒
  (Binds xs (Lam v x) ≅? Lam v (Binds xs x)) b
Proof
  cheat
QED

Theorem Binds_App:
  (Binds xs (App x y) ≅? App (Binds xs x) (Binds xs y)) b
Proof
  cheat
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
  cheat
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
      \\ cheat
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
  \\ fs [vars_of_append]
  \\ Cases_on `x` \\ Cases_on `r` \\ rw [] \\ fs [vars_of_def]
  \\ cheat
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
    ‘∀xs ys e x. MEM e xs ∧ ALL_DISTINCT (MAP FST xs) ∧ EVERY (bind_ok (ys ++ xs)) xs ⇒
      (Binds xs x ≅? Binds (xs ++ [e]) x) b’
  >- (
    fs [binds_ok_def] \\ metis_tac [APPEND]
  )
  \\ Induct \\ fs []
  \\ reverse $ rw []
  >- (
    sg ‘EVERY (bind_ok ((ys ++ [h]) ++ xs)) xs’ 
    >- asm_rewrite_tac [GSYM APPEND_ASSOC,APPEND]
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
    >- cheat (* needs assumption in binds_ok ??? *)
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Let_Let_copy
    \\ rw []
    >- cheat (* Same as above *)
    \\ irule exp_eq_Let_cong
    \\ simp [exp_eq_refl]
    \\ irule exp_eq_Let_cong
    \\ simp [exp_eq_refl]
    \\ simp [Once exp_eq_sym]
  )
  >- (
    cheat
  )
  >- (
    cheat
  )
  \\ cheat
QED

Theorem Binds_FILTER:
  v ∉ freevars x ⇒
  (Binds (FILTER (λ(w,_). w ≠ v) xs) x ≅? Binds xs x) b
Proof
  
QED

Theorem list_subst_rel_IMP_exp_eq_lemma:
  ∀xs x y.
    list_subst_rel xs x y ∧ binds_ok xs ∧
    DISJOINT (boundvars x) (set (MAP FST xs)) ∧ (* v ∉ set (MAP FST xs) *)
    DISJOINT (boundvars x) (vars_of xs) ∧ (* v ∉ boundvars e (where e ∈ MAP SND xs), this is required for DISJOINT (boundvars x) (set (MAP FST xs)) in bind_ok *)
    DISJOINT (boundvars x) (freevars x) ∧ (* v ∉ freevars x *)
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
    \\ last_x_assum $ irule_at Any
  
    \\ cheat

    (* \\ fs [MAP_FILTER,FILTER_ALL_DISTINCT]
    \\ irule exp_eq_trans
    \\ first_x_assum $ irule_at Any
    \\ fs [GSYM EVERY_MEM] *)
    
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
      \\ rw []
      >- (
        fs [EVERY_MEM]
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
        \\ fs [vars_of_append_FILTER]
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
      )
      >- (
        fs [vars_of_append_FILTER]
        \\ fs [DISJOINT_SYM]
        \\ fs [vars_of_def]
        \\ fs [vars_of_DISJOINT_FILTER]
      )
      \\ cheat (* bind_ok_rec (xs ++ [(v,Exp x)]) *)
    )
    \\ conj_tac
    >- simp [DISJOINT_SYM]
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
    DISJOINT (boundvars x) (freevars x) ⇒
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
  \\ fs [binds_ok_def,vars_of_def,closed_def]
QED

(*



Theorem xxx:
  list_subst_rel (l ++ [(v,x)]) t u = ∃r. list_subst_rel l t r ∧ subst_rel v x r u
Proof
  cheat
QED

Inductive list_deep_rel:
[~refl:]
  (∀l x. list_deep_rel l x x) ∧
[~left:]
  (∀l x y z. deep_subst_rel x y ∧ list_deep_rel l y z ⇒ list_deep_rel l x z) ∧
[~right:]
  (∀l x y z. list_deep_rel l x y ∧ deep_subst_rel y z ⇒ list_deep_rel l x z) ∧
[~cons:]
  (∀v e l x y z. subst_rel v e x y ∧ list_deep_rel l y z ⇒ list_deep_rel ((v,e)::l) x z) ∧
[~trans:]
  (∀l x y z. list_deep_rel l x y ∧ list_deep_rel l y z ⇒ list_deep_rel l x z) ∧
[~ignore:]
  (∀l m x y. list_deep_rel l x y ⇒ list_deep_rel (m::l) x y)
End

Theorem list_subst_IMP_list_deep_rel:
  ∀l x y. list_subst_rel l x y ⇒ list_deep_rel l x y
Proof
  Induct_on ‘list_subst_rel’
  \\ rpt strip_tac
  >- simp [list_deep_rel_refl]
  >~ [‘Var _’]
  >- (
    Induct_on ‘l’
    >- simp []
    \\ simp []
    \\ rpt strip_tac
    \\ gvs []
    >- (
      irule list_deep_rel_cons
      \\ irule_at Any list_deep_rel_refl
      \\ irule subst_rel_Var
    )
    \\ irule list_deep_rel_ignore
    \\ simp []
  )
  >~ [‘Let _ _ _’]
  >- (
    irule list_deep_rel_trans
    \\ qexists ‘Let v x' y’
    \\ conj_tac
    >- cheat
    \\ irule list_deep_rel_left
    \\ irule_at Any deep_subst_rel_Let
  )
QED

Theorem list_deep_rel_semantics:
  list_deep_rel [] t u ⇒ (t ≅? u) b
Proof
  qsuff_tac ‘∀l t u. list_deep_rel l t u ∧ l = [] ⇒ (t ≅? u) b’
  >- fs []
  \\ Induct_on ‘list_deep_rel’
  \\ simp []
  \\ rpt strip_tac
  >- simp [exp_eq_refl]
  \\ irule exp_eq_trans
  \\ first_x_assum $ irule_at Any
  \\ simp [deep_subst_rel_IMP_exp_eq]
QED


Inductive e_subst_rel:
[~refl:]
  (∀x y b l. (x ≅? y) b ⇒ e_subst_rel l x y) ∧
[~Cons:]
  (∀x y v e l. (∃u. subst_rel v e x u ∧ e_subst_rel l u y) ⇒ e_subst_rel ((v,e)::l) x y)
End

Definition expand_subst_rel_def:
  expand_subst_rel [] x y = (x = y) ∧
  expand_subst_rel ((v,e)::l) x y = ∃u. subst_rel v e x u ∧ expand_subst_rel l u y
End

Theorem expand_subst_rel_refl:
  expand_subst_rel l t t
Proof
  Induct_on ‘l’
  >- simp [expand_subst_rel_def]
  \\ Cases_on ‘h’
  \\ simp [expand_subst_rel_def]
  \\ qexists ‘t’
  \\ simp [subst_rel_refl]
QED

Theorem list_subst_IMP_e_subst_rel:
  list_subst_rel l x y ⇒ e_subst_rel l x y
Proof
  cheat

  (* Induct_on ‘list_subst_rel’
  \\ rpt strip_tac
  >- simp [exp_eq_refl,e_subst_rel_refl] *)
QED


Theorem list_subst_IMP_expand_subst_rel:
  list_subst_rel l x y ⇒ expand_subst_rel l x y
Proof
  cheat

  (* Induct_on ‘list_subst_rel’
  \\ rpt strip_tac
  >- (
    Induct_on ‘l’
    >- simp [expand_subst_rel_def]
    \\ Cases_on ‘h’
    \\ simp [expand_subst_rel_def]
    \\ qexists ‘t’
    \\ rw [subst_rel_refl]
  )
  >- (
    (* Induct_on ‘l’
    >- (
      rw []
      \\ fs [expand_subst_rel_def]
    ) *)
    cheat
  )
  >- (
    Induct_on ‘l’
    >- rw []
    \\ Cases_on ‘h’
    \\ Cases_on ‘(v,x) = (q,r)’
    >- (
      rw []
      >- (
        simp [expand_subst_rel_def]
        \\ qexists ‘r’
        \\ simp [subst_rel_Var,expand_subst_rel_refl]
      )
      \\ gvs []
      \\ simp [expand_subst_rel_def]
      \\ qexists ‘(Var v)’
      \\ simp [subst_rel_refl]
    )
  )
  \\ cheat *)
QED

Theorem list_subst_rel_semantics:
  list_subst_rel [] t u ⇒ (t ≅? u) b
Proof
  cheat
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

*)

val _ = export_theory();
