(*
   Theorem that help prove inlining correct
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
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


  \\ reverse $ qsuff_tac ‘∀v. v ∈ FRANGE (f \\ w) ⇒ closed v’

  >- (
    rw []
    \\ qspecl_then [‘f \\ w’] assume_tac (iffLR FLOOKUP_closed_FRANGE_closed)
    \\ gvs []
    \\ rw []
    \\ first_x_assum irule
    \\ rw[]
    \\ first_x_assum irule
    \\ qexists ‘n’
    \\ fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
    \\ fs [DOMSUB_FAPPLY_THM]
    \\ gvs []
  )

  \\ rw []


  \\ qsuff_tac ‘w ∉ freevars (subst (f \\ w) e)’

  >- (
    rw []
    \\ qspecl_then [‘w’, ‘subst (f \\ w) e’, ‘subst f e’] assume_tac subst1_notin
    \\ gvs []
    \\ irule subst_fdomsub
    \\ rw []
  )

  \\ qsuff_tac ‘closed (subst (f \\ w) e)’
  >- (
    rw []
    \\ fs [closed_def]
  )

  \\ qspecl_then [‘f’, ‘e’, ‘w’] assume_tac subst_fdomsub
  \\ gvs []
QED

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

  >- (

    (* //TODO(kπ) there has to be a better way for this *)

    rw []
    \\ irule IMP_closed_subst
    \\ rw []
    \\ qspecl_then [‘f’] assume_tac (iffLR FLOOKUP_closed_FRANGE_closed)
    \\ gvs []
    \\ first_x_assum irule
    \\ rw []
    \\ first_x_assum irule
    \\ qexists ‘n’
    \\ rw []
  )

  \\ rw []
  \\ irule IMP_closed_subst
  \\ rw []
  \\ qspecl_then [‘f’] assume_tac (iffLR FLOOKUP_closed_FRANGE_closed)
  \\ gvs []
  \\ first_x_assum irule
  \\ rw []
  \\ first_x_assum irule
  \\ qexists ‘n’
  \\ rw []
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
  \\ cheat

  m “(Letrec _ _ ≅? _) b”

  (*
    pure_congruenceTheory.exp_eq_Letrec_cong (THEOREM)
    --------------------------------------------------
    ⊢ LIST_REL (λx y. (x ≅? y) b) (MAP SND xs) (MAP SND xs') ∧ (e ≅? e') b ∧
      MAP FST xs = MAP FST xs' ⇒
      (Letrec xs e ≅? Letrec xs' e') b
  *)
QED

  (* (Let v x (App t t') ≅? Let v x (App u u')) b *)
  (* (App (Lam v (Lam w t)) x) ≅? App (Lam v (Lam w u)) x) b *)


(*

TODO:
 - remember to add a simplifying pass after inlining (particularly to simplify Case)

*)

val _ = export_theory();
