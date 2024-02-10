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
     pure_letrec_seqTheory pure_demandTheory pure_barendregtTheory;

val _ = new_theory "pure_inline_rel";

(*------------------------------------------------------------------------------*
   Definition of what inliner can remember
 *------------------------------------------------------------------------------*)

Datatype:
  inline_mem = Simple string exp (* TODO: | Rec ... *)
End

Definition lhs_name_def[simp]:
  lhs_name (Simple v e) = v
End

(*------------------------------------------------------------------------------*
   Definition of precondition pre
 *------------------------------------------------------------------------------*)

Definition vars_of_def:
  vars_of [] = {} ∧
  vars_of ((Simple v e)::rest) = {v} ∪ freevars e ∪ vars_of rest
End

Definition pre_def:
  pre l x ⇔
    barendregt x ∧
    DISJOINT (boundvars x) (freevars x) ∧
    DISJOINT (boundvars x) (vars_of l)
End

(*------------------------------------------------------------------------------*
   Definition of inline_rel
 *------------------------------------------------------------------------------*)

Inductive inline_rel:
[~refl:]
  (∀l t.
    inline_rel l t t)
[~Var:]
  (∀v x l.
    MEM (Simple v x) l ⇒
    inline_rel l (Var v) x)
[~Let:]
  (∀l v x y.
    inline_rel l x x' ∧
    inline_rel (l ++ [Simple v x]) y y' ⇒
    inline_rel l (Let v x y) (Let v x' y'))
[~Prim:]
  (∀l p xs ys.
    LIST_REL (inline_rel l) xs ys ⇒
    inline_rel l (Prim p xs) (Prim p ys))
[~App:]
  (∀l t1 t2 u1 u2.
    inline_rel l t1 u1 ∧
    inline_rel l t2 u2 ⇒
    inline_rel l (App t1 t2) (App u1 u2))
[~Lam:]
  (∀l t u w.
    inline_rel l t u ⇒
    inline_rel l (Lam w t) (Lam w u))
[~Letrec:]
  (∀l t u xs ys.
    LIST_REL (λ(n,t1) (m,u1). n = m ∧ inline_rel l t1 u1) xs ys ∧
    inline_rel l t u ⇒
    inline_rel l (Letrec xs t) (Letrec ys u))
[~spec:]
  (∀l t u v x y x1.
    inline_rel l x y ∧
    (∀e. Letrec [(v, x)] e ≅ Let v x1 e) ∧
    v ∉ freevars x1 ∧
    DISJOINT (boundvars t) (boundvars x1) ∧
    DISJOINT (boundvars t) (freevars x1) ∧
    inline_rel (l ++ [Simple v x1]) t u ⇒
    inline_rel l (Letrec [(v, x)] t) (Letrec [(v, y)] u))
[~trans:]
  (∀l x y z.
    inline_rel l x y ∧
    inline_rel l y z ∧
    pre l y ⇒
    inline_rel l x z)
[~simp:]
  (∀l t u u1.
    inline_rel l t u ∧
    u ≅ u1 ⇒
    inline_rel l t u1)
End

(*------------------------------------------------------------------------------*
   Definition of lets_ok
 *------------------------------------------------------------------------------*)

Definition lets_ok_def:
  (lets_ok [] ⇔ T) ∧
  (lets_ok ((Simple v x)::rest) ⇔
    v ∉ freevars x ∧
    DISJOINT ({v} ∪ freevars x) (set (MAP lhs_name rest)) ∧
    lets_ok rest)
End

(*------------------------------------------------------------------------------*
   Lemmas about lets_ok etc.
 *------------------------------------------------------------------------------*)

Theorem vars_of_DISJOINT_MAP_FST:
  DISJOINT s (vars_of xs) ⇒ DISJOINT s (set (MAP lhs_name xs))
Proof
  rw []
  \\ Induct_on `xs` \\ reverse $ rw [vars_of_def]
  \\ Cases_on ‘h’ \\ gvs [vars_of_def]
  \\ gvs [DISJOINT_SYM]
QED

Theorem vars_of_append:
  ∀xs ys. vars_of (xs ++ ys) = vars_of xs ∪ vars_of ys
Proof
  rw []
  \\ Induct_on ‘xs’ \\ rw []
  >- fs [vars_of_def]
  \\ Cases_on `h`
  \\ fs [vars_of_def]
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

Theorem vars_of_not_in_MAP_FST:
  v ∉ vars_of xs ⇒ ¬MEM v (MAP lhs_name xs)
Proof
  rw []
  \\ Induct_on `xs`
  >- rw [vars_of_def,MAP]
  \\ Cases_on `h`
  \\ rw [vars_of_def,MAP]
QED

Theorem lets_ok_SNOC_alt:
  lets_ok xs ∧ v ∉ freevars x1 ∧ ~MEM v (MAP lhs_name xs) ∧
  v ∉ vars_of xs
  ⇒
  lets_ok (xs ++ [Simple v x1])
Proof
  Induct_on ‘xs’
  \\ fs [lets_ok_def,FORALL_PROD,vars_of_def]
  \\ Cases \\ rw [] \\ simp [DISJOINT_SYM,lets_ok_def]
  \\ fs [lets_ok_def,FORALL_PROD,vars_of_def]
QED

Theorem lets_ok_SNOC:
  lets_ok xs ∧ pre xs (Let v x y) ⇒
  lets_ok (xs ++ [Simple v x])
Proof
  strip_tac
  \\ irule lets_ok_SNOC_alt \\ fs []
  \\ fs [pre_def]
  \\ imp_res_tac vars_of_not_in_MAP_FST
QED

Theorem map_fst_subset_vars_of:
  ∀xs. set (MAP lhs_name xs) ⊆ vars_of xs
Proof
  Induct \\ fs [vars_of_def,FORALL_PROD] \\ fs [SUBSET_DEF]
  \\ Cases \\ gvs [vars_of_def]
QED

(*------------------------------------------------------------------------------*
   Lemmas and precondition pre
 *------------------------------------------------------------------------------*)

Theorem pre_App:
  pre xs (App x y) ⇒ pre xs x ∧ pre xs y
Proof
  gvs [pre_def,barendregt_alt_def]
  \\ fs [IN_DISJOINT]
  \\ metis_tac []
QED

Theorem pre_Prim:
  pre xs (Prim x ys) ⇒ EVERY (pre xs) ys
Proof
  gvs [pre_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,barendregt_alt_def]
QED

Theorem pre_Lam:
  pre xs (Lam w x) ⇒
  ¬MEM w (MAP lhs_name xs) ∧ w ∉ vars_of xs ∧ pre xs x
Proof
  fs [pre_def,barendregt_alt_def] \\ strip_tac
  \\ imp_res_tac vars_of_not_in_MAP_FST \\ fs []
  \\ gvs [IN_DISJOINT] \\ metis_tac []
QED

Theorem pre_SNOC:
  pre xs x ∧
  v ∉ freevars x1 ∧ v ∉ boundvars x ∧
  DISJOINT (boundvars x) (boundvars x1) ∧
  DISJOINT (boundvars x) (freevars x1) ⇒
  pre (xs ++ [Simple v x1]) x
Proof
  fs [pre_def,vars_of_append,vars_of_def,barendregt_alt_def] \\ rw []
  \\ simp [DISJOINT_SYM]
QED

Theorem pre_Let:
  pre xs (Let v x y) ⇒
  pre xs x ∧ pre (xs ++ [Simple v x]) y ∧
  ¬MEM v (MAP lhs_name xs) ∧ v ∉ vars_of xs
Proof
  fs [lets_ok_def,pre_def,barendregt_alt_def]
  \\ simp [DISJOINT_SYM,vars_of_append,vars_of_def]
  \\ strip_tac
  \\ imp_res_tac vars_of_not_in_MAP_FST \\ fs []
  \\ gvs [IN_DISJOINT]
  \\ metis_tac []
QED

Theorem pre_Letrec:
  pre xs (Letrec ys x) ⇒
  pre xs x ∧ EVERY (pre xs) (MAP SND ys) ∧
  DISJOINT (set (MAP FST ys)) (boundvars x) ∧
  EVERY (λ(v,e). ¬MEM v (MAP lhs_name xs) ∧ v ∉ vars_of xs) ys
Proof
  rpt strip_tac
  >-
   (gvs [pre_def,barendregt_alt_def]
    \\ gvs [IN_DISJOINT] \\ metis_tac [])
  >-
   (pop_assum mp_tac \\ fs [pre_def] \\ strip_tac
    \\ ‘EVERY barendregt (MAP SND ys)’ by gvs [barendregt_alt_def]
    \\ gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,pre_def,IN_DISJOINT]
    \\ gvs [IN_DISJOINT,SF SFY_ss]
    \\ rw [] \\ CCONTR_TAC \\ gvs []
    \\ first_x_assum drule
    \\ gvs [barendregt_def,IN_DISJOINT]
    \\ metis_tac [])
  \\ pop_assum mp_tac \\ fs [pre_def,barendregt_alt_def]
  \\ gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,pre_def]
  \\ rpt disch_tac
  \\ rpt gen_tac
  \\ rpt disch_tac \\ fs []
  \\ ‘set (MAP lhs_name xs) ⊆ vars_of xs’ by gvs [map_fst_subset_vars_of]
  \\ gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,pre_def,IN_DISJOINT,SUBSET_DEF]
  \\ metis_tac []
QED

(*------------------------------------------------------------------------------*
   Theorems about pushing and pulling let-expressions
 *------------------------------------------------------------------------------*)

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
QED

Theorem inline_rel_Var_trans:
  ∀v x x1 x2 l.
    MEM (Simple v x) l ∧ x ≅ x1 ∧ pre l x1 ∧ inline_rel l x1 x2 ⇒
    inline_rel l (Var v) x2
Proof
  rw []
  \\ irule inline_rel_trans
  \\ pop_assum $ irule_at Any \\ fs []
  \\ irule_at Any inline_rel_simp
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any inline_rel_Var
  \\ fs []
QED

Definition Binds_def:
  Binds [] y = y ∧
  Binds ((Simple v x)::xs) y = Let v x (Binds xs y)
End

Theorem Binds_snoc:
  ∀xs. Binds (xs ++ [Simple v x]) y = Binds xs (Let v x y)
Proof
  Induct \\ fs [Binds_def] \\ Cases \\ fs [Binds_def]
QED

Theorem exp_eq_Let_cong:
  (e1 ≅? e2) b ∧ (bod1 ≅? bod2) b ⇒
  (Let v e1 bod1 ≅? Let v e2 bod2) b
Proof
  simp[exp_eq_App_cong, exp_eq_Lam_cong]
QED

Theorem Binds_Lam:
  v ∉ set (MAP lhs_name xs) ∧
  v ∉ vars_of xs ⇒
  (Binds xs (Lam v x) ≅? Lam v (Binds xs x)) b
Proof
  rw []
  \\ Induct_on `xs` \\ rw [Binds_def]
  >- simp [exp_eq_refl]
  \\ Cases_on `h` \\ rw [Binds_def]
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ once_rewrite_tac [exp_eq_sym]
  \\ irule_at Any Let_Lam
  \\ fs [FST,vars_of_def]
  \\ irule exp_eq_Let_cong
  \\ fs [exp_eq_refl]
QED

Theorem Binds_App:
  ∀xs x y. (Binds xs (App x y) ≅? App (Binds xs x) (Binds xs y)) b
Proof
  Induct \\ fs [Binds_def,exp_eq_refl]
  \\ Cases \\ fs [Binds_def]
  \\ rw []
  \\ irule exp_eq_trans
  \\ irule_at Any pure_congruenceTheory.Let_App
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
  \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl]
QED

Theorem Binds_Let:
  v ∉ set (MAP lhs_name xs) ∧
  v ∉ vars_of xs ⇒
  (Binds xs (Let v x y) ≅? Let v (Binds xs x) (Binds xs y)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any Binds_App
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl,Binds_Lam]
QED

(*
Theorem Letrec1_Letrec:
  ∀v x xs e.
  EVERY (λ(n,u). n ∉ freevars x) xs ∧
  ¬MEM v (MAP FST xs) ⇒
    (Letrec [(v, x)] (Letrec xs e) ≅? Letrec (MAP (λ(n,t). (n, Letrec [(v, x)] t)) xs) (Letrec [(v, x)] e)) b
Proof
  rw []
  \\ sg `DISJOINT (set (MAP FST xs)) (freevars x)`
  >- (
    fs [IN_DISJOINT]
    \\ rw []
    \\ fs [MEM_MAP,FST,NOT_EXISTS]
    \\ Cases_on `x' ∉ freevars x` \\ rw []
    \\ Cases_on `y`
    \\ fs [EVERY_MEM]
    \\ last_x_assum $ qspec_then `(q, r)` assume_tac
    \\ gvs []
  )
  \\ irule exp_eq_subst_IMP_exp_eq
  \\ rw []
  \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro]
  \\ simp [subst_def]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality_Letrec
  \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro,FDIFF_FDIFF,subst_funs_def]
  \\ sg `(∀w. w ∈ FRANGE (FDIFF f {v}) ⇒ closed w)`
  >- (
    rw []
    \\ fs [FLOOKUP_DEF,PULL_EXISTS,FRANGE_DEF]
    \\ first_x_assum $ qspec_then `x'` assume_tac
    \\ gvs []
    \\ fs [FDIFF_def,DRESTRICT_DEF]
  )
  \\ conj_tac
  >- (
    fs [freevars_subst,DIFF_SUBSET]
    \\ irule SUBSET_TRANS
    \\ last_x_assum $ irule_at Any
    \\ fs [SUBSET_UNION]
    \\ fs [SUBSET_DEF]
  )
  \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ sg `closed (Letrec [(v,subst (FDIFF f {v}) x)] (subst (FDIFF f {v}) x))`
  >- (
    fs [freevars_subst,DIFF_SUBSET]
    \\ irule SUBSET_TRANS
    \\ last_x_assum $ irule_at Any
    \\ fs [SUBSET_UNION]
    \\ fs [SUBSET_DEF]
  )
  \\ fs [bind1_def]
  \\ rw [subst_def]
  \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro,FDIFF_FDIFF,subst_funs_def,FDIFF_FUPDATE]
  \\ irule exp_eq_Letrec_cong
  \\ rw []
  >- fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST]
  >- (
    fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,SND,LIST_REL_EVERY_ZIP,ZIP_MAP,EVERY_MAP]
    \\ fs [EVERY_MEM]
    \\ rw []
    \\ Cases_on `e'`
    \\ rw []
    \\ DEP_REWRITE_TAC [subst_subst_FUNION]
    \\ conj_tac
    >- (
      fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
      \\ fs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
    )
    \\ fs [FUNION_FUPDATE_2]
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any beta_equality_Letrec
    \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro,FDIFF_FDIFF,subst_funs_def]
    \\ sg `(∀w. w ∈ FRANGE (FDIFF f (set (MAP FST xs) ∪ {v})) ⇒ closed w)`
    >- (
      rw []
      \\ fs [FLOOKUP_DEF,PULL_EXISTS,FRANGE_DEF]
      \\ first_x_assum $ qspec_then `x'` assume_tac
      \\ gvs []
      \\ fs [FDIFF_def,DRESTRICT_DEF]
    )
    \\ conj_tac
    >- (
      fs [freevars_subst,DIFF_SUBSET]
      \\ fs [SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ fs [IN_DISJOINT]
      \\ rw []
      \\ metis_tac []
    )
    \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST]
    \\ sg `closed (Letrec [(v,subst (FDIFF f (set (MAP FST xs) ∪ {v})) x)]
              (subst (FDIFF f (set (MAP FST xs) ∪ {v})) x))`
    >- (
      fs [freevars_subst,DIFF_SUBSET]
      \\ fs [SUBSET_UNION]
      \\ fs [SUBSET_DEF]
      \\ fs [IN_DISJOINT]
      \\ rw []
      \\ metis_tac []
    )
    \\ fs [bind1_def]
    \\ DEP_REWRITE_TAC [subst_subst_FUNION]
    \\ conj_tac
    >- (
      fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
      \\ fs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
    )
    \\ fs [FUNION_FUPDATE_2]
    \\ simp [Once exp_eq_sym]
    \\ qmatch_goalsub_abbrev_tac ‘(subst f1 e1 ≅? subst f2 e2) b’
    \\ qsuff_tac ‘f1 = f2’
    >- simp [exp_eq_refl]
    \\ unabbrev_all_tac
    \\ fs [UNION_COMM]
    \\ MK_COMB_TAC \\ fs []
    \\ sg `FDIFF f ({v} ∪ set (MAP FST xs)) = FDIFF (FDIFF f {v}) (set (MAP FST xs))`
    >- fs [FDIFF_FDIFF]
    \\ fs []
    \\ irule subst_FDIFF'
    \\ rw []
    \\ fs [IN_DISJOINT]
    \\ res_tac
    \\ metis_tac []
  )
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ conj_tac
  >- (
    fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
    \\ fs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
  )
  \\ fs [FUNION_FUPDATE_2]
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality_Letrec
  \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro,FDIFF_FDIFF,subst_funs_def]
  \\ sg `(∀w. w ∈ FRANGE (FDIFF f (set (MAP FST xs) ∪ {v})) ⇒ closed w)`
  >- (
    rw []
    \\ fs [FLOOKUP_DEF,PULL_EXISTS,FRANGE_DEF]
    \\ first_x_assum $ qspec_then `x'` assume_tac
    \\ gvs []
    \\ fs [FDIFF_def,DRESTRICT_DEF]
  )
  \\ conj_tac
  >- (
    fs [freevars_subst,DIFF_SUBSET]
    \\ fs [SUBSET_UNION]
    \\ fs [SUBSET_DEF]
    \\ fs [IN_DISJOINT]
    \\ rw []
    \\ metis_tac []
  )
  \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ sg `closed (Letrec [(v,subst (FDIFF f (set (MAP FST xs) ∪ {v})) x)]
            (subst (FDIFF f (set (MAP FST xs) ∪ {v})) x))`
  >- (
    fs [freevars_subst,DIFF_SUBSET]
    \\ fs [SUBSET_UNION]
    \\ fs [SUBSET_DEF]
    \\ fs [IN_DISJOINT]
    \\ rw []
    \\ metis_tac []
  )
  \\ fs [bind1_def]
  \\ DEP_REWRITE_TAC [subst_subst_FUNION]
  \\ conj_tac
  >- (
    fs [FLOOKUP_DEF, PULL_EXISTS, FRANGE_DEF]
    \\ fs [FDIFF_def,DRESTRICT_DEF,DOMSUB_FAPPLY_THM]
  )
  \\ fs [FUNION_FUPDATE_2]
  \\ simp [Once exp_eq_sym]
  \\ qmatch_goalsub_abbrev_tac ‘(subst f1 e1 ≅? subst f2 e2) b’
  \\ qsuff_tac ‘f1 = f2’
  >- simp [exp_eq_refl]
  \\ unabbrev_all_tac
  \\ fs [UNION_COMM]
  \\ MK_COMB_TAC \\ fs []
  \\ sg `FDIFF f ({v} ∪ set (MAP FST xs)) = FDIFF (FDIFF f {v}) (set (MAP FST xs))`
  >- fs [FDIFF_FDIFF]
  \\ fs []
  \\ irule subst_FDIFF'
  \\ rw []
  \\ fs [IN_DISJOINT]
  \\ res_tac
  \\ metis_tac []
QED
*)

Theorem Binds_Letrec:
  EVERY (λ(v, e). v ∉ set (MAP lhs_name xs) ∧ v ∉ vars_of xs) l ⇒
    (Binds xs (Letrec l y) ≅?
     Letrec (MAP (λ(v, e). (v, Binds xs e)) l) (Binds xs y)) b
Proof
  rw []
  \\ Induct_on `xs` \\ rw [Binds_def]
  >- (
    irule exp_eq_Letrec_cong
    \\ fs [MAP_MAP_o, o_DEF,LAMBDA_PROD,FST]
    \\ conj_tac
    >- fs [FST_intro]
    \\ simp [exp_eq_refl]
    \\ fs [LIST_REL_MAP_MAP, LAMBDA_PROD, SND]
    \\ fs [EVERY_MEM]
    \\ rw []
    \\ Cases_on `e` \\ rw []
    \\ simp [exp_eq_refl]
  )
  \\ Cases_on `h` \\ rw [Binds_def]
  \\ rename [‘Let q r _’]
  \\ qsuff_tac `(Let q r (Binds xs (Letrec l y)) ≅?
                     Letrec (MAP (λ(v,t). (v,Let q r t)) (MAP (λ(v,t). (v,Binds xs t)) l))
                     (Let q r (Binds xs y))) b`
  >- fs [MAP_MAP_o, o_DEF, LAMBDA_PROD]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Letrec
  \\ fs [vars_of_def]
  \\ fs [EVERY_MAP, LAMBDA_PROD]
  \\ fs [MAP_MAP_o, o_DEF, LAMBDA_PROD, FST_intro]
  \\ conj_tac
  >-
   (fs [EVERY_MEM]
    \\ rw [MEM_MAP]
    \\ PairCases_on `e` \\ rw []
    \\ last_x_assum $ qspec_then `(e0,e1)` assume_tac
    \\ gvs [])
  \\ sg `EVERY
        (λv.
           (v ≠ q ∧ ¬MEM v (MAP lhs_name xs)) ∧ v ∉ freevars r ∧
           v ∉ vars_of xs) (MAP FST l)`
  >- (fs [EVERY_MAP, LAMBDA_PROD, FST, SF CONJ_ss]
      \\ gvs [EVERY_MEM,FORALL_PROD] \\ metis_tac [])
  \\ conj_tac >-
   (fs [EVERY_MEM]
    \\ reverse $ Cases_on `MEM q (MAP FST l)`
    >- simp []
    \\ last_x_assum $ qspec_then `q` assume_tac
    \\ gvs [])
  \\ conj_tac >-
   (fs [EVERY_MEM, IN_DISJOINT]
    \\ rw []
    \\ last_x_assum $ qspec_then `x` assume_tac
    \\ Cases_on `MEM x (MAP FST l)` \\ rw [])
  \\ irule exp_eq_Let_cong
  \\ simp [exp_eq_refl]
  \\ first_x_assum irule
  \\ fs [EVERY_MEM]
  \\ rw []
  \\ first_x_assum $ qspec_then `e` assume_tac
  \\ gvs []
  \\ PairCases_on `e` \\ simp []
  \\ gvs []
QED

Theorem Binds_Prim:
  (Binds xs (Prim op ys) ≅? Prim op (MAP (Binds xs) ys)) b
Proof
  rw []
  \\ Induct_on `xs` \\ rw [Binds_def]
  >- (
    irule exp_eq_Prim_cong
    \\ simp [LIST_REL_MAP2,Binds_def]
    \\ simp [LIST_REL_EL_EQN]
    \\ simp [exp_eq_refl]
  )
  \\ Cases_on `h` \\ rw [Binds_def]
  \\ qsuff_tac `(Let s e (Binds xs (Prim op ys)) ≅?
         Prim op (MAP (Let s e) (MAP (Binds xs) ys))) b`
  >-
   (rw []
    \\ fs [MAP_MAP_o, o_DEF,Binds_def]
    \\ irule exp_eq_trans
    \\ first_x_assum $ irule_at Any
    \\ qsuff_tac `(MAP (λx. Let s e (Binds xs x)) ys) =
                  (MAP (Binds ((Simple s e)::xs)) ys)`
    >- simp [exp_eq_refl]
    \\ simp [MAP_EQ_EVERY2,Binds_def]
    \\ simp [EVERY2_refl_EQ])
  \\ rw [Binds_def]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Prim
  \\ irule exp_eq_Let_cong
  \\ simp [exp_eq_refl,Binds_def]
QED

Theorem Binds_cong:
  (x ≅? y) b ⇒ (Binds xs x ≅? Binds xs y) b
Proof
  rw []
  \\ Induct_on `xs`
  >- rw [Binds_def]
  \\ Cases \\ rw [Binds_def]
  \\ irule exp_eq_Let_cong
  \\ rw [exp_eq_refl]
QED

Theorem Binds_append:
  ∀xs ys e. Binds (xs ++ ys) e = Binds xs (Binds ys e)
Proof
  rw []
  \\ Induct_on `xs`
  >- rw [Binds_def]
  \\ Cases_on `h`
  \\ rw [Binds_def]
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
    lets_ok [e] ⇒
    (Binds [e] x ≅? Binds [e; e] x) b
Proof
  rw []
  \\ Induct_on `e` \\ rw []
  \\ fs [lets_ok_def,Binds_def]
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
    \\ sg ‘(∀w. w ∈ FRANGE (f \\ s) ⇒ closed w)’
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
  \\ sg ‘(∀w. w ∈ FRANGE (f \\ s) ⇒ closed w)’
  >- (
    simp [FRANGE_FLOOKUP]
    \\ rw [EQ_IMP_THM]
    \\ first_x_assum irule
    \\ qexists ‘k’
    \\ rw []
    \\ fs [DOMSUB_FLOOKUP_THM]
  )
  \\ qsuff_tac `(subst1 s (subst f e) (subst (f \\ s) e)) = (subst f e)`
  >- rw [exp_eq_refl]
  \\ qsuff_tac `s ∉ freevars (subst (f \\ s) e)`
  >- (
    rw []
    \\ simp [subst1_notin]
    \\ simp [subst_fdomsub]
  )
  \\ simp [freevars_subst]
QED

Theorem Let_Let_copy:
  ∀v w x y e.
    v ≠ w ∧
    w ∉ freevars x ∧
    v ∉ freevars x ⇒
    (Let v x (Let v x (Let w y e)) ≅?
     Let v x (Let w y (Let v x e))) b
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

Theorem FDIFF_SING:
  FDIFF f {x} = f \\ x
Proof
  fs [FDIFF_def,fmap_EXT,DRESTRICT_DEF,DOMSUB_FAPPLY_NEQ]
  \\ gvs [EXTENSION]
QED

Theorem Letrec1_dup:
  (Letrec [(v,x)] (Letrec [(v,x)] y) ≅?
   Letrec [(v,x)] y) b
Proof
  rw []
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [freevars_def,subst_def] \\ rw []
  \\ simp [Once eval_wh_Letrec]
  \\ gvs [subst_funs_def]
  \\ reverse $ rw [bind_def]
  >- simp [Once eval_wh_Letrec,subst_funs_def,bind_def]
  \\ fs [FUPDATE_LIST]
  \\ DEP_REWRITE_TAC [subst1_ignore]
  \\ fs [FDIFF_SING]
QED

Theorem Let_dup:
  v ∉ freevars x ⇒
  (Let v x (Let v x y) ≅?
   Let v x y) b
Proof
  rw []
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [freevars_def,subst_def] \\ rw []
  \\ simp [Once eval_wh_App,eval_wh_Lam]
  \\ reverse $ rw [bind_def]
  >- fs [Once eval_wh_App,eval_wh_Lam,bind_def,SF SFY_ss,FLOOKUP_UPDATE]
  \\ DEP_REWRITE_TAC [subst1_ignore]
  \\ fs [FDIFF_SING]
  \\ DEP_REWRITE_TAC [freevars_subst]
  \\ gvs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM]
  \\ ntac 2 (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp [Once EQ_SYM_EQ]
  \\ irule subst_fdomsub \\ fs []
QED

Theorem Letrec1_Let_copy:
  ∀v w x y e.
    v ≠ w ∧
    w ∉ freevars x ⇒
    (Letrec [(v,x)] (Letrec [(v,x)] (Let w y e)) ≅?
     Letrec [(v,x)] (Let w y (Letrec [(v,x)] e))) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at (Pos hd) Letrec1_dup
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [freevars_def,subst_def] \\ rw []
  \\ simp [Once eval_wh_Letrec,subst_funs_def]
  \\ reverse $ rw [bind_def]
  >- fs [eval_wh_Letrec,bind_def,subst_funs_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ simp [Once eval_wh_Letrec,subst_funs_def,bind_def]
  \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST,FDIFF_SING]
  \\ once_rewrite_tac [DOMSUB_COMMUTES] \\ fs []
  \\ ‘subst (f \\ v \\ w) x = subst (f \\ v) x’ by
    (simp [Once EQ_SYM_EQ] \\ irule subst_fdomsub \\ fs [])
  \\ fs [] \\ fs [subst_def]
  \\ simp [Once eval_wh_App,eval_wh_Lam,subst_funs_def]
  \\ reverse $ rw [bind_def]
  >- fs [eval_wh_App,eval_wh_Lam,bind_def,subst_funs_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ gvs [FLOOKUP_UPDATE,FDIFF_SING,DOMSUB_FUPDATE_THM]
  \\ simp [Once eval_wh_App,eval_wh_Lam,subst_funs_def,bind_def]
  \\ gvs [FLOOKUP_UPDATE,FDIFF_SING,DOMSUB_FUPDATE_THM]
  \\ gvs [subst_def,FDIFF_SING,DOMSUB_FUPDATE_THM]
  \\ ‘∀a. subst1 w a (subst (f \\ v) x) = (subst (f \\ v) x)’ by
   (rw []
    \\ DEP_REWRITE_TAC [subst1_ignore]
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [FRANGE_DEF,PULL_EXISTS,FLOOKUP_DEF,DOMSUB_FAPPLY_NEQ])
  \\ fs []
  \\ fs [eval_wh_Letrec,subst_funs_def,FUPDATE_LIST]
  \\ DEP_REWRITE_TAC [bind_eq_subst]
  \\ gvs [FLOOKUP_UPDATE]
  \\ drule_at (Pos last) subst1_subst1
  \\ disch_then $ DEP_REWRITE_TAC o single
  \\ fs []
  \\ metis_tac [DOMSUB_COMMUTES]
QED

Theorem Letrec1_Letrec1_copy:
  ∀v w x y e.
    v ≠ w ∧
    w ∉ freevars x ⇒
    (Letrec [(v,x)] (Letrec [(v,x)] (Letrec [(w,y)] e)) ≅?
     Letrec [(v,x)] (Letrec [(w,y)] (Letrec [(v,x)] e))) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at (Pos hd) Letrec1_dup
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [freevars_def,subst_def] \\ rw []
  \\ simp [Once eval_wh_Letrec,subst_funs_def]
  \\ reverse $ rw [bind_def]
  >- fs [eval_wh_Letrec,bind_def,subst_funs_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ simp [Once eval_wh_Letrec,subst_funs_def,bind_def]
  \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST,FDIFF_SING]
  \\ once_rewrite_tac [DOMSUB_COMMUTES] \\ fs []
  \\ ‘subst (f \\ v \\ w) x = subst (f \\ v) x’ by
    (simp [Once EQ_SYM_EQ] \\ irule subst_fdomsub \\ fs [])
  \\ fs [] \\ fs [subst_def,FDIFF_SING,DOMSUB_FUPDATE_THM]
  \\ simp [Once eval_wh_Letrec,subst_funs_def]
  \\ reverse $ rw [bind_def]
  >- fs [eval_wh_Letrec,bind_def,subst_funs_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ gvs [FLOOKUP_UPDATE,FDIFF_SING,DOMSUB_FUPDATE_THM,FUPDATE_LIST]
  \\ simp [Once eval_wh_Letrec,subst_funs_def,bind_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ gvs [FLOOKUP_UPDATE,FDIFF_SING,DOMSUB_FUPDATE_THM]
  \\ gvs [subst_def,FDIFF_SING,DOMSUB_FUPDATE_THM]
  \\ ‘∀a. subst1 w a (subst (f \\ v) x) = (subst (f \\ v) x)’ by
   (rw []
    \\ DEP_REWRITE_TAC [subst1_ignore]
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [FRANGE_DEF,PULL_EXISTS,FLOOKUP_DEF,DOMSUB_FAPPLY_NEQ])
  \\ fs []
  \\ fs [eval_wh_Letrec,subst_funs_def,FUPDATE_LIST]
  \\ DEP_REWRITE_TAC [bind_eq_subst]
  \\ gvs [FLOOKUP_UPDATE]
  \\ drule_at (Pos last) subst1_subst1
  \\ disch_then $ DEP_REWRITE_TAC o single
  \\ fs []
  \\ metis_tac [DOMSUB_COMMUTES]
QED

Theorem Let_Letrec1_copy:
  ∀v w x y e.
    v ≠ w ∧
    w ∉ freevars x ∧
    v ∉ freevars x ⇒
    (Let v x (Let v x (Letrec [(w, y)] e)) ≅?
     Let v x (Letrec [(w, y)] (Let v x e))) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at (Pos hd) Let_dup \\ fs []
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [freevars_def,subst_def] \\ rw []
  \\ simp [Once eval_wh_App,eval_wh_Lam,subst_funs_def]
  \\ reverse $ rw [bind_def]
  >- fs [eval_wh_App,eval_wh_Lam,bind_def,subst_funs_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ simp [Once eval_wh_App,eval_wh_Lam,subst_funs_def,bind_def]
  \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST,FDIFF_SING]
  \\ once_rewrite_tac [DOMSUB_COMMUTES] \\ fs []
  \\ ‘subst (f \\ v \\ w) x = subst (f \\ v) x’ by
    (simp [Once EQ_SYM_EQ] \\ irule subst_fdomsub \\ fs [])
  \\ fs [] \\ fs [subst_def,FDIFF_SING,DOMSUB_FUPDATE_THM]
  \\ simp [Once eval_wh_Letrec,subst_funs_def]
  \\ reverse $ rw [bind_def]
  >- fs [eval_wh_Letrec,bind_def,subst_funs_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ fs [FLOOKUP_UPDATE,FDIFF_SING,DOMSUB_FUPDATE_THM,FUPDATE_LIST]
  \\ simp [Once eval_wh_Letrec,subst_funs_def,bind_def,FLOOKUP_UPDATE,FUPDATE_LIST]
  \\ gvs [FLOOKUP_UPDATE,FDIFF_SING,DOMSUB_FUPDATE_THM]
  \\ gvs [subst_def,FDIFF_SING,DOMSUB_FUPDATE_THM]
  \\ ‘∀a. subst1 v a (subst (f \\ w \\ v) x) = (subst (f \\ w \\ v) x)’ by
   (rw []
    \\ DEP_REWRITE_TAC [subst1_ignore]
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [FRANGE_DEF,PULL_EXISTS,FLOOKUP_DEF,DOMSUB_FAPPLY_NEQ])
  \\ ‘∀a. subst1 w a (subst (f \\ w \\ v) x) = (subst (f \\ w \\ v) x)’ by
   (rw []
    \\ DEP_REWRITE_TAC [subst1_ignore]
    \\ DEP_REWRITE_TAC [freevars_subst]
    \\ fs [FRANGE_DEF,PULL_EXISTS,FLOOKUP_DEF,DOMSUB_FAPPLY_NEQ])
  \\ fs []
  \\ fs [eval_wh_App,eval_wh_Lam,subst_funs_def,FUPDATE_LIST]
  \\ DEP_REWRITE_TAC [bind_eq_subst]
  \\ ‘subst (f \\ w \\ v) x = subst f x’ by
    (DEP_REWRITE_TAC [GSYM subst_fdomsub] \\ fs [])
  \\ gvs [FLOOKUP_UPDATE]
  \\ drule_at (Pos last) subst1_subst1
  \\ disch_then $ DEP_REWRITE_TAC o single
  \\ fs []
  \\ metis_tac [DOMSUB_COMMUTES]
QED

Theorem Binds_MEM_lemma:
  ∀xs.
    lets_ok (e::xs) ⇒
    (Binds (e::xs) x ≅? Binds (e::(xs ++ [e])) x) b
Proof
  Induct
  >- (
    fs []
    \\ rw []
    \\ irule Binds_copy
    \\ Cases_on ‘e’
    \\ rw [] \\ fs [lets_ok_def,Binds_def]
  )
  \\ rw []
  \\ Cases_on ‘e’ \\ Cases_on ‘h’ \\ fs [Binds_def]
  \\ gvs [lets_ok_def]
  \\ irule exp_eq_trans
  \\ rename [‘Simple s e1’]
  \\ irule_at (Pos hd) (Binds_copy
       |> Q.SPEC ‘Simple s e1’ |> REWRITE_RULE [Binds_def])
  \\ gvs [lets_ok_def]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Let_copy \\ fs []
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at (Pos hd) (Binds_copy
       |> Q.SPEC ‘Simple s e1’ |> REWRITE_RULE [Binds_def])
  \\ gvs [lets_ok_def]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Let_copy \\ fs []
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
  \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl]
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
  \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl]
  \\ simp [Once exp_eq_sym]
QED

Theorem Binds_MEM:
  ∀xs e x.
    MEM e xs ∧ lets_ok xs ⇒
    (Binds xs x ≅? Binds (xs ++ [e]) x) b
Proof
  Induct \\ fs [] \\ rw []
  >- (irule Binds_MEM_lemma \\ fs [])
  \\ Cases_on ‘h’ \\ gvs [lets_ok_def,Binds_def]
  \\ irule exp_eq_App_cong \\ gvs [exp_eq_refl]
  \\ irule exp_eq_Lam_cong \\ gvs [exp_eq_refl]
QED

(*------------------------------------------------------------------------------*
   The main result of this script
 *------------------------------------------------------------------------------*)

Theorem inline_rel_IMP_exp_eq_lemma:
  ∀xs x y.
    inline_rel xs x y ∧ lets_ok xs ∧ pre xs x ⇒
    (Binds xs x ≅? Binds xs y) b
Proof
  Induct_on ‘inline_rel’
  \\ rpt strip_tac \\ fs [exp_eq_refl]
  >~ [‘Var’] >- (
    rw []
    \\ fs [lets_ok_def,EVERY_MEM,Binds_def]
    \\ res_tac
    \\ fs []
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_MEM
    \\ first_assum $ irule_at $ Pos hd
    \\ fs [EVERY_MEM,lets_ok_def]
    \\ fs [Binds_append,Binds_def]
    \\ irule Binds_cong
    \\ irule Let_Var
  )
  >~ [‘Let _ _ _’] >- (
    imp_res_tac pre_Let \\ gvs []
    \\ fs [Binds_snoc]
    \\ irule exp_eq_trans
    \\ last_x_assum $ irule_at Any
    \\ drule_all lets_ok_SNOC \\ fs [] \\ strip_tac
    \\ irule_at Any exp_eq_trans
    \\ irule_at Any Binds_Let \\ fs []
    \\ irule_at Any exp_eq_trans
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule_at (Pos $ el 2) Binds_Let \\ fs []
    \\ irule_at Any exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ once_rewrite_tac [exp_eq_sym] \\ fs []
  )
  >~ [‘App’] >- (
    imp_res_tac pre_App \\ gvs []
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_App
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_App
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_App_cong
    \\ fs []
  )
  >~ [‘Prim’] >- (
    irule exp_eq_trans
    \\ irule_at Any Binds_Prim
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Prim
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_Prim_cong
    \\ fs [LIST_REL_MAP]
    \\ imp_res_tac pre_Prim
    \\ gvs [LIST_REL_EL_EQN,EVERY_MEM,MEM_EL,PULL_EXISTS]
  )
  >~ [‘Lam’] >- (
    imp_res_tac pre_Lam \\ gvs []
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Lam \\ fs []
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Lam \\ fs []
    \\ irule exp_eq_Lam_cong \\ fs []
    \\ once_rewrite_tac [exp_eq_sym] \\ fs []
  )
  >~ [‘Letrec’] >- (
    imp_res_tac pre_Letrec \\ gvs []
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Letrec \\ fs []
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Letrec \\ fs []
    \\ conj_tac >-
     (fs [LIST_REL_EL_EQN,EVERY_EL,FORALL_PROD]
      \\ rw [] \\ gvs []
      \\ res_tac
      \\ rpt (pairarg_tac \\ fs []))
    \\ irule exp_eq_Letrec_cong
    \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro]
    \\ once_rewrite_tac [exp_eq_sym] \\ fs []
    \\ gvs [LIST_REL_MAP]
    \\ last_x_assum mp_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ rename [‘MAP FST ys = MAP FST zs’]
    \\ qid_spec_tac ‘ys’
    \\ qid_spec_tac ‘zs’
    \\ Induct \\ fs [PULL_EXISTS,EXISTS_PROD,FORALL_PROD]
  )
  >~ [‘Letrec’] >- (
    imp_res_tac pre_Letrec \\ gvs []
    \\ fs [Binds_snoc]
    \\ sg `(∀e. Binds xs (Letrec [(v,x')] e) ≅ Binds xs (Let v x1 e))`
    >- (rw [] \\ irule Binds_cong \\ gvs [])
    \\ first_assum $ qspecl_then [`x`] assume_tac
    \\ irule exp_eq_trans
    \\ drule_then (qspec_then `b` assume_tac) exp_eq_T_IMP_F
    \\ first_x_assum $ irule_at Any
    \\ irule exp_eq_trans
    \\ last_x_assum $ irule_at Any
    \\ irule_at Any pre_SNOC \\ fs []
    \\ irule_at Any lets_ok_SNOC_alt \\ fs []
    \\ first_assum $ qspecl_then [`y`] assume_tac
    \\ irule exp_eq_trans
    \\ drule_then (qspec_then `b` assume_tac) exp_eq_T_IMP_F
    \\ simp [Once exp_eq_sym]
    \\ first_x_assum $ irule_at Any
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Letrec \\ fs []
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Letrec \\ fs []
    \\ irule exp_eq_Letrec_cong
    \\ gvs [exp_eq_refl]
    \\ simp [Once exp_eq_sym]
  )
  >-
   (irule exp_eq_trans
    \\ last_x_assum $ irule_at Any \\ fs [])
  \\ irule exp_eq_trans
  \\ last_x_assum $ irule_at Any
  \\ irule Binds_cong
  \\ fs [exp_eq_T_IMP_F]
QED

Theorem inline_rel_IMP_exp_eq_lemma_specialized:
  ∀xs x y.
    inline_rel xs x y ∧ lets_ok xs ∧ pre xs x ⇒
    Binds xs x ≅ Binds xs y
Proof
  rw [] \\ irule inline_rel_IMP_exp_eq_lemma \\ simp []
QED

Theorem inline_rel_IMP_exp_eq:
  inline_rel [] x y ∧ barendregt x ∧ closed x ⇒
  (x ≅? y) b
Proof
  rw [] \\ drule inline_rel_IMP_exp_eq_lemma
  \\ fs [pre_def,lets_ok_def,vars_of_def,closed_def,Binds_def]
QED

Theorem inline_rel_IMP_exp_eq_specialized:
  inline_rel [] x y ∧ barendregt x ∧ closed x ⇒
  x ≅ y
Proof
  rw [] \\ irule inline_rel_IMP_exp_eq \\ fs []
QED

val _ = export_theory();
