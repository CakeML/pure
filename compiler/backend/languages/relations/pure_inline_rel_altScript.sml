(*
   Relation describing inlining and proof that it fits bidir from pure_pres
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     combinTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_exp_relTheory
     pure_alpha_equivTheory pure_miscTheory pure_congruenceTheory
     pure_letrec_seqTheory pure_demandTheory pure_barendregtTheory
     pure_presTheory pure_pres_lemmasTheory;

val _ = new_theory "pure_inline_rel_alt";

val _ = Parse.hide "bind_ok";

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
  ∀w e e1. w ∉ freevars e ⇒ subst1 w e1 e = e
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

Theorem LIST_REL_swap:
  ∀xs ys. LIST_REL R xs ys = LIST_REL (λx y. R y x) ys xs
Proof
  Induct \\ fs []
QED

Datatype:
  rhs = Exp ('a cexp)
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
  (∀v. no_shadowing (Var v))
[~Prim:]
  (∀l p.
    EVERY no_shadowing l ⇒
    no_shadowing (Prim p l))
[~App:]
  (∀x y.
    no_shadowing x ∧ no_shadowing y ∧
    DISJOINT (boundvars x) (boundvars y) ⇒
    no_shadowing (App x y))
[~Lam:]
  (∀v x.
    no_shadowing x ∧ v ∉ boundvars x ⇒
    no_shadowing (Lam v x))
[~Letrec:]
  (∀l x.
    EVERY (λ(v,e).
            no_shadowing e ∧
            DISJOINT (freevars e) (boundvars x) ∧
            DISJOINT (boundvars e) (boundvars x) ∧
            DISJOINT (boundvars e) (freevars e) ∧
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

Theorem barendregt_imp_no_shadowing:
  ∀e. barendregt e ⇒ no_shadowing e
Proof
  simp[barendregt_def] >>
  Induct using unique_boundvars_ind >>
  rw[unique_boundvars_Letrec, unique_boundvars_def] >>
  gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD, SF DNF_ss]
  >- (first_x_assum irule >> simp[Once DISJOINT_SYM])
  >- (first_x_assum irule >> simp[Once DISJOINT_SYM])
  >- (first_x_assum irule >> gvs[DISJOINT_ALT] >> metis_tac[]) >>
  simp[Once no_shadowing_cases, EVERY_MEM] >> reverse $ rw[]
  >- (last_x_assum irule >> gvs[DISJOINT_ALT] >> metis_tac[]) >>
  first_x_assum drule >> pairarg_tac >> gvs[] >> rw[]
  >- (
    first_x_assum irule >> simp[SF SFY_ss] >>
    first_x_assum drule >> gvs[DISJOINT_ALT] >>
    rw[] >> first_x_assum drule >> rw[] >> gvs[] >>
    gvs[MEM_MAP, FORALL_PROD, DISJ_EQ_IMP, PULL_FORALL] >> metis_tac[]
    )
  >- (
    simp[Once DISJOINT_SYM] >> irule DISJOINT_SUBSET >>
    qexists `(freevars body DIFF set (MAP FST fns)) ∪ set (MAP FST fns)` >> simp[] >>
    simp[Once DISJOINT_SYM] >>
    qpat_x_assum `DISJOINT (boundvars e) (_ DIFF _)` mp_tac >> rw[DISJOINT_ALT] >>
    first_x_assum drule >> simp[DISJ_EQ_IMP, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
    rw[] >> first_x_assum irule >> rw[SF SFY_ss]
    )
  >- simp[Once DISJOINT_SYM]
  >- (
    first_x_assum drule >> gvs[DISJOINT_ALT] >> rw[] >>
    first_x_assum drule >> rw[] >> gvs[] >>
    gvs[MEM_MAP, FORALL_PROD, DISJ_EQ_IMP, PULL_FORALL] >> metis_tac[]
    )
QED

Definition TAKE_WHILE_def:
  (TAKE_WHILE P [] = []) ∧
  (TAKE_WHILE P (h::t) = if P h then h::(TAKE_WHILE P t) else [])
End

Definition vars_of_def:
  vars_of [] = {} ∧
  vars_of ((v,Exp e)::rest) = explode v INSERT boundvars (exp_of e) ∪ vars_of rest
End

Definition freevars_of_def:
  freevars_of [] = {} ∧
  freevars_of ((v,Exp e)::rest) = freevars (exp_of e) ∪ freevars_of rest
End

Inductive inline_rel:
[~refl:]
  (∀l (t:'a cexp).
    inline_rel l t t)
[~Let:]
  (∀l v x y a.
    inline_rel l x x' ∧
    inline_rel (l ++ [(v,Exp x)]) y y' ⇒
    inline_rel l (Let a v x y) (Let a v x' y'))
[~Var:]
  (∀v x x1 x2 l a.
    MEM (v, Exp x) l ∧
    x <--> x1 ∧
    no_shadowing (exp_of x1) ∧
    DISJOINT (boundvars (exp_of x1)) (freevars (exp_of x1)) ∧
    DISJOINT (boundvars (exp_of x1)) (vars_of l) ∧
    DISJOINT (boundvars (exp_of x1)) (freevars_of l) ∧
    inline_rel l x1 x2 ⇒
    inline_rel l (Var a v) x2)
[~VarSimp:]
  (∀v x l a.
    MEM (v, Exp x) l ⇒
    inline_rel l (Var a v) x)
[~Prim:]
  (∀l p xs ys a.
    LIST_REL (inline_rel l) xs ys ⇒
    inline_rel l (Prim a p xs) (Prim a p ys))
[~App:]
  (∀l t1 t2 u1 u2 a.
    inline_rel l t1 u1 ∧
    LIST_REL (inline_rel l) t2 u2 ⇒
    inline_rel l (App a t1 t2) (App a u1 u2))
[~Lam:]
  (∀l t u w a.
    inline_rel l t u ⇒
    inline_rel l (Lam a w t) (Lam a w u))
[~Letrec:]
  (∀l t u xs ys a.
    LIST_REL (λ(n,t1) (m,u1). n = m ∧ inline_rel l t1 u1) xs ys ∧
    inline_rel l t u ⇒
    inline_rel l (Letrec a xs t) (Letrec a ys u))
[~LetRecIntroExp:]
  (∀l t u v x y x1 a.
    inline_rel l x y ∧
    (∀e. (Letrec a [(v, x)] e) <--> (Let a v x1 e)) ∧
    explode v ∉ freevars (exp_of x1) ∧
    DISJOINT (boundvars (exp_of t)) (boundvars (exp_of x1)) ∧
    DISJOINT (boundvars (exp_of t)) (freevars (exp_of x1)) ∧
    inline_rel (l ++ [(v,Exp x1)]) t u ⇒
    inline_rel l (Letrec a [(v, x)] t) (Letrec a [(v, y)] u))
[~trans:]
  (∀l x y z.
    inline_rel l x y ∧
    inline_rel l y z ∧
    DISJOINT (boundvars (exp_of y)) (vars_of l) ∧
    DISJOINT (boundvars (exp_of y)) (freevars (exp_of y)) ∧
    DISJOINT (boundvars (exp_of y)) (freevars_of l) ∧
    no_shadowing (exp_of y) ⇒
    inline_rel l x z)
[~ExpEq:]
  (∀l t u u1.
    inline_rel l t u ∧
    (u <--> u1) ⇒
    inline_rel l t u1)
End

Definition Binds_def[simp]:
  Binds a [] e = e ∧
  Binds a ((v,Exp x)::xs) e = Let a v x (Binds a xs e)
End

Theorem Binds_snoc:
  ∀xs. Binds a (xs ++ [(v,Exp x)]) y = Binds a xs (Let a v x y)
Proof
  Induct \\ fs []
  \\ PairCases \\ Cases_on ‘h1’ \\ fs []
QED

Definition bind_ok_def:
  bind_ok (v,Exp x) ⇔ explode v ∉ freevars (exp_of x)
End

Definition bind_ok_rec_def:
  (bind_ok_rec [] = T) ∧
  (bind_ok_rec ((v:mlstring,Exp (x:'a cexp))::rest) =
    (DISJOINT (freevars (exp_of x)) (IMAGE explode (set (MAP FST rest))) ∧
    bind_ok_rec rest))
End

val xs = mk_var("xs",“:(mlstring # α rhs) list”);

Definition binds_ok_def:
  binds_ok ^xs ⇔
    ALL_DISTINCT (MAP FST xs) ∧
    EVERY bind_ok xs ∧
    bind_ok_rec xs
End

Theorem bind_ok_rec_APPEND:
  bind_ok_rec (ys ++ ^xs) ⇒ bind_ok_rec xs
Proof
  rw []
  \\ Induct_on `ys` \\ rw []
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  \\ fs [bind_ok_rec_def]
QED

Theorem vars_of_MEM_not_in:
  MEM (q,Exp e) ^xs ∧ v ∉ vars_of xs ⇒ v ∉ boundvars (exp_of e)
Proof
  rw []
  \\ Induct_on `xs` \\ rw []
  >- fs [vars_of_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ fs [vars_of_def]
QED

Theorem vars_of_DISJOINT_MAP_FST:
  DISJOINT s (vars_of ^xs) ⇒
  DISJOINT s (IMAGE explode (set (MAP FST xs : mlstring list)))
Proof
  rw []
  \\ Induct_on `xs` \\ reverse $ rw [vars_of_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ fs [vars_of_def]
  \\ last_x_assum irule
  \\ fs [DISJOINT_SYM]
QED

Theorem vars_of_MEM_DISJOINT:
  MEM (q,Exp e) ^xs ∧ DISJOINT s (vars_of xs) ⇒
  DISJOINT s (boundvars (exp_of e))
Proof
  rw []
  \\ Induct_on `xs` \\ rw []
  >- fs [vars_of_def,DISJOINT_SYM]
  \\ Cases_on `h` \\ Cases_on `r` \\ fs [vars_of_def,DISJOINT_SYM]
QED

Theorem vars_of_append:
  ∀xs ys. vars_of (^xs ++ ys) = vars_of xs ∪ vars_of ys
Proof
  rw []
  \\ Induct_on ‘xs’ \\ rw []
  >- fs [vars_of_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  \\ fs [vars_of_def]
  \\ fs [UNION_ASSOC]
  \\ fs [INSERT_UNION_EQ]
QED

Theorem freevars_of_append:
  ∀xs ys. freevars_of (^xs ++ ys) = freevars_of xs ∪ freevars_of ys
Proof
  rw []
  \\ Induct_on ‘xs’ \\ rw []
  >- fs [freevars_of_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  \\ fs [freevars_of_def]
  \\ fs [UNION_ASSOC]
QED

Theorem vars_of_DISJOINT_FILTER:
  ∀xs ys. DISJOINT s (vars_of ys) ⇒ DISJOINT s (vars_of (FILTER P ys))
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

Theorem bind_ok_EVERY_Exp_append:
  EVERY bind_ok ^xs ∧
  explode v ∉ vars_of xs
  ⇒
  EVERY bind_ok xs
Proof
  rw []
  \\ fs [EVERY_MEM]
  \\ rw []
  \\ first_assum $ qspec_then `e` assume_tac
  \\ Cases_on `e` \\ Cases_on `r` \\ rw []
  \\ fs [bind_ok_def,vars_of_def]
  \\ gvs []
  \\ fs [vars_of_append]
QED

Theorem bind_ok_rec_Exp_append:
  bind_ok_rec ^xs ∧
  explode v ∉ freevars_of xs
  ⇒
  bind_ok_rec (xs ++ [(v,Exp x)])
Proof
  rw []
  \\ Induct_on `xs` \\ rw []
  >- fs [bind_ok_rec_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  \\ fs [bind_ok_rec_def]
  \\ fs [DISJOINT_SYM]
  \\ fs [freevars_of_def]
  \\ last_x_assum $ irule
  \\ fs [DISJOINT_SYM]
QED

Theorem exp_eq_Let_cong:
  (e1 ≅? e2) b ∧ (bod1 ≅? bod2) b ⇒
  (Let v e1 bod1 ≅? Let v e2 bod2) b
Proof
  simp[exp_eq_App_cong, exp_eq_Lam_cong]
QED

Theorem Binds_Lam:
  EVERY (λv. v ∉ set (MAP FST xs) ∧ explode v ∉ freevars_of xs) vs
  ⇒
  ((Binds a xs (Lam b vs x)) <--> (Lam b vs (Binds a xs x)))
Proof
  cheat
(*
  rw []
  \\ Induct_on `xs` \\ rw []
  >- simp [exp_eq_refl]
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  >- (
    simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule_at Any Let_Lam
    \\ fs [FST,freevars_of_def]
    \\ irule exp_eq_Let_cong
    \\ fs [exp_eq_refl]
  )
  \\ simp [Once exp_eq_sym]
  \\ irule exp_eq_trans
  \\ once_rewrite_tac [exp_eq_sym]
  \\ irule_at Any Letrec_Lam_weak
  \\ fs [FST,freevars_of_def,MAP]
  \\ irule exp_eq_Letrec_cong1
  \\ fs [exp_eq_refl] *)
QED

(*
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
  v ∉ set (MAP FST xs) ∧
  v ∉ freevars_of xs ⇒
  (Binds xs (Let v x y) ≅? Let v (Binds xs x) (Binds xs y)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any Binds_App
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl,Binds_Lam]
QED
*)

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

(*
Theorem Binds_Letrec:
  EVERY (λ(v, e). v ∉ set (MAP FST xs) ∧ v ∉ freevars_of xs) l ⇒
    (Binds xs (Letrec l y) ≅? Letrec (MAP (λ(v, e). (v, Binds xs e)) l) (Binds xs y)) b
Proof
  rw []
  \\ Induct_on `xs` \\ rw []
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
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  \\ qsuff_tac `(Let q e (Binds xs (Letrec l y)) ≅?
       Letrec (MAP (λ(v,t). (v,Let q e t)) (MAP (λ(v,t). (v,Binds xs t)) l))
         (Let q e (Binds xs y))) b`
  >- fs [MAP_MAP_o, o_DEF, LAMBDA_PROD]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Letrec
  \\ fs [freevars_of_def]
  \\ fs [EVERY_MAP, LAMBDA_PROD]
  \\ fs [MAP_MAP_o, o_DEF, LAMBDA_PROD, FST_intro]
  \\ conj_tac
  >- (
    fs [EVERY_MEM]
    \\ rw [MEM_MAP]
    \\ Cases_on `e'` \\ rw []
    \\ last_x_assum $ qspec_then `(q', r)` assume_tac
    \\ gvs []
  )
  \\ sg `EVERY
        (λv.
             (v ≠ q ∧ ¬MEM v (MAP FST xs)) ∧ v ∉ freevars e ∧
             v ∉ freevars_of xs) (MAP FST l)`
  >- fs [EVERY_MAP, LAMBDA_PROD, FST]
  \\ conj_tac
  >- (
    fs [EVERY_MEM]
    \\ reverse $ Cases_on `MEM q (MAP FST l)`
    >- simp []
    \\ last_x_assum $ qspec_then `q` assume_tac
    \\ gvs []
  )
  \\ conj_tac
  >- (
    fs [EVERY_MEM, IN_DISJOINT]
    \\ rw []
    \\ last_x_assum $ qspec_then `x` assume_tac
    \\ Cases_on `MEM x (MAP FST l)` \\ rw []
  )
  \\ irule exp_eq_Let_cong
  \\ simp [exp_eq_refl]
  \\ first_x_assum irule
  \\ fs [EVERY_MEM]
  \\ rw []
  \\ first_x_assum $ qspec_then `e'` assume_tac
  \\ gvs []
  \\ Cases_on `e'` \\ simp []
  \\ gvs []
QED

Theorem Binds_Prim:
  (Binds xs (Prim op ys) ≅? Prim op (MAP (Binds xs) ys)) b
Proof
  rw []
  \\ Induct_on `xs` \\ rw []
  >- (
    irule exp_eq_Prim_cong
    \\ simp [LIST_REL_MAP2]
    \\ simp [LIST_REL_EL_EQN]
    \\ simp [exp_eq_refl]
  )
  \\ Cases_on `h` \\ Cases_on `r` \\ rw []
  \\ qsuff_tac `(Let q e (Binds xs (Prim op ys)) ≅?
       Prim op (MAP (Let q e) (MAP (Binds xs) ys))) b`
  >- (
    rw []
    \\ fs [MAP_MAP_o, o_DEF]
    \\ irule exp_eq_trans
    \\ first_x_assum $ irule_at Any
    \\ qsuff_tac `(MAP (λx. Let q e (Binds xs x)) ys) = (MAP (Binds ((q,Exp e)::xs)) ys)`
    >- simp [exp_eq_refl]
    \\ simp [MAP_EQ_EVERY2]
    \\ simp [EVERY2_refl_EQ]
  )
  \\ rw []
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Prim
  \\ irule exp_eq_Let_cong
  \\ simp [exp_eq_refl]
QED
*)

Theorem vars_of_not_in_MAP_FST:
  v ∉ vars_of xs ⇒ ¬MEM v (MAP (explode o FST) ^xs)
Proof
  rw []
  \\ Induct_on `xs`
  >- rw [vars_of_def,MAP]
  \\ Cases_on `h` \\ Cases_on `r`
  \\ rw [vars_of_def,MAP]
QED

Theorem Binds_append:
  ∀xs ys e. Binds a (^xs ++ ys) e = Binds a xs (Binds a ys e)
Proof
  rw []
  \\ Induct_on `xs`
  >- rw [Binds_def]
  \\ Cases_on `h` \\ Cases_on `r`
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

(*
Theorem Binds_copy:
  ∀e x.
    bind_ok [] e ⇒
    (Binds [e] x ≅? Binds [e; e] x) b
Proof
  rw []
  \\ Induct_on `e` \\ rw [] \\ Induct_on `p_2` \\ rw []
  \\ fs [binds_ok_def,bind_ok_def]
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
QED
*)

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

Theorem Binds_cons_dup:
  bind_ok e ⇒
  Binds a (e::es) x <--> Binds a (e::e::es) x
Proof
  PairCases_on ‘e’ \\ Cases_on ‘e1’ \\ gvs [Binds_def,bind_ok_def]
  \\ rw [] \\ irule bidir_Let_dup \\ fs []
QED

Theorem Binds_cons_cons_swap:
  bind_ok e /\ bind_ok_rec (e::h::es) ∧ FST e ≠ FST h ⇒
  Binds a (e::e::h::es) x <--> Binds a (e::h::e::es) x
Proof
  PairCases_on ‘e’ \\ Cases_on ‘e1’ \\ gvs [Binds_def]
  \\ PairCases_on ‘h’ \\ Cases_on ‘h1’ \\ gvs [Binds_def,bind_ok_def]
  \\ gvs [bind_ok_rec_def] \\ rw []
  \\ irule bidir_Let_Let_Let \\ fs []
QED

Theorem Binds_same_hd:
  Binds a xs x <--> Binds a ys y ==>
  Binds a (e::xs) x <--> Binds a (e::ys) y
Proof
  PairCases_on ‘e’ \\ Cases_on ‘e1’ \\ gvs [Binds_def]
  \\ rw [] \\ irule bidir_Let \\ fs []
QED

Theorem Binds_MEM_lemma:
   ∀xs ys.
     ¬MEM (FST e) (MAP FST xs) ∧
     ALL_DISTINCT (MAP FST xs) ∧
     bind_ok e ∧
     EVERY bind_ok xs ∧
     bind_ok_rec (e::xs)
     ⇒
     Binds a (e::xs) x <--> Binds a (e::(xs ++ [e])) x
Proof
  Induct
  >- (fs [] \\ rw [] \\ irule Binds_cons_dup \\ fs [])
  \\ rw []
  \\ first_x_assum $ qspec_then ‘ys’ assume_tac
  \\ gvs []
  \\ ‘bind_ok_rec (e::xs) ∧ bind_ok e’ by
    (PairCases_on ‘e’ \\ Cases_on ‘e1’ \\ fs [bind_ok_rec_def,bind_ok_def]
     \\ PairCases_on ‘h’ \\ Cases_on ‘h1’ \\ fs [bind_ok_rec_def])
  \\ gvs []
  \\ irule bidir_trans
  \\ irule_at (Pos hd) Binds_cons_dup \\ fs []
  \\ simp [Once bidir_sym]
  \\ irule bidir_trans
  \\ irule_at (Pos hd) Binds_cons_dup \\ fs []
  \\ simp [Once bidir_sym]
  \\ irule bidir_trans
  \\ irule_at (Pos hd) Binds_cons_cons_swap \\ fs []
  \\ simp [Once bidir_sym]
  \\ irule bidir_trans
  \\ irule_at (Pos hd) Binds_cons_cons_swap \\ fs []
  \\ ntac 2 (irule_at Any Binds_same_hd \\ fs [])
  \\ simp [Once bidir_sym]
  \\ gvs [bind_ok_rec_def]
  \\ PairCases_on ‘e’ \\ Cases_on ‘e1’ \\ gvs []
  \\ PairCases_on ‘h’ \\ Cases_on ‘h1’ \\ gvs [bind_ok_rec_def]
  \\ fs [DISJOINT_SYM]
  \\ gvs [IN_DISJOINT]
  \\ cheat
QED

Theorem Binds_MEM:
  ∀xs e x.
    MEM e xs ∧ binds_ok ^xs ⇒
    ((Binds a xs x) <--> (Binds a (xs ++ [e]) x))
Proof
  rw []
  \\ gvs [MEM_SPLIT]
  \\ pop_assum mp_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ rewrite_tac [Binds_append]
  \\ Induct_on ‘l1’ \\ gvs []
  >- (rw [] \\ irule Binds_MEM_lemma \\ gvs [binds_ok_def])
  \\ rw []
  \\ irule Binds_same_hd
  \\ last_x_assum irule
  \\ gvs [binds_ok_def,bind_ok_rec_def]
  \\ PairCases_on ‘h’ \\ Cases_on ‘h1’ \\ gvs[bind_ok_rec_def]
QED

(*

Theorem inline_rel_IMP_exp_eq_lemma:
  ∀xs x y.
    inline_rel xs x y ∧ binds_ok xs ∧
    DISJOINT (boundvars x) (vars_of xs) ∧
    DISJOINT (boundvars x) (freevars x) ∧
    DISJOINT (boundvars x) (freevars_of xs) ∧
    no_shadowing x ⇒
    (Binds xs x ≅? Binds xs y) b
Proof
  Induct_on ‘inline_rel’
  \\ rpt strip_tac \\ fs [exp_eq_refl]
  >~ [‘Var’] >- (
    rw []
    \\ fs [binds_ok_def,EVERY_MEM,bind_ok_def]
    \\ res_tac
    \\ gvs [bind_ok_def]
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
    \\ drule_then (qspec_then `b` assume_tac) exp_eq_T_IMP_F
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
      \\ fs [vars_of_not_in_MAP_FST]
      \\ fs [vars_of_DISJOINT_MAP_FST]
      \\ fs [FILTER_APPEND]
      \\ fs [vars_of_DISJOINT_FILTER]
      \\ fs [bind_ok_EVERY_Exp_append]
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
    \\ fs [IN_DISJOINT,vars_of_not_in_MAP_FST]
  )
  >~ [‘App’] >- (
    irule exp_eq_trans
    \\ irule_at Any Binds_App
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_App
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_App_cong
    \\ first_x_assum $ irule_at Any
    \\ first_x_assum $ irule_at Any
    \\ fs [IN_DISJOINT]
    \\ metis_tac []
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
    \\ gvs [LIST_REL_EL_EQN]
    \\ rw []
    \\ first_x_assum $ qspec_then `n` assume_tac
    \\ gvs []
    \\ first_x_assum $ irule
    \\ fs [binds_ok_def,EVERY_MEM]
    \\ fs [EL_MEM]
    \\ conj_tac
    >- (
      last_x_assum $ irule
      \\ fs [MEM_MAP]
      \\ conj_tac
      >- (
        qexists `(EL n xs')`
        \\ simp [EL_MEM]
      )
      \\ qexists `(EL n xs')`
      \\ simp [EL_MEM]
    )
    \\ conj_tac
    >- (
      first_x_assum $ qspec_then `boundvars (EL n xs')` assume_tac
      \\ qsuff_tac `MEM (boundvars (EL n xs')) (MAP (λa. boundvars a) xs')`
      >- simp []
      \\ fs [MEM_MAP]
      \\ qexists `(EL n xs')`
      \\ simp [EL_MEM]
    )
    \\ last_x_assum $ qspec_then `boundvars (EL n xs')` assume_tac
    \\ qsuff_tac `MEM (boundvars (EL n xs')) (MAP (λa. boundvars a) xs')`
    >- simp []
    \\ fs [MEM_MAP]
    \\ qexists `(EL n xs')`
    \\ simp [EL_MEM]
  )
  >~ [‘Lam’] >- (
    irule exp_eq_trans
    \\ irule_at Any Binds_Lam
    \\ fs [vars_of_not_in_MAP_FST]
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Lam
    \\ fs [vars_of_not_in_MAP_FST]
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_Lam_cong
    \\ first_x_assum $ irule_at Any
    \\ fs [IN_DISJOINT]
    \\ metis_tac []
  )
  >~ [`Letrec`] >- (
    irule exp_eq_trans
    \\ irule_at Any Binds_Letrec
    \\ conj_tac
    >- (
      fs [Once no_shadowing_cases]
      \\ fs [EVERY_MEM]
      \\ Cases \\ fs [FORALL_PROD]
      \\ strip_tac
      \\ conj_tac
      >- (
        fs [IN_DISJOINT]
        \\ qsuff_tac `q ∉ vars_of xs`
        >- fs [vars_of_not_in_MAP_FST]
        \\ fs [MEM_MAP, FORALL_PROD]
        \\ metis_tac []
      )
      \\ fs [IN_DISJOINT]
      \\ fs [MEM_MAP, FORALL_PROD]
      \\ metis_tac []
    )
    \\ once_rewrite_tac [exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Letrec
    \\ conj_tac
    >- (
      fs [Once no_shadowing_cases]
      \\ fs [LIST_REL_EL_EQN]
      \\ rw []
      \\ fs [EVERY_MEM]
      \\ Cases \\ fs [FORALL_PROD]
      \\ simp [Once MEM_EL]
      \\ strip_tac
      \\ first_x_assum $ qspec_then `n` assume_tac
      \\ gvs []
      \\ Cases_on `(EL n xs')`
      \\ Cases_on `(EL n ys)`
      \\ gvs []
      \\ conj_tac
      >- (
        fs [IN_DISJOINT]
        \\ qsuff_tac `q ∉ vars_of xs`
        >- fs [vars_of_not_in_MAP_FST]
        \\ qpat_x_assum `∀x. ¬MEM x (MAP FST xs') ∨ x ∉ vars_of xs` $ qspec_then `q` mp_tac
        \\ sg `MEM (EL n xs') xs'`
        >- (
          fs [MEM_EL]
          \\ qexists `n`
          \\ rw []
        )
        \\ simp [MEM_MAP]
        \\ fs [FORALL_PROD]
        \\ metis_tac []
      )
      \\ fs [IN_DISJOINT]
      \\ fs [MEM_MAP, FORALL_PROD]
      \\ qpat_x_assum `∀x. (∀p_2. ¬MEM (x,p_2) xs') ∨ x ∉ freevars_of xs` $ qspec_then `q` mp_tac
      \\ sg `MEM (EL n xs') xs'`
      >- (
        fs [MEM_EL]
        \\ qexists `n`
        \\ rw []
      )
      \\ metis_tac []
    )
    \\ irule exp_eq_Letrec_cong
    \\ conj_tac
    >- (
      simp [Once EQ_SYM_EQ]
      \\ simp [MAP_EQ_EVERY2]
      \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD,FST_intro]
      \\ simp [LIST_REL_MAP]
      \\ fs [LIST_REL_EVERY_ZIP]
      \\ fs [EVERY_MEM,FORALL_PROD]
      \\ fs [LIST_REL_EL_EQN]
      \\ rw []
      \\ first_x_assum (qspecl_then [‘p_1’, ‘p_2’, ‘p_1'’, ‘p_2'’] assume_tac)
      \\ gvs []
    )
    \\ reverse $ conj_tac
    >- (
      once_rewrite_tac [exp_eq_sym]
      \\ first_x_assum irule
      \\ fs [Once no_shadowing_cases]
      \\ fs [IN_DISJOINT]
      \\ metis_tac []
    )
    \\ simp [Once LIST_REL_SYM,exp_eq_sym]
    \\ fs [MAP_MAP_o,o_DEF,LAMBDA_PROD]
    \\ fs [LIST_REL_MAP]
    \\ last_x_assum $ mp_tac
    \\ match_mp_tac LIST_REL_mono
    \\ PairCases
    \\ PairCases
    \\ fs []
    \\ rpt strip_tac
    \\ first_x_assum irule
    \\ gvs []
    \\ conj_tac
    >- (
      qpat_x_assum `no_shadowing _` mp_tac
      \\ simp [Once no_shadowing_cases]
      \\ rpt strip_tac
      \\ fs [EVERY_MEM]
      \\ res_tac
      \\ fs []
    )
    \\ conj_tac
    >- (
      qpat_x_assum `no_shadowing _` mp_tac
      \\ simp [Once no_shadowing_cases]
      \\ rpt strip_tac
      \\ fs [EVERY_MEM]
      \\ res_tac
      \\ fs []
    )
    \\ conj_tac
    >- (
      qpat_x_assum `∀s'.
        MEM s' (MAP (λ(fn,e'). boundvars e') xs') ⇒
        DISJOINT s' (freevars_of xs)` $ qspec_then `boundvars x'1` mp_tac
      \\ fs [MEM_MAP]
      \\ impl_tac
      >- (
        qexists `(x'0,x'1)`
        \\ simp []
      )
      \\ simp []
    )
    \\ qpat_x_assum `∀s'.
      MEM s' (MAP (λ(fn,e'). boundvars e') xs') ⇒
      DISJOINT s' (vars_of xs)` $ qspec_then `boundvars x'1` mp_tac
    \\ fs [MEM_MAP]
    \\ impl_tac
    >- (
      qexists `(x'0,x'1)`
      \\ simp []
    )
    \\ simp []
  )
  >~ [`Letrec`] >- (
    fs [Binds_snoc]
    \\ sg `(∀e. Binds xs (Letrec [(v,x')] e) ≅ Binds xs (Let v x1 e))`
    >- (
      rw []
      \\ irule Binds_cong
      \\ gvs []
    )
    \\ qpat_assum `∀e. Binds xs (Letrec [(v,x')] e) ≅ Binds xs (Let v x1 e)` $ qspecl_then [`x`] assume_tac
    \\ irule exp_eq_trans
    \\ drule_then (qspec_then `b` assume_tac) exp_eq_T_IMP_F
    \\ first_x_assum $ irule_at Any
    \\ irule exp_eq_trans
    \\ last_x_assum $ irule_at Any
    \\ qpat_x_assum `no_shadowing _` mp_tac
    \\ simp [Once no_shadowing_cases]
    \\ strip_tac
    \\ gvs [freevars_of_append,vars_of_append,vars_of_def,freevars_of_def,DISJOINT_SYM]
    \\ conj_tac
    >- (
      fs [binds_ok_def,bind_ok_def]
      \\ fs [ALL_DISTINCT_APPEND]
      \\ fs [DISJOINT_SYM]
      \\ fs [vars_of_not_in_MAP_FST]
      \\ fs [vars_of_DISJOINT_MAP_FST]
      \\ fs [FILTER_APPEND]
      \\ fs [vars_of_DISJOINT_FILTER]
      \\ fs [bind_ok_EVERY_Exp_append]
      \\ fs [bind_ok_rec_def]
      \\ fs [bind_ok_rec_Exp_append]
    )
    \\ conj_tac
    >- (
      fs [IN_DISJOINT]
      \\ metis_tac []
    )
    \\ qpat_assum `∀e. Binds xs (Letrec [(v,x')] e) ≅ Binds xs (Let v x1 e)` $ qspecl_then [`y`] assume_tac
    \\ irule exp_eq_trans
    \\ drule_then (qspec_then `b` assume_tac) exp_eq_T_IMP_F
    \\ simp [Once exp_eq_sym]
    \\ first_x_assum $ irule_at Any
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Letrec
    \\ gvs [vars_of_not_in_MAP_FST]
    \\ simp [Once exp_eq_sym]
    \\ irule exp_eq_trans
    \\ irule_at Any Binds_Letrec
    \\ gvs [vars_of_not_in_MAP_FST]
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
    inline_rel xs x y ∧ binds_ok xs ∧
    DISJOINT (boundvars x) (vars_of xs) ∧ no_shadowing x ∧
    DISJOINT (boundvars x) (freevars x) ∧
    DISJOINT (boundvars x) (freevars_of xs) ⇒
    Binds xs x ≅ Binds xs y
Proof
  rw []
  \\ irule inline_rel_IMP_exp_eq_lemma
  \\ simp []
QED

Theorem inline_rel_IMP_exp_eq:
  inline_rel [] x y ∧ no_shadowing x ∧ closed x ⇒
  (x ≅? y) b
Proof
  rw [] \\ drule inline_rel_IMP_exp_eq_lemma
  \\ fs [binds_ok_def,vars_of_def,freevars_of_def,closed_def,bind_ok_rec_def]
QED

Theorem inline_rel_IMP_exp_eq_specialized:
  inline_rel [] x y ∧ no_shadowing x ∧ closed x ⇒
  x ≅ y
Proof
  rw []
  \\ irule inline_rel_IMP_exp_eq
  \\ fs []
QED

*)

val _ = export_theory();
