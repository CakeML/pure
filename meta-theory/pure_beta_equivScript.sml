(*
  Theorem beta_equivalence:
    App (Lam x body) arg ≅ ca_subst x arg body

  where ca_subst is the capture-avoiding substitution of the free variables "x"
  in the expression "body" with the expression "arg"

  The main theorem above states that two beta-equivalent expressions
  belong to the same equivalence class under the eval function.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_limitTheory pure_miscTheory
     pure_exp_relTheory pure_alpha_equivTheory pure_congruenceTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "pure_beta_equiv";


Definition fresh_var_def:
  fresh_var v xs = if ¬MEM v xs then v else fresh_var (v ++ "'") xs
Termination
  WF_REL_TAC ‘measure (λ(v,xs). (LENGTH (FLAT xs) + 1) - LENGTH v)’ \\ rw[]
  \\ Induct_on ‘xs’ \\ fs[] \\ rpt strip_tac \\ fs[]
End

Theorem fresh_var_correctness:
  ∀v l. ¬ MEM (fresh_var v l) l
Proof
  recInduct fresh_var_ind \\ rw []
  \\ once_rewrite_tac [fresh_var_def]
  \\ IF_CASES_TAC \\ fs[]
QED

Theorem fresh_var_avoid_eq:
  ∀x avoid1 avoid2.
    set avoid1 = set avoid2
  ⇒ fresh_var x avoid1 = fresh_var x avoid2
Proof
  recInduct fresh_var_ind >> rw[EXTENSION] >>
  once_rewrite_tac[fresh_var_def] >> gvs[] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem fresh_var_DISJ:
  ∀v l. (fresh_var v l = v ∧ ¬ MEM v l) ∨ (fresh_var v l ≠ v ∧ MEM v l)
Proof
  once_rewrite_tac[fresh_var_def] >> rw[] >>
  metis_tac[fresh_var_correctness]
QED

Definition fresh_var_list_def:
  fresh_var_list []      to_avoid = [] ∧
  fresh_var_list (x::xs) to_avoid =
    let fresh = fresh_var x to_avoid in
    ((x,fresh)::fresh_var_list xs (fresh::to_avoid))
End

Theorem MAP_FST_fresh_var_list:
  ∀ v avoid. MAP FST (fresh_var_list v avoid) = v
Proof
  Induct \\ fs[fresh_var_list_def,MAP]
QED

Theorem fresh_var_list_correctness:
  ∀v l. DISJOINT (set (MAP SND (fresh_var_list v l))) (set l)
Proof
  Induct \\ fs[fresh_var_list_def]
  \\ rw[] \\ fs[fresh_var_correctness]
  \\ pop_assum (qspec_then ‘(fresh_var h l::l)’ assume_tac)
  \\ fs[EXTENSION,DISJOINT_DEF]
  \\ metis_tac[]
QED

Theorem fresh_var_list_distinctness:
  ∀vars avoids. ALL_DISTINCT (MAP SND (fresh_var_list vars avoids))
Proof
  Induct \\ fs[fresh_var_list_def]
  \\ rw[] \\ fs[]
  \\ CCONTR_TAC \\ fs[]
  \\ qspecl_then [‘vars’,‘(fresh_var h avoids::avoids)’]
                 assume_tac fresh_var_list_correctness
  \\ CCONTR_TAC
  \\ fs[]
QED

Theorem fresh_var_list_SUBSET:
  ∀l avoid.
    set l ⊆ set (MAP SND (fresh_var_list l avoid)) ∪ set avoid
Proof
  Induct >> rw[fresh_var_list_def]
  >- (simp[Once fresh_var_def] >> IF_CASES_TAC >> gvs[]) >>
  gvs[SUBSET_DEF] >> rw[] >>
  last_x_assum drule >>
  disch_then (qspec_then `fresh_var h avoid::avoid` assume_tac) >> gvs[]
QED

Theorem fresh_var_list_avoid_eq:
  ∀l avoid1 avoid2.
    set avoid1 = set avoid2
  ⇒ fresh_var_list l avoid1 = fresh_var_list l avoid2
Proof
  Induct >> rw[fresh_var_list_def]
  >- (
    once_rewrite_tac[fresh_var_def] >>
    drule fresh_var_avoid_eq >> gvs[EXTENSION]
    ) >>
  first_x_assum irule >> gvs[] >>
  drule fresh_var_avoid_eq >> simp[]
QED

Definition exp_size_alt_def:
  exp_size_alt (Var v) = 1 ∧
  exp_size_alt (Prim op xs) = 1 + SUM (MAP exp_size_alt xs) ∧
  exp_size_alt (App e1 e2) = 1 + exp_size_alt e1 + exp_size_alt e2 ∧
  exp_size_alt (Lam x e) = 1 + exp_size_alt e ∧
  exp_size_alt (Letrec fns e) =
    1 + exp_size_alt e + SUM (MAP (λ(v,fn). exp_size_alt fn) fns)
Termination
  WF_REL_TAC `measure (λe. exp_size e)` >> rw[exp_size_def]
  >- (Induct_on `fns` >> rw[] >> gvs[exp_size_def])
  >- (Induct_on `xs` >> rw[] >> gvs[exp_size_def])
End

Theorem perm_exp_size:
  ∀e x y. exp_size_alt e = exp_size_alt (perm_exp x y e)
Proof
  recInduct exp_size_alt_ind >> rw[exp_size_alt_def, perm_exp_def]
  >- (AP_TERM_TAC >> rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f])
  >- metis_tac[]
  >- (
    pop_assum (once_rewrite_tac o single) >> simp[] >>
    AP_TERM_TAC >> rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
    pairarg_tac >> gvs[] >> res_tac >> simp[]
    )
QED

Definition perm_exp_list_def:
  perm_exp_list [] e = e ∧
  perm_exp_list ((old,new)::binds) e = perm_exp old new (perm_exp_list binds e)
End

Theorem perm_exp_list_size:
  ∀ binds e. exp_size_alt (perm_exp_list binds e) = exp_size_alt e
Proof
  recInduct perm_exp_list_ind >> rw[perm_exp_list_def] >>
  metis_tac[perm_exp_size]
QED

Theorem exp_alpha_perm_exp_list:
  ∀ binds e.
      (DISJOINT (set (MAP FST binds)) (freevars e))
    ∧ (DISJOINT (set (MAP SND binds)) (freevars e))
    ⇒ exp_alpha e (perm_exp_list binds e)
Proof
  recInduct perm_exp_list_ind >> rw[perm_exp_list_def, exp_alpha_refl] >>
  irule exp_alpha_Trans >> qexists_tac `perm_exp old new e` >>
  irule_at Any exp_alpha_perm_irrel >> simp[] >>
  irule exp_alpha_perm_closed >>
  last_x_assum irule >> simp[]
QED

Theorem freevars_perm_exp_list_unchanged:
  ∀ binds e.
    DISJOINT (set (MAP FST binds)) (freevars e) ∧
    DISJOINT (set (MAP SND binds)) (freevars e)
  ⇒ freevars (perm_exp_list binds e) = freevars e
Proof
  recInduct perm_exp_list_ind >> rw[perm_exp_list_def] >>
  gvs[freevars_eqvt] >>
  rw[EXTENSION, perm1_def] >>
  eq_tac >> rw[]
  >- (EVERY_CASE_TAC >> gvs[])
  >- (qexists_tac `x` >> EVERY_CASE_TAC >> gvs[])
QED

Definition freshen_def:
  freshen avoid (Var x) = (Var x) ∧
  freshen avoid (Prim op es) = Prim op (MAP (freshen avoid) es) ∧
  freshen avoid (Lam x e) =
    (let y = fresh_var x avoid in
    Lam y (freshen (y::avoid) (perm_exp x y e))) ∧
  freshen avoid (App e1 e2) = App (freshen avoid e1) (freshen avoid e2) ∧
  freshen avoid (Letrec lcs e) =
    let fresh_vars = fresh_var_list (MAP FST lcs) avoid in
    let fresh_lcs = MAP (λ(n,e). (n, freshen (MAP SND fresh_vars ++ avoid) e)) lcs in
    let fresh_e = freshen (MAP SND fresh_vars ++ avoid) e in
    perm_exp_list fresh_vars (Letrec fresh_lcs fresh_e)
Termination
  WF_REL_TAC `measure (λ(_,e). exp_size_alt e)` >> rw[exp_size_alt_def] >>
  simp[GSYM perm_exp_size, perm_exp_list_size]
  >- (Induct_on `lcs` >> rw[] >> gvs[])
  >- (Induct_on `es` >> rw[] >> gvs[] >> DECIDE_TAC)
End

Theorem exp_alpha_freshen:
  ∀ avoid e. freevars e ⊆ (set avoid) ⇒ exp_alpha e (freshen avoid e)
Proof
  recInduct freshen_ind >> rw[freshen_def, exp_alpha_refl]
  >- (
    irule exp_alpha_Prim >> rw[LIST_REL_EL_EQN, EL_MAP] >>
    last_x_assum irule >> simp[EL_MEM] >>
    gvs[SUBSET_DEF, PULL_EXISTS, MEM_MAP] >> rw[] >>
    first_x_assum irule >> goal_assum (drule_at Any) >> simp[EL_MEM]
    )
  >- (
    Cases_on `fresh_var x avoid = x` >> gvs[perm_exp_id]
    >- (
      irule exp_alpha_Lam >> first_x_assum irule >>
      gvs[SUBSET_INSERT_DELETE]
      ) >>
    `¬ MEM (fresh_var x avoid) avoid` by simp[fresh_var_correctness] >>
    qabbrev_tac `y = fresh_var x avoid` >>
    irule exp_alpha_Trans >>
    qexists_tac `Lam y (perm_exp x y e)`  >>
    irule_at Any exp_alpha_Lam >>
    first_x_assum (irule_at Any) >>
    gvs[freevars_eqvt, SUBSET_DEF, perm1_def] >>
    conj_tac >- metis_tac[] >>
    irule exp_alpha_Alpha >> simp[] >>
    metis_tac[]
    )
  >- (irule exp_alpha_App >> res_tac >> simp[])
  >- (
    gvs[DIFF_SUBSET] >>
    qpat_x_assum `_ ⇒ exp_alpha _ _` mp_tac >>
    impl_keep_tac
    >- (
      qspecl_then [`MAP FST lcs`,`avoid`] assume_tac fresh_var_list_SUBSET >>
      gvs[SUBSET_DEF] >> rw[] >> metis_tac[]
      ) >>
    strip_tac >>
    imp_res_tac exp_alpha_freevars >> pop_assum (assume_tac o GSYM) >>
    `∀p1 p2. MEM (p1,p2) lcs ⇒
      exp_alpha p2
      (freshen (MAP SND (fresh_var_list (MAP FST lcs) avoid) ++ avoid) p2)` by (
      rw[] >> first_x_assum irule >> simp[PULL_EXISTS] >> goal_assum drule >>
      qspecl_then [`MAP FST lcs`,`avoid`] assume_tac fresh_var_list_SUBSET >>
      gvs[SUBSET_DEF] >> rw[] >>
      qsuff_tac `MEM x (MAP FST lcs) ∨ MEM x avoid` >- metis_tac[] >>
      last_x_assum irule >> simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
      goal_assum drule >> goal_assum drule) >>
    last_x_assum kall_tac >>
    qmatch_goalsub_abbrev_tac `exp_alpha _ (perm_exp_list l exp)` >>
    irule exp_alpha_Trans >> qexists_tac `exp` >> rw[]
    >- (
      unabbrev_all_tac >> irule exp_alpha_Letrec >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
      rw[LIST_REL_EL_EQN, EL_MAP, UNCURRY] >>
      first_x_assum irule >>
      qexists_tac `FST (EL n lcs)` >> gvs[EL_MEM]
      ) >>
    irule exp_alpha_perm_exp_list >> unabbrev_all_tac >>
    simp[MAP_FST_fresh_var_list] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[GSYM FST_THM, DISJOINT_DIFF] >>
    `MAP (λ(p1,p2).
      freevars (freshen
        (MAP SND (fresh_var_list (MAP FST lcs) avoid) ++ avoid) p2)) lcs =
      MAP (λ(p1,p2). freevars p2) lcs` by (
        rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
        first_x_assum drule >> strip_tac >>
        imp_res_tac exp_alpha_freevars >> simp[]) >>
    gvs[] >> pop_assum kall_tac >>
    qspecl_then [`MAP FST lcs`,`avoid`]
      assume_tac fresh_var_list_correctness >>
    gvs[DISJOINT_DEF, EXTENSION] >> rw[] >>
    pop_assum (qspec_then `x` assume_tac) >> gvs[] >>
    Cases_on `MEM x (MAP FST lcs)` >> gvs[] >>
    gvs[SUBSET_DEF] >>
    last_x_assum (qspec_then `x` assume_tac) >>
    last_x_assum (qspec_then `x` assume_tac) >> gvs[]
    )
QED

Theorem freevars_freshen_mono:
  ∀ avoid e . freevars e ⊆ set avoid
  ⇒ freevars (freshen avoid e) = freevars e
Proof
  rw[]
  \\ drule exp_alpha_freshen
  \\ disch_tac
  \\ imp_res_tac exp_alpha_freevars
  \\ fs[]
QED

(********Capture avoiding substitution**********)

Theorem App_Lam_bisim:
  closed (Lam x body) ∧ closed arg ⇒
  App (Lam x body) arg ≃ subst1 x arg body
Proof
  rw [] \\ match_mp_tac eval_IMP_app_bisimilarity
  \\ fs [eval_Let,bind1_def]
  \\ match_mp_tac IMP_closed_subst
  \\ fs [] \\ fs [closed_def,FILTER_EQ_NIL,EVERY_MEM,SUBSET_DEF]
QED

Triviality app_bisimilarity_trans =
  transitive_app_bisimilarity |> SIMP_RULE std_ss [transitive_def];

Triviality app_bisimilarity_sym =
  symmetric_app_bisimilarity |> SIMP_RULE std_ss [symmetric_def];

Definition perm1_list_def:
  perm1_list [] z = z ∧
  perm1_list ((x,y)::rest) z = perm1 x y (perm1_list rest z)
End

Theorem boundvars_perm_exp_list:
  ∀l e. boundvars (perm_exp_list l e) = IMAGE (perm1_list l) (boundvars e)
Proof
  recInduct perm_exp_list_ind >> rw[perm_exp_list_def]
  >- (rw[EXTENSION, perm1_list_def]) >>
  gvs[EXTENSION, boundvars_eqvt, PULL_EXISTS] >>
  rw[perm1_list_def]
QED

Theorem perm1_list_unchanged:
  ∀l x. ¬ MEM x (MAP FST l) ∧ ¬ MEM x (MAP SND l) ⇒ perm1_list l x = x
Proof
  recInduct perm1_list_ind >> rw[perm1_list_def] >>
  gvs[perm1_def]
QED

Theorem perm1_list_fresh_var_list_correctness:
  ∀l avoid A.
    A ⊆ set avoid
  ⇒ DISJOINT (IMAGE (perm1_list (fresh_var_list l avoid)) (set l)) A
Proof
  Induct >> rw[] >>
  gvs[fresh_var_list_def, DISJOINT_DEF, EXTENSION,
      DISJ_EQ_IMP, PULL_EXISTS, PULL_FORALL] >>
  rw[]
  >- (
    simp[perm1_list_def] >>
    qspecl_then [`h`,`avoid`] assume_tac fresh_var_DISJ >> gvs[perm1_simps]
    >- (last_x_assum irule >> gvs[SUBSET_DEF]) >>
    qabbrev_tac `fh = fresh_var h avoid` >> rename1 `MEM x l` >>
    last_x_assum (qspecl_then [`fh::avoid`,`fh INSERT set avoid`] mp_tac) >>
    simp[SUBSET_OF_INSERT] >> disch_then drule >> strip_tac >>
    simp[perm1_def] >> gvs[SUBSET_DEF] >>
    rw[] >> metis_tac[]
    ) >>
  qspecl_then [`h`,`avoid`] assume_tac fresh_var_DISJ >> gvs[]
  >- (
    simp[perm1_list_def, perm1_simps] >>
    Cases_on `MEM h l`
    >- (last_x_assum irule >> gvs[SUBSET_DEF]) >>
    qsuff_tac `perm1_list (fresh_var_list l (h::avoid)) h = h`
    >- (gvs[SUBSET_DEF] >> metis_tac[]) >>
    irule perm1_list_unchanged >> simp[MAP_FST_fresh_var_list] >>
    qspecl_then [`l`,`h::avoid`] assume_tac fresh_var_list_correctness >>
    gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
    ) >>
  qabbrev_tac `fh = fresh_var h avoid` >>
  simp[perm1_list_def, perm1_def] >>
  qspecl_then [`h`,`avoid`] assume_tac fresh_var_correctness >>
  IF_CASES_TAC >- metis_tac[SUBSET_DEF] >>
  qspecl_then [`l`,`fh::avoid`] assume_tac fresh_var_list_correctness >>
  gvs[DISJOINT_DEF, EXTENSION] >>
  pop_assum (qspec_then `h` assume_tac) >> gvs[] >>
  Cases_on `¬MEM h l`
  >- (drule_at Any perm1_list_unchanged >> simp[MAP_FST_fresh_var_list]) >>
  gvs[] >> reverse IF_CASES_TAC
  >- (last_x_assum irule >> gvs[SUBSET_DEF]) >>
  last_x_assum (qspecl_then [`fh::avoid`,`fh INSERT set avoid`] assume_tac) >>
  gvs[]
QED

Theorem freshen_safe_renaming:
  ∀ avoid e.
    freevars e ⊆ set avoid
  ⇒ DISJOINT (boundvars (freshen avoid e)) (set avoid)
Proof
  recInduct freshen_ind >> rw[freshen_def]
  >- (
    gvs[DISJOINT_DEF, EXTENSION, DISJ_EQ_IMP] >> rw[] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF] >>
    gvs[MEM_FLAT, MEM_MAP] >>
    first_x_assum irule >> goal_assum drule >> simp[] >>
    gvs[SUBSET_DEF] >> rw[] >>
    last_x_assum irule >> simp[MEM_MAP, PULL_EXISTS] >>
    goal_assum drule >> simp[]
    )
  >- (
    gvs[DISJOINT_DEF, EXTENSION, DISJ_EQ_IMP] >> rw[] >>
    gvs[IMP_CONJ_THM, FORALL_AND_THM] >>
    first_x_assum irule >> gvs[GSYM SUBSET_INSERT_DELETE] >>
    gvs[freevars_eqvt, SUBSET_DEF, PULL_EXISTS] >> rw[] >>
    rename1 `z ∈ _` >> simp[perm1_def] >>
    IF_CASES_TAC >> gvs[] >>
    reverse IF_CASES_TAC >> gvs[] >- metis_tac[] >>
    pop_assum mp_tac >> simp[Once fresh_var_def] >>
    IF_CASES_TAC >> gvs[]
    )
  >- simp[fresh_var_correctness] >>
  gvs[DIFF_SUBSET, AND_IMP_INTRO, GSYM CONJ_ASSOC] >>
  qspecl_then [`MAP FST lcs`,`avoid`] assume_tac fresh_var_list_SUBSET >>
  `freevars e ⊆
    set (MAP SND (fresh_var_list (MAP FST lcs) avoid)) ∪ set avoid` by (
      irule SUBSET_TRANS >> goal_assum drule >> simp[]) >>
  gvs[] >> rw[boundvars_perm_exp_list]
  >- (
    qmatch_goalsub_abbrev_tac `IMAGE _ bvars` >>
    `DISJOINT (set (MAP FST lcs)) bvars` by (
      gvs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
    gvs[DISJOINT_DEF, EXTENSION] >> rw[] >>
    Cases_on `MEM x avoid` >> gvs[] >> rw[] >>
    rename1 `_ ≠ _ z` >>
    first_x_assum (qspec_then `z` assume_tac) >> gvs[] >>
    first_x_assum (qspec_then `z` assume_tac) >> gvs[] >>
    drule_at Any perm1_list_unchanged >> simp[MAP_FST_fresh_var_list] >>
    strip_tac >>
    Cases_on `x = z` >> gvs[] >> metis_tac[]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[IMAGE_BIGUNION] >> rw[] >> pop_assum mp_tac >>
    simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
    qspecl_then [`MAP FST lcs`,`avoid`,`set avoid`]
      assume_tac perm1_list_fresh_var_list_correctness >>
    gvs[DISJOINT_DEF, EXTENSION, DISJ_EQ_IMP, PULL_EXISTS, MEM_MAP] >>
    rw[] >> first_x_assum drule >> simp[GSYM FST_THM]
    )
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    simp[IMAGE_BIGUNION] >> rw[] >> pop_assum mp_tac >>
    simp[MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
    qpat_x_assum `DISJOINT _ _` kall_tac >>
    qpat_x_assum `DISJOINT _ _` kall_tac >>
    ntac 2 $ qpat_x_assum `freevars e ⊆ _` kall_tac >>
    last_x_assum drule >>
    impl_tac
    >- (
      qpat_x_assum `BIGUNION _ ⊆ _` mp_tac >> simp[SUBSET_DEF, PULL_EXISTS] >>
      simp[Once MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
      first_x_assum drule_all >> rw[] >> gvs[] >> gvs[SUBSET_DEF]
      ) >>
    strip_tac >>
    gvs[DISJOINT_DEF, EXTENSION] >> rw[] >>
    Cases_on `MEM x avoid` >> gvs[] >> rw[] >>
    rename1 `z ∉ _` >>
    first_assum (qspec_then `x` assume_tac) >>
    first_x_assum (qspec_then `z` assume_tac) >> gvs[] >>
    first_x_assum (qspec_then `z` assume_tac) >> gvs[] >>
    gvs[SUBSET_DEF] >>
    `¬ MEM z (MAP FST lcs)` by metis_tac[] >>
    drule_at Any perm1_list_unchanged >> simp[MAP_FST_fresh_var_list] >>
    strip_tac >> simp[DISJ_EQ_IMP] >> rw[] >> gvs[]
    )
QED

Definition ca_subst_def:
   ca_subst x arg body =
       subst1 x arg (freshen (freevars_l arg ++ freevars_l body) body)
End

Theorem beta_equivalence:
  App (Lam x body) arg ≅ ca_subst x arg body
Proof
  fs[ca_subst_def, exp_eq_def] >> rw[bind_def, subst_def] >>
  irule app_bisimilarity_trans >>
  irule_at Any App_Lam_bisim >>
  conj_asm1_tac
  >- (
    simp[] >> dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
    simp[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] >> conj_tac >- metis_tac[] >>
    gvs[SUBSET_DEF] >> metis_tac[]
    ) >>
  conj_asm1_tac
  >- (
    simp[closed_def] >> once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
    dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >> simp[IN_FRANGE_FLOOKUP] >>
    simp[SUBSET_DIFF_EMPTY]
    ) >>
  dep_rewrite.DEP_REWRITE_TAC[subst1_distrib] >> rw[] >- metis_tac[]
  >- (
    qspecl_then [`freevars_l arg ++ freevars_l body`,`body`]
      assume_tac freshen_safe_renaming >> gvs[] >>
    gvs[freevars_equiv]
    ) >>
  dep_rewrite.DEP_REWRITE_TAC[subst_subst_FUNION] >>
  simp[FUNION_FUPDATE_2, IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] >>
  conj_tac >- (gvs[freevars_equiv] >> metis_tac[]) >>
  irule exp_alpha_app_bisimilarity >>
  simp[closed_def] >>
  dep_rewrite.DEP_REWRITE_TAC[freevars_subst, freevars_freshen_mono] >>
  simp[IN_FRANGE_FLOOKUP, FLOOKUP_UPDATE] >>
  conj_asm1_tac
  >- (rw[] >> EVERY_CASE_TAC >> gvs[freevars_equiv] >> metis_tac[]) >>
  gvs[SUBSET_DIFF_EMPTY, SUBSET_INSERT_DELETE] >>
  irule exp_alpha_subst_all_closed'' >>
  simp[IN_FRANGE_FLOOKUP, FLOOKUP_UPDATE] >>
  irule exp_alpha_freshen >> simp[]
QED

Theorem beta_bisimilarity:
  closed (Let x arg body) ⇒
  Let x arg body ≃ ca_subst x arg body
Proof
  rw[app_bisimilarity_eq, beta_equivalence] >>
  simp[closed_def, ca_subst_def] >>
  DEP_REWRITE_TAC [freevars_subst, freevars_freshen_mono] >>
  simp[IN_FRANGE_FLOOKUP, FLOOKUP_UPDATE, SUBSET_DIFF_EMPTY] >>
  gvs[freevars_equiv]
QED

(* TODO

Theorem disjoint_namespaces_avoid_vars_mono:
  ∀ avoids body.
      DISJOINT (set avoids) (boundvars body)
    ∧ freevars body ⊆ set avoids
    ⇒ avoid_vars avoids body = body
Proof
  recInduct avoid_vars_ind
  \\ rpt conj_tac
  THEN1 (rw[] \\ fs[avoid_vars_def])
  THEN1 (
    rw[] \\ fs[avoid_vars_def]
    \\ irule MAP_ID_ON
    \\ rw[]
    \\ fs[BIGUNION_SUBSET]
    \\ first_x_assum (qspec_then ‘freevars x’ assume_tac)
    \\ fs[MEM_MAP]
    \\ res_tac \\ rw[] \\ fs[]
  )
  THEN1 (
    rw[]
    \\ fs[avoid_vars_def]
    \\ Cases_on ‘fresh_var x avoid ≠ x’
    THEN1 (
      fs[]
      \\ pop_assum mp_tac \\ fs[]
      \\ once_rewrite_tac[fresh_var_def]
      \\ IF_CASES_TAC \\ fs[]
    )
    \\ fs[perm_exp_id]
    \\ last_x_assum irule
    \\ fs[DELETE_SUBSET_INSERT]
    \\ cheat (wrong)
  )
  THEN1 (
    rw[]
    \\ fs[avoid_vars_def]
    \\ conj_tac
    \\ last_assum irule
    \\ fs[EXTENSION,SUBSET_DEF,DISJOINT_DEF] \\ metis_tac[]
  )
  \\ rw[]
  \\ fs[avoid_vars_def]
  \\ fs[ZIP_MAP]
  \\ fs[MAP_MAP_o,combinTheory.o_DEF]
  \\ cheat
QED

Theorem disjoint_namespaces_beta_equivalence:
    DISJOINT (freevars arg)  (boundvars body)
  ∧ DISJOINT (freevars body) (boundvars body)
  ⇒ App (Lam x body) arg ≅ subst x arg body
Proof
  rw[]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘CA_subst x arg body’
  \\ fs[beta_equivalence]
  \\ fs[CA_subst_def]
  \\ qspecl_then [‘freevars arg ++ freevars body’,‘body’] assume_tac avoid_vars_safe_renaming
  \\ fs[]
  \\ qsuff_tac ‘avoid_vars (freevars arg ++ freevars body) body = body’
  THEN1 (fs[exp_eq_refl])
  \\ irule disjoint_namespaces_avoid_vars_mono
  \\ fs[]
QED

*)

val _ = export_theory();
