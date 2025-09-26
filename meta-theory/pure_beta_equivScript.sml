(*
  Capture-avoiding substitution (ca_subst) and beta equivalences:
    App (Lam x body) arg ≅ ca_subst [(x,arg)] body
    Letrec fns e ≅ ca_subst (MAP (λ(f,body). (f, Letrec fns body)) fns) e
*)
Theory pure_beta_equiv
Ancestors
  pair list rich_list alist finite_map pred_set pure_misc
  pure_exp pure_exp_lemmas pure_eval pure_exp_rel
  pure_alpha_equiv pure_congruence
Libs
  BasicProvers dep_rewrite

(********** Freshening as a relation **********)

Definition binds_ok_def:
  binds_ok m ⇔
    ∀l x y r. m = l ++ [x,y] ++ r ⇒
      ¬MEM x (MAP SND r) ∧ ¬MEM y (MAP SND r)
End

Definition perm1_list_def:
  perm1_list [] z = z ∧
  perm1_list ((x,y)::rest) z = perm1 x y (perm1_list rest z)
End

Definition perm_exp_list_def:
  perm_exp_list [] e = e ∧
  perm_exp_list ((old,new)::binds) e = perm_exp old new (perm_exp_list binds e)
End

Inductive freshen_rel:
  freshen_rel avoid (Var x) (Var x) ∧

  (LIST_REL (freshen_rel avoid) es es'
    ⇒ freshen_rel avoid (Prim op es) (Prim op es')) ∧

  (y ∉ avoid ∧ freshen_rel (y INSERT avoid) (perm_exp x y e) e'
    ⇒ freshen_rel avoid (Lam x e) (Lam y e')) ∧

  (freshen_rel avoid e1 e1' ∧ freshen_rel avoid e2 e2'
    ⇒ freshen_rel avoid (App e1 e2) (App e1' e2')) ∧

  (binds_ok binds ∧ EVERY (λx. x ∉ avoid) (MAP SND binds) ∧
   MAP FST binds = MAP FST fns ∧
   LIST_REL (λ(f,body) (f',body').
      perm1_list binds f = f' ∧
      freshen_rel (avoid ∪ set (MAP SND binds)) (perm_exp_list binds body) body')
    fns fns' ∧
   freshen_rel (avoid ∪ set (MAP SND binds)) (perm_exp_list binds e) e'
   ⇒ freshen_rel avoid (Letrec fns e) (Letrec fns' e'))
End


(* Proofs *)

Theorem binds_ok_all_distinct:
  ∀m. binds_ok m ⇒ ALL_DISTINCT (MAP SND m)
Proof
  Induct >> rw[] >> PairCases_on `h` >> gvs[binds_ok_def]
QED

Theorem perm1_list_APPEND:
  ∀l1 l2.  perm1_list (l1 ++ l2) = (perm1_list l1) o (perm1_list l2)
Proof
  Induct >> rw[FUN_EQ_THM, perm1_list_def] >>
  PairCases_on `h` >> rw[perm1_list_def]
QED

Theorem freevars_perm_exp_list:
  ∀binds e. freevars (perm_exp_list binds e) = IMAGE (perm1_list binds) (freevars e)
Proof
  recInduct perm_exp_list_ind >> rw[perm_exp_list_def]
  >- (rw[EXTENSION, perm1_list_def]) >>
  gvs[EXTENSION, freevars_eqvt, PULL_EXISTS] >>
  rw[perm1_list_def]
QED

Theorem perm1_list_id:
  ∀l x. MAP FST l = MAP SND l ⇒ perm1_list l x = x
Proof
  Induct >> rw[perm1_list_def] >>
  PairCases_on `h` >> rw[perm1_list_def] >> gvs[perm1_simps]
QED

Theorem perm_exp_list_id:
  ∀l e. MAP FST l = MAP SND l ⇒ perm_exp_list l e = e
Proof
  Induct >> rw[perm_exp_list_def] >>
  PairCases_on `h` >> rw[perm_exp_list_def] >> gvs[perm_exp_id]
QED

Theorem perm1_list_unchanged:
  ∀l x. ¬ MEM x (MAP FST l) ∧ ¬ MEM x (MAP SND l) ⇒ perm1_list l x = x
Proof
  recInduct perm1_list_ind >> rw[perm1_list_def] >>
  gvs[perm1_def]
QED

Theorem perm1_list_changed:
  ∀m a.
    MEM a (MAP FST m) ∧ ¬ MEM a (MAP SND m) ∧
    binds_ok m
  ⇒ perm1_list m a ≠ a
Proof
  simp[binds_ok_def] >>
  gen_tac >> completeInduct_on `LENGTH m` >> rw[] >> gvs[PULL_FORALL] >>
  Cases_on `m` >> gvs[] >> PairCases_on `h` >> rw[perm1_list_def] >> gvs[] >>
  rename1 `(x,y)`
  >- (
    reverse $ Cases_on `MEM x (MAP FST t)` >> gvs[]
    >- (
      first_x_assum $ qspec_then `[]` assume_tac >> gvs[] >>
      drule_all perm1_list_unchanged >> simp[perm1_def]
      ) >>
    `∃tl z tr. t = tl ++ [x,z] ++ tr ∧ ¬ MEM x (MAP FST tr)` by (
      pop_assum mp_tac >> simp[Once MEM_SPLIT_APPEND_last] >>
      simp[MAP_EQ_APPEND, PULL_EXISTS, FORALL_PROD] >> rw[] >>
      irule_at Any EQ_REFL >> simp[]) >>
    gvs[] >>
    `¬MEM x (MAP SND tr)` by (
      first_x_assum $ qspec_then `(x,y)::tl` mp_tac >> simp[]) >>
    once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[Once perm1_list_APPEND] >>
    simp[perm1_list_def] >> drule_all perm1_list_unchanged >> rw[perm1_simps] >>
    `¬MEM z (MAP FST tl) ∧ ¬MEM z (MAP SND tl)` by (
      rw[] >> simp[MEM_MAP, FORALL_PROD, Once MEM_SPLIT_APPEND_first] >> rw[] >>
      first_x_assum $ qspec_then `(x,y)::pfx` assume_tac >> gvs[]) >>
    drule_all perm1_list_unchanged >> rw[] >>
    `x ≠ z ∧ y ≠ z` by (
      first_assum $ qspec_then `[]` mp_tac >>
      first_x_assum $ qspec_then `(x,y)::tl` mp_tac >> simp[]) >>
    simp[perm1_def]
    )
  >- (
    rename1 `perm1_list _ w` >>
    `∃tl z tr. t = tl ++ [w,z] ++ tr ∧ ¬ MEM w (MAP FST tr)` by (
      qpat_x_assum `MEM _ _` mp_tac >> simp[Once MEM_SPLIT_APPEND_last] >>
      simp[MAP_EQ_APPEND, PULL_EXISTS, FORALL_PROD] >> rw[] >>
      irule_at Any EQ_REFL >> simp[]) >>
    gvs[] >> once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[Once perm1_list_APPEND] >>
    `¬MEM w (MAP SND tr)` by (CCONTR_TAC >> gvs[]) >>
    simp[perm1_list_def] >> drule_all perm1_list_unchanged >> rw[perm1_simps] >>
    `¬MEM z (MAP FST tl) ∧ ¬MEM z (MAP SND tl)` by (
      rw[] >> simp[MEM_MAP, FORALL_PROD, Once MEM_SPLIT_APPEND_first] >> rw[] >>
      first_x_assum $ qspec_then `(x,y)::pfx` assume_tac >> gvs[]) >>
    drule_all perm1_list_unchanged >> rw[] >>
    `x ≠ z ∧ y ≠ z` by (
      first_assum $ qspec_then `[]` mp_tac >>
      first_x_assum $ qspec_then `(x,y)::tl` mp_tac >> simp[]) >>
    simp[perm1_def]
    )
QED

Theorem perm1_list_apply:
  ∀m x.
    MEM x (MAP FST m) ∧
    binds_ok m
  ⇒ ALOOKUP (REVERSE m) x = SOME (perm1_list m x)
Proof
  Induct >> rw[perm1_list_def] >> gvs[binds_ok_def] >>
  PairCases_on `h` >> rename1 `(a,b)` >> gvs[perm1_list_def, ALOOKUP_APPEND]
  >- (
    reverse $ Cases_on `MEM a (MAP FST m)` >> gvs[]
    >- (
      gvs[AllCaseEqs(), ALOOKUP_NONE, MAP_REVERSE] >> disj1_tac >>
      first_x_assum $ qspec_then `[]` mp_tac >> simp[] >> strip_tac >>
      Cases_on `a = b` >> gvs[perm1_list_unchanged, perm1_def]
      ) >>
    last_x_assum drule >> strip_tac >> gvs[] >>
    `perm1_list m a ≠ b` by (
      CCONTR_TAC >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP]) >>
    Cases_on `a = b` >- gvs[perm1_def] >>
    `¬MEM a (MAP SND m)` by (
      first_x_assum $ qspec_then `[]` mp_tac >> simp[]) >>
    first_x_assum $ qspec_then `(a,b)::l` $ assume_tac o GEN_ALL >> gvs[] >>
    simp[perm1_def, AllCaseEqs()] >>
    irule perm1_list_changed >> simp[binds_ok_def]
    )
  >- (
    last_x_assum drule >> strip_tac >> gvs[] >>
    `perm1_list m x ≠ b` by (
      CCONTR_TAC >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP]) >>
    Cases_on `a = b` >- gvs[perm1_def] >>
    `¬MEM a (MAP SND m)` by (
      first_x_assum $ qspec_then `[]` mp_tac >> simp[]) >>
    rw[perm1_def] >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP]
    )
QED

Theorem perm_exp_list_Letrec:
  ∀l fns e.
    perm_exp_list l (Letrec fns e) =
    Letrec
      (MAP (λ(fn,e). (perm1_list l fn, perm_exp_list l e)) fns)
      (perm_exp_list l e)
Proof
  Induct >> rw[perm_exp_list_def]
  >- (rw[perm1_list_def] >> Induct_on `fns` >> rw[] >> pairarg_tac >> gvs[]) >>
  PairCases_on `h` >> gvs[perm_exp_list_def, perm1_list_def] >>
  simp[perm_exp_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

Theorem exp_alpha_perm_exp_list:
  ∀binds e.
    (DISJOINT (set (MAP FST binds)) (freevars e)) ∧
    (DISJOINT (set (MAP SND binds)) (freevars e))
  ⇒ exp_alpha e (perm_exp_list binds e)
Proof
  recInduct perm_exp_list_ind >> rw[perm_exp_list_def, exp_alpha_refl] >>
  irule exp_alpha_Trans >> qexists_tac `perm_exp old new e` >>
  irule_at Any exp_alpha_perm_irrel >> simp[] >>
  irule exp_alpha_perm_closed >>
  last_x_assum irule >> simp[]
QED

Theorem freshen_rel_exp_alpha:
  ∀avoid e1 e2.
    freshen_rel avoid e1 e2 ∧ freevars e1 ⊆ avoid
  ⇒ exp_alpha e1 e2
Proof
  Induct_on `freshen_rel` >> rw[exp_alpha_refl]
  >- ( (* Prim *)
    irule exp_alpha_Prim >> gvs[LIST_REL_EL_EQN] >> rw[] >>
    first_x_assum drule >> strip_tac >>
    first_x_assum irule >> gvs[BIGUNION_SUBSET, MEM_MAP, MEM_EL, PULL_EXISTS]
    )
  >- ( (* Lam *)
    Cases_on `x = y` >> gvs[perm_exp_id]
    >- (
      irule exp_alpha_Lam >> first_x_assum irule >>
      gvs[SUBSET_INSERT_DELETE]
      ) >>
    irule exp_alpha_Trans >> qexists_tac `Lam y (perm_exp x y e)`  >>
    irule_at Any exp_alpha_Lam >>
    first_x_assum (irule_at Any) >> irule_at Any exp_alpha_Alpha >>
    gvs[freevars_eqvt, SUBSET_DEF, perm1_def] >> metis_tac[]
    )
  >- (irule exp_alpha_App >> gvs[]) (* App *)
  >- (
    gvs[DIFF_SUBSET] >> qpat_x_assum `_ ⇒ exp_alpha _ _` mp_tac >> impl_keep_tac
    >- (
      qpat_x_assum `freevars e ⊆ _` mp_tac >> rw[SUBSET_DEF] >>
      gvs[freevars_perm_exp_list] >> Cases_on `MEM x' (MAP FST fns)` >> gvs[]
      >- (
        drule_at Any perm1_list_apply >> simp[] >> disch_then drule >> strip_tac >>
        imp_res_tac ALOOKUP_MEM >> gvs[] >> simp[MEM_MAP, EXISTS_PROD, SF SFY_ss]
        ) >>
      first_x_assum drule >> rw[] >>
      qsuff_tac `perm1_list binds x' = x'` >> simp[] >>
      irule perm1_list_unchanged >> simp[] >>
      rw[MEM_EL, Once MONO_NOT_EQ] >>
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]
      ) >>
    strip_tac >> irule exp_alpha_Trans >>
    irule_at Any exp_alpha_perm_exp_list >> qexists `binds` >> simp[] >> rw[]
    >- simp[DISJOINT_ALT]
    >- (
      irule DISJOINT_SUBSET >> qexists `avoid` >> simp[DIFF_SUBSET] >>
      rw[DISJOINT_ALT] >> gvs[EVERY_MEM]
      ) >>
    simp[perm_exp_list_Letrec] >>
    irule_at Any exp_alpha_Letrec >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> rw[]
    >- (
      gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2, EL_MAP] >> rw[] >>
      first_x_assum drule >> simp[UNCURRY]
      ) >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    first_x_assum drule >> rpt (pairarg_tac >> gvs[]) >>
    strip_tac >> pop_assum irule >>
    qpat_x_assum `BIGUNION _ ⊆ _` mp_tac >>
    simp[SUBSET_DEF] >> simp[Once MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> rw[] >>
    gvs[freevars_perm_exp_list] >> Cases_on `MEM x' (MAP FST fns)` >> gvs[]
    >- (
      drule_at Any perm1_list_apply >> simp[] >> disch_then drule >> strip_tac >>
      imp_res_tac ALOOKUP_MEM >> gvs[] >> simp[MEM_MAP, EXISTS_PROD, SF SFY_ss]
      ) >>
    first_x_assum drule >> simp[Once MEM_EL, PULL_EXISTS] >>
    disch_then drule >> rw[] >>
    qsuff_tac `perm1_list binds x' = x'` >> simp[] >>
    irule perm1_list_unchanged >> simp[] >>
    rw[MEM_EL, Once MONO_NOT_EQ] >>
    gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]
    )
QED

(* ALL_DISTINCT is necessary - consider ``Lam "x" (Lam "x" Fail)`` *)
Theorem freshen_rel_refl:
  ∀e avoid.
    DISJOINT avoid (boundvars e) ∧
    ALL_DISTINCT (boundvars_l e) ∧
    freevars e ⊆ avoid
  ⇒ freshen_rel avoid e e
Proof
  Induct using freevars_ind >> rw[] >> simp[Once freshen_rel_cases]
  >- (
    gvs[LIST_REL_EL_EQN, MEM_EL, EL_MAP, SUBSET_DEF, PULL_EXISTS, SF CONJ_ss] >>
    rw[] >> last_x_assum drule >> disch_then irule >> gvs[] >>
    rw[] >> gvs[] >- metis_tac[] >>
    drule ALL_DISTINCT_FLAT_IMP >> simp[MEM_EL, EL_MAP, PULL_EXISTS]
    )
  >- (
    gvs[ALL_DISTINCT_APPEND] >> rpt $ first_x_assum $ irule_at Any >>
    gvs[DISJOINT_ALT, boundvars_equiv] >> metis_tac[]
    )
  >- (
    simp[perm_exp_id] >> last_x_assum irule >> simp[] >>
    gvs[boundvars_equiv, SUBSET_DEF] >> metis_tac[]
    ) >>
  gvs[ALL_DISTINCT_APPEND] >>
  qexists `ZIP (MAP FST lcs, MAP FST lcs)` >>
  simp[MAP_ZIP, perm1_list_id, perm_exp_list_id] >> rw[]
  >- (
    qpat_x_assum `ALL_DISTINCT (MAP FST lcs)` mp_tac >>
    rpt $ pop_assum kall_tac >> rename1 `ALL_DISTINCT l` >>
    Induct_on `l` >> rw[binds_ok_def] >>
    Cases_on `l'` >> gvs[] >> gvs[binds_ok_def]
    )
  >- gvs[EVERY_MEM, DISJOINT_ALT]
  >- (
    rw[LIST_REL_EL_EQN] >> rpt (pairarg_tac >> gvs[]) >>
    last_x_assum irule >> simp[MEM_EL, PULL_EXISTS] >>
    goal_assum $ drule_at Any >> simp[] >>
    irule_at Any ALL_DISTINCT_FLAT_IMP >> goal_assum drule >>
    simp[MEM_EL, EL_MAP, PULL_EXISTS, SF CONJ_ss] >>
    goal_assum $ drule_at Any >> simp[] >>
    gvs[boundvars_equiv, DISJOINT_ALT, MEM_FLAT] >> rw[]
    >- (
      CCONTR_TAC >> gvs[] >> first_x_assum $ drule_at Concl >>
      simp[MEM_EL, EL_MAP, SF CONJ_ss, PULL_EXISTS] >>
      goal_assum drule >> simp[]
      )
    >- (
      CCONTR_TAC >> gvs[] >>
      first_x_assum drule >> simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
      goal_assum $ drule_at Any >> simp[MEM_EL] >> goal_assum drule >> simp[]
      )
    >- (
      gvs[SUBSET_DEF, SF DNF_ss] >> rw[] >>
      first_x_assum $ qspecl_then [`x`,`freevars body`] mp_tac >>
      simp[Once MEM_EL, EL_MAP, SF CONJ_ss, PULL_EXISTS] >>
      disch_then drule >> simp[] >> metis_tac[]
      )
    )
  >- (
    first_x_assum irule >>
    gvs[DISJOINT_ALT, boundvars_equiv, SUBSET_DEF] >>
    metis_tac[]
    )
QED

Theorem freshen_rel_safe_renaming:
  ∀avoid e1 e2.
    freshen_rel avoid e1 e2 ∧
    freevars e1 ⊆ avoid
  ⇒ DISJOINT avoid (boundvars e2)
Proof
  Induct_on `freshen_rel` >> rw[] >> gvs[DIFF_SUBSET]
  >- gvs[BIGUNION_SUBSET, MEM_EL, EL_MAP, LIST_REL_EL_EQN, PULL_EXISTS]
  >- (
    qpat_x_assum `_ ⇒ _` mp_tac >> impl_tac >> rw[] >>
    simp[freevars_eqvt] >> gvs[SUBSET_DEF] >> rw[perm1_def] >> gvs[] >>
    rw[] >> gvs[]
    )
  >- simp[Once DISJOINT_SYM]
  >- simp[Once DISJOINT_SYM]
  >- (
    simp[Once DISJOINT_SYM] >> qpat_x_assum `_ ⇒ _` mp_tac >> impl_tac >> rw[] >>
    simp[freevars_perm_exp_list] >> gvs[SUBSET_DEF] >> rw[] >>
    Cases_on `MEM x' (MAP FST fns)` >> rw[] >> gvs[]
    >- (
      drule_at Any perm1_list_apply >> simp[] >> disch_then drule >> rw[] >>
      drule ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD, SF SFY_ss]
      )
    >- (
      first_x_assum drule >> rw[] >>
      DEP_REWRITE_TAC[perm1_list_unchanged] >> simp[] >>
      CCONTR_TAC >> gvs[EVERY_MEM]
      )
    )
  >- (
    gvs[LIST_REL_EL_EQN] >>
    `set (MAP FST fns') = IMAGE (perm1_list binds) $ set (MAP FST fns)` by (
      rw[EXTENSION, MEM_EL, EL_MAP, SF CONJ_ss, PULL_EXISTS] >> eq_tac >> rw[] >>
      goal_assum $ drule_at Any >> first_x_assum drule >> rw[UNCURRY]) >>
    `set (MAP FST fns') ⊆ set (MAP SND binds)` by (
      rw[SUBSET_DEF] >>
      drule_at Any perm1_list_apply >> simp[] >> disch_then drule >> rw[] >>
      drule ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD, SF SFY_ss]) >>
    pop_assum mp_tac >> pop_assum kall_tac >>
    rw[SUBSET_DEF, DISJOINT_ALT] >> first_x_assum drule >> rw[] >> gvs[EVERY_MEM]
    )
  >- (
    gvs[BIGUNION_SUBSET] >>
    ntac 2 $ pop_assum mp_tac >> rw[MEM_EL, EL_MAP, SF CONJ_ss, PULL_EXISTS] >>
    gvs[LIST_REL_EL_EQN] >> last_x_assum drule >> rw[UNCURRY] >>
    rw[Once DISJOINT_SYM] >> pop_assum mp_tac >> impl_tac >> rw[] >>
    rw[SUBSET_DEF, freevars_perm_exp_list] >>
    Cases_on `MEM x' (MAP FST fns)` >> gvs[]
    >- (
      drule_at Any perm1_list_apply >> simp[] >> disch_then drule >> rw[] >>
      drule ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD, SF SFY_ss]
      )
    >- (
      DEP_REWRITE_TAC[perm1_list_unchanged] >> simp[] >>
      first_x_assum drule >> simp[UNCURRY, SUBSET_DEF] >>
      disch_then drule >> rw[] >> gvs[] >> CCONTR_TAC >> gvs[EVERY_MEM]
      )
    )
QED

Theorem freshen_rel_freevars:
  ∀avoid e1 e2.
    freshen_rel avoid e1 e2 ∧ freevars e1 ⊆ avoid
  ⇒ freevars e2 = freevars e1
Proof
  rw[] >> drule_all freshen_rel_exp_alpha >> rw[] >>
  drule exp_alpha_freevars >> rw[]
QED

Theorem freshen_rel_reduce:
  ∀avoid e1 e2 avoid'.
    freshen_rel avoid e1 e2 ∧ avoid' ⊆ avoid ⇒
    freshen_rel avoid' e1 e2
Proof
  Induct_on `freshen_rel` >> rw[] >> simp[Once freshen_rel_cases] >> gvs[]
  >- gvs[LIST_REL_EL_EQN]
  >- (gvs[SUBSET_DEF] >> first_x_assum $ irule_at Any >> simp[] >> metis_tac[])
  >- (
    goal_assum drule >> simp[] >> first_x_assum $ irule_at Any >> simp[] >>
    gvs[EVERY_MEM, SUBSET_DEF, LIST_REL_EL_EQN] >> rw[] >> gvs[UNCURRY]
    >- metis_tac[] >>
    first_x_assum drule >> strip_tac >> pop_assum irule >> simp[] >> metis_tac[]
    )
QED


(********** Freshening as a function **********)

Definition fresh_var_def:
  fresh_var v xs = if ¬MEM v xs then v else fresh_var (v ++ "'") xs
Termination
  WF_REL_TAC ‘measure (λ(v,xs). (LENGTH (FLAT xs) + 1) - LENGTH v)’ \\ rw[]
  \\ Induct_on ‘xs’ \\ fs[] \\ rpt strip_tac \\ fs[]
End

Definition fresh_var_list_def:
  fresh_var_list []      to_avoid = [] ∧
  fresh_var_list (x::xs) to_avoid =
    let fresh = fresh_var x to_avoid in
    ((x,fresh)::fresh_var_list xs (fresh::to_avoid))
End

Definition exp_size_alt_def:
  exp_size_alt (Var v) = 1 ∧
  exp_size_alt (Prim op xs) = 1 + SUM (MAP exp_size_alt xs) ∧
  exp_size_alt (App e1 e2) = 1 + exp_size_alt e1 + exp_size_alt e2 ∧
  exp_size_alt (Lam x e) = 1 + exp_size_alt e ∧
  exp_size_alt (Letrec fns e) =
    1 + exp_size_alt e + SUM (MAP (λ(v,fn). exp_size_alt fn) fns)
Termination
  WF_REL_TAC `measure (λe. exp_size e)` >> rw[exp_size_def]
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

Theorem perm_exp_list_size:
  ∀ binds e. exp_size_alt (perm_exp_list binds e) = exp_size_alt e
Proof
  recInduct perm_exp_list_ind >> rw[perm_exp_list_def] >>
  metis_tac[perm_exp_size]
QED

Definition freshen_def:
  freshen avoid (Var x) = (Var x) ∧
  freshen avoid (Prim op es) = Prim op (MAP (freshen avoid) es) ∧
  freshen avoid (Lam x e) =
    (let y = fresh_var x avoid in
    Lam y (freshen (y::avoid) (perm_exp x y e))) ∧
  freshen avoid (App e1 e2) = App (freshen avoid e1) (freshen avoid e2) ∧
  freshen avoid (Letrec fns e) =
    let fresh_vars = fresh_var_list (MAP FST fns) avoid in
    let fresh_fns =
      MAP (λ(f,body).
        perm1_list fresh_vars f,
        freshen (MAP SND fresh_vars ++ avoid) (perm_exp_list fresh_vars body)) fns in
    let fresh_e = freshen (MAP SND fresh_vars ++ avoid) (perm_exp_list fresh_vars e) in
    Letrec fresh_fns fresh_e
Termination
  WF_REL_TAC `measure (λ(_,e). exp_size_alt e)` >> rw[exp_size_alt_def] >>
  simp[GSYM perm_exp_size, perm_exp_list_size]
  >- (Induct_on `fns` >> rw[] >> gvs[])
  >- (Induct_on `es` >> rw[] >> gvs[] >> DECIDE_TAC)
End


(* Proofs *)

Theorem fresh_var_correctness:
  ∀v l. ¬ MEM (fresh_var v l) l
Proof
  recInduct fresh_var_ind \\ rw []
  \\ once_rewrite_tac [fresh_var_def]
  \\ IF_CASES_TAC \\ fs[]
QED

Theorem fresh_var_DISJ:
  ∀v l. (fresh_var v l = v ∧ ¬ MEM v l) ∨ (fresh_var v l ≠ v ∧ MEM v l)
Proof
  once_rewrite_tac[fresh_var_def] >> rw[] >>
  metis_tac[fresh_var_correctness]
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

Theorem MAP_FST_fresh_var_list:
  ∀ v avoid. MAP FST (fresh_var_list v avoid) = v
Proof
  Induct \\ fs[fresh_var_list_def,MAP]
QED

Theorem fresh_var_list_binds_ok:
  ∀vs avoid m.  binds_ok (fresh_var_list vs avoid)
Proof
  simp[binds_ok_def] >>
  Induct >> simp[fresh_var_list_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `l` >> gvs[]
  >- (
    qspecl_then [`h`,`avoid`] assume_tac fresh_var_DISJ >> gvs[] >>
    qspecl_then [`vs`,`fresh_var h avoid::avoid`]
      assume_tac fresh_var_list_correctness >>
    gvs[DISJOINT_ALT] >> metis_tac[]
    )
  >- (
    first_assum drule >> simp[] >> strip_tac >> CCONTR_TAC >> gvs[]
    )
QED

Theorem freshen_imp_freshen_rel:
  ∀avoid e. freshen_rel (set avoid) e (freshen avoid e)
Proof
  recInduct freshen_ind >> rw[freshen_def] >> simp[Once freshen_rel_cases]
  >- gvs[LIST_REL_EL_EQN, MEM_EL, EL_MAP, PULL_EXISTS]
  >- simp[fresh_var_correctness] >>
  qexists `fresh_var_list (MAP FST fns) avoid` >>
  gvs[AC UNION_ASSOC UNION_COMM] >>
  simp[fresh_var_list_binds_ok, MAP_FST_fresh_var_list] >> conj_tac
  >- (
    qspecl_then [`MAP FST fns`,`avoid`] mp_tac fresh_var_list_correctness >>
    simp[DISJOINT_ALT, EVERY_MEM]
    ) >>
  gvs[LIST_REL_EL_EQN, EL_MAP, MEM_EL, PULL_EXISTS] >> rw[] >>
  rpt (pairarg_tac >> gvs[]) >> first_x_assum drule >> simp[]
QED

Theorem exp_alpha_freshen:
  ∀avoid e. freevars e ⊆ (set avoid) ⇒ exp_alpha e (freshen avoid e)
Proof
  rw[] >> irule freshen_rel_exp_alpha >> goal_assum drule >>
  simp[freshen_imp_freshen_rel]
QED


(********** Capture avoiding substitution **********)

Definition ca_subst_def:
  ca_subst binds e =
    subst (FEMPTY |++ binds) (freshen
        (FLAT (MAP (λ(x,e'). freevars_l e') binds) ++ freevars_l e)
        e)
End


(********** Beta equivalences **********)

Theorem beta_equivalence_bisimulation:
  closed (Lam x body) ∧ closed arg
  ⇒ (App (Lam x body) arg ≃ subst1 x arg body) b
Proof
  rw [] \\ match_mp_tac eval_IMP_app_bisimilarity
  \\ fs [eval_Let,bind1_def]
  \\ match_mp_tac IMP_closed_subst
  \\ fs [] \\ fs [closed_def,FILTER_EQ_NIL,EVERY_MEM,SUBSET_DEF]
QED

Theorem disjoint_vars_beta_equivalence:
    DISJOINT (freevars arg) (boundvars body)
  ⇒ App (Lam x body) arg ≅ subst1 x arg body
Proof
  rw[exp_eq_def, bind_def] >> rw[] >> simp[subst_def] >>
  DEP_REWRITE_TAC[subst1_distrib] >> simp[] >> conj_tac >> gvs[] >>
  irule beta_equivalence_bisimulation >> rw[]
  >- (irule IMP_closed_subst >> simp[IN_FRANGE_FLOOKUP])
  >- (
    DEP_REWRITE_TAC[freevars_subst] >>
    simp[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM, PULL_EXISTS] >>
    gvs[SUBSET_DEF] >> metis_tac[]
    )
QED

Theorem beta_equivalence:
  App (Lam x body) arg ≅ ca_subst [(x,arg)] body
Proof
  simp[ca_subst_def] >> qmatch_goalsub_abbrev_tac `freshen avoid` >>
  irule exp_eq_trans >> qexists `Let x arg (freshen avoid body)` >> rw[]
  >- (
    irule exp_eq_App_cong >> irule_at Any exp_eq_Lam_cong >> simp[exp_eq_refl] >>
    irule exp_alpha_exp_eq >> irule exp_alpha_freshen >>
    unabbrev_all_tac >> simp[freevars_equiv]
    )
  >- (
    simp[GSYM FUPDATE_EQ_FUPDATE_LIST] >>
    irule disjoint_vars_beta_equivalence >>
    qspecl_then [`avoid`,`body`] assume_tac freshen_imp_freshen_rel >>
    dxrule freshen_rel_safe_renaming >>
    unabbrev_all_tac >> simp[DISJOINT_ALT, freevars_equiv]
    )
QED

Theorem beta_equivalence_Letrec_bisimulation:
  closed (Letrec fns e) ⇒
  (Letrec fns e ≃ subst (FEMPTY |++ (MAP (λ(f,body). f, Letrec fns body) fns)) e) b
Proof
  rw[] >> irule eval_IMP_app_bisimilarity >>
  simp[eval_Letrec, subst_funs_def, bind_def, FLOOKUP_FUPDATE_LIST, AllCaseEqs()] >>
  reverse $ IF_CASES_TAC >> gvs[]
  >- (
    irule FALSITY >> pop_assum mp_tac >> simp[] >>
    dxrule ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> strip_tac >> gvs[] >>
    gvs[EVERY_MAP, EVERY_MEM] >> first_x_assum drule >> simp[]
    ) >>
  irule IMP_closed_subst >>
  simp[IN_FRANGE_FLOOKUP, FLOOKUP_FUPDATE_LIST, AllCaseEqs()] >>
  simp[FDOM_FUPDATE_LIST] >> gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
QED

Theorem disjoint_vars_beta_equivalence_Letrec:
    EVERY (λ(f,body). DISJOINT (freevars body DIFF set (MAP FST fns)) (boundvars e)) fns
  ⇒ Letrec fns e ≅ subst (FEMPTY |++ (MAP (λ(f,body). f, Letrec fns body) fns)) e
Proof
  rw[exp_eq_def, bind_def] >> rw[] >> simp[subst_def] >>
  DEP_ONCE_REWRITE_TAC[subst_distrib] >> simp[AC CONJ_ASSOC CONJ_COMM] >>
  conj_tac >> gvs[] >>
  simp[o_f_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  qabbrev_tac `g = FDIFF f (set (MAP FST fns))` >>
  simp[subst_def, FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  simp[GSYM FST_THM] >>
  simp[IN_FRANGE_FLOOKUP, FLOOKUP_FUPDATE_LIST, PULL_EXISTS, AllCaseEqs()] >> rw[]
  >- (
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, EXISTS_PROD] >>
    rw[UNION_DIFF_DISTRIBUTE]
    >- (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
    simp[BIGUNION_DIFF, PULL_EXISTS, MEM_MAP] >> rw[] >> pairarg_tac >> gvs[] >>
    gvs[EVERY_MEM] >> first_x_assum drule >> simp[]
    ) >>
  irule $ SRULE [relationTheory.transitive_def] transitive_app_bisimilarity >>
  irule_at Any beta_equivalence_Letrec_bisimulation >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
  irule_at Any $ SRULE [relationTheory.reflexive_def] reflexive_app_bisimilarity >>
  simp[EVERY_MAP, LAMBDA_PROD] >>
  irule_at Any IMP_closed_subst >>
  simp[IN_FRANGE_FLOOKUP, FLOOKUP_FUPDATE_LIST, FDOM_FUPDATE_LIST] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
  simp[AllCaseEqs(), PULL_EXISTS, SF CONJ_ss] >> conj_asm2_tac >> rw[]
  >- (
    imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, EXISTS_PROD] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM] >>
    gvs[EVERY_MAP, LAMBDA_PROD] >> gvs[EVERY_MEM, FORALL_PROD] >>
    first_x_assum drule >> simp[]
    )
  >- (
    DEP_REWRITE_TAC[freevars_subst] >>
    unabbrev_all_tac >> simp[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF] >>
    gvs[SUBSET_DEF] >> metis_tac[]
    )
  >- (
    gvs[EVERY_MEM, FORALL_PROD] >> rw[] >>
    DEP_REWRITE_TAC[freevars_subst] >>
    unabbrev_all_tac >> simp[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF, FDOM_FDIFF_alt] >>
    gvs[SUBSET_DEF, MEM_MAP, EXISTS_PROD, PULL_EXISTS] >> metis_tac[]
    )
QED

Theorem beta_equivalence_Letrec:
  Letrec fns e ≅ ca_subst (MAP (λ(f,body). f, Letrec fns body) fns) e
Proof
  rw[ca_subst_def] >> qmatch_goalsub_abbrev_tac `freshen avoid` >>
  irule exp_eq_trans >> qexists `Letrec fns (freshen avoid e)` >> rw[]
  >- (
    irule exp_eq_Letrec_cong >> simp[LIST_REL_EL_EQN, exp_eq_refl] >>
    irule exp_alpha_exp_eq >> irule exp_alpha_freshen >>
    unabbrev_all_tac >> simp[freevars_equiv]
    ) >>
  irule disjoint_vars_beta_equivalence_Letrec >>
  qspecl_then [`avoid`,`e`] assume_tac freshen_imp_freshen_rel >>
  dxrule freshen_rel_safe_renaming >> impl_tac
  >- (unabbrev_all_tac >> gvs[freevars_equiv]) >>
  qsuff_tac
    `EVERY (λ(f,body). freevars (Letrec fns body) ⊆ set avoid) fns`
  >- (rw[EVERY_MEM, SUBSET_DEF, DISJOINT_ALT, UNCURRY] >> metis_tac[]) >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
      Excl "freevars_l_def", Excl "freevars_def"] >>
  rw[EVERY_MEM, SUBSET_DEF, Excl "freevars_def", Excl "freevars_l_def"] >>
  pairarg_tac >> gvs[Excl "freevars_def", Excl "freevars_l_def"] >>
  gen_tac >> strip_tac >> unabbrev_all_tac >>
  gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS, EXISTS_PROD, freevars_equiv,
      Excl "freevars_def", Excl "freevars_l_def"] >>
  disj1_tac >> goal_assum drule >> simp[]
QED


(******** Example:  λx.x ≅ λy. (λx.x) y **********)

Definition id_exp_def:
  id_exp = Lam "x" (Var "x")
End

Definition iidd_exp_def:
  iidd_exp = Lam "y" (App id_exp (Var "y"))
End

(* Would be nice to have a tactic that, given a goal like:

        exp_alpha (Lam "y" (Var "y")) (Lam "x" (Var "x"))

        checks whether two closed expressions are exp_alpha, and, if so,
        proves the goal.
        Alternatively, de Bruijn indexes.
*)

Theorem id_iidd_equivalence:
  id_exp ≅ iidd_exp
Proof
 simp[id_exp_def,iidd_exp_def]
 \\ once_rewrite_tac [exp_eq_sym]
 \\ qspecl_then [‘"x"’,‘Var "x"’,‘Var "y"’] assume_tac (GEN_ALL beta_equivalence)
 \\ fs[ca_subst_def,freshen_def,GSYM FUPDATE_EQ_FUPDATE_LIST,subst1_def]
 \\ drule exp_eq_Lam_cong \\ disch_then $ qspec_then `"y"` assume_tac
 \\ irule exp_eq_trans
 \\ qexists_tac ‘Lam "y" (Var "y")’ \\ fs[]
 \\ irule exp_alpha_exp_eq
 \\ qspecl_then [‘"x"’,‘"y"’,‘Lam "y" (Var "y")’] assume_tac exp_alpha_perm_irrel
 \\ fs[perm_exp_def,perm1_def]
QED

Theorem id_iidd_equivalence_expanded =
   id_iidd_equivalence |> REWRITE_RULE [iidd_exp_def,id_exp_def]

