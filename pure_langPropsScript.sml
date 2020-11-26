
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory configTheory expTheory pure_langTheory
     listTheory pairTheory pred_setTheory alistTheory;

val _ = new_theory "pure_langProps";

Theorem freevars_expandLets:
  ∀y i cn nm vs cs.
    MEM y (freevars (expandLets i cn nm vs cs)) ∧ y ≠nm ⇒
    MEM y (FILTER (λn. ¬MEM n vs) (freevars cs))
Proof
  strip_tac >>
  Induct_on ‘vs’ >>
  rw[expandLets_def,MEM_FILTER] >>
  gvs[] >>
  gvs[MEM_FILTER] >> metis_tac[]
QED

Theorem freevars_expandRows:
  ∀y nm css.
    MEM y (freevars (expandRows nm css)) ∧ y ≠ nm ⇒
      ∃cn vs cs. MEM (cn,vs,cs) css ∧ MEM y (FILTER (λn. ¬MEM n vs) (freevars cs))
Proof
  strip_tac >>
  ho_match_mp_tac expandRows_ind >>
  rw[freevars_def,expandRows_def,freevars_expandLets] >>
  gvs[MEM_FILTER] >>
  imp_res_tac freevars_expandLets >>
  gvs[MEM_FILTER] >>
  metis_tac[]
QED

Theorem freevars_expandCases:
  ∀y x nm css.
    MEM y (freevars (expandCases x nm css)) ⇒
      (nm ≠ y ∧
       ∃cn vs cs. MEM (cn,vs,cs) css ∧ MEM y (FILTER (λn. ¬MEM n vs) (freevars cs))) ∨
      MEM y (freevars x)
Proof
  rw[expandCases_def,MEM_FILTER] >> simp[] >>
  disj1_tac >>
  drule freevars_expandRows >>
  impl_tac >- simp[] >>
  rw[MEM_FILTER]
QED

Theorem freevars_subst:
  ∀s y e.
  closed y ⇒
  set(freevars (subst s y e)) =
  set(freevars e) DIFF {s}
Proof
  ho_match_mp_tac subst_ind >>
  rw[subst_def,closed_def] >>
  rw[SET_EQ_SUBSET,SUBSET_DEF,MEM_FLAT,MEM_MAP,PULL_EXISTS,MEM_FILTER] >>
  gvs[MEM_MAP,ELIM_UNCURRY,MEM_FILTER,PULL_EXISTS]
  >- metis_tac[]
  >- (goal_assum drule >> gvs[])
  >- metis_tac[]
  >- (BasicProvers.FULL_CASE_TAC >> gvs[] >>
      disj2_tac >> goal_assum drule >>
      rw[] >>
      qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      rw[])
  >- (BasicProvers.FULL_CASE_TAC >> gvs[] >>
      qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      rw[])
  >- (disj2_tac >> goal_assum drule >>
      rw[] >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      simp[])
  >- (BasicProvers.FULL_CASE_TAC >> gvs[] >>
      disj2_tac >> goal_assum drule >>
      rw[] >>
      qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      rw[])
  >- (BasicProvers.FULL_CASE_TAC >> gvs[]
      >- (qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
          qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          conj_tac >- metis_tac[PAIR,FST,SND] >>
          rw[]) >>
      spose_not_then strip_assume_tac >> gvs[])
  >- (disj2_tac >> goal_assum drule >>
      rw[] >>
      qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      rw[])
QED

Theorem freevars_subst:
  ∀s y e.
  closed y ⇒
  set(freevars (subst s y e)) =
  set(freevars e) DIFF {s}
Proof
  ho_match_mp_tac subst_ind >>
  rw[subst_def,closed_def] >>
  rw[SET_EQ_SUBSET,SUBSET_DEF,MEM_FLAT,MEM_MAP,PULL_EXISTS,MEM_FILTER] >>
  gvs[MEM_MAP,ELIM_UNCURRY,MEM_FILTER,PULL_EXISTS]
  >- metis_tac[]
  >- (goal_assum drule >> gvs[])
  >- metis_tac[]
  >- (BasicProvers.FULL_CASE_TAC >> gvs[] >>
      disj2_tac >> goal_assum drule >>
      rw[] >>
      qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      rw[])
  >- (BasicProvers.FULL_CASE_TAC >> gvs[] >>
      qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      rw[])
  >- (disj2_tac >> goal_assum drule >>
      rw[] >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      simp[])
  >- (BasicProvers.FULL_CASE_TAC >> gvs[] >>
      disj2_tac >> goal_assum drule >>
      rw[] >>
      qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      rw[])
  >- (BasicProvers.FULL_CASE_TAC >> gvs[]
      >- (qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
          qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          conj_tac >- metis_tac[PAIR,FST,SND] >>
          rw[]) >>
      spose_not_then strip_assume_tac >> gvs[])
  >- (disj2_tac >> goal_assum drule >>
      rw[] >>
      qpat_x_assum ‘MEM _ (freevars _)’ mp_tac >>
      qpat_x_assum ‘∀g m e'. _ ⇒ _’ (dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
      conj_tac >- metis_tac[PAIR,FST,SND] >>
      rw[])
QED

Theorem freevars_bind:
  ∀f y.
  set(freevars (bind f y)) =
  if EVERY closed (MAP SND f) then
    set(FILTER (λy. ¬MEM y (MAP FST f)) (freevars y))
  else
    {}
Proof
  ho_match_mp_tac bind_ind >>
  rw[bind_def,freevars_subst,LIST_TO_SET_FILTER] >>
  rw[SET_EQ_SUBSET,SUBSET_DEF] >>
  gvs[] >>
  simp[closed_subst |> REWRITE_RULE [closed_def]]
QED

Theorem bind_Var_lemma:
  ∀bs x.
  EVERY closed (MAP SND bs) ∧ ALL_DISTINCT(MAP FST bs) ⇒
    bind bs (Var x) =
    case ALOOKUP bs x of
      SOME e => e
    | NONE => Var x
Proof
  Induct_on ‘bs’ >- rw[bind_def,subst_def] >>
  PairCases >> rw[bind_def,subst_def] >>
  BasicProvers.TOP_CASE_TAC >> gvs[subst_def] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  res_tac >>
  fs[] >>
  metis_tac[FST,SND]
QED

Theorem bind_Lam:
  ∀names x e1.
  ¬MEM x (MAP FST names) ∧ EVERY closed (MAP SND names) ⇒
  bind names (Lam x e1) = Lam x (bind names e1)
Proof
  Induct >- rw[bind_def,subst_def] >>
  PairCases >> rw[bind_def,subst_def]
QED

Theorem bind_App:
  ∀names x e1 e2.
  EVERY closed (MAP SND names) ⇒
  bind names (App e1 e2) = App (bind names e1) (bind names e2)
Proof
  Induct >- rw[bind_def,subst_def] >>
  PairCases >> rw[bind_def,subst_def]
QED

Theorem bind_alt_def:
  ∀ sub.
    EVERY (λe. closed e) (MAP SND sub) ∧
    ALL_DISTINCT (MAP FST sub)
  ⇒
    (∀s.
      bind sub (Var s) = case ALOOKUP sub s of SOME v => v | NONE => Var s) ∧
    (∀op xs. bind sub (Prim op xs) = Prim op (MAP (λe. bind sub e) xs)) ∧
    (∀x y. bind sub (App x y) = App (bind sub x) (bind sub y)) ∧
    (∀s x. bind sub (Lam s x) =
      let sub' = FILTER (λn. FST n ≠ s) sub in (Lam s (bind sub' x))) ∧
    (∀f x. bind sub (Letrec f x) =
      let sub' = FILTER (λn. ALOOKUP f (FST n) = NONE) sub in
      Letrec
        (MAP (λ(g,m,z).
          let sub'' = FILTER (λn. FST n ≠ m) sub' in
          (g,m, bind sub'' z)) f)
      (bind sub' x)) ∧
    (∀e vn css. bind sub (Case e vn css) =
      Case (bind sub e) vn
      (MAP (λ(cn,ans,cb).
        let sub' = FILTER (λn. ¬ MEM (FST n) (vn::ans)) sub in
        (cn, ans, bind sub' cb)) css))
Proof
  Induct >> rw[] >> fs[bind_def]
  >- (Induct_on `f` >> rw[] >> PairCases_on `h` >> fs[])
  >- (Induct_on `css` >> rw[] >> PairCases_on `h` >> fs[]) >>
  PairCases_on `h` >> fs[ALOOKUP_def, bind_def, subst_def]
  >- (
    rw[]
    >- (
      qsuff_tac `ALOOKUP sub h0 = NONE` >> fs[subst_def] >>
      fs[ALOOKUP_NONE]
      ) >>
    CASE_TAC >> fs[subst_def] >>
    irule closed_subst >>
    imp_res_tac ALOOKUP_MEM >>
    fs[EVERY_MEM, MEM_MAP] >>
    first_x_assum irule >>
    qexists_tac `(s,x)` >> fs[]
    )
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF]
    )
  >- (rw[] >> fs[bind_def])
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF] >>
    qpat_abbrev_tac `f' = MAP _ f` >>
    `f' = MAP FST f` by (
      unabbrev_all_tac >>
      rw[MAP_EQ_f] >>
      PairCases_on `x` >> fs[]) >>
    gvs[] >> unabbrev_all_tac >>
    IF_CASES_TAC >> gvs[ALOOKUP_NONE, bind_def] >>
    rw[MAP_EQ_f] >>
    PairCases_on `x` >> gvs[] >>
    IF_CASES_TAC >> gvs[bind_def]
    )
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF] >>
    rw[MAP_EQ_f] >>
    PairCases_on `x` >> fs[] >>
    IF_CASES_TAC >> fs[bind_def]
    )
QED

val _ = export_theory ();
