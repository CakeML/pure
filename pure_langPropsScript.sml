
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory configTheory expTheory pure_langTheory listTheory pairTheory pred_setTheory;

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
  TOP_CASE_TAC >> gvs[subst_def] >>
  imp_res_tac ALOOKUP_MEM >>
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

val _ = export_theory ();
