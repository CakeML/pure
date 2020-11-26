
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory configTheory expTheory pure_langTheory;

val _ = new_theory "pure_langProps";

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

val _ = export_theory ();
