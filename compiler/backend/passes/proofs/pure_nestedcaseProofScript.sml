open HolKernel Parse boolLib bossLib;

open listTheory pairTheory

open pure_nestedcaseTheory pureLangTheory pure_cexpTheory pure_congruenceTheory
     pure_exp_lemmasTheory

val _ = new_theory "pure_nestedcaseProof";

Theorem exp_eq_refl[simp] = exp_eq_refl

Theorem silly_cong_lemma[local]:
  ((∀a b. MEM (a,b) l2 ⇒ P a b) ⇔ (∀p. MEM p l2 ⇒ P (FST p) (SND p))) ∧
  ((∀a b c. MEM (a,b,c) l3 ⇒ Q a b c) ⇔
     (∀t. MEM t l3 ⇒ Q (FST t) (FST (SND t)) (SND (SND t))))
Proof
  simp[FORALL_PROD]
QED


Theorem MEM_updlast:
  ∀l rep x.
    l ≠ [] ⇒
    (MEM x (updlast l rep) ⇔ MEM x (FRONT l) ∨ MEM x rep)
Proof
  recInduct updlast_ind >> simp[] >> metis_tac[]
QED

Theorem updlast_SNOC:
  ∀l rep y. updlast (l ++ [y]) rep = l ++ rep
Proof
  Induct >> simp[] >> Cases_on ‘l’ >> gvs[]
QED

Definition nested_rows_term_def:
  nested_rows_term v t [] = t ∧
  nested_rows_term v t (pe::pes) =
  let (gd,binds) = patguards [(v, FST pe)]
  in
    If gd (FOLDR (λ(u,e) A. Let u e A) (SND pe) binds)
       (nested_rows_term v t pes)
End

Theorem nested_rows_to_termform:
  nested_rows v pes = nested_rows_term v Fail pes
Proof
  Induct_on ‘pes’ >> simp[nested_rows_def, nested_rows_term_def]
QED

Theorem nested_rows_term_APPEND:
  nested_rows_term v t (l1 ++ l2) =
  nested_rows_term v (nested_rows_term v t l2) l1
Proof
  Induct_on ‘l1’ >> simp[nested_rows_term_def]
QED

Theorem lift_uscore_correct:
  ∀e. exp_of (lift_uscore e) ≅ exp_of e
Proof
  ho_match_mp_tac better_cexp_induction >> cheat (*
  rpt conj_tac >>
  simp[lift_uscore_thm, exp_of_def, MAP_MAP_o, Cong MAP_CONG,
       combinTheory.o_ABS_L] >> simp[SF ETA_ss]
  >- (simp[UNCURRY] >> rpt strip_tac >>
      irule MAP_CONG >> simp[FORALL_PROD] >> metis_tac[])
  >- (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, EXISTS_PROD] >>
      rw[] >> rw[] >> AP_TERM_TAC >> irule MAP_CONG >>
      simp[FORALL_PROD] >> metis_tac[]) >>
  rpt strip_tac >> rename [‘pes = []’] >>
  Cases_on ‘pes = []’ >> simp[exp_of_def] >>
  pairarg_tac >>
  rename [‘LAST pes = (p,e)’, ‘NestedCase _ (lift_uscore test)’] >>
  simp[] >> reverse $ Cases_on ‘p = cepatUScore’ >> simp[]
  >- (simp[exp_of_def, MAP_MAP_o, combinTheory.o_ABS_R,
           pairTheory.o_UNCURRY_R] >>
      simp[ELIM_UNCURRY] >> rw[] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[FORALL_PROD] >>
      metis_tac[]) >>
  simp[] >>
  Cases_on ‘dest_nestedcase (lift_uscore e)’ >> simp[]
  >- (simp[exp_of_def, MAP_MAP_o, combinTheory.o_ABS_R,
           pairTheory.o_UNCURRY_R] >>
      simp[ELIM_UNCURRY] >> rw[] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[FORALL_PROD] >>
      metis_tac[]) >>
  ‘∃te' tn' pes'. dest_nestedcase (lift_uscore e) = SOME (te',tn',pes')’
    by metis_tac[pair_CASES] >> gvs[] >>
  Cases_on ‘dest_var te'’ >> simp[]
  >- (simp[exp_of_def, MAP_MAP_o, combinTheory.o_ABS_R,
           pairTheory.o_UNCURRY_R] >>
      simp[ELIM_UNCURRY] >> rw[] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[FORALL_PROD] >>
      metis_tac[]) >>
  rename [‘NestedCase _ (lift_uscore test) nm1’, ‘nm2 = nm1’] >>
  reverse $ Cases_on ‘nm1 = nm2’ >> simp[]
  >- (simp[exp_of_def, MAP_MAP_o, combinTheory.o_ABS_R,
           pairTheory.o_UNCURRY_R] >>
      simp[ELIM_UNCURRY] >> rw[] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[FORALL_PROD] >>
      metis_tac[]) >>
  gvs[] >> simp[exp_of_def] >>
  qabbrev_tac ‘pes0 = FRONT pes’ >>
  ‘pes = pes0 ++ [(cepatUScore, e)]’ by metis_tac[APPEND_FRONT_LAST] >>
  Q.RM_ABBREV_TAC ‘pes0’ >> pop_assum SUBST_ALL_TAC >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, updlast_SNOC, MAP_MAP_o,
      pairTheory.o_UNCURRY_R, combinTheory.o_ABS_R] >>
  Cases_on ‘lift_uscore e’ >> gvs[dest_nestedcase_def, exp_of_def] >>
  simp[nested_rows_to_termform, nested_rows_term_APPEND] >>
  simp[nested_rows_term_def, patguards_def]
*)
QED



val _ = export_theory();
