
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory pairTheory listTheory
     finite_mapTheory pred_setTheory;

val _ = new_theory "pure_misc";

Theorem FDIFF_FUNION:
  ∀fm1 fm2 s. FDIFF (fm1 ⊌ fm2) s = (FDIFF fm1 s) ⊌ (FDIFF fm2 s)
Proof
  rw[FDIFF_def, DRESTRICTED_FUNION] >>
  rw[fmap_eq_flookup] >>
  rw[FLOOKUP_DRESTRICT, FLOOKUP_FUNION] >> fs[] >>
  rw[FLOOKUP_DEF]
QED

Theorem BIGUNION_DIFF:
  ∀as b. (BIGUNION as) DIFF b = BIGUNION {a DIFF b | a ∈ as}
Proof
  rw[EXTENSION] >> eq_tac >> rw[] >> gvs[]
  >- (
    qexists_tac `s DIFF b` >> fs[] >>
    goal_assum (drule_at Any) >> fs[]
    )
  >- (
    goal_assum (drule_at Any) >> fs[]
    )
QED

val _ = export_theory();
