
open bossLib boolLib;
open HolKernel llistTheory listTheory quotientLib pure_miscTheory;

val _ = new_theory "quotient_llist";

Triviality LMAP_id:
  LMAP (\x. x) = \x. x
Proof
  irule EQ_EXT >>
  irule LLIST_EQ >>
  rw[] >>
  Cases_on `x` >> gvs[LMAP]
QED

Theorem llist_map_I:
  LMAP I = I
Proof
  rw [I_def, LMAP_id]
QED

Theorem llist_rel_equality:
  llist_rel $= = $=
Proof
  irule EQ_EXT >> rw[] >>
  irule EQ_EXT >> rw[] >>
  rename1 `llist_rel _ a b` >>
  fs[llist_rel_def] >>
  EQ_TAC >> rw[] >> gvs[] >>
  rw[LNTH_EQ] >>
  Cases_on `LNTH n a`
  >- (
    imp_res_tac LNTH_NONE_LLENGTH >> gvs[] >>
    imp_res_tac LNTH_LLENGTH_NONE >> gvs[]
    ) >>
  reverse (Cases_on `LNTH n b`) >> gvs[]
  >- (
    first_x_assum irule >>
    goal_assum drule >> simp[]
    )
  >- (
    imp_res_tac LNTH_NONE_LLENGTH >> gvs[] >>
    imp_res_tac LNTH_LLENGTH_NONE >> gvs[]
    )
QED

Theorem llist_rel_REFL:
  ∀R.
    (∀x y. R x y ⇔ R x = R y) ⇒
    ∀z. llist_rel R z z
Proof
  simp [llist_rel_def, PULL_FORALL]
  \\ rpt gen_tac
  \\ map_every qid_spec_tac [‘x’, ‘y’, ‘z’, ‘i’]
  \\ Induct \\ rw []
  >- fs [LNTH]
  \\ Q.ISPECL_THEN [‘z’] strip_assume_tac llist_CASES \\ fs []
QED

Triviality llist_rel_lemma:
  ∀R.
    (∀x y. R x y ⇔ R x = R y) ⇒
    ∀z w.
      llist_rel R z w ⇒ llist_rel R z = llist_rel R w
Proof
  rw[] >> irule EQ_EXT >> fs[llist_rel_def] >>
  rw[] >> EQ_TAC >> rw[] >>
  rfs[] >> res_tac
  >- (
    qsuff_tac `∃ elem_z . LNTH i z = SOME elem_z`
    >- (strip_tac >> gvs[]) >>
    Cases_on `LNTH i z` >> gvs[] >>
    imp_res_tac LNTH_NONE_LLENGTH >> gvs[] >>
    imp_res_tac LNTH_LLENGTH_NONE >> gvs[]
    )
  >- (
    qsuff_tac `∃ elem_w . LNTH i w = SOME elem_w`
    >- (strip_tac >> gvs[]) >>
    Cases_on `LNTH i w` >> gvs[] >>
    imp_res_tac LNTH_NONE_LLENGTH >> gvs[] >>
    imp_res_tac LNTH_LLENGTH_NONE >> gvs[]
    )
QED

Theorem llist_EQUIV:
  ∀R. EQUIV R ⇒ EQUIV (llist_rel R)
Proof
  gen_tac
  \\ rw [EQUIV_def]
  \\ eq_tac
  >- metis_tac [llist_rel_lemma]
  \\ rw [FUN_EQ_THM]
  \\ irule llist_rel_REFL \\ fs []
QED

Theorem llist_QUOTIENT:
  ∀R abs rep.
    QUOTIENT R abs rep ⇒
      QUOTIENT (llist_rel R) (LMAP abs) (LMAP rep)
Proof
  rpt strip_tac >>
  rw[QUOTIENT_def]
  >- (
    drule QUOTIENT_ABS_REP >>
    rw[LMAP_MAP, combinTheory.o_DEF, LMAP_id]
    )
  >- (
    drule_then assume_tac QUOTIENT_REP_REFL >>
    rw[llist_rel_def] >> fs[]
    ) >>
  rw[llist_rel_def] >> EQ_TAC >> rw[] >> gvs[]
  >- (
    first_x_assum drule >>
    Cases_on `LNTH i s` >> gvs[]
    >- (
      imp_res_tac LNTH_NONE_LLENGTH >> gvs[] >>
      imp_res_tac LNTH_LLENGTH_NONE >> gvs[]
      ) >>
    qpat_x_assum `QUOTIENT _ _ _` mp_tac >>
    once_rewrite_tac [QUOTIENT_def] >>
    rpt strip_tac >> res_tac
    )
  >- (
    first_x_assum (drule_at (Pos last)) >>
    Cases_on `LNTH i r` >> gvs[]
    >- (
      imp_res_tac LNTH_NONE_LLENGTH >> gvs[] >>
      imp_res_tac LNTH_LLENGTH_NONE >> gvs[]
      ) >>
    qpat_x_assum `QUOTIENT _ _ _` mp_tac >>
    once_rewrite_tac [QUOTIENT_def] >>
    rpt strip_tac >> res_tac
    )
  >- (
    rw[LNTH_EQ] >>
    Cases_on `LNTH n r`
    >- (
      imp_res_tac LNTH_NONE_LLENGTH >> gvs[] >>
      imp_res_tac LNTH_LLENGTH_NONE >> gvs[]
      ) >>
    Cases_on `LNTH n s`
    >- (
      imp_res_tac LNTH_NONE_LLENGTH >> gvs[] >>
      imp_res_tac LNTH_LLENGTH_NONE >> gvs[]
      ) >>
    fs[] >>
    first_x_assum (drule_all_then assume_tac) >>
    drule_then assume_tac QUOTIENT_REL >>
    res_tac
    )
  >- (
    `LLENGTH (LMAP abs r) = LLENGTH (LMAP abs s)` by fs[] >>
    fs[LLENGTH_MAP]
    )
  >- (
    rpt (first_x_assum drule_all >> strip_tac) >>
    qpat_x_assum `QUOTIENT _ _ _` mp_tac >>
    once_rewrite_tac [QUOTIENT_def] >> strip_tac >>
    simp[] >>
    `LNTH i (LMAP abs r) = LNTH i (LMAP abs s)` by metis_tac[] >>
    pop_assum mp_tac >> simp[]
    )
QED

val _ = export_theory ();

