
open bossLib boolLib;
open HolKernel quotient_llistTheory ltreeTheory quotientLib;

val _ = new_theory "quotient_ltree";

Triviality I_def:
  I = \x. x
Proof
  rw [combinTheory.I_DEF, combinTheory.S_DEF]
QED

Triviality ltree_map_id:
  ltree_map (\x. x) = \x. x
Proof
  rw [FUN_EQ_THM, GSYM I_def, ltreeTheory.ltree_map_id]
QED

Triviality ltree_map_I:
  ltree_map I = I
Proof
  rw [I_def, ltree_map_id]
QED

Theorem ltree_rel_equality:
  ltree_rel $= = $=
Proof
  rpt (irule EQ_EXT >> rw[]) >>
  rw[ltree_rel_eq]
QED

Theorem ltree_rel_REFL:
  ∀R.
    (∀x y. R x y ⇔ R x = R y) ⇒
    ∀z. ltree_rel R z z
Proof
  simp [ltree_rel_def, llist_rel_REFL]
QED

Theorem ltree_EQUIV:
  ∀R. EQUIV R ⇒ EQUIV (ltree_rel R)
Proof
  rw [EQUIV_def] >> eq_tac
  >- (
    strip_tac >>
    irule EQ_EXT >> strip_tac >>
    rename1 `ltree_rel _ a b ⇔ ltree_rel _ c b` >>
    fs[ltree_rel_def] >>
    eq_tac >> rw[] >>
    ntac 2 (first_x_assum (qspec_then `path` assume_tac)) >>
    Cases_on `ltree_el a path` >> gvs[optionTheory.OPTREL_def]
    )
  >- (
    rw[] >>
    irule ltree_rel_REFL >> simp[]
    )
QED

Theorem ltree_el_map:
  ∀ path f t.
    ltree_el (ltree_map f t) path =
    OPTION_MAP (f ## OPTION_MAP I) (ltree_el t path)
Proof
  Induct >> rw[] >>
  qspec_then `t` STRUCT_CASES_TAC ltree_cases >>
  fs[ltree_el_def, ltree_map, llistTheory.LLENGTH_MAP] >>
  Cases_on `LNTH h ts` >> fs[]
QED

Theorem ltree_QUOTIENT:
  ∀R abs rep.
    QUOTIENT R abs rep ⇒
      QUOTIENT (ltree_rel R) (ltree_map abs) (ltree_map rep)
Proof
  rpt strip_tac >> rw[QUOTIENT_def]
  >- (
    drule QUOTIENT_ABS_REP >>
    rw[ltree_map_map, combinTheory.o_DEF, ltree_map_id]
    )
  >- (
    drule QUOTIENT_REP_REFL >>
    rw[ltree_rel_def] >>
    fs[ltree_el_map] >>
    Cases_on `ltree_el a path` >>
    fs[optionTheory.OPTION_MAP_DEF]
    ) >>
  rw[ltree_rel_def] >> EQ_TAC >> rw[]
  >- (
    first_x_assum (qspec_then `path` assume_tac) >>
    Cases_on `ltree_el r path` >>
    Cases_on `ltree_el s path` >>
    fs[optionTheory.OPTION_MAP_DEF] >>
    rename1 `ltree_el r _ = SOME pr` >> rename1 `ltree_el s _ = SOME ps` >>
    PairCases_on `pr` >> fs[] >> PairCases_on `ps` >> gvs[] >>
    qpat_x_assum `QUOTIENT _ _ _` mp_tac >>
    once_rewrite_tac [QUOTIENT_def] >>
    strip_tac >> res_tac
    )
  >- (
    first_x_assum (qspec_then `path` assume_tac) >>
    Cases_on `ltree_el r path` >>
    Cases_on `ltree_el s path` >>
    fs[optionTheory.OPTION_MAP_DEF] >>
    rename1 `ltree_el r _ = SOME pr` >> rename1 `ltree_el s _ = SOME ps` >>
    PairCases_on `pr` >> fs[] >> PairCases_on `ps` >> gvs[] >>
    qpat_x_assum `QUOTIENT _ _ _` mp_tac >>
    once_rewrite_tac [QUOTIENT_def] >>
    strip_tac >> res_tac
    )
  >- (
    fs[ltree_el_eqv, ltree_el_map] >> rw[] >>
    first_x_assum (qspec_then `path` assume_tac) >>
    gvs[optionTheory.OPTREL_def, optionTheory.OPTION_MAP_DEF] >>
    PairCases_on `x` >> PairCases_on `y` >> gvs[] >>
    qpat_x_assum `QUOTIENT _ _ _` mp_tac >>
    once_rewrite_tac [QUOTIENT_def] >>
    strip_tac >> res_tac
    )
  >- (
    `ltree_el (ltree_map abs r) path = ltree_el (ltree_map abs s) path` by
      simp[] >>
    fs[ltree_el_map] >>
    Cases_on `ltree_el r path` >> Cases_on `ltree_el s path` >>
    fs[optionTheory.OPTION_MAP_DEF] >>
    rename1 `ltree_el r _ = SOME pr` >> rename1 `ltree_el s _ = SOME ps` >>
    PairCases_on `pr` >> PairCases_on `ps` >> gvs[] >>
    ntac 2 (first_x_assum (qspec_then `path` assume_tac)) >> gvs[] >>
    qpat_x_assum `QUOTIENT _ _ _` mp_tac >>
    once_rewrite_tac [QUOTIENT_def] >> strip_tac >>
    res_tac
    )
QED

val _ = export_theory ();
