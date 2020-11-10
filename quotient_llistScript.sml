
open bossLib boolLib;
open HolKernel llistTheory listTheory quotientLib;

val _ = new_theory "quotient_llist";

Triviality I_def:
  I = \x. x
Proof
  rw [combinTheory.I_DEF, combinTheory.S_DEF]
QED

Triviality LMAP_id:
  LMAP (\x. x) = \x. x
Proof
  cheat
QED

Theorem llist_map_I:
  LMAP I = I
Proof
  rw [I_def, LMAP_id]
QED

Theorem llist_rel_equality:
  llist_rel $= = $=
Proof
  cheat
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
  cheat
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
  rpt strip_tac
  \\ rw [QUOTIENT_def]
  >-
   (drule QUOTIENT_ABS_REP
    \\ rw [LMAP_MAP, combinTheory.o_DEF, LMAP_id])
  >-
   (drule_then assume_tac QUOTIENT_REP_REFL
    \\ cheat)
  \\ cheat
QED

val _ = export_theory ();

