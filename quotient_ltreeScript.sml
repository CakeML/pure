
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
  cheat
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
  rw [EQUIV_def]
  \\ eq_tac
  >- cheat
  \\ rw [FUN_EQ_THM]
  \\ irule ltree_rel_REFL
  \\ fs []
QED

Theorem ltree_QUOTIENT:
  ∀R abs rep.
    QUOTIENT R abs rep ⇒
      QUOTIENT (ltree_rel R) (ltree_map abs) (ltree_map rep)
Proof
  cheat
QED

val _ = export_theory ();
