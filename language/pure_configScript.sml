
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory integerTheory stringTheory optionTheory;

val _ = new_theory "pure_config";

val atom_op_ty = new_type ("atom_op", 0);
val atom_lit_ty = new_type ("lit", 0);
val the_config = new_constant ("eval_op", “:atom_op -> lit list -> (lit + bool) option”);

val _ = export_theory ();
