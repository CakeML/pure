
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory integerTheory stringTheory optionTheory;

val _ = new_theory "pure_config";

(* Configuration record for the parametric atoms.
   parAtomOp:
     It takes an element of type 'a (from AtomOp) and returns a
     function that takes a "'b list" element and SOME b if the
     number of arguments is correct, NONE otherwise
*)

Datatype:
  conf = <| parAtomOp  : 'a -> 'b list -> 'b option; |>
End

(*
 * Assume an abstract configuration exists.
 *)

val atom_op_ty = new_type ("atom_op", 0);
val atom_lit_ty = new_type ("lit", 0);
val the_config = new_constant ("config", “:(atom_op, lit) conf”);

val _ = export_theory ();
