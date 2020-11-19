
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory integerTheory stringTheory optionTheory;

val _ = new_theory "config";

(*
 * A basic configuration that supports integers and strings. This configuration
 * is hardcoded into the types defined in [{exp,value,pure_lang}Script.sml].
 *)

Datatype:
  lit = Int int
      | Str string
End

Datatype:
  atom = Add | Concat | Length
End

Definition atom_op_def:
  atom_op op args =
    case (op, args) of
      (Add, [Int x; Int y]) => SOME (Int (x + y))
    | (Concat, [Str s; Str t]) => SOME (Str (STRCAT s t))
    | (Length, [Str s]) => SOME (Int &(STRLEN s))
    | _ => NONE
End

val _ = export_theory ();

