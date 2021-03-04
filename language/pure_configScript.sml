
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory integerTheory stringTheory optionTheory;

val _ = new_theory "pure_config";

Datatype:
  lit = Int int            (* mathematical integer           *)
      | Str string         (* string of characters           *)
      | Loc num            (* location of an array           *)
      | Msg string string  (* message: channel name, content *)
End

Datatype:
  atom_op =
    (* literal Int or Str *)
      Lit lit
    (* equality *)
    | Eq
    (* integer operations *)
    | Add | Sub | Mul | Div | Mod
    | Lt | Leq | Gt | Geq
    (* string operations *)
    | Len | Elem | Concat | Implode | Substring
    | StrLt | StrLeq | StrGt | StrGeq
    (* creation of a communication message for use with FFI *)
    | Message string
End

Overload Atom[local] = “λl. SOME (INL l) : (lit + bool) option”;
Overload Bool[local] = “λb. SOME (INR b) : (lit + bool) option”;

Definition concat_def:
  concat [] = SOME "" ∧
  concat (Str s :: t) = OPTION_MAP (λr. s ++ r) (concat t) ∧
  concat (Int _ :: _) = NONE
End

Definition implode_def:
  implode [] = SOME "" ∧
  implode (Int i :: t) = OPTION_MAP (λr. CHR (Num (i % 256)) :: r) (implode t) ∧
  implode (Str _ :: _) = NONE
End

Definition str_el_def:
  str_elem s i =
    if 0 ≤ i ∧ i < & LENGTH s then & (ORD (EL (Num i) s)) else -1
End

Definition eval_op_def[simp]:
  eval_op (Lit (Int i)) [] = Atom (Int i) ∧
  eval_op (Lit (Str s)) [] = Atom (Str s) ∧
  eval_op Eq  [x; y] = Bool (x = y) ∧
  eval_op Add [Int i; Int j] = Atom (Int (i + j)) ∧
  eval_op Sub [Int i; Int j] = Atom (Int (i - j)) ∧
  eval_op Mul [Int i; Int j] = Atom (Int (i * j)) ∧
  eval_op Div [Int i; Int j] = Atom (Int (if j = 0 then 0 else i / j)) ∧
  eval_op Mod [Int i; Int j] = Atom (Int (if j = 0 then 0 else i % j)) ∧
  eval_op Lt  [Int i; Int j] = Bool (i < j) ∧
  eval_op Leq [Int i; Int j] = Bool (i ≤ j) ∧
  eval_op Gt  [Int i; Int j] = Bool (i > j) ∧
  eval_op Geq [Int i; Int j] = Bool (i ≥ j) ∧
  eval_op Len [Str s]  = Atom (Int (& (LENGTH s))) ∧
  eval_op Elem [Str s; Int i] = (Atom (Int (str_elem s i))) ∧
  eval_op Concat strs = OPTION_MAP (INL o Str) (concat strs) ∧
  eval_op Implode ords = OPTION_MAP (INL o Str) (implode ords) ∧
  eval_op Substring [Str s; Int i] = Atom (Str (DROP (Num (i % (& LENGTH s))) s)) ∧
  eval_op StrLt  [Str s; Str t] = Bool (s < t) ∧
  eval_op StrLeq [Str s; Str t] = Bool (s ≤ t) ∧
  eval_op StrGt  [Str s; Str t] = Bool (s > t) ∧
  eval_op StrGeq [Str s; Str t] = Bool (s ≥ t) ∧
  eval_op (Message chl) [Str s] = Atom (Msg chl s) ∧
  eval_op _ _ = NONE
End

Theorem eval_op_SOME =
  “eval_op op vs = SOME r”
  |> SIMP_CONV (srw_ss()) [DefnBase.one_line_ify NONE eval_op_def,
                           AllCaseEqs(),PULL_EXISTS];

Theorem eval_op_NONE =
  “eval_op op vs = NONE”
  |> SIMP_CONV (srw_ss()) [DefnBase.one_line_ify NONE eval_op_def,
                           AllCaseEqs(),PULL_EXISTS];

Definition isStr_def[simp]:
  isStr (Str s) = T ∧ isStr _ = F
End

Definition isInt_def[simp]:
  isInt (Int i) = T ∧ isInt _ = F
End

val _ = export_theory ();
