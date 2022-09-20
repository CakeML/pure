
open HolKernel Parse boolLib bossLib BasicProvers;
open arithmeticTheory integerTheory stringTheory optionTheory intLib pred_setTheory;

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
    (* integer operations *)
    | Add | Sub | Mul | Div | Mod
    | Eq | Lt | Leq | Gt | Geq
    (* string operations *)
    | Len | Elem | Concat | Implode | Substring
    | StrEq | StrLt | StrLeq | StrGt | StrGeq
    (* creation of a communication message for use with FFI *)
    | Message string
End

Overload Atom[local] = “λl. SOME (INL l) : (lit + bool) option”;
Overload Bool[local] = “λb. SOME (INR b) : (lit + bool) option”;

Definition concat_def:
  concat [] = SOME "" ∧
  concat (Str s :: t) = OPTION_MAP (λr. s ++ r) (concat t) ∧
  concat (    _ :: _) = NONE
End

Definition implode_def:
  implode [] = SOME "" ∧
  implode (Int i :: t) = OPTION_MAP (λr. CHR (Num (i % 256)) :: r) (implode t) ∧
  implode (    _ :: _) = NONE
End

Definition str_el_def:
  str_elem s i =
    if 0 ≤ i ∧ i < & LENGTH s then & (ORD (EL (Num i) s)) else -1
End

Definition eval_op_def[simp]:
  eval_op (Lit l) [] = Atom l ∧
  eval_op Add [Int i; Int j] = Atom (Int (i + j)) ∧
  eval_op Sub [Int i; Int j] = Atom (Int (i - j)) ∧
  eval_op Mul [Int i; Int j] = Atom (Int (i * j)) ∧
  eval_op Div [Int i; Int j] = Atom (Int (if j = 0 then 0 else i / j)) ∧
  eval_op Mod [Int i; Int j] = Atom (Int (if j = 0 then 0 else i % j)) ∧
  eval_op Eq  [Int i; Int j] = Bool (i = j) ∧
  eval_op Lt  [Int i; Int j] = Bool (i < j) ∧
  eval_op Leq [Int i; Int j] = Bool (i ≤ j) ∧
  eval_op Gt  [Int i; Int j] = Bool (i > j) ∧
  eval_op Geq [Int i; Int j] = Bool (i ≥ j) ∧
  eval_op Len [Str s]  = Atom (Int (& (LENGTH s))) ∧
  eval_op Elem [Str s; Int i] = (Atom (Int (str_elem s i))) ∧
  eval_op Concat strs = OPTION_MAP (INL o Str) (concat strs) ∧
  eval_op Implode ords = OPTION_MAP (INL o Str) (implode ords) ∧
  eval_op Substring [Str s; Int i] =
    Atom $ Str $ DROP (if i < 0 then 0 else Num i) s ∧
  eval_op Substring [Str s; Int i; Int l] =
    (if l < 0 then Atom (Str "") else
      Atom $ Str $ TAKE (Num l) (DROP (if i < 0 then 0 else Num i) s)) ∧
  eval_op StrEq  [Str s; Str t] = Bool (s = t) ∧
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

Definition monad_cns_def:
  monad_cns =
    {"Ret";"Bind";"Raise";"Handle";"Alloc";"Length";"Deref";"Update";"Act"}
End

Definition reserved_cns_def:
  reserved_cns = {"";"True";"False";"Subscript"} ∪ monad_cns
End

Theorem reserved_cns_def:
  reserved_cns =
    {"";"True";"False";"Subscript";
     "Ret";"Bind";"Raise";"Handle";"Alloc";"Length";"Deref";"Update";"Act"}
Proof
  rw[reserved_cns_def, monad_cns_def, EXTENSION] >> eq_tac >> rw[]
QED

Definition max_FFI_return_size_def:
  max_FFI_return_size = 4096n (* bytes *)
End

Definition num_atomop_args_ok_def:
  num_atomop_args_ok (Lit l) n      = (n = 0n) ∧
  num_atomop_args_ok Add n          = (n = 2) ∧
  num_atomop_args_ok Sub n          = (n = 2) ∧
  num_atomop_args_ok Mul n          = (n = 2) ∧
  num_atomop_args_ok Div n          = (n = 2) ∧
  num_atomop_args_ok Mod n          = (n = 2) ∧
  num_atomop_args_ok Eq n           = (n = 2) ∧
  num_atomop_args_ok Lt n           = (n = 2) ∧
  num_atomop_args_ok Leq n          = (n = 2) ∧
  num_atomop_args_ok Gt n           = (n = 2) ∧
  num_atomop_args_ok Geq n          = (n = 2) ∧
  num_atomop_args_ok Len n          = (n = 1) ∧
  num_atomop_args_ok Elem n         = (n = 2) ∧
  num_atomop_args_ok Concat n       = T ∧
  num_atomop_args_ok Implode n      = T ∧
  num_atomop_args_ok Substring n    = (n = 2 ∨ n = 3) ∧
  num_atomop_args_ok StrEq n        = (n = 2) ∧
  num_atomop_args_ok StrLt n        = (n = 2) ∧
  num_atomop_args_ok StrLeq n       = (n = 2) ∧
  num_atomop_args_ok StrGt n        = (n = 2) ∧
  num_atomop_args_ok StrGeq n       = (n = 2) ∧
  num_atomop_args_ok (Message ch) n = (n = 1)
End

Theorem num_atomop_args_ok_check:
  num_atomop_args_ok op n ⇔ ∃l res. n = LENGTH l ∧ eval_op op l = SOME res
Proof
  simp[DefnBase.one_line_ify NONE num_atomop_args_ok_def] >>
  TOP_CASE_TAC >> rw[EQ_IMP_THM] >>
  gvs[DefnBase.one_line_ify NONE eval_op_def, AllCaseEqs(), PULL_EXISTS]
  >- (
    qexists_tac `REPLICATE n (Str "")` >> simp[] >>
    Induct_on `n` >> rw[concat_def]
    )
  >- (
    qexists_tac `REPLICATE n (Int 0)` >> simp[] >>
    Induct_on `n` >> rw[implode_def]
    )
  >- (
    simp[SF DNF_ss] >> metis_tac[]
    )
QED

Definition num_monad_args_def:
  num_monad_args cn =
         if cn = "Ret"    then SOME 1n
    else if cn = "Bind"   then SOME 2
    else if cn = "Raise"  then SOME 1
    else if cn = "Handle" then SOME 2
    else if cn = "Alloc"  then SOME 2
    else if cn = "Length" then SOME 1
    else if cn = "Deref"  then SOME 2
    else if cn = "Update" then SOME 3
    else if cn = "Act"    then SOME 1
    else NONE
End

Theorem num_monad_args_ok_monad_cns:
  IS_SOME (num_monad_args cn) ⇔ cn ∈ monad_cns
Proof
  rw[DefnBase.one_line_ify NONE num_monad_args_def] >>
  simp[monad_cns_def]
QED

val _ = export_theory ();
