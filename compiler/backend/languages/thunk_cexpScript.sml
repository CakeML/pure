(*
  Compiler expressions for thunkLang
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory;

local open mlstringTheory in end

val _ = new_theory "thunk_cexp";

Datatype:
  cop = Cons mlstring
      | AtomOp atom_op
      | Seq
End

Type cvname = “:mlstring”

Datatype:
  cexp = Var cvname                           (* variable                 *)
       | Prim cop (cexp list)                 (* primitive operations     *)
       | App cexp (cexp list)                 (* function application     *)
       | Lam (cvname list) cexp               (* lambda                   *)
       | Let cvname cexp cexp                 (* let                      *)
       | Letrec ((cvname # cexp) list) cexp   (* mutually recursive exps  *)
       | Case cexp cvname ((cvname # cvname list # cexp) list) (* case of *)
       | Delay cexp                           (* suspend in a Thunk       *)
       | Box cexp                             (* wrap result in a Thunk   *)
       | Force cexp                           (* evaluates a Thunk        *)
End

val cexp_size_eq = fetch "-" "cexp_size_eq";
val cexp_size_def = fetch "-" "cexp_size_def";

Theorem cexp_size_lemma:
  (∀xs a. MEM a xs ⇒ cexp_size a < cexp6_size xs) ∧
  (∀xs p e. MEM (p,e) xs ⇒ cexp_size e < cexp4_size xs) ∧
  (∀xs a1 a2 a. MEM (a1,a2,a) xs ⇒ cexp_size a < cexp1_size xs)
Proof
  rpt conj_tac
  \\ Induct \\ rw [] \\ fs [cexp_size_def] \\ res_tac \\ fs []
QED

Definition is_Delay_def:
  is_Delay (Delay _) = T ∧
  is_Delay _ = F
End

Definition form_of_monad_args_def:
  form_of_monad_args cn =
         if cn = "Ret"    then SOME [K T]
    else if cn = "Raise"  then SOME [K T]
    else if cn = "Bind"   then SOME [is_Delay; is_Delay]
    else if cn = "Handle" then SOME [is_Delay; is_Delay]
    else if cn = "Alloc"  then SOME [is_Delay; is_Delay]
    else if cn = "Length" then SOME [is_Delay]
    else if cn = "Deref"  then SOME [is_Delay; is_Delay]
    else if cn = "Update" then SOME [is_Delay; is_Delay; is_Delay]
    else if cn = "Act"    then SOME [is_Delay]
    else NONE
End

Definition args_ok_def:
  args_ok (Cons cn) n = (
    case form_of_monad_args (explode cn) of
    | SOME ar => LIST_REL (λf e. f e) ar n
    | NONE => T) ∧
  args_ok (AtomOp aop) n = num_atomop_args_ok aop (LENGTH n) ∧
  args_ok Seq n = (LENGTH n = 2)
End

Definition ok_bind_def:
  ok_bind (Delay _) = T ∧
  ok_bind (Lam _ _) = T ∧
  ok_bind _ = F
End

Definition cexp_wf_def:
  cexp_wf (Var v) = T ∧
  cexp_wf (Prim op es) = (args_ok op es ∧ EVERY cexp_wf es) ∧
  cexp_wf (App e es) = (cexp_wf e ∧ EVERY cexp_wf es ∧ es ≠ []) ∧
  cexp_wf (Lam vs e) = (cexp_wf e ∧ vs ≠ []) ∧
  cexp_wf (Let v e1 e2) = (cexp_wf e1 ∧ cexp_wf e2) ∧
  cexp_wf (Letrec fns e) = (EVERY cexp_wf $ MAP SND fns ∧ cexp_wf e ∧ fns ≠ [] ∧
                            EVERY ok_bind $ MAP SND fns ∧
                            ALL_DISTINCT $ MAP FST fns) ∧
  cexp_wf (Case e v css) = (
    cexp_wf e ∧ EVERY cexp_wf $ MAP (SND o SND) css ∧ css ≠ [] ∧
    ¬ MEM v (FLAT $ MAP (FST o SND) css) ∧
    (∀cn. MEM cn (MAP FST css) ⇒ explode cn ∉ monad_cns)) ∧
  cexp_wf (Delay e) = cexp_wf e ∧
  cexp_wf (Force e) = cexp_wf e ∧
  cexp_wf (Box e) = cexp_wf e
Termination
  WF_REL_TAC `measure $ cexp_size` >> rw[fetch "-" "cexp_size_def"] >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 `MEM _ es` >> Induct_on `es` >> rw[] >> gvs[fetch "-" "cexp_size_def"]
End

val _ = export_theory();
