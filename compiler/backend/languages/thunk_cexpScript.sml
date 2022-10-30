(*
   This file defines expressions for thunkLang as the compiler sees them.
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory mlstringTheory pure_configTheory;

val _ = new_theory "thunk_cexp";

Type name[local] = “:mlstring”

Datatype:
  cop = Cons name          (* datatype constructor            *)
      | AtomOp atom_op     (* primitive operations over Atoms *)
End

Datatype:
  cexp = Var name                                    (* variable                 *)
       | Prim cop (cexp list)                        (* primitive operations     *)
       | App cexp (cexp list)                        (* function application     *)
       | Lam (name list) cexp                        (* lambda                   *)
       | Let (name option) cexp cexp                 (* let                      *)
       | Letrec ((name # cexp) list) cexp            (* mutually recursive exps  *)
       | Case name ((name # (name list) # cexp) list)    (* pattern match        *)
                    (((name # num) list # cexp) option)  (* optional fallthrough *)
       | Delay cexp                   (* delay a computation as a thunk          *)
       | Box cexp                     (* eagerly compute, but wrap as a thunk    *)
       | Force cexp                   (* force a thunk                           *)
End

val cexp_size_def = fetch "-" "cexp_size_def";

Theorem cexp_size_lemma:
  (∀xs a. MEM a xs ⇒ cexp_size a < cexp8_size xs) ∧
  (∀xs p e. MEM (p,e) xs ⇒ cexp_size e < cexp6_size xs) ∧
  (∀xs a1 a2 a. MEM (a1,a2,a) xs ⇒ cexp_size a < cexp2_size xs)
Proof
  rpt conj_tac
  \\ Induct \\ rw [] \\ fs [fetch "-" "cexp_size_def"] \\ res_tac \\ fs []
QED


val _ = export_theory();
