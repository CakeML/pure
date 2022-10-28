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

val _ = export_theory();
