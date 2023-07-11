(*
   This file defines expressions for thunkLang as the compiler sees them.
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory mlstringTheory pure_configTheory
     pred_setTheory;

val _ = new_theory "thunk_cexp";

Type name[local] = “:mlstring”

Datatype:
  cop = Cons name          (* datatype constructor            *)
      | AtomOp atom_op     (* primitive operations over Atoms *)
End

Datatype:
  cexp = Var name                                    (* variable                 *)
       | Prim cop (cexp list)                        (* primitive operations     *)
       | Monad mop (cexp list)                       (* monadic operations       *)
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

Definition cns_arities_def:
  cns_arities (Var v :cexp) = {} ∧
  cns_arities (Prim op es) = (
    (case op of
     | Cons cn => {{explode cn, LENGTH es}}
     | _ => {}) ∪
    BIGUNION (set (MAP cns_arities es))) ∧
  cns_arities (Monad mop es) = (BIGUNION (set (MAP cns_arities es))) ∧
  cns_arities (App e1 es) = cns_arities e1 ∪ BIGUNION (set (MAP cns_arities es)) ∧
  cns_arities (Lam vs e) = cns_arities e ∧
  cns_arities (Letrec funs e) =
    BIGUNION (set (MAP (λ(v,e). cns_arities e) funs)) ∪ cns_arities e ∧
  cns_arities (Let x e1 e2) = cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (Case v css d) = (
    let css_cn_ars = set (MAP (λ(cn,vs,e). explode cn, LENGTH vs) css) in
    (case d of
      | NONE => {css_cn_ars}
      | SOME (a,e) =>
        (set (MAP (λ(cn,ar). explode cn, ar) a) ∪ css_cn_ars) INSERT cns_arities e) ∪
    BIGUNION (set (MAP (λ(cn,vs,e). cns_arities e) css))) ∧
  cns_arities (Box e) = cns_arities e ∧
  cns_arities (Delay e) = cns_arities e ∧
  cns_arities (Force e) = cns_arities e
Termination
  WF_REL_TAC `measure cexp_size`
End

val _ = export_theory();
