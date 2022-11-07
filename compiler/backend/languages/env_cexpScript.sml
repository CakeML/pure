(*
  Compiler expressions for stateLang
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory arithmeticTheory mlstringTheory
     pred_setTheory;

val _ = new_theory "env_cexp";

val _ = set_grammar_ancestry ["pure_exp","mlstring"];

val _ = numLib.prefer_num();

Type vname = “:mlstring”

Datatype:
  cop = Cons mlstring
      | AtomOp atom_op
End

Datatype:
  cexp = Var vname
       | Prim cop (cexp list)
       | App cexp cexp
       | Lam vname cexp
       | Letrec ((vname # cexp) list) cexp
       | Let (vname option) cexp cexp
       | If cexp cexp cexp
       | Delay cexp
       | Box cexp
       | Force cexp
       | Case vname ((vname # (vname list) # cexp) list)
                    (((vname # num) list # cexp) option)
       (* monads *)
       | Ret cexp
       | Raise cexp
       | Bind cexp cexp
       | Handle cexp cexp
       | Act cexp
       | Length cexp
       | Alloc cexp cexp
       | Deref cexp cexp
       | Update cexp cexp cexp
End

Definition cns_arities_def:
  cns_arities (Var v :cexp) = {} ∧
  cns_arities (Prim op es) = (
    (case op of
     | Cons cn => if explode cn ∈ monad_cns then {} else {{explode cn, LENGTH es}}
     | _ => {}) ∪
    BIGUNION (set (MAP cns_arities es))) ∧
  cns_arities (App e1 e2) = cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (Lam x e) = cns_arities e ∧
  cns_arities (Letrec funs e) =
    BIGUNION (set (MAP (λ(v,e). cns_arities e) funs)) ∪ cns_arities e ∧
  cns_arities (Let x e1 e2) = cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (If e e1 e2) = cns_arities e ∪ cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (Case v css d) = (
    let css_cn_ars = set (MAP (λ(cn,vs,e). explode cn, LENGTH vs) css) in
    (case d of
      | NONE => {css_cn_ars}
      | SOME (a,e) =>
        (set (MAP (λ(cn,ar). explode cn, ar) a) ∪ css_cn_ars) INSERT cns_arities e) ∪
    BIGUNION (set (MAP (λ(cn,vs,e). cns_arities e) css))) ∧
  cns_arities (Box e) = cns_arities e ∧
  cns_arities (Delay e) = cns_arities e ∧
  cns_arities (Force e) = cns_arities e ∧
  cns_arities (Ret e) = cns_arities e ∧
  cns_arities (Raise e) = cns_arities e ∧
  cns_arities (Act e) = cns_arities e ∧
  cns_arities (Length e) = cns_arities e ∧
  cns_arities (Bind e1 e2) = cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (Handle e1 e2) = cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (Deref e1 e2) = cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (Alloc e1 e2) = cns_arities e1 ∪ cns_arities e2 ∧
  cns_arities (Update e1 e2 e3) = cns_arities e1 ∪ cns_arities e2 ∪ cns_arities e3
Termination
  WF_REL_TAC `measure cexp_size`
End

val _ = export_theory();
