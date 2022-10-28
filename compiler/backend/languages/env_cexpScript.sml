(*
  Compiler expressions for stateLang
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory arithmeticTheory mlstringTheory;

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

val _ = export_theory();
