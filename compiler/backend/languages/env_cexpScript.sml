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
       | Case cexp vname ((vname # (vname list) # cexp) list)
       (* monads *)
       | Ret cexp
       | Bind cexp cexp
End

val _ = export_theory();