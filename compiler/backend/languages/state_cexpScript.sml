(*
  Compiler expressions for stateLang
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory arithmeticTheory mlstringTheory;

val _ = new_theory "state_cexp";

val _ = set_grammar_ancestry ["pure_exp","mlstring"];

val _ = numLib.prefer_num();

Type vname = “:mlstring”

Datatype:
  csop = (* Primitive operations *)
       | AppOp              (* function application                     *)
       | Cons mlstring      (* datatype constructor                     *)
       | AtomOp atom_op     (* primitive parametric operator over Atoms *)
       | Alloc              (* allocate an array                        *)
       | Ref                (* allocates an array in a different way    *)
       | Length             (* query the length of an array             *)
       | Sub                (* de-reference a value in an array         *)
       | UnsafeSub          (* de-reference but without a bounds check  *)
       | Update             (* update a value in an array               *)
       | UnsafeUpdate       (* update without a bounds check            *)
       | FFI mlstring       (* make an FFI call                         *)
End

Datatype:
  cexp = (* stateLang expressions *)
       | Var vname                                 (* variable                *)
       | App csop (cexp list)                      (* application - prim/fun  *)
       | Lam (vname option) cexp                   (* lambda                  *)
       | Letrec ((vname # vname # cexp) list) cexp (* mutually recursive funs *)
       | Let (vname option) cexp cexp              (* non-recursive let       *)
       | If cexp cexp cexp                         (* if-then-else            *)
       | Case cexp vname ((vname # vname list # cexp) list)        (* case of *)
       | Raise cexp                                (* raise an exception      *)
       | Handle cexp vname cexp                    (* handle an exception     *)
       | HandleApp cexp cexp                       (* handle that takes fun   *)
End

Overload True  = “App (Cons (strlit "True"))  []”;
Overload False = “App (Cons (strlit "False")) []”;

Overload "app" = “λe1 e2. App AppOp [e1;(e2:cexp)]”;
Overload "Unit" = “App (Cons (strlit "")) [] :cexp”;

Overload IntLit = “λi. App (AtomOp (Lit (Int i))) []”
Overload Eq = “λx y. App (AtomOp Eq) [x; y]”

val _ = export_theory();
