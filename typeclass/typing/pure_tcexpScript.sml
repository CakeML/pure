(*
   This file defines expressions for pure_lang as the type system sees them.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open arithmeticTheory listTheory rich_listTheory alistTheory stringTheory
     optionTheory pairTheory pred_setTheory mlmapTheory;
open pure_cexpTheory pure_cexp_lemmasTheory pure_expTheory pure_evalTheory
     pure_exp_lemmasTheory pure_exp_relTheory pure_congruenceTheory;
open pure_typesTheory pure_kindCheckTheory;
val _ = new_theory "pure_tcexp";

Datatype:
  tcexp = Var (PredType option) cvname                     (* variable                 *)
        | Prim (PredType option) cop (tcexp list)          (* primitive operations     *)
        | App (PredType option) tcexp (tcexp list)         (* function application     *)
        | Lam ((PredType option # cvname) list)
           (PredType option) tcexp                         (* lambda                   *)
        | Let (PredType_scheme option) cvname tcexp
            (PredType option) tcexp                        (* let                      *)
        | Letrec (((PredType_scheme option) # cvname # tcexp) list)
            (PredType option) tcexp                        (* mutually recursive exps  *)
        | NestedCase (PredType option) tcexp cvname cepat tcexp
            ((cepat # tcexp) list)                         (* case of                  *)
End

(* top level declarations *)
Datatype:
  tcdecl = FuncDecl PredType tcexp (* enforce top level declarations *)
End

Type minImplAST = ``:(mlstring list) list``; (* DNF of function names*)

Datatype:
  classinfo =
    <| super : mlstring list
     ; kind : Kind option
     ; methodsig : (cvname, PredType) map
     ; minImp : minImplAST
     ; defaults : (cvname, tcexp) map |>
End

Inductive super_reachable:
  (!src dst sup.
    cdb src = SOME c /\ MEM sup c.super /\
    super_reachable cdb sup dst ==>
      super_reachable cdb src dst) /\
  (!src sup.
    cdb src = SOME c /\ MEM sup c.super ==>
      super_reachable cdb src sup)
End

Definition super_ok_def:
  super_ok cdb =
    !x c. FLOOKUP cdb x = SOME c ==>
      ~(super_reachable (FLOOKUP cdb) x x)
End

Datatype:
  instinfo =
    <| cstr : (mlstring # 'b) list (* class and type variable*)
     ; class : mlstring
     ; insttype : type
     ; impl : (cvname,tcexp) map |> (* function name and its expression *)
End

Definition instinfo_constraint_ok_def:
  instinfo_constraint_ok inst =
    !x. MEM x inst.cstr ==>
      (* everything in the left must be in used in the right *)
      SND x IN collect_type_vars inst.insttype /\
      (* everything in the left must be smaller than the type in the right *)
      (* since we only allow a single type variable on the right now,
      * so the following check should suffice *)
      TypeVar (SND x) <> inst.insttype
End

Definition instinfo_impl_ok:
  instinfo_impl_ok cdb inst <=>
  ?c. FLOOKUP cdb inst.class = SOME c /\
    (!meth ty. lookup c.methodsig meth = SOME ty ==>
      ?exp.
       (lookup inst.impl meth = SOME exp
       (* /\ TODO: check if the tcexp has the correct instantiated type *)) \/
       lookup c.defaults meth = SOME exp) /\
    (?minimpl. !m.
      MEM minimpl c.minImp /\ MEM m minimpl ==>
        ?exp. lookup inst.impl m = SOME exp)
End

val _ = export_theory();
