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
  (* The first argument for each constructor is the type of the whole expression *)
  tcexp = Var (PredType option) cvname                            (* variable                 *)
          (* the first type is the type for the whole expression,
          *  and the second type is the type for the operator *)
        | Prim (PredType option) cop (tcexp list)                 (* primitive operations     *)
        | App (PredType option) tcexp (tcexp list)                (* function application     *)
          (* the types inside the list are the types assigned for
          * the corresponding variables *)
        | Lam (PredType option) ((PredType option # cvname) list)
            tcexp                                                 (* lambda                   *)
          (* the type scheme is the polymorphic type for
          *  the binding expression. Used for inferencing *)
        | Let (PredType option)
             (PredType_scheme option) cvname tcexp tcexp          (* let                      *)
        | Letrec (PredType option)
            (((PredType_scheme option) # cvname # tcexp) list)
            tcexp                                                 (* mutually recursive exps  *)
        | NestedCase (PredType option) tcexp cvname cepat tcexp
            ((cepat # tcexp) list)                                (* case of                  *)
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
     ; methodsig : cvname |-> PredType
     ; minImp : minImplAST
     ; defaults : cvname |-> tcexp |>
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
     ; impl : cvname |-> tcexp |> (* function name and its expression *)
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
    (!meth ty. FLOOKUP c.methodsig meth = SOME ty ==>
      ?exp.
       (FLOOKUP inst.impl meth = SOME exp
       (* /\ TODO: check if the tcexp has the correct instantiated type *)) \/
       FLOOKUP c.defaults meth = SOME exp) /\
    (?minimpl. !m.
      MEM minimpl c.minImp /\ MEM m minimpl ==>
        ?exp. FLOOKUP inst.impl m = SOME exp)
End

val _ = export_theory();
