open HolKernel Parse boolLib bossLib BasicProvers;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory
     listTheory alistTheory;
open mlstringTheory;
open pure_configTheory;

val _ = new_theory "pure_types";


(******************** Types ********************)

Datatype:
  prim_ty = Integer | String | Message | Bool
End

Datatype:
  comp_prim_ty = Function | Array | M | Tuple num
End

Datatype:
  type =
       | PrimTy prim_ty
       | Exception
       | TypeCons (num + comp_prim_ty) (type list)
        (* INL: user-defined types, INR: built-in types *)
       | VarTypeCons num (type list) (* consider type list vs type *)
        (* for sth like fmap::(a -> b) -> f a -> f a *)
End

Type class = ``:mlstring``; (* key for map from classname to class *)

Datatype:
  PredType = Pred ((class # type) list) type
    (* e.g. Monad m, Monad m2, Functor f => m1 (f a) -> m2 a *)
End

Overload Unit = ``TypeCons (INR $ Tuple 0) []``;
Overload TypeVar = ``\x. VarTypeCons x []``;
Type type_scheme[pp] = ``:num # type``;
Type PredType_scheme[pp] = ``:num # PredType``;

(*
  A type definition is an arity and a collection of constructor definitions.
  Each constructor definition is a name and a type scheme for its arguments
  (closed wrt the type definition arity).

  Like CakeML, use numbers to refer to types - known typedefs represented as
    : typedef list
  We could instead have:
    : (string # typedef) list     or     : string |-> typedef     etc.
  Unlike CakeML, we group constructors by their type (i.e. group siblings).

  E.g. the type definitions for Maybe and List might look like:
  [
    (1, [ ("Nothing", []) ; ("Just", [Var 0]) ]);
    (1, [ ("Nil", []) ; ("Cons", [Var 0; TypeCons 1 [Var 0]]) ])
  ]

  The exception definition is a list of constructors associated to (closed)
  argument types.

  Together, the exception definition and a collection of type definitions form
  our typing namespace.
*)

(* TODO make finite maps *)
Type typedef[pp] = ``:num # ((mlstring # type list) list)``;
Type typedefs[pp] = ``:typedef list``;
Type exndef[pp] = ``:(mlstring # type list) list``;

Definition collect_type_vars_def:
  (collect_type_vars (TypeCons c ts) =
    BIGUNION $ set (MAP collect_type_vars ts)) /\
  (collect_type_vars (VarTypeCons v ts) = {v} UNION
    (BIGUNION $ set $ MAP collect_type_vars ts)) /\
  (collect_type_vars _ = {})
Termination
  WF_REL_TAC `measure type_size`
End

val _ = export_theory();
