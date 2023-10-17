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
  type = (* TypeVar num VarTypeCons num [] *)
       | PrimTy prim_ty
       | Exception
       | TypeCons (num option) (type list) (* NONE for Tuple *)
       | VarTypeCons num (type list) (* consider type list vs type *)
         (* for sth like fmap::(a -> b) -> f a -> f a *)
         (* need to kind-check *)
       (* | Tuple (type list) *)
       | Function type type
       | Array type
       | M type
End

Type class = ``:string``; (* key for map from classname to class *)
(* or string? *)

Datatype:
  PredType = Pred ((class # type) list) type
    (* e.g. Monad m, Monad m2, Functor f => m1 (f a) -> m2 a *)
End
(* Translation
* h :: (Ord (f [b]), Functor f) => (a -> b) -> f [a] -> f [b] -> Bool
* h f x y = fmap (map f) x < y
* ~> h ordd fund f x y = ordd.(<) ((fund.fmap) (map f) x) y
* g :: (Ord b) => (a->b) -> [[a]] -> [[b]] -> [[b]]
* instance Ord a => Ord [a] where ...
* ~> list_ordd ordd = (..,..) 
* g f x y = if h f x y then y else fmap (fmap f) x
* g orbd f x y = if h (list_ordd (list_ordd orbd)) list_fund f x y then y
*   else list_fund.fmap (list_fund.fmap f) x
* only allow single-param type classes *)

Overload Unit = ``Tuple []``;
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
  (collect_type_vars (Function a b) =
    collect_type_vars a UNION collect_type_vars b) /\
  (collect_type_vars (Array t) = collect_type_vars t) /\
  (collect_type_vars (M t) = collect_type_vars t) /\
  (collect_type_vars _ = {})
Termination
  WF_REL_TAC `measure type_size`
End

(* f < m f a *)
(* m < m f a *)
(* m f < m f a *)
(* type constructor may not be fully applied *)
(*
Definition type_leq_cons_def:
  (type_leq_cons [] ts = T) /\
  (type_leq_cons (t::ts) [] = F) /\
  (type_leq_cons (t::ts) (t'::ts') = if t = t' then type_leq_cons ts ts' else F)
End

Definition type_leq_def:
   ((type_leq:(type -> type -> bool)) (VarTypeCons v' ts') (VarTypeCons v ts) = (if v' = v
      then (type_leq_cons ts' ts \/
        EXISTS (type_leq $ VarTypeCons v' ts') ts)
      else EXISTS (type_leq $ VarTypeCons v' ts') ts)) /\
   (type_leq t (VarTypeCons v ts) = EXISTS (type_leq t) ts) /\
   (type_leq t (TypeCons c' ts') (TypeCons c ts) = (if c' = c
      then (type_leq_cons ts' ts \/
        EXISTS (type_leq $ TypeCons c' ts') ts)
      else EXISTS (type_leq $ TypeCons c' ts') ts)) /\
   (type_leq t (TypeCons c ts) = EXISTS (type_leq t) ts) /\
   (type_leq (Tuple ts') (Tuple ts) = (type_leq_cons ts' ts \/
      EXISTS (type_leq $ Tuple ts') ts)) /\
   (type_leq t (Tuple ts) = EXISTS (type_leq t) ts) /\
   (type_leq t (Function a b)= (t = Function a b \/
      type_leq t a \/ type_leq t b)) /\
   (type_leq t (Array a)= (t = Array a \/
      type_leq t a)) /\
   (type_leq t (M a) = (t = M a \/
      type_leq t a)) /\
   (type_leq t a = (t = a))
End
Termination
  WF_REL_TAC `measure $ type_size o SND`
End

Definition type_lt_def:
  type_lt a b = (type_leq a b /\ a <> b)
End
*)
(* CakeML assumes the following initial namespace:
      Exceptions: 0 -> Bind, 1 -> Chr, 2 -> Div, 3 -> Subscript
      Types: 0 -> Bool, 1 -> List

   In Pure, we need only Subscript and List - Bool is built in and none of the
   others are used. Therefore, the Pure initial namespace should be:
      Exception: 0 -> Subscript
      Types: 0 -> List
*)
val _ = export_theory();
