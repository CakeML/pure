(*
  Letrec specialization for cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open listTheory pairTheory topological_sortTheory;
open pure_cexpTheory pure_varsTheory balanced_mapTheory;

val _ = new_theory "pure_letrec_spec_cexp";

(*******************)

(*
  For every elemen in xs, if y is a variable reference to the corresponding
  element from xs, then return (SOME x). Otherwise NONE.

  Output list is the same as the length of xs.
*)
Definition min_call_args_def:
  min_call_args [] ys = [] ∧
  min_call_args xs [] = MAP (λ_. NONE) xs ∧
  min_call_args (NONE::xs) (y::ys) = (
    NONE::(min_call_args xs ys)
  ) ∧
  min_call_args ((SOME x)::xs) ((Var a v)::ys) = (
    if x = v then (SOME x)::(min_call_args xs ys)
    else NONE::(min_call_args xs ys)
  ) ∧
  min_call_args ((SOME x)::xs) (y::ys) = (
    NONE::(min_call_args xs ys)
  )
End

(*
  For a recursive function f with arguments vs. Compute the list of mlstring
  option. Where (SOME v) means that the element on that position is always
  called as a reference to itself, NONE otherwise.
*)
Definition const_call_args_def:
  const_call_args f vs (App (a: 'a) e es) = (
    case e of
    | (Var a v) => (
        if v = f then (
          let vs1 = min_call_args vs es
          in const_call_args_list f vs1 es
        )
        else
          const_call_args_list f vs es
    )
    | _ => const_call_args_list f vs (e::es)
  ) ∧
  const_call_args f vs (Var a v) = (
    if v = f then []
    else vs
  ) ∧
  const_call_args f vs (Let a v e1 e2) = (
    let vs1 = const_call_args f vs e1
    in const_call_args f vs1 e2
  ) ∧
  const_call_args f vs (Lam a vss e1) = (
    const_call_args f vs e1
  ) ∧
  const_call_args f vs (Prim a p es) = (
    const_call_args_list f vs es
  ) ∧
  const_call_args f vs (Letrec a ves e1) = (
    let vs1 = const_call_args_list f vs (MAP SND ves)
    in const_call_args f vs1 e1
  ) ∧
  const_call_args f vs (Case a e1 v bs d) = (
    let vs1 = const_call_args f vs e1
    in case d of
    | NONE => const_call_args_list f vs1 (MAP (λ(v, vs, e). e) bs)
    | SOME (_, d) => (
      let vs2 = const_call_args f vs1 d
      in const_call_args_list f vs2 (MAP (λ(v, vs, e). e) bs)
    )
  ) ∧
  const_call_args f vs (NestedCase a e v p e' bs) = vs ∧
  const_call_args_list f vs [] = vs ∧
  const_call_args_list f vs (e::es) = (
    let vs1 = const_call_args f vs e
    in const_call_args_list f vs1 es
  )
Termination
  cheat
End

Definition can_spec_cond_def:
  can_spec_cond const_args =
    EXISTS (λx. x ≠ NONE) const_args
End

Definition spec_map_def:
  spec_map p args =
    FOLDL2 (λacc x y.
      case x of
      | NONE => acc
      | SOME x =>
        insert acc x y
    ) empty p args
End

(*
  Simple substitution of element in a map
*)
Definition subst_map_def:
  subst_map m (Var a v) = (
    case lookup m v of
    | NONE => Var a v
    | SOME e => e
  ) ∧
  subst_map m (App a e es) = (
    let e1 = subst_map m e
    in let es1 = MAP (subst_map m) es
    in (App a e1 es1)
  ) ∧
  subst_map m (Let a v e1 e2) = (
    let e11 = subst_map m e1
    in let e21 = subst_map m e2
    in (Let a v e11 e21)
  ) ∧
  subst_map m (Lam a vs e) = (
    let e1 = subst_map m e
    in (Lam a vs e1)
  ) ∧
  subst_map m (Prim a p es) = (
    let es1 = MAP (subst_map m) es
    in (Prim a p es1)
  ) ∧
  subst_map m (Letrec a ves e) = (
    let ves1 = MAP (λ(v, e). (v, subst_map m e)) ves
    in let e1 = subst_map m e
    in (Letrec a ves1 e1)
  ) ∧
  subst_map m (Case a e v bs d) = (
    let e1 = subst_map m e
    in let bs1 = MAP (λ(v, vs, e). (v, vs, subst_map m e)) bs
    in let d1 = case d of
      | NONE => NONE
      | SOME (v, e) => SOME (v, subst_map m e)
    in (Case a e1 v bs1 d1)
  ) ∧
  subst_map m (NestedCase a e v p e' bs) =
    (NestedCase a e v p e' bs)
Termination
  cheat
End

Definition take_non_const_def:
  take_non_const [] args = args ∧
  take_non_const (NONE::xs) (arg::args) = arg :: (take_non_const xs args) ∧
  take_non_const ((SOME x)::xs) (arg::args) = take_non_const xs args
End

(*
For every reference of f applied to some arguments, remove the constant arguments
i.e. the ones that correspond to SOMEs in vs
*)
Definition remove_const_args_def:
  remove_const_args f vs (App a e es) = (
    let e1 = remove_const_args f vs e
    in let es1 = MAP (remove_const_args f vs) es
    in (case e1 of
      | (Var a v) => (
        if v = f then
          App a e1 (take_non_const vs es1)
        else
          App a e es1
      )
      | _ => App a e1 es1
    )
  ) ∧
  remove_const_args f vs (Var a v) = (Var a v) ∧
  remove_const_args f vs (Let a v e1 e2) = (
    let e11 = remove_const_args f vs e1
    in let e21 = remove_const_args f vs e2
    in (Let a v e11 e21)
  ) ∧
  remove_const_args f vs (Lam a vss e1) = (
    let e11 = remove_const_args f vs e1
    in (Lam a vss e11)
  ) ∧
  remove_const_args f vs (Prim a p es) = (
    let es1 = MAP (remove_const_args f vs) es
    in (Prim a p es1)
  ) ∧
  remove_const_args f vs (Letrec a ves e) = (
    let ves1 = MAP (λ(v, e). (v, remove_const_args f vs e)) ves
    in let e1 = remove_const_args f vs e
    in (Letrec a ves1 e1)
  ) ∧
  remove_const_args f vs (Case a e v bs d) = (
    let e1 = remove_const_args f vs e
    in let bs1 = MAP (λ(v, vss, e). (v, vss, remove_const_args f vs e)) bs
    in let d1 = case d of
      | NONE => NONE
      | SOME (v, e) => SOME (v, remove_const_args f vs e)
    in (Case a e1 v bs1 d1)
  ) ∧
  remove_const_args f vs (NestedCase a e v p e' bs) =
    (NestedCase a e v p e' bs)
Termination
  cheat
End

(*
  Can the given letrec be specialized for any arguments?
  - f : function name
  - e : definition of function f
*)
Definition can_spec_def:
  can_spec f (Lam a vs e) = (
    let p = const_call_args f (MAP SOME vs) e
    in can_spec_cond p
  ) ∧
  can_spec f e = F
End

(*
  Specialize a letrec expression for a given:
  - f : function name
  - args : list of arguments it is called with
  - e : definition of function f
*)
Definition spec_def:
  spec f args (Lam a vs e) = (
    let p = const_call_args f (MAP SOME vs) e
    in let m = spec_map p args
    in if m = empty then
      NONE
    else
      SOME (Lam a vs (subst_map m e))
  ) ∧
  spec f args e = NONE
End

Definition inv_const_args_def:
  inv_const_args (vs: 'a list) p =
    MAP2 (λx y. case y of
      | NONE => SOME x
      | SOME y => NONE
    ) vs p
End

Definition get_SOMEs_def:
  get_SOMEs [] = [] ∧
  get_SOMEs (NONE :: xs) = get_SOMEs xs ∧
  get_SOMEs ((SOME x) :: xs) = x :: (get_SOMEs xs)
End

(*
Problems with this implementation:
- all arguments are left in the outer lambda

Currently works like so:

map f [] = []
map f (x::xs) = (f x)::(map f xs)

==>

\f xs.
  let map1 [] = []
      map1 (x::xs) = (f x)::(map1 xs)
  in map1 xs

*)
Definition specialise_def:
  specialise v (Lam a vs e) = (
    let p = const_call_args v (MAP SOME vs) e
    in let inner_vs = get_SOMEs (inv_const_args vs p)
    in let inner_lam = Lam a inner_vs (remove_const_args v p e)
    in let const_vs = get_SOMEs p
    in let inner_refs = MAP (λv. Var a v) inner_vs
    in let ltrec = Letrec a [(v, inner_lam)] (App a (Var a v) inner_refs)
    in SOME (Lam a vs ltrec)
  ) ∧
  specialise v e = NONE
End

(*******************)

val _ = export_theory();
