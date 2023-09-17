(*
  Letrec specialization for cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open listTheory pairTheory topological_sortTheory;
open pure_cexpTheory pure_varsTheory balanced_mapTheory;

val _ = new_theory "pure_letrec_spec_cexp";

Definition eq_Var_def:
  eq_Var f (Var a v) = (f = v:mlstring) ∧
  eq_Var f _ = F
End

(*
  For every elemen in xs, if y is a variable reference to the corresponding
  element from xs, then return (SOME x). Otherwise NONE.

  Output list is the same as the length of xs.
*)
Definition min_call_args_def:
  min_call_args [] ys = [] ∧
  min_call_args xs [] = [] ∧
  min_call_args (NONE::xs) (y::ys) = NONE::(min_call_args xs ys) ∧
  min_call_args ((SOME x)::xs) (y::ys) =
    if eq_Var x y then (SOME x)::(min_call_args xs ys)
    else NONE::(min_call_args xs ys)
End

Triviality const_call_args_lemma:
  ∀bs.
    list_size (cexp_size (K 1)) (MAP (λ(v,vs,e). e) bs)
    ≤
    list_size
      (pair_size mlstring_size
        (pair_size (list_size mlstring_size) (cexp_size (K 1)))) bs
Proof
  Induct \\ fs []
  \\ fs [list_size_def]
  \\ PairCases \\ fs [basicSizeTheory.pair_size_def]
QED

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
  WF_REL_TAC ‘measure (λx. case x of
    | INL (f,vs,c) => cexp_size (K 1) c
    | INR (f,vs,c) => list_size (cexp_size (K 1)) c)’
  \\ rw [cexp_size_eq] \\ fs []
  >- (Induct_on ‘ves’ \\ fs [list_size_def]
      \\ PairCases \\ fs [basicSizeTheory.pair_size_def])
  \\ irule arithmeticTheory.LESS_EQ_LESS_TRANS
  \\ irule_at Any const_call_args_lemma \\ fs []
End

Definition drop_common_prefix_def:
  drop_common_prefix [] ys = ([],ys) ∧
  drop_common_prefix xs [] = (xs,[]) ∧
  drop_common_prefix (x::xs) (y::ys) =
    if x = y then drop_common_prefix xs ys else (x::xs,y::ys)
End

Definition drop_common_suffix_def:
  drop_common_suffix xs ys =
    let (xs1,ys1) = drop_common_prefix (REVERSE xs) (REVERSE ys) in
      (REVERSE xs1, REVERSE ys1)
End

Definition all_somes_def:
  all_somes [] = [] ∧
  all_somes (NONE :: xs) = all_somes xs ∧
  all_somes (SOME a :: xs) = (a:mlstring) :: all_somes xs
End

Definition delete_with_def:
  delete_with [] es = es ∧
  delete_with (F::bs) [] = [] ∧
  delete_with (F::bs) (x::xs) = delete_with bs xs ∧
  delete_with (T::bs) [] = [] ∧
  delete_with (T::bs) (x::xs) = x::delete_with bs xs
End

Definition check_arg_def:
  check_arg v [] es = T ∧
  check_arg v (F::bs) [] = F ∧
  check_arg v (F::bs) (x::xs) = (eq_Var v x ∧ check_arg v bs xs) ∧
  check_arg v (T::bs) [] = F ∧
  check_arg v (T::bs) (x::xs) = check_arg v bs xs
End

Definition spec_one_def:
  spec_one f v vs (App (a: 'a) e es) =
    (if eq_Var f e then
       case spec_one_list f v vs es of
       | NONE => NONE
       | SOME es =>
         if check_arg v vs es then
           SOME (App a e (delete_with vs es))
         else NONE
     else
       case (spec_one f v vs e, spec_one_list f v vs es) of
       | (SOME e, SOME es) => SOME (App a e es)
       | _ => NONE) ∧
  spec_one f v vs (Var a x) =
    (if x = f then NONE else SOME (Var a x)) ∧
  spec_one f v vs (Let a w e1 e2) =
    (case (spec_one f v vs e1, spec_one f v vs e2) of
     | (SOME e1, SOME e2) => SOME (Let a w e1 e2)
     | _ => NONE) ∧
  spec_one f v vs (Lam a vss e) =
    (case spec_one f v vs e of
     | SOME e => SOME (Lam a vss e)
     | _ => NONE) ∧
  spec_one f v vs (Prim a p es) =
    (case spec_one_list f v vs es of
     | SOME es => SOME (Prim a p es)
     | _ => NONE) ∧
  spec_one f v vs (Letrec a ves e1) =
    (case (spec_one_letrec f v vs ves, spec_one f v vs e1) of
     | (SOME ves, SOME e1) => SOME (Letrec a ves e1)
     | _ => NONE) ∧
  spec_one f v vs (Case a e w bs d) =
    (case (spec_one f v vs e, spec_one_case f v vs bs, spec_one_opt f v vs d) of
     | (SOME e, SOME bs, SOME d) => SOME (Case a e w bs d)
     | _ => NONE) ∧
  spec_one f v vs (NestedCase a e w p e' bs) = NONE ∧
  spec_one_list f v vs [] = SOME [] ∧
  spec_one_list f v vs (e::es) =
    (case (spec_one f v vs e, spec_one_list f v vs es) of
     | (SOME e, SOME es) => SOME (e::es)
     | _ => NONE) ∧
  spec_one_letrec f v vs [] = SOME [] ∧
  spec_one_letrec f v vs ((b,e)::es) =
    (case (spec_one f v vs e, spec_one_letrec f v vs es) of
     | (SOME e, SOME es) => SOME ((b,e)::es)
     | _ => NONE) ∧
  spec_one_case f v vs [] = SOME [] ∧
  spec_one_case f v vs ((b,ps,e)::es) =
    (case (spec_one f v vs e, spec_one_case f v vs es) of
     | (SOME e, SOME es) => SOME ((b,ps,e)::es)
     | _ => NONE) ∧
  spec_one_opt f v vs NONE = SOME NONE ∧
  spec_one_opt f v vs (SOME (d,e)) =
    (case spec_one f v vs e of
     | SOME e => SOME (SOME (d,e))
     | _ => NONE)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
    | INL (f,v,vs,c) => cexp_size (K 0) c
    | INR (INL (f,v,vs,c)) => list_size (cexp_size (K 0)) c
    | INR (INR (INL (f,v,vs,c))) =>
        list_size (pair_size mlstring_size (cexp_size (K 0))) c
    | INR (INR (INR (INL (f,v,vs,c)))) => list_size (cexp_size (K 0)) (MAP (SND o SND) c)
    | INR (INR (INR (INR (f,v,vs,NONE)))) => 0
    | INR (INR (INR (INR (f,v,vs,SOME (d,e))))) => 1 + cexp_size (K 0) e’
  \\ fs [cexp_size_eq] \\ rw [list_size_def]
  \\ rpt (CASE_TAC \\ fs [])
  \\ fs [basicSizeTheory.pair_size_def,basicSizeTheory.option_size_def]
  \\ Induct_on ‘bs’ \\ fs [list_size_def] \\ PairCases
  \\ fs [basicSizeTheory.pair_size_def,basicSizeTheory.option_size_def]
End

Definition specialise_each_def:
  specialise_each [] vs f e = (vs,e) ∧
  specialise_each (p::ps) vs f e =
    if LENGTH vs < 2 then (vs,e) else
      let bs = MAP (λv. p ≠ (v:mlstring)) vs in
        if NULL (FILTER I bs) then specialise_each ps vs f e else
          case spec_one f p bs e of
          | NONE => specialise_each ps vs f e
          | SOME e1 => specialise_each ps (delete_with bs vs) f e1
End

Definition split_at_def:
  split_at n xs =
    if n = 0:num then ([],xs) else
      case xs of
      | [] => ([],[])
      | (x::xs) => let (ys,zs) = split_at (n-1) xs in
                     (x::ys,zs)
End

Definition specialise_def:
  specialise f (Lam a vs e) =
    (let args = const_call_args f (MAP SOME vs) e in
     let p = all_somes args in
      if NULL p then NONE else
        let (ws1,ws2) = split_at (LENGTH args) vs in
        let (params,e1) = specialise_each p ws1 f (SmartLam a ws2 e) in
        let (outer_vs,inner_vs) = drop_common_suffix ws1 params in
          if NULL outer_vs then NONE else
            SOME (SmartLam a outer_vs $
                    Letrec a [(f,SmartLam a params e1)] $
                      SmartApp a (Var a f) (MAP (Var a) inner_vs))) ∧
  specialise f e = NONE
End

val _ = export_theory();
