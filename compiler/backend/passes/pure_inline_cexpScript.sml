(*
  Inlining optimization for cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open listTheory pairTheory topological_sortTheory;
open pure_cexpTheory pure_varsTheory balanced_mapTheory;

val _ = new_theory "pure_inline_cexp";

(*******************)

Datatype:
  cexp_rhs = cExp ('a cexp) | cRec ('a cexp)
End

(* heuristic for deciding when to inline *)
Type heuristic = “:'a cexp -> bool”

Triviality cexp_size_lemma:
  ∀vbs.
    list_size (cexp_size (K 0)) (MAP SND vbs) ≤
    list_size (pair_size mlstring_size (cexp_size (K 0))) vbs
Proof
  Induct  \\ fs [] \\ rw [] \\ res_tac
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
  \\ PairCases_on `h`
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
QED

Definition heuristic_insert_def:
  heuristic_insert m h v e =
    if h e then
      insert m v (cExp e)
    else
      m
End

Definition heuristic_insert_Rec_def:
  heuristic_insert_Rec m h fs =
    case fs of
      | [(v, e)] =>
        if h e then
          insert m v (cRec e)
        else
          m
      | _ => m
End

Definition is_Lam_def:
  is_Lam (Lam a vs e) = T ∧
  is_Lam _ = F
End

Definition inline_def:
  inline (m: ('a cexp_rhs) var_map) (ns: var_set) (h: 'a heuristic) (Var (a: 'a) v) =
    (case lookup m v of
      NONE => (Var a v, ns)
    | SOME (cExp e) =>
      if is_Lam e
      then (Var a v, ns)
      else (e, ns) (* Might want to freshen the names and recurse *)
    | SOME (cRec e) => (Var a v, ns)) ∧
  inline m ns h (Prim a op es) =
    (let (es2, ns2) = inline_list m ns h es
     in (Prim a op es2, ns2)) ∧
  inline m ns h (App a e es) =
    (let (e1, ns1) = inline m ns h e in
     let (es2, ns2) = inline_list m ns1 h es
     in (App a e1 es2, ns2)) ∧
  inline m ns h (Lam a vs e) =
    (let (e1, ns1) = inline m ns h e
    in (Lam a vs e1, ns1)) ∧
  inline m ns h (Let a v e1 e2) =
    (let m1 = heuristic_insert m h v e1
     in let (e3, ns3) = inline m ns h e1
     in let (e4, ns4) = inline m1 ns3 h e2
     in (Let a v e3 e4, ns4)) ∧
  inline m ns h (Letrec a vbs e) =
    (let m1 = heuristic_insert_Rec m h vbs
     in let (vbs1, ns1) = inline_list m ns h (MAP SND vbs)
     in let (e2, ns2) = inline m1 ns1 h e
     in (Letrec a (MAP2 (λ(v,_) x. (v, x)) vbs vbs1) e2, ns2)) ∧
  inline m ns h (Case a e v bs f) =
    (let (e1, ns1) = inline m ns h e
     in let (bs2, ns2) = inline_list m ns1 h (MAP (λ(v, vs, e). e) bs)
     in let (f3, ns3) = case f of
          NONE => (NONE, ns2)
        | SOME (vs, e) =>
          let (e4, ns4) = inline m ns2 h e
          in (SOME (vs, e4), ns4)
     in (Case a e1 v (MAP2 (λ(v, vs, _) e. (v, vs, e)) bs bs2) f3, ns3)) ∧
  inline m ns h (NestedCase a e v p e' bs) =
    (NestedCase a e v p e' bs, ns) ∧
  inline_list m ns h [] = ([], ns) ∧
  inline_list m ns h (e::es) =
    (let (e1, ns1) = inline m ns h e in
     let (es2, ns2) = inline_list m ns1 h es
     in (e1::es2, ns2))
Termination
  WF_REL_TAC `measure $ λx. case x of
    | INL (m, ns, h, e) => cexp_size (K 0) e
    | INR (m, ns, h, es) => list_size (cexp_size (K 0)) es`
  \\ fs [cexp_size_eq] \\ rw [] \\ gvs []
  \\ qspec_then `vbs` assume_tac cexp_size_lemma \\ fs []
  \\ cheat
End

Definition inline_all_def:
  inline_all = inline pure_vars$empty empty
End

Triviality cexp_size_lemma2:
  ∀xs e.
    MEM e xs ⇒
    cexp_size (K 0) e ≤ list_size (cexp_size (K 0)) xs
Proof
  Induct  \\ fs [] \\ rw [] \\ res_tac \\ fs [list_size_def]
QED

Definition tree_size_heuristic_rec_def:
  tree_size_heuristic_rec n (Var a v) = (n - 1) ∧
  tree_size_heuristic_rec n (Prim a op es) =
    FOLDL (λa e. if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) es ∧
  tree_size_heuristic_rec n (App a e es) =
    FOLDL (λa e. if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) (e::es) ∧
  tree_size_heuristic_rec n (Lam a vs e) =
    tree_size_heuristic_rec (n - 1) e ∧
  tree_size_heuristic_rec n (Let a v e1 e2) =
    (let n1 = tree_size_heuristic_rec (n - 1) e1
    in if n1 < 0 then n1 else tree_size_heuristic_rec n1 e2) ∧
  tree_size_heuristic_rec n (Letrec a vbs e) =
    (let n1 = FOLDL (λa (v, e). if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) vbs
    in if n1 < 0 then n1 else tree_size_heuristic_rec n1 e) ∧
  tree_size_heuristic_rec n (Case a e v bs f) =
    (let n1 = FOLDL (λa (v, vs, e). if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) bs
    in if n1 < 0 then n1 else
      case f of
        NONE => n1
      | SOME (vs, e) => tree_size_heuristic_rec n1 e) ∧
  tree_size_heuristic_rec n (NestedCase a e v p e' bs) =
    (let n1 = FOLDL (λa (p, e). if a < 0 then a else tree_size_heuristic_rec a e) (n - 1) bs
    in if n1 < 0 then n1 else tree_size_heuristic_rec n1 e')
Termination
  WF_REL_TAC ‘measure $ λx. case x of
    | (n, e) => cexp_size (K 0) e’
  \\ fs [cexp_size_eq] \\ rw [] \\ gvs []
  \\ imp_res_tac cexp_size_lemma2 \\ fs []
End

Definition tree_size_def:
  tree_size (Var a v) = 1 ∧
  tree_size (Prim a op es) = 1 + SUM (MAP tree_size es) ∧
  tree_size (App a e es) = 1 + SUM (MAP tree_size (e::es)) ∧
  tree_size (Lam a vs e) = 1 + tree_size e ∧
  tree_size (Let a v e1 e2) = 1 + tree_size e1 + tree_size e2 ∧
  tree_size (Letrec a vbs e) = 1 + tree_size e + SUM (MAP (λ(v, e). tree_size e) vbs) ∧
  tree_size (Case a e v bs f) =
    1 + tree_size e + SUM (MAP (λ(v, vs, e). tree_size e) bs) +
    (case f of
      None => 0
    | Some (vs, e) => tree_size e) ∧
  tree_size (NestedCase a e v p e' bs) =
    1 + tree_size e + tree_size e' + SUM (MAP (λ(p, e). tree_size e) bs)
Termination
  WF_REL_TAC ‘measure $ cexp_size (K 0)’
  \\ fs [cexp_size_eq] \\ rw [] \\ gvs []
  \\ imp_res_tac cexp_size_lemma2 \\ fs []
End

(* rewrite *)
Definition tree_size_heuristic_def:
  tree_size_heuristic n =
    (λe. tree_size_heuristic_rec n e ≥ 0)
End

(*******************)

val _ = export_theory();
