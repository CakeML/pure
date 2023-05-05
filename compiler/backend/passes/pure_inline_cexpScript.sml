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
  ∀xs v e.
    MEM (v,e) xs ⇒
    cexp_size (K 0) e ≤ list_size (pair_size mlstring_size (cexp_size (K 0))) xs
Proof
  Induct  \\ fs [] \\ rw [] \\ res_tac
  \\ fs [list_size_def,basicSizeTheory.pair_size_def]
QED

Definition inline_def:
  inline (m: ('a cexp_rhs) var_map) (h: 'a heuristic) (Var (a: 'a) v) =
    (case lookup m v of
      None => Var a v
    | Some (cExp e) => e (* Might want to freshen the names and recurse *)
    | Some (cRec e) => Var a v) ∧
  inline m h (Prim a op es) =
    Prim a op (MAP (inline m h) es) ∧
  inline m h (App a e es) =
    App a (inline m h e) (MAP (inline m h) es) ∧
  inline m h (Lam a vs e) =
    Lam a vs (inline m h e) ∧
  inline m h (Let a v e1 e2) =
    (if h e1 then
      inline (insert m v (cExp e1)) h e2
    else
      Let a v (inline m h e1) (inline m h e2)) ∧
  inline m h (Letrec a [(v, e)] e') =
    (if h e then
      inline (insert m v (cRec e)) h e'
    else
      Letrec a [(v, inline m h e)] (inline m h e')) ∧
  inline m h (Letrec a vbs e) =
    Letrec a (MAP (λ(v, e). (v, inline m h e)) vbs) (inline m h e) ∧
  inline m h (Case a e v bs f) =
    Case a (inline m h e) v
      (MAP (λ(v, vs, e). (v, vs, inline m h e)) bs)
      (case f of
        None => None
      | Some (vs, e) => Some (vs, inline m h e)) ∧
  inline m h (NestedCase a e v p e' bs) =
    NestedCase a (inline m h e) v p (inline m h e')
      (MAP (λ(p, e). (p, inline m h e)) bs)
Termination
  WF_REL_TAC ‘measure $ cexp_size (K 0) o SND o SND’
  \\ fs [cexp_size_eq] \\ rw [] \\ gvs []
  \\ imp_res_tac cexp_size_lemma \\ fs []
End

Definition inline_all_def:
  inline_all = inline pure_vars$empty
End

Triviality cexp_size_lemma2:
  ∀xs e.
    MEM e xs ⇒
    cexp_size (K 0) e ≤ list_size (cexp_size (K 0)) xs
Proof
  Induct  \\ fs [] \\ rw [] \\ res_tac \\ fs [list_size_def]
QED

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

Definition tree_size_heuristic_def:
  tree_size_heuristic n =
    (λe. tree_size e < n)
End

(*******************)

val _ = export_theory();
