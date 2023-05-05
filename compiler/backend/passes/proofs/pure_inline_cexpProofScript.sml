(*
  Inlining optimization proofs for cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open listTheory pairTheory topological_sortTheory;
open pure_cexpTheory pure_varsTheory balanced_mapTheory pureLangTheory;
open pure_inlineTheory pure_inline_cexpTheory;

val _ = new_theory "pure_inline_cexpProof";

Definition crhs_to_rhs_def:
  crhs_to_rhs (cExp e) = (Exp $ exp_of e) ∧
  crhs_to_rhs (cRec e) = (Rec $ exp_of e)
End

(* xs and m have the same elements *)
Definition memory_inv_def:
  memory_inv xs m =
    ∀v e. (MEM (explode v, (crhs_to_rhs e)) xs) ⇔ (lookup m v = SOME e)
End

(* check assumptions *)
Theorem inline_cexp_list_subst_rel:
  ∀h m x xs.
    memory_inv xs m ∧
    no_shadowing (exp_of x) ∧
    DISJOINT (set (MAP FST xs)) (boundvars (exp_of x)) ⇒
    list_subst_rel xs (exp_of x) (exp_of (inline m h x))
Proof
  \\ cheat
  (* evantually: ho_match_mp_tac *)
QED


(*******************)

val _ = export_theory();
