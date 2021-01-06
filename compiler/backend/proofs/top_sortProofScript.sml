(*
   Correctness proof for top_sort implementation
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     (* fromCakeML: *) reachable_sptTheory
     top_sortTheory;

val _ = new_theory "top_sortProof";

Theorem top_sort_any_correct:
  ∀lets res.
    ALL_DISTINCT (MAP FST lets) ∧
    res = top_sort_any lets ⇒
      ALL_DISTINCT (FLAT res) ∧
      set (FLAT res) = set (MAP FST lets) ∧
      ∀xss ys zss y.
        (* for any element ys in the result res, for any y in that ys: *)
        res = xss ++ [ys] ++ zss ∧ MEM y ys ⇒
        (* all dependencies of y must be defined in ys or earlier, i.e. xss *)
        ∃deps. ALOOKUP lets y = SOME deps ∧
               ∀d. MEM d deps ⇒ MEM d (FLAT xss ++ ys)
Proof
  cheat
QED

val _ = export_theory();
