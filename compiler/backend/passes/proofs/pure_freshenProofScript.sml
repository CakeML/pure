(*
   Correctness for freshening of bound variables.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory listTheory rich_listTheory pred_setTheory
open pure_expTheory pure_cexpTheory pureLangTheory pure_congruenceTheory
     pure_varsTheory var_setTheory
     pure_freshenTheory;

val _ = new_theory "pure_freshenProof";

Definition avoid_set_ok_def:
  avoid_set_ok avoid ce ⇔
    vars_ok avoid ∧
    ∀x. x ∈ freevars (exp_of ce) ∪ boundvars (exp_of ce)
      ⇒ ∃v. lookup (FST avoid) (implode x) = SOME v
End

Theorem freshen_cexp_correctness:
  ∀ce avoid ce' avoid'.
    freshen_cexp ce avoid = (ce',avoid') ∧
    avoid_set_ok avoid ce
  ⇒ exp_of ce ≅ exp_of ce' ∧ avoid_set_ok avoid ce' ∧
    (closed $ exp_of ce ⇒ closed $ exp_of ce') ∧
    cns_arities ce' = cns_arities ce ∧
    (cexp_wf ce ⇒ cexp_wf ce')
Proof
  cheat
QED

val _ = export_theory();

