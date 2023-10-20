(*
  Correctness of compilation pass that introduces Box
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory intLib
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory combinTheory
     envLangTheory thunkLang_primitivesTheory env_cexpTheory env_semanticsTheory
     env_box_1ProofTheory env_boxTheory;
local open pure_semanticsTheory in end

val _ = new_theory "env_boxProof";

val _ = set_grammar_ancestry ["env_box_1Proof","env_box"];

Theorem itree_of_compile_to_box:
  closed (exp_of x) ⇒
  itree_of (exp_of x) =
  itree_of (exp_of (env_box$compile_to_box c x))
Proof
  cheat
QED

Theorem compile_to_box_wf:
  cexp_wf (env_box$compile_to_box c x) = cexp_wf x ∧
  cns_arities (env_box$compile_to_box c x) = cns_arities x
Proof
  cheat
QED

val _ = export_theory ();
