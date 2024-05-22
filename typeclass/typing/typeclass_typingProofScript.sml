open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory integerTheory stringTheory optionTheory miscTheory;
open listTheory alistTheory relationTheory set_relationTheory pred_setTheory;
open typeclass_typesTheory pure_cexpTheory;
open pure_tcexpTheory pure_tcexp_typingTheory
pure_tcexp_typingPropsTheory;
open typeclass_texpTheory;
open typeclass_kindCheckTheory pure_configTheory;
open monadsyntax;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "option";

val _ = new_theory "typeclass_typingProof";

val _ = export_theory();
