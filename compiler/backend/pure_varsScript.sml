(*
   This file defines implementation-style functions for computing sets
   of free variables and maps from variable names to things.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory mlmapTheory mlstringTheory;

val _ = new_theory "pure_vars";

(* definitions *)

Type var_map = “:(string, 'a) mlmap$map”
Type var_set = “:unit var_map”

Definition var_cmp_def:
  var_cmp s1 s2 = mlstring$compare (implode s1) (implode s2)
End

Definition empty_def:
  empty = mlmap$empty var_cmp
End

(* lemmas *)

Theorem map_ok_empty[simp]:
  map_ok empty
Proof
  fs [map_ok_def,empty_def,empty_thm]
  \\ assume_tac TotOrd_compare
  \\ fs [totoTheory.TotOrd]
  \\ fs [var_cmp_def,mlstringTheory.implode_def]
  \\ metis_tac []
QED

val _ = export_theory();
