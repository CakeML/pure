(*
   This file defines implementation-style functions for computing sets
   of free variables and maps from variable names to things.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
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

Definition list_union_def:
  list_union l = FOLDL (λs1 s2. union s1 s2) empty l
End

Definition list_delete_def:
  list_delete s l = FOLDL (λs v. delete s v) s l
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

Theorem lookup_empty[simp]:
  ∀k. lookup empty k = NONE
Proof
  rw[empty_def, mlmapTheory.empty_def, balanced_mapTheory.empty_def,
     mlmapTheory.lookup_def, balanced_mapTheory.lookup_def]
QED

Theorem cmp_of_empty[simp]:
  cmp_of empty = var_cmp
Proof
  rw[empty_def]
QED

Theorem lookup_union:
  ∀s1 s2 k.
    map_ok s1 ∧ map_ok s2 ∧ cmp_of s1 = cmp_of s2
  ⇒ lookup (union s1 s2) k =
      case lookup s1 k of
        SOME v => SOME v
      | NONE => lookup s2 k
Proof
  rw[] >>
  DEP_REWRITE_TAC[lookup_thm] >>
  qspecl_then [`s2`,`s1`] assume_tac $ GEN_ALL union_thm >> gvs[] >>
  simp[FLOOKUP_FUNION]
QED

Theorem map_ok_list_union:
  ∀l. EVERY (λm. map_ok m ∧ cmp_of m = var_cmp) l
  ⇒ map_ok (list_union l) ∧ cmp_of (list_union l) = var_cmp
Proof
  Induct using SNOC_INDUCT >> rw[] >> gvs[list_union_def, FOLDL_SNOC] >>
  gvs[SNOC_APPEND] >> qspec_then `x` mp_tac $ GEN_ALL union_thm >>
  simp[IMP_CONJ_THM, FORALL_AND_THM] >> rw[]
QED

Theorem lookup_list_union_var_set:
  ∀l k. EVERY (λm. map_ok m ∧ cmp_of m = var_cmp) l
  ⇒ lookup (list_union l) k =
    if ∃a. MEM a l ∧ lookup a k = SOME () then SOME () else NONE
Proof
  Induct using SNOC_INDUCT >> rw[list_union_def, FOLDL_SNOC, SNOC_APPEND] >>
  gvs[GSYM list_union_def] >>
  DEP_REWRITE_TAC[lookup_union] >> gvs[] >>
  qspec_then `l` assume_tac map_ok_list_union >> simp[] >>
  CASE_TAC >> gvs[] >>
  last_x_assum (qspec_then `x` mp_tac) >> gvs[] >>
  Cases_on `lookup x k` >> gvs[]
QED

Theorem map_ok_list_delete:
  ∀l m. map_ok m ⇒ map_ok (list_delete m l) ∧ cmp_of (list_delete m l) = cmp_of m
Proof
  Induct using SNOC_INDUCT >> rw[] >> gvs[list_delete_def, FOLDL_SNOC] >>
  last_x_assum drule >> rw[] >> drule delete_thm >> simp[]
QED

Theorem lookup_list_delete:
  ∀l s k. map_ok s ⇒
    lookup (list_delete s l) k = if MEM k l then NONE else lookup s k
Proof
  Induct using SNOC_INDUCT >> rw[list_delete_def, FOLDL_SNOC, SNOC_APPEND] >>
  gvs[GSYM list_delete_def] >>
  DEP_REWRITE_TAC[lookup_delete] >> drule map_ok_list_delete >> simp[]
QED

val _ = export_theory();
