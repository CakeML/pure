(*
   Defines implementation style functions for managaing a
   set of variables, including inventing fresh ones.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open listTheory stringTheory alistTheory optionTheory pairTheory
     pred_setTheory finite_mapTheory mlintTheory;
open mlmapTheory mlstringTheory;

val _ = new_theory "var_set";

(* --- type abbreviation --- *)

Type vars = “:(mlstring, unit) mlmap$map # num”

(* --- implementation functions --- *)

Definition empty_vars_def:
  empty_vars = ((mlmap$empty mlstring$compare, 0):vars)
End

Definition insert_var_def:
  insert_var ((vs,n):vars) v =
    (insert vs v (), MAX (strlen v) n)
End

Definition insert_vars_def:
  insert_vars s [] = s ∧
  insert_vars s (n::ns) = insert_vars (insert_var s n) ns
End

Definition invent_var_aux_def:
  invent_var_aux base (k:num) (l:num) (vs,n) =
    if l = 0 then NONE else
      let candidate = base ^ toString k in
        case lookup vs candidate of
        | NONE => SOME (candidate, insert_var (vs,n) candidate)
        | SOME _ => invent_var_aux base (k+1) (l-1) (vs,n)
End

Definition invent_var_def:
  invent_var base ((vs,n):vars) =
    case lookup vs base of
    | NONE => (base, insert_var (vs,n) base)
    | SOME _ =>
    case invent_var_aux base 0 1000 (vs,n) of
    | SOME res => res
    | NONE =>
        let new_var = concat (REPLICATE (n+1) (strlit "t")) in
          (new_var, insert_var (vs,n) new_var)
End

Definition contains_var_def:
  contains_var v ((vs,n):vars) =
    case lookup vs v of
    | NONE => F
    | SOME _ => T
End

Definition delete_var_def:
  delete_var ((vs,n):vars) v = (delete vs v, n)
End

Definition delete_vars_def:
  delete_vars s [] = s ∧
  delete_vars s (n::ns) = delete_vars (delete_var s n) ns
End

Definition var_union_def:
  var_union ((vs1,n1):vars) ((vs2,n2):vars) = (union vs1 vs2, MAX n1 n2)
End

(* --- definitions for proofs --- *)

Definition vars_ok_def:
  vars_ok (vs,n) ⇔
    mlmap$map_ok vs ∧
    mlmap$cmp_of vs = mlstring$compare ∧
    ∀k v. lookup vs k = SOME v ⇒ strlen k ≤ n
End

Definition set_of_def:
  set_of ((vs,n):vars) = IMAGE explode (FDOM (to_fmap vs))
End

(* --- lemmas --- *)

Theorem vars_ok_empty_vars[simp]:
  vars_ok empty_vars
Proof
  fs [empty_vars_def,vars_ok_def]
  \\ fs [map_ok_def,empty_thm]
  \\ assume_tac TotOrd_compare
  \\ fs [totoTheory.TotOrd]
  \\ rw[empty_def, mlmapTheory.empty_def, balanced_mapTheory.empty_def,
        mlmapTheory.lookup_def, balanced_mapTheory.lookup_def]
  \\ metis_tac []
QED

Theorem set_of_empty_vars[simp]:
  set_of empty_vars = ∅
Proof
  fs [set_of_def,empty_vars_def,mlmapTheory.empty_thm]
QED

Theorem vars_ok_insert_var[simp]:
  vars_ok vs ⇒ vars_ok (insert_var vs n)
Proof
  PairCases_on ‘vs’
  \\ fs [insert_var_def,vars_ok_def,insert_thm,lookup_insert]
  \\ rw [] \\ fs [AllCaseEqs()]
QED

Theorem vars_ok_insert_vars[simp]:
  vars_ok vs ⇒ vars_ok (insert_vars vs ns)
Proof
  qid_spec_tac ‘vs’ \\ Induct_on ‘ns’ \\ fs [insert_vars_def]
QED

Theorem vars_ok_delete_var[simp]:
  vars_ok vs ⇒ vars_ok (delete_var vs n)
Proof
  PairCases_on ‘vs’
  \\ fs [delete_var_def,vars_ok_def,delete_thm,lookup_delete]
QED

Theorem vars_ok_delete_vars[simp]:
  vars_ok vs ⇒ vars_ok (delete_vars vs ns)
Proof
  qid_spec_tac ‘vs’ \\ Induct_on ‘ns’ \\ fs [delete_vars_def]
QED

Theorem vars_ok_union[simp]:
  vars_ok vs1 ∧ vars_ok vs2 ⇒ vars_ok (var_union vs1 vs2)
Proof
  PairCases_on ‘vs1’
  \\ PairCases_on ‘vs2’
  \\ fs [var_union_def,vars_ok_def,lookup_thm,union_thm,FLOOKUP_FUNION]
  \\ strip_tac \\ gen_tac
  \\ CASE_TAC \\ gs [lookup_thm]
QED

Theorem set_of_insert_var[simp]:
  vars_ok vs ⇒
  set_of (insert_var vs n) = explode n INSERT set_of vs
Proof
  PairCases_on ‘vs’
  \\ fs [insert_var_def,vars_ok_def,insert_thm,lookup_insert,set_of_def]
QED

Theorem set_of_insert_vars[simp]:
  vars_ok vs ⇒
  set_of (insert_vars vs ns) = set (MAP explode ns) ∪ set_of vs
Proof
  qid_spec_tac ‘vs’ \\ Induct_on ‘ns’ \\ fs [insert_vars_def]
  \\ fs [EXTENSION] \\ metis_tac []
QED

Theorem set_of_delete_var[simp]:
  vars_ok vs ⇒
  set_of (delete_var vs n) = set_of vs DELETE explode n
Proof
  PairCases_on ‘vs’
  \\ fs [delete_var_def,vars_ok_def,delete_thm,lookup_delete,set_of_def]
  \\ rw [EXTENSION] \\ eq_tac
  \\ rw []
  >- metis_tac []
  >- (strip_tac \\ first_x_assum irule
      \\ irule EQ_TRANS
      \\ irule_at (Pos hd) $ GSYM implode_explode
      \\ asm_rewrite_tac [] \\ simp [])
  >- (irule_at (Pos hd) EQ_REFL \\ simp []
      \\ strip_tac \\ gs [])
QED

Theorem set_of_delete_vars[simp]:
  vars_ok vs ⇒
  set_of (delete_vars vs ns) = set_of vs DIFF set (MAP explode ns)
Proof
  qid_spec_tac ‘vs’ \\ Induct_on ‘ns’ \\ fs [delete_vars_def]
  \\ fs [EXTENSION] \\ metis_tac []
QED

Theorem set_of_var_union[simp]:
  vars_ok vs1 ∧ vars_ok vs2 ⇒ set_of (var_union vs1 vs2) = set_of vs1 ∪ set_of vs2
Proof
  PairCases_on ‘vs1’
  \\ PairCases_on ‘vs2’
  \\ fs [var_union_def,vars_ok_def,lookup_thm,union_thm,set_of_def,EXTENSION]
QED

Theorem contains_var_in_set_of:
  vars_ok vs ⇒ (contains_var v vs ⇔ explode v ∈ set_of vs)
Proof
  PairCases_on ‘vs’
  \\ fs [contains_var_def,vars_ok_def,set_of_def, lookup_thm]
  \\ CASE_TAC \\ gs [flookup_thm]
QED

Theorem invent_var_thm:
  invent_var base vs = (n,vs1) ∧
  vars_ok vs ⇒
  vars_ok vs1 ∧ explode n ∉ set_of vs ∧
  set_of vs1 = explode n INSERT set_of vs
Proof
  PairCases_on ‘vs’
  \\ fs [invent_var_def,AllCaseEqs()] \\ strip_tac \\ gvs []
  >- fs [set_of_def,vars_ok_def,lookup_thm,FLOOKUP_DEF]
  >-
   (fs [set_of_def,vars_ok_def,lookup_thm,FLOOKUP_DEF]
    \\ gvs [lookup_thm,FLOOKUP_DEF]
    \\ CCONTR_TAC \\ fs [] \\ res_tac
    \\ fs [strlen_def,concat_def])
  \\ rename [‘invent_var_aux base n1 n2’]
  \\ qpat_x_assum ‘invent_var_aux base n1 n2 _ = _’ mp_tac
  \\ qid_spec_tac ‘n1’
  \\ qid_spec_tac ‘n2’
  \\ Induct \\ simp [Once invent_var_aux_def]
  \\ gvs [AllCaseEqs()]
  \\ gen_tac \\ strip_tac \\ gvs [set_of_def]
  >-
   (Cases \\ fs [] \\ rw [] \\ gvs [lookup_thm,vars_ok_def,FLOOKUP_DEF]
    \\ fs [strcat_def,concat_def]
    \\ Cases_on ‘base’ \\ fs []
    \\ Cases_on ‘toString n1’ \\ fs [])
  \\ res_tac \\ fs []
QED

val _ = export_theory();
