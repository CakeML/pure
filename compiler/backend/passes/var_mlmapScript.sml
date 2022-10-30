(*
   This file defines implementation-style functions for computing sets
   of free variables and maps from variable names to things.
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open listTheory stringTheory alistTheory optionTheory pairTheory
     pred_setTheory finite_mapTheory;
open mlmapTheory mlstringTheory;

val _ = new_theory "var_mlmap";

(* definitions *)

Type var_map = “:(mlstring, 'a) mlmap$map”
Type var_set = “:unit var_map”

Definition var_cmp_def:
  var_cmp s1 s2 = mlstring$compare s1 s2
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

(* TODO move to mlmapTheory *)
Definition unionWith_def:
  unionWith f (Map cmp t1) (Map _ t2) =
    Map cmp (balanced_map$unionWith cmp f t1 t2)
End

Definition new_var_def:
  new_var ml s =
  if map_ok ml
  then
    case lookup ml s of
       | NONE => (s, insert ml s ())
       | SOME _ => new_var ml (s ^ (strlit "'"))
  else (s, ml)
Termination
  WF_REL_TAC ‘measure $ (λ(ml, s). CARD (FDOM (to_fmap ml) ∩ {s2 | strlen s ≤ strlen s2}))’ \\ rw []
  \\ irule CARD_PSUBSET
  \\ irule_at Any FINITE_INTER
  \\ gvs [finite_mapTheory.FDOM_FINITE, PSUBSET_DEF, SUBSET_DEF, SET_EQ_SUBSET]
  \\ qexists_tac ‘s’ \\ gvs [lookup_thm, finite_mapTheory.FLOOKUP_DEF]
End

(* lemmas *)

Theorem map_ok_empty[simp]:
  map_ok empty
Proof
  fs [map_ok_def,empty_def,empty_thm]
  \\ assume_tac TotOrd_compare
  \\ fs [totoTheory.TotOrd]
  \\ fs [var_cmp_def]
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

(* TODO move to mlmapTheory *)
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

(* TODO move to mlmapTheory *)
Theorem MAP_KEYS_sing_set_FMERGE_WITH_KEY:
  FMERGE_WITH_KEY (λk a b. f k a b)
    (MAP_KEYS (λx. {x}) t1) (MAP_KEYS (λx. {x}) t2) =
  MAP_KEYS (λx. {x}) (FMERGE_WITH_KEY (λk a b. f {k} a b) t1 t2)
Proof
  rw[fmap_eq_flookup, FLOOKUP_FMERGE_WITH_KEY] >>
  `∀u. INJ (λx. {x}) u UNIV` by simp[INJ_IFF] >>
  simp[FLOOKUP_MAP_KEYS] >>
  Cases_on `x` >> gvs[] >> reverse $ Cases_on `t` >> gvs[]
  >- (
    rename1 `a INSERT b INSERT s` >>
    qsuff_tac `∀y. a INSERT b INSERT s <> {y}` >> gvs[] >>
    rw[EXTENSION] >> metis_tac[]
    ) >>
  `∀P v. x' = v ∧ P v ⇔ x' = v /\ P x'` by metis_tac [] >> gvs[] >>
  rename1 `a ∈ _` >>
  Cases_on `a ∈ FDOM t1` >> Cases_on `a ∈ FDOM t2` >> gvs[] >>
  gvs[FLOOKUP_DEF, FMERGE_WITH_KEY_DEF]
QED

(* TODO move to mlmapTheory *)
Theorem unionWith_thm:
   map_ok t1 /\ map_ok t2 /\ cmp_of t1 = cmp_of t2 ==>
   map_ok (unionWith f t1 t2) /\
   cmp_of (unionWith f t1 t2) = cmp_of t1 /\
   to_fmap (unionWith f t1 t2) = FMERGE f (to_fmap t1) (to_fmap t2)
Proof
  Cases_on `t1` >> Cases_on `t2` >> gvs[cmp_of_def] >> strip_tac >> gvs[] >>
  simp[unionWith_def, cmp_of_def] >> conj_asm1_tac
  >- (
    gvs[map_ok_def] >>
    imp_res_tac comparisonTheory.TotOrder_imp_good_cmp >>
    gvs[balanced_mapTheory.unionWith_thm]
    ) >>
  rename1 `unionWith k f t1 t2` >>
  gvs[map_ok_def] >> imp_res_tac comparisonTheory.TotOrder_imp_good_cmp >>
  drule balanced_mapTheory.unionWith_thm >>
  disch_then $ qspecl_then [`f`,`t1`,`t2`] assume_tac >> gvs[] >>
  gvs[to_fmap_thm, MAP_KEYS_sing_set_FMERGE_WITH_KEY, MAP_KEYS_sing_set] >>
  simp[FMERGE_WITH_KEY_FMERGE]
QED

(* TODO move to mlmapTheory *)
Theorem lookup_unionWith:
  ∀s1 s2 k.
    map_ok s1 ∧ map_ok s2 ∧ cmp_of s1 = cmp_of s2
  ⇒ lookup (unionWith f s1 s2) k =
      case lookup s1 k of
      | NONE => lookup s2 k
      | SOME v1 =>
          case lookup s2 k of
          | NONE => SOME v1
          | SOME v2 => SOME $ f v1 v2
Proof
  rw[] >>
  DEP_REWRITE_TAC[lookup_thm] >>
  qspecl_then [`s2`,`s1`] assume_tac $ GEN_ALL unionWith_thm >> gvs[] >>
  simp[FLOOKUP_FMERGE]
QED

Definition var_creator_ok_def:
  var_creator_ok vc = (mlmap$map_ok vc ∧ mlmap$cmp_of vc = mlstring$compare)
End

Definition vc_to_set_def:
  vc_to_set vc = IMAGE explode (FDOM (to_fmap vc))
End

Theorem new_var_soundness:
  ∀vc' s'. new_var vc s = (s', vc') ∧ var_creator_ok vc ⇒
           var_creator_ok vc' ∧ explode s' ∉ vc_to_set vc ∧
           vc_to_set vc' = vc_to_set vc ∪ {explode s'}
Proof
  completeInduct_on ‘CARD (FDOM (to_fmap vc) ∩ {s2 | strlen s ≤ strlen s2})’
  \\ gvs [var_creator_ok_def]
  \\ gen_tac \\ gen_tac \\ strip_tac
  \\ gen_tac \\ gen_tac
  \\ simp [Once new_var_def]
  \\ gvs [lookup_thm, FLOOKUP_DEF, SF CONJ_ss]
  \\ IF_CASES_TAC \\ strip_tac
  \\ gvs [insert_thm, vc_to_set_def]
  >- (last_x_assum irule \\ simp []
      \\ last_x_assum $ irule_at (Pos last)
      \\ irule CARD_PSUBSET
      \\ irule_at Any FINITE_INTER
      \\ gvs [finite_mapTheory.FDOM_FINITE, PSUBSET_DEF, SUBSET_DEF, SET_EQ_SUBSET]
      \\ first_x_assum $ irule_at Any
      \\ gvs [lookup_thm, finite_mapTheory.FLOOKUP_DEF])
  \\ simp [Once INSERT_SING_UNION, UNION_COMM]
QED

val _ = export_theory();
