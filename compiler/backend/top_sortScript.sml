(*
   This file defines functions for a topological-sort-like
   partitioning of related nodes. Strictly speaking this is not a
   topological sort because we allow cycles in the dependencies. The
   implementation is a divide-and-conquer algorithm.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     sptreeTheory
(* fromCakeML: *)
open reachable_sptProofTheory

val _ = new_theory "top_sort";

(* the algorithm is defined over num for efficiency *)

Definition needs_def:
  needs n m (reach:num_set num_map) =
    case lookup n reach of
    | NONE => F (* cannot happen *)
    | SOME s => IS_SOME (lookup m s)
End

Definition partition_def:
  partition n [] reach acc = acc ∧
  partition n (k::ks) reach (xs,ys,zs) =
    if needs k n reach then
      if needs n k reach then
        partition n ks reach (xs,k::ys,zs)
      else
        partition n ks reach (xs,ys,k::zs)
    else
      partition n ks reach (k::xs,ys,zs)
End

Theorem partition_LENGTH[local]:
  ∀ks n reach xs ys zs xs1 ys1 zs1.
    partition n ks reach (xs,ys,zs) = (xs1,ys1,zs1) ⇒
    LENGTH xs1 ≤ LENGTH xs + LENGTH ks ∧
    LENGTH ys1 ≤ LENGTH ys + LENGTH ks ∧
    LENGTH zs1 ≤ LENGTH zs + LENGTH ks
Proof
  Induct \\ fs [partition_def] \\ rw [] \\ res_tac \\ fs []
QED

Definition top_sort_aux_def:
  top_sort_aux [] reach acc = acc ∧
  top_sort_aux (n::ns) reach acc =
    let (xs,ys,zs) = partition n ns reach ([],[],[]) in
      top_sort_aux xs reach ((n::ys) :: top_sort_aux zs reach acc)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’ \\ rw []
  \\ pop_assum (assume_tac o GSYM)
  \\ imp_res_tac partition_LENGTH \\ fs []
End

(******************** TODO move to CakeML? ********************)

Theorem superdomain_rewrite:
  ∀n tree.
      n ∈ domain (superdomain tree) ⇔
      ∃k aSet. lookup k tree = SOME aSet ∧ n ∈ domain aSet
Proof
  rw[] >> eq_tac >> rw[]
  >- (irule superdomain_inverse_thm >> simp[]) >>
  CCONTR_TAC >> drule superdomain_not_in_thm >>
  simp[] >> goal_assum drule >> simp[]
QED

Theorem domain_spt_fold_union_eq:
  ∀y tree. domain (spt_fold union y tree) = domain y ∪ domain (superdomain tree)
Proof
  rw[EXTENSION, domain_lookup, miscTheory.lookup_spt_fold_union_STRONG] >>
  eq_tac >> rw[] >> simp[]
  >- (imp_res_tac superdomain_thm >> gvs[SUBSET_DEF, domain_lookup]) >>
  DISJ2_TAC >>
  qspecl_then [`x`,`tree`] assume_tac superdomain_inverse_thm >>
  gvs[domain_lookup] >> goal_assum drule >> simp[]
QED

Definition closure_spt_alt_def:
  closure_spt_alt (reachable: num_set) tree =
    let sets = inter tree reachable in
    let nodes = spt_fold union LN sets in
    if subspt nodes reachable then reachable
    else closure_spt_alt (union reachable nodes) tree
Termination
  WF_REL_TAC `measure (λ (r,t). size (difference (superdomain t) r))` >> rw[] >>
  gvs[subspt_domain, SUBSET_DEF] >>
  irule size_diff_less >>
  fs[domain_union, domain_difference, domain_spt_fold_union_eq,
     GSYM MEMBER_NOT_EMPTY] >>
  goal_assum drule >> simp[] >>
  gvs[superdomain_rewrite, lookup_inter] >>
  EVERY_CASE_TAC >> gvs[] >> goal_assum drule >> simp[]
End

(******************** END TODO ********************)

Definition trans_clos_def:
  (* computes the transitive closure for each node given nexts *)
  trans_clos nexts = map (λx. closure_spt_alt x nexts) nexts
End

Definition top_sort_def:
  top_sort (let_bindings : (num (* name *) # num_set (* free vars *)) list) =
    let roots = MAP FST let_bindings in
    let nexts = fromAList let_bindings in
    let reach = trans_clos nexts in
      top_sort_aux roots reach []
End

val _ = computeLib.add_funs [subspt_eq];

Triviality top_sort_test:
   top_sort
     [(0,fromAList[]);               (* 0 has no deps *)
      (1,fromAList[(2,());(0,())]);  (* 1 depens on 2 and 0 *)
      (2,fromAList[(1,())]);         (* 2 depends on 1 *)
      (3,fromAList[(1,())])]         (* 3 depends on 1 *)
   =
   [[0]; [1; 2]; [3]]  (* 0 defined first, 1 and 2 are mutual, 3 is last *)
Proof
  EVAL_TAC
QED

(* generalisation to any type *)

Definition to_nums_def:
  to_nums b [] = LN ∧
  to_nums b (x::xs) =
    case ALOOKUP b x of
    | NONE => to_nums b xs
    | SOME n => insert n () (to_nums b xs)
End

Definition top_sort_any_def:
  top_sort_any (lets : ('a # 'a list) list) =
    if NULL lets (* so that HD names, below, is well defined *) then [] else
      let names = MAP FST lets in
      let to_num = MAPi (λi n. (n,i)) names in
      let from_num = fromAList (MAPi (λi n. (i,n)) names) in
      let nesting = top_sort (MAPi (λi (n,ns). (i,to_nums to_num ns)) lets) in
        MAP (MAP (λn. misc$lookup_any n from_num (HD names))) nesting
End

Triviality top_sort_any_test:
   top_sort_any
     [("A",[]);          (* A has no deps *)
      ("B",["C";"A"]);   (* B depens on C and A *)
      ("C",["B";"X"]);   (* C depends on B and X -- X is intentionally not defined here *)
      ("D",["B"])]       (* D depends on B *)
   =
   [["A"]; ["B"; "C"]; ["D"]]  (* A defined first, B and C are mutual, D is last *)
Proof
  EVAL_TAC
QED

val _ = export_theory();
