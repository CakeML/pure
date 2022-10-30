(*
  A function tha collects all names in a pureLang cexp
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open listTheory pairTheory mlstringTheory;
open pure_cexpTheory var_setTheory;

val _ = set_grammar_ancestry ["var_set", "pure_cexp"];

val _ = new_theory "pure_names";

Definition extract_names_def:
  extract_names s (pure_cexp$Var c v) = insert_var s v ∧
  extract_names s (Lam c ns x) = extract_names (insert_vars s ns) x ∧
  extract_names s (Letrec c xs y) =
    (let s = insert_vars s (MAP FST xs) in
     let s = extract_names_list s (MAP SND xs) in
       extract_names s y) ∧
  extract_names s (Prim c p xs) =
    extract_names_list s xs ∧
  extract_names s (App c x ys) =
    extract_names_list (extract_names s x) ys ∧
  extract_names s (Let c n x y) =
    extract_names (extract_names (insert_var s n) x) y ∧
  extract_names s (Case c x n ys eopt) =
    (let s = extract_names (insert_var s n) x in
     let s = extract_names_list s (MAP (SND o SND) ys) in
       case eopt of
       | NONE => s
       | SOME (a,e) => extract_names s e) ∧
  extract_names s (NestedCase c g gv p e pes) =
    (let s = extract_names (insert_var s gv) g in
     let s = extract_names s e in
       extract_names_list s (MAP SND pes)) ∧
  extract_names_list s [] = s ∧
  extract_names_list s (x::xs) =
    extract_names_list (extract_names s x) xs
Termination
  WF_REL_TAC `measure $ λx. case x of
              | INL x => cexp_size (K 0) (SND x)
              | INR x => list_size (cexp_size (K 0)) (SND x)`
  \\ fs [pure_cexpTheory.cexp_size_eq] \\ rw []
  >~ [‘list_size (cexp_size (K 0)) (MAP SND pes)’] >-
    (Induct_on ‘pes’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [basicSizeTheory.pair_size_def])
  >~ [‘list_size (cexp_size (K 0)) (MAP SND xs)’] >-
    (pop_assum kall_tac
     \\ Induct_on ‘xs’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [basicSizeTheory.pair_size_def])
  >~ [‘list_size (cexp_size (K 0)) (MAP (λx. SND (SND x)) ys)’] >-
    (Induct_on ‘ys’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [basicSizeTheory.pair_size_def])
End

Definition all_names_def:
  all_names e = extract_names empty_vars e
End

val _ = export_theory();
