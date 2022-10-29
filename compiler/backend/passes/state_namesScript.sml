(*
  Definition of compilation that inserts names for Lam NONE and
  replaces HandleApp by a Handle and an App.
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory;
open state_cexpTheory state_cexpTheory mlstringTheory;

val _ = new_theory "state_names";

val _ = set_grammar_ancestry ["state_cexp"];

Overload str_prefix = “strlit "ignore"”
Overload str_prefix_len = (EVAL “strlen str_prefix” |> concl |> rand);

Definition max_name_def:
  max_name (v:mlstring) =
    if isPrefix str_prefix v then
      (strlen v + 1) - str_prefix_len
    else 0
End

Triviality max_name_test:
  max_name (strlit "hello") = 0 ∧
  max_name (strlit "ignore") = 1 ∧
  max_name (strlit "ignore'") = 2
Proof
  EVAL_TAC
QED

Definition make_name_def:
  make_name n = str_prefix ^ concat (REPLICATE n (strlit "'"))
End

Definition list_max_def:
  list_max [] = 0:num ∧
  list_max (n::ns) = MAX n (list_max ns)
End

Definition give_names_def:
  give_names ((Var v):cexp) =
    (Var v, max_name v) ∧
  give_names (Lam vn x) =
    (let (y,n) = give_names x in
       case vn of
       | NONE => (Lam (SOME (make_name n)) y, n)
       | _ => (Lam vn y, n)) ∧
  give_names (Let vn x y) =
    (let (x',m) = give_names x in
     let (y',n) = give_names y in
     let k = MAX n m in
       case vn of
       | NONE => (Let (SOME (make_name n)) x' y', k)
       | _ => (Let vn x' y', k)) ∧
  give_names (App op xs) =
    (let res = MAP give_names xs in
       (App op (MAP FST res), list_max (MAP SND res))) ∧
  give_names (Handle x t y) =
    (let (x',m) = give_names x in
     let (y',n) = give_names y in
       (Handle x' t y', MAX n m)) ∧
  give_names (HandleApp x y) =
    (let (x',m) = give_names x in
     let (y',n) = give_names y in
     let nm = make_name m in
       (Handle y' nm (App AppOp [x'; Var nm]), MAX n m)) ∧
  give_names (If x y z) =
    (let (x',m) = give_names x in
     let (y',n) = give_names y in
     let (z',k) = give_names z in
       (If x' y' z', MAX n (MAX m k))) ∧
  give_names (Raise x) =
    (let (x',m) = give_names x in
       (Raise x', m)) ∧
  give_names (Letrec fs d) =
    (let res = MAP (λx. case x of (_,_,y) => give_names y) fs in
     let rs = MAP2 (λ(a,b,_) (x,_). (a,b,x)) fs res in
     let n = list_max (MAP SND res) in
     let (e,m) = give_names d in
       (Letrec rs e, MAX n m)) ∧
  give_names (Case v rows d) =
    (let res = MAP (λ(_,_,x). give_names x) rows in
     let rs = MAP2 (λ(a,b,_) (x,_). (a,b,x)) rows res in
     let n = list_max (max_name v :: MAP SND res) in
       case d of
       | NONE => (Case v rs d, n)
       | SOME (a,e) =>
           let (e1,n1) = give_names e in
             (Case v rs (SOME (a,e1)), MAX n n1))
Termination
  WF_REL_TAC ‘measure cexp_size’
End

Definition give_all_names_def:
  give_all_names e = FST (give_names e)
End

val _ = export_theory ();
