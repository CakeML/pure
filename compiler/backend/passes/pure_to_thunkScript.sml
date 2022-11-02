(*
  Compilation from pureLang to thunkLang
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_namesTheory thunk_cexpTheory pure_cexpTheory;

val _ = new_theory "pure_to_thunk";

val _ = set_grammar_ancestry
  ["pure_cexp", "thunk_cexp", "pure_names"];

Definition any_el_def:
  any_el n [] = thunk_cexp$Prim (AtomOp Add) [] ∧
  any_el n (x::xs) = if n = 0 then x else any_el (n-1) xs
End

Definition to_thunk_def:
  to_thunk (s:vars) (pure_cexp$Var c v) =
    (thunk_cexp$Force (Var v),s) ∧
  to_thunk s (Lam c ns x) =
    (let (x,s) = to_thunk s x in (Lam ns x,s)) ∧
  to_thunk s (App c x ys) =
    (let (x,s) = to_thunk s x in
     let (ys,s) = to_thunk_list s ys in
       (App x (MAP Delay ys), s)) ∧
  to_thunk s (Letrec c xs y) =
    (let (y,s) = to_thunk s y in
     let (ys,s) = to_thunk_list s (MAP SND xs) in
       (Letrec (MAP2 (λ(n,_) y. (n, Delay y)) xs ys) y,s)) ∧
  to_thunk s (Let c v x y) =
    (let (x,s) = to_thunk s x in
     let (y,s) = to_thunk s y in
       (Let (SOME v) (Delay x) y,s)) ∧
  to_thunk s (Prim c p xs) =
    (let (xs,s) = to_thunk_list s xs in
       case p of
       | Seq => (Let NONE (any_el 0 xs) (any_el 1 xs),s)
       | AtomOp a => (Prim (AtomOp a) xs,s)
       | Cons t => (Prim (Cons t) (MAP Delay xs),s)) ∧
  to_thunk s (Case c x v ys opt) =
    (let (x,s) = to_thunk s x in
     let (rs,s) = to_thunk_list s (MAP (SND o SND) ys) in
     let (w,s) = invent_var (v ^ strlit "_forced") s in
       case opt of
       | NONE =>
           ((Let (SOME v) (Delay x) $
             Let (SOME w) (Force (Var v)) $
              Case w (MAP2 (λ(c,n,_) y. (c,n,y)) ys rs) NONE,s))
       | SOME (a,y) =>
          let (y,s) = to_thunk s y in
            ((Let (SOME v) (Delay x) $
              Let (SOME w) (Force (Var v)) $
               Case w (MAP2 (λ(c,n,_) y. (c,n,y)) ys rs) (SOME (a,y))),s)) ∧
  to_thunk s (NestedCase c g gv p e pes) = to_thunk s e ∧
  to_thunk_list s [] = ([],s) ∧
  to_thunk_list s (x::xs) =
    (let (x,s) = to_thunk s x in
     let (xs,s) = to_thunk_list s xs in
       (x::xs,s))
Termination
  WF_REL_TAC `measure $ λx. case x of
              | INL x => cexp_size (K 0) (SND x)
              | INR x => list_size (cexp_size (K 0)) (SND x)`
  \\ fs [pure_cexpTheory.cexp_size_eq] \\ rw []
  >~ [‘list_size (cexp_size (K 0)) (MAP SND xs)’] >-
    (pop_assum kall_tac
     \\ Induct_on ‘xs’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [basicSizeTheory.pair_size_def])
  >~ [‘list_size (cexp_size (K 0)) (MAP (λx. SND (SND x)) ys)’] >-
    (Induct_on ‘ys’ \\ fs [listTheory.list_size_def,FORALL_PROD]
     \\ rw [] \\ fs [basicSizeTheory.pair_size_def])
End

Definition compile_to_thunk_def:
  compile_to_thunk e = FST (to_thunk (pure_names e) e)
End

val _ = export_theory ();