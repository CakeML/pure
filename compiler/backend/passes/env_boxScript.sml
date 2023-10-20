(*
  Optimisation pass that turns some Delays into Boxes
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_miscTheory pure_configTheory pure_comp_confTheory env_cexpTheory;

val _ = new_theory "env_box";

val _ = set_grammar_ancestry ["env_cexp", "pure_comp_conf"];

Definition is_Lit_def:
  is_Lit (Lit _ : atom_op) = T ∧
  is_Lit _ = F
End

Definition to_box_def:
  to_box (Delay x) =
    (let (x1,b) = to_box x in
       if b then (Box x1,T) else (Delay x1, T)) ∧
  to_box (env_cexp$Var n) = (env_cexp$Var n, T) ∧
  to_box (App x y) =
    (let (x1,_) = to_box x in
     let (y1,_) = to_box y in
       (App x1 y1, F)) ∧
  to_box (Lam v x) =
    (let (x1,_) = to_box x in
       (Lam v x1, T)) ∧
  to_box (Ret x) =
    (let (x1,_) = to_box x in
       (Ret x1, T)) ∧
  to_box (Raise x) =
    (let (x1,_) = to_box x in
       (Raise x1, T)) ∧
  to_box (Bind x y) =
    (let (x1,_) = to_box x in
     let (y1,_) = to_box y in
       (Bind x1 y1, T)) ∧
  to_box (Handle x y) =
    (let (x1,_) = to_box x in
     let (y1,_) = to_box y in
       (Handle x1 y1, T)) ∧
  to_box (Act x) =
    (let (x1,_) = to_box x in
       (Act x1, T)) ∧
  to_box (Length x) =
    (let (x1,_) = to_box x in
       (Length x1, T)) ∧
  to_box (Alloc x y) =
    (let (x1,_) = to_box x in
     let (y1,_) = to_box y in
       (Alloc x1 y1, T)) ∧
  to_box (Update x y z) =
    (let (x1,_) = to_box x in
     let (y1,_) = to_box y in
     let (z1,_) = to_box z in
       (Update x1 y1 z1, T)) ∧
  to_box (Deref x y) =
    (let (x1,_) = to_box x in
     let (y1,_) = to_box y in
       (Deref x1 y1, T)) ∧
  to_box (Box x) =
    (let (x1,b) = to_box x in
       (Box x1, b)) ∧
  to_box (Force x) =
    (let (x1,_) = to_box x in
       (Force x1, F)) ∧
  to_box (Let vo x y) =
    (let (x1,_) = to_box x in
     let (y1,_) = to_box y in
       (Let vo x1 y1, F)) ∧
  to_box (If x y z) =
    (let (x1,_) = to_box x in
     let (y1,_) = to_box y in
     let (z1,_) = to_box z in
       (If x1 y1 z1, F)) ∧
  to_box (Prim (Cons m) xs) =
    (let (xs1,b) = to_box_list xs in
       (Prim (Cons m) xs1,b)) ∧
  to_box (Prim (AtomOp a) xs) =
    (let (ys,b) = to_box_list xs in
       (Prim (AtomOp a) xs, is_Lit a ∧ NULL xs)) ∧
  to_box (Case v rs d) =
    (let (ys,b) = to_box_list (MAP (SND o SND) rs) in
       (Case v (MAP2 (λ(n,cs,_) e. (n,cs,e)) rs ys)
          (case d of
           | NONE => NONE
           | SOME (c,e) => SOME (c,let (e,_) = to_box e in e)), F)) ∧
  to_box (Letrec xs x) =
    (let (ys,_) = to_box_list (MAP SND xs) in
     let (y,_) = to_box x in
       (Letrec (MAP2 (λ(n,_) e. (n,e)) xs ys) y, F)) ∧
  to_box_list [] = ([],T) ∧
  to_box_list (e::es) =
    (let (x1,b1) = to_box e in
     let (xs1,b2) = to_box_list es in
       (x1::xs1,b1 ∧ b2))
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL y => cexp_size y
                            | INR ys => list_size cexp_size ys’
  \\ conj_tac
  >-
   (Induct_on ‘xs’
    \\ gvs [listTheory.list_size_def,FORALL_PROD,cexp_size_eq,
            basicSizeTheory.pair_size_def] \\ rw []
    \\ pop_assum $ assume_tac o SPEC_ALL \\ gvs [])
  >-
   (Induct_on ‘rs’
    \\ gvs [listTheory.list_size_def,FORALL_PROD,cexp_size_eq,
            basicSizeTheory.pair_size_def] \\ rw []
    \\ pop_assum $ assume_tac o SPEC_ALL \\ gvs [])
End

Definition compile_to_box_def:
  compile_to_box (c:compiler_opts) e =
    if c.do_to_box
    then (let (e1,_) = to_box e in e1)
    else e
End

val _ = export_theory ();
