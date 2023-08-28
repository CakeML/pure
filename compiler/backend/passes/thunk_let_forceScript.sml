(*
  Optimisation pass that turns Force (Var v) into Var w under
  Let (SOME w) (Force (Var v)).
*)

open HolKernel Parse boolLib bossLib pairTheory listTheory;
open thunk_cexpTheory mlstringTheory;

val _ = new_theory "thunk_let_force";

Definition d_Var_def[simp]:
  d_Var (Var n : thunk_cexp$cexp) = SOME n ∧
  d_Var _ = NONE
End

Definition d_Force_Var_def:
  d_Force_Var v (Force x) =
    (case d_Var x of NONE => NONE | SOME n => if n ≠ v then SOME n else NONE) ∧
  d_Force_Var v _ = NONE
End

Definition can_keep_def:
  can_keep m (a,b) ⇔ m ≠ a ∧ m ≠ b:mlstring
End

Definition can_keep_list_def:
  can_keep_list ms (a,b) ⇔ ~MEM a ms ∧ ~MEM (b:mlstring) ms
End

Definition let_force_def:
  let_force (m:(mlstring # mlstring) list) ((Var v):thunk_cexp$cexp) = Var v:thunk_cexp$cexp∧
  let_force m (Let opt x y) =
    (case opt of
     | NONE => Let opt (let_force m x) (let_force m y)
     | SOME v =>
       case d_Force_Var v x of
       | NONE => Let opt (let_force m x) (let_force (FILTER (can_keep v) m) y)
       | SOME w =>
         let m1 = FILTER (can_keep v) m in
           case ALOOKUP m w of
           | SOME t => Let opt (Var t) (let_force m1 y)
           | NONE => Let opt x (let_force ((w,v)::m1) y)) ∧
  let_force m (Lam vs x) = Lam vs (let_force (FILTER (can_keep_list vs) m) x) ∧
  let_force m (App x xs) = App (let_force m x) (MAP (let_force m) xs) ∧
  let_force m (Delay x) = Delay (let_force m x) ∧
  let_force m (Force x) =
    (case d_Var x of
     | NONE => Force (let_force m x)
     | SOME v => case ALOOKUP m v of
                 | NONE => Force (let_force m x)
                 | SOME t => Var t) ∧
  let_force m (Box x) = Box (let_force m x) ∧
  let_force m (Letrec fs x) =
    (let m1 = FILTER (can_keep_list (MAP FST fs)) m in
       Letrec (MAP (λ(n,x). (n,let_force m1 x)) fs) (let_force m1 x)) ∧
  let_force m (Case v rows d) =
    Case v (MAP (λ(n,p,x). (n,p,let_force (FILTER (can_keep_list p) m) x)) rows)
      (case d of NONE => NONE | SOME (a,e) => SOME (a,let_force m e)) ∧
  let_force m (Prim p xs) = Prim p (MAP (let_force m) xs) ∧
  let_force m (Monad mop xs) = Monad mop (MAP (let_force m) xs)
Termination
  WF_REL_TAC ‘measure $ cexp_size o SND’
End

Definition simp_let_force_def:
  simp_let_force do_it e = if do_it then let_force [] e else e
End

val _ = export_theory ();
