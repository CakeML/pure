(*
   Verification of pure_letrec_fun, i.e. simplification of Letrec.
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open arithmeticTheory listTheory alistTheory optionTheory pairTheory dep_rewrite
     pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory pure_exp_relTheory pure_evalTheory
     pure_congruenceTheory pure_miscTheory pure_eval_lemmasTheory
     pure_letrecTheory topological_sortTheory;

val _ = new_theory "pure_letrec_funProof";

Definition Apps_def:
  Apps x [] = x ∧
  Apps x (a::as) = Apps (App x a) as
End

Definition Lams_def:
  Lams [] b = b ∧
  Lams (v::vs) b = Lam v (Lams vs b)
End

(* the input is a variable specification: recursive calls will be made
   with these arguments in this order:
    - NONE indicates var value can change,
    - SOME (n,v) indicates that variable is n and will always have value v *)
Definition make_subst_def:
  make_subst [] = FEMPTY ∧
  make_subst (a::args) =
    case a of
    | NONE => make_subst args
    | SOME (n,v) => make_subst args |+ (n,v)
End

(* the first list is the arg specification
   the second list is the long form (must be same length as first list)
   the third list is the short form (only contains values for NONE vars) *)
Inductive args_rel:
  (args_rel [] [] [])
  ∧
  (∀args x xs ys.
     args_rel args xs ys ⇒
     args_rel (NONE::args) (x::xs) (x::ys))
  ∧
  (∀v w args xs ys.
     args_rel args xs ys ⇒
     args_rel (SOME (v,w)::args) (Var v::xs) ys)
End

Inductive body_rel:
  (* recursive function f does not appear *)
  (∀x.
     ~MEM f (freevars x) ⇒
     body_rel f args x (subst (make_subst args) x))
  ∧
  (* this is the recursive call function: short form om LHS; long form on RHS *)
  (∀xs ys.
     args_rel args xs ys ⇒
     body_rel f args (Apps (Var f) ys)
                     (Apps (Var f) xs))
  ∧
  (* one must not bind the vars that are not to change *)
  (∀v x y.
     (∀n z. MEM (SOME (n,z)) args ⇒ v ≠ n) ∧
     body_rel f args x y ⇒
     body_rel f args (Lam v x) (Lam v y))
  ∧
  (* Prim *)
  (∀p xs ys.
     LIST_REL (body_rel f args) xs ys ⇒
     body_rel f args (Prim p xs) (Prim p ys))
  (* TODO: fill in missing cases *)
End

Inductive letrec_rel:
  (* this what the optimisation wants to achieve in reverse -- but it might
     not be provable directly ...
  (∀vs b b1 f args.
    body_rel f args b b1 ∧
    LENGTH args = LENGTH vs ∧ ALL_DISTINCT vs ∧
    (∀n v. MEM (SOME (n,v)) args ⇒ v = Var n ∧ MEM n vs) ∧
    closed (Letrec [(f,Lams vs b1)] x1) ∧
    letrec_fun x x1 ⇒
    letrec_fun (Let f (Lams vs (Letrec [(f,Lams vs1 b)] (Apps (Var f) (MAP Var vs1)))) x)
               (Letrec [(f,Lams vs b1)] x1))
  ∧
    ... so how about this one instead: *)
  (∀vs b b1 f args.
    body_rel f args b b1 ∧
    LENGTH args = LENGTH vs ∧ ALL_DISTINCT vs ∧
    (∀n v. MEM (SOME (n,v)) args ⇒ MEM n vs) ∧
    closed (Letrec [(f,Lams vs b1)] (Lams vs b1)) ⇒
    letrec_fun
      (Letrec [(f,Lams vs1 (subst (make_subst args) b))]
                 (Lams vs1 (subst (make_subst args) b)))
      (Letrec [(f,Lams vs b1)] (Lams vs b1)))
  ∧
  (* cases below are just recursion *)
  (∀n.
    letrec_fun (Var n) (Var n))
  ∧
  (∀n x y.
    letrec_fun x y ⇒
    letrec_fun (Lam n x) (Lam n y))
  ∧
  (∀f g x y.
    letrec_fun f g ∧ letrec_fun x y ⇒
    letrec_fun (App f x) (App g y))
  ∧
  (∀n xs ys.
    LIST_REL (letrec_fun) xs ys ⇒
    letrec_fun (Prim n xs) (Prim n ys))
  ∧
  (∀xs y xs1 y1.
    LIST_REL (letrec_fun) (MAP SND xs) (MAP SND xs1) ∧
    MAP FST xs = MAP FST xs1 ∧ letrec_fun y y1 ⇒
    letrec_fun (Letrec xs y) (Letrec xs1 y1))
End

Theorem Letrec_Lams:
  body_rel f args b b1 ∧ LENGTH args = LENGTH vs ∧ ALL_DISTINCT vs ∧
  (∀n v. MEM (SOME (n,v)) args ⇒ v = Var n ∧ MEM n vs) ∧
  closed (Letrec [(f,Lams vs b1)] x1)
  ⇒
  Letrec [(f,Lams vs b1)] x ≅
  Let f (Lams vs (Letrec [(f,Lams vs1 b)] (Apps (Var f) (MAP Var vs1)))) x
Proof
  cheat
QED

val _ = export_theory();
