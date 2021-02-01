(*
  Lambdifying of Letrec
*)
open HolKernel Parse boolLib bossLib term_tactic;
open pure_expTheory pure_miscTheory pure_beta_equivTheory;

val _ = new_theory "pure_letrec_lam";

(*
  This pass ensures that every variable bound by a Letrec is a Lambda.
  This will permit compatibility with CakeML letrecs.
*)

(* Arbitrary closed term - TODO replace with unit, if not already equal *)
Definition cl_tm_def:
  cl_tm = Cons "" []
End

Definition make_apps_def:
  make_apps [] = FEMPTY ∧
  make_apps ((_,Lam _ _)::fs) = make_apps fs ∧
  make_apps ((v,e)::fs) = make_apps fs |+ (v, App (Var v) cl_tm)
End

Definition lambdify_one_def:
  lambdify_one fns e =
    let apps = make_apps fns in
    let fresh = fresh_var "x" (MAP FST fns ++ FLAT (MAP (freevars o SND) fns)) in
    let fns' = MAP (λ(v,f).
                if v ∈ FDOM apps then (v, Lam fresh (subst apps f))
                else (v,subst apps f)) fns in
    Letrec fns' (subst apps e)
End

Definition lambdify_all_def:
  lambdify_all (Letrec xs e) = lambdify_one xs (lambdify_all e) ∧
  lambdify_all (Lam n x) = Lam n (lambdify_all x) ∧
  lambdify_all (Prim p xs) = Prim p (MAP lambdify_all xs) ∧
  lambdify_all (App x y) = App (lambdify_all x) (lambdify_all y) ∧
  lambdify_all res = res
Termination
  WF_REL_TAC `measure exp_size` >> rw [] >>
  Induct_on `xs` >> rw[] >> gvs[exp_size_def]
End

val _ = export_theory();
