(*
  Lambdifying of Letrec
*)
Theory pure_letrec_lam
Ancestors
  pure_exp pure_beta_equiv pure_letrec

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
  make_apps ((_,pure_exp$Lam _ _)::fs) = make_apps fs ∧
  make_apps ((v,e)::fs) = make_apps fs |+ (v, App (Var v) cl_tm)
End

Definition lambdify_one_def:
  lambdify_one fns e =
    let apps = make_apps fns in
    let fresh = fresh_var "x" (MAP FST fns ++ FLAT (MAP (freevars_l o SND) fns)) in
    let fns' = MAP (λ(v,f).
                if v ∈ FDOM apps then (v, Lam fresh (subst apps f))
                else (v,subst apps f)) fns in
    Letrec fns' (subst apps e)
End

Definition lambdify_all_def:
  lambdify_all e = letrec_recurse lambdify_one e
End

