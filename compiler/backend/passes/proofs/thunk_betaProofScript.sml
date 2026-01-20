(*
  Define beta reduction
*)

Theory thunk_beta
Ancestors
  string option sum pair list alist finite_map pred_set rich_list
  thunkLang thunkLang_primitives wellorder arithmetic pure_misc
  thunkLangProps thunk_semantics thunk_remove_unuseful_bindings
Libs
  term_tactic monadsyntax dep_rewrite

(*
SKETCH: For expressions M,N and Var x

  BETA_R ((λx.M)N) (M[x := M])

  BETA_R M N ==> BETA_R (λx.M) (λx.N)
  BETA_R M N ==> BETA_R (λx.M) (λx.N)
  BETA_R M N ==> BETA_R FM FN, for any expr F


Definition beta_rel_def:
  (∀ exp1 exp2 vname. beta_rel (App (Lam vname exp1) exp2) = (subst exp1 exp2)) ∧ 
  (∀ exp1 exp2 vname. beta_rel exp1 exp2  ==> beta_rel (Lam vname exp1) (Lam vname exp2)) ∧
  (∀ exp1 exp2. beta_rel exp1 exp2 ==> (∀exp3. beta_rel (App exp3 exp1) (App exp3 exp2)))
End

*)

Definition beta_rel_def:
(*
Problems:
  1. I can't figure out how Letrec works
  2. Current expression is really awkward,
  need to find a better way to recursively check the program body. aux_beta?

e.g.
foo =
  Lam x (Lam y (Lam z
    Let x = Force x in
      Let z = Force z in
        foo_aux x y z))
-->
foo =
  Lam x (Lam y (Lam z
    foo_aux (Force x) y (Force z)))
*)

(beta_rel (Lam v1 (Var vname)) (Fail)) ∧

(beta_rel (Lam v1 (Prim op explist) (
  MAP (fn e => case e of
    (Let (SOME v2) v2exp body) => (subst (freevars (Lam v1 body)) v2exp)
    | _ => e) explist))) ∧

(beta_rel (Lam v1 (Monad mop (explist)) exp) (
  MAP (fn e => 
    case e of
      (Let (SOME v2) v2exp body) => (subst (freevars (Lam v1 body)) v2exp)
      | _ => e) explist)) ∧

(beta_rel (Lam v1 (App exp1 exp2) exp) (App
  (case exp1 of
      (Let v2 body exp1') => (subst (freevars (Lam v1 body)) exp1')
      | _ => exp1)
  (case exp2 of
      (Let v3 body exp2') => (subst (freevars (Lam v1 body)) exp2')
      | _ => exp2))) ∧

(beta_rel (Lam v1 (Lam v2 exp)) (Lam v1 (Lam v2 exp))) ∧

(*letrec*)
(beta_rel (Lam v1 (Letrec pairList exp)) (Lam v1 (
  MAP (fn pair => subst (freevars (Lam v1 (SND pair))) exp) pairList))) ∧

(beta_rel (Lam v1 (Let (SOME v2) v2exp body))
  (Lam v1 (subst (freevars (Lam v1 body) v2exp)))) ∧ 

(*Seq case*)
(beta_rel (Lam v1 (Let NONE body1 body2)) (Lam v1 )) ∧ 

(beta_rel (Lam v1 (If exp1 exp2 exp3)) ((Lam v1 (If exp1 exp2 exp3)))) ∧ 

(beta_rel (Lam v1 (Delay exp)) (Lam v1 (Delay exp))) ∧

(beta_rel (Lam v1 (Force exp)) (Lam v1 (Force exp))) ∧

(*Value v cases*)
(beta_rel (Lam v1 (Value v)) (Lam v1 (
  case v of
    Constructor str vList => _
    | Monadic mop expList => _
    | Closure vname exp => _
    | Recclosure pairList vname => _
    | Thunk exp => _
    | Atom lit => _
    | DoTick t => _
  ))) ∧

(beta_rel (Lam v1 (MkTick exp)) (Lam v1 (MkTick exp))) ∧ 


(* TODO inductive cases*)
End
