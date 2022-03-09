(*
  Correctness for compilation that replaces Delay, Box, Force
  with stateful operations
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory arithmeticTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     stateLangTheory;

val _ = new_theory "state_unthunkProof";

val _ = set_grammar_ancestry ["stateLang"];

Overload "app" = “λe1 e2. App AppOp [e1;e2]”;

Overload True  = “App (Cons "True")  []”;
Overload False = “App (Cons "False") []”;

Overload True_v  = “stateLang$Constructor "True"  []”;
Overload False_v = “stateLang$Constructor "False" []”;

(****************************************)

Overload "box" = “λx. App Ref [True; x]”

Overload "delay" = “λx. App Ref [False; Lam NONE x]”

Overload "force" = “λx.
  Let (SOME "v") x $
  Let (SOME "v1") (App UnsafeSub [Var "v"; IntLit 0]) $
  Let (SOME "v2") (App UnsafeSub [Var "v"; IntLit 1]) $
    If (Var "v1") (Var "v2") $
      Let (SOME "a") (app (Var "v2") Unit) $
      Let NONE (App UnsafeUpdate [Var "v"; IntLit 0; True]) $
      Let NONE (App UnsafeUpdate [Var "v"; IntLit 1; Var "a"]) $
        Var "a"”

Inductive compile_rel:

[~Var:]
  compile_rel (stateLang$Var v) (stateLang$Var v) ∧

[~Lam:]
  (compile_rel x y ⇒
  compile_rel (Lam z x) (Lam z y)) ∧

[~Raise:]
  (compile_rel x y ⇒
  compile_rel (Raise x) (Raise y)) ∧

[~Handle:]
  (compile_rel x1 y1 ∧ compile_rel x2 y2 ⇒
  compile_rel (Handle x1 v x2) (Handle y1 v y2)) ∧

[~HandleApp:]
  (compile_rel x1 y1 ∧ compile_rel x2 y2 ⇒
  compile_rel (HandleApp x1 x2) (HandleApp y1 y2)) ∧

[~App:]
  (LIST_REL compile_rel xs ys ⇒
  compile_rel (App op xs) (App op ys)) ∧

[~Letrec:]
  (∀tfns sfns te se.
    MAP FST tfns = MAP FST sfns ∧
    LIST_REL compile_rel (MAP SND tfns) (MAP SND sfns) ∧
    compile_rel te se ⇒
    compile_rel (Letrec tfns te) (Letrec sfns se)) ∧

[~Let:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (Let x_opt te1 te2) (Let x_opt se1 se2)) ∧

[~If:]
  (compile_rel te se ∧
   compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (If te te1 te2) (If se se1 se2)) ∧

[~Box:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Box te) (box se)) ∧

[~Delay:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Delay te) (delay se)) ∧

[~Force:]
  (∀te se.
    compile_rel te se ⇒
    compile_rel (Force te) (force se))

End

Inductive v_rel:

[~Loc:]
  (∀p st n1 n2.
     FLOOKUP p n1 = SOME n2 ⇒
     v_rel p st (Atom (Loc n1)) (Atom (Loc n2))) ∧

[~Atom:]
  (∀p st a.
     (∀l. a ≠ Loc l) ⇒
     v_rel p st (Atom a) (Atom a)) ∧

[~Constructor:]
  (∀p st tvs svs.
     LIST_REL (v_rel p st) tvs svs ⇒
     v_rel p st (Constructor s tvs) (Constructor s svs)) ∧

[~Closure:]
  (∀p st tenv senv te se x.
     env_rel p st tenv senv ∧
     compile_rel te se ⇒
     v_rel p st (Closure x tenv te) (Closure x senv se)) ∧

[~Recclosure:]
  (∀p st tenv senv tfns sfns n.
     env_rel p st tenv senv ∧
     LIST_REL ((=) ### compile_rel) tfns sfns ⇒
     v_rel p st (Recclosure tfns tenv n) (Recclosure sfns senv n)) ∧

[~Thunk_True:]
  (∀p st tv sv n.
     v_rel p st tv sv ∧
     ~(n IN FRANGE p) ∧
     oEL n st = SOME [True_v; sv] ⇒
     v_rel p st (Thunk $ INL tv) (Atom (Loc n))) ∧

[~Thunk_False:]
  (∀tenv senv te se.
     env_rel p st tenv senv ∧
     compile_rel te se ∧
     ~(n IN FRANGE p) ∧
     oEL n st = SOME [False_v; Closure NONE senv se] ⇒
     v_rel p st (Thunk $ INR (tenv, te)) (Atom (Loc n))) ∧

[env_rel:]
  (∀p st tenv senv.
     (∀n tv.
       ALOOKUP tenv n = SOME tv ⇒
       ∃sv. ALOOKUP senv n = SOME sv ∧ v_rel p st tv sv) ⇒
     env_rel p st tenv senv)

End

Theorem env_rel_def = “env_rel p st tenv senv”
  |> SIMP_CONV (srw_ss()) [Once v_rel_cases];

val _ = export_theory ();
