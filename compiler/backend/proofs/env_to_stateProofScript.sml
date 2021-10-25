(*
  Correctness for compilation from envLang to stateLang
 *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory
open pure_exp_lemmasTheory pure_miscTheory pure_configTheory
     envLangTheory thunkLang_primitivesTheory envLang_cexpTheory
     stateLangTheory;

val _ = new_theory "env_to_stateProof";

Overload "app" = ``λe1 e2. App AppOp [e1;e2]``;
Overload "cons0" = ``λs. App (Cons s) []``;

Definition Lets_def:
  Lets [] e = e ∧
  Lets ((x,a)::rest) e = stateLang$Let x a (Lets rest e)
End

(****************************************)

(*
  We don't seem to be able to remain error-preserving in both directions here,
  as `envLang$Cons "bind" _` etc. become lambdas in stateLang.
  As a result, `App (thinkLang$Cons "bind" _) _` gives an error, whereas
  `App (Lam _ _) _` succeeds.

  Note that we expect the arguments to `envLang$Cons _` to be `Delay`-wrapped
  things, allowing us to "force" them by removing the `Delay`.
*)

Inductive compile_rel:

[~Var:]
  compile_rel (envLang$Var v) (stateLang$Var v) ∧

[~Ret:]
  (compile_rel te se ∧ u ∉ freevars se ⇒
  compile_rel (Prim (Cons "Ret") [Delay te]) (Lam u se)) ∧

[~Bind:]
  (compile_rel te1 se1 ∧ compile_rel te2 se2 ∧
   u ∉ freevars se1 ∪ freevars se2 ∧ x ∉ freevars se2 ∧ u ≠ x ⇒
  compile_rel
    (Prim (Cons "Bind") [Delay te1; Delay te2])
    (Lam u $ App AppOp
      [Lam x (app (app se2 (Var x)) (Var u)); app se1 (Var u)])) ∧
(*
  e.g.
    Ret (Delay a)   -->   Lam "u". a'
    Lam "x". Ret (Delay "x")   --> Lam "x". Lam "u". "x"
  so consider `return a >>= (λx. return x)`:
      Bind (Delay $ Ret (Delay a)) (Delay $ Lam "x". Ret (Delay "x")):
  --> Lam "u". (Lam "x". (Lam "x". Lam "u". "x") "x" "u") ((Lam "u". a') "u")
*)

[~Raise:]
  (compile_rel te se ∧
   u ∉ freevars se ⇒
  compile_rel (Prim (Cons "Raise") [Delay te]) (Lam u $ Raise se)) ∧

[~Handle:]
  (compile_rel te1 se1 ∧ compile_rel te2 se2 ∧
   u ∉ freevars se1 ∪ freevars se2 ∧ x ∉ freevars se2 ∧ u ≠ x ⇒
  compile_rel
    (Prim (Cons "Handle") [Delay te1; Delay te2])
    (Lam u $ Handle (app se1 (Var u)) x (app (app se2 (Var x)) (Var u)))) ∧

[~Alloc:]
  (LIST_REL compile_rel tes ses ∧
   EVERY (λse. u ∉ freevars se) ses ⇒
  compile_rel (Prim (Cons "Alloc") (MAP Delay tes)) (Lam u $ App Alloc ses)) ∧

[~Length:]
  (LIST_REL compile_rel tes ses ∧
   EVERY (λse. u ∉ freevars se) ses ⇒
  compile_rel (Prim (Cons "Length") (MAP Delay tes)) (Lam u $ App Length ses)) ∧

[~Deref:]
  (LIST_REL compile_rel tes ses ∧
   EVERY (λse. u ∉ freevars se) ses ⇒
  compile_rel (Prim (Cons "Deref") (MAP Delay tes)) (Lam u $ App Sub ses)) ∧

[~Update:]
  (LIST_REL compile_rel tes ses ∧
   EVERY (λse. u ∉ freevars se) ses ⇒
  compile_rel (Prim (Cons "Update") (MAP Delay tes)) (Lam u $ App Update ses)) ∧

[~Act:]
  (compile_rel te se ∧
   u ∉ freevars se ⇒
  compile_rel (Prim (Cons "Act") [Delay te]) (Lam u $ app se (Var u))) ∧

[~Cons:]
  (LIST_REL compile_rel tes ses ∧
   s ∉ monad_cns ⇒
  compile_rel (Prim (Cons s) tes) (App (Cons s) ses)) ∧

[~Case:]
  (compile_rel te se ∧
   MAP FST tcss = MAP FST scss ∧
   MAP (FST o SND) tcss = MAP (FST o SND) scss ∧
   LIST_REL (λ(_,_,te) (_,_,se). compile_rel te se) tcss scss ⇒
  compile_rel (Let (SOME v) te (rows_of v tcss)) (Case se v scss)) ∧

[~Message:]
  (compile_rel te se ∧ u ≠ x ⇒
  compile_rel
    (Prim (AtomOp (Message s)) [te])
    (Let (SOME x) se $ Lam u $ App (FFI s) [Var x])) ∧

[~AtomOp:]
  (LIST_REL compile_rel tes ses ∧
   (∀s. aop ≠ Message s) ⇒
  compile_rel (Prim (AtomOp aop) tes) (App (AtomOp aop) ses)) ∧

[~App:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (App te1 te2) (App AppOp [se1;se2])) ∧

[~Lam:]
  (compile_rel te se ⇒
   compile_rel (Lam x te) (Lam x se)) ∧

[~Letrec:]
  (ALL_DISTINCT (MAP FST tfns) ∧
   letrec_funs_rel (freevars (Letrec fns te) ∪ set (MAP FST fns)) tfns sfns sets ∧
   compile_rel te se
  ⇒ compile_rel
      (Letrec fns te)
      (Lets
        (MAP (λ(fn,_). (SOME fn, ref (inl (Lam u (Raise $ cons0 TODO))))) fns) $
        stateLang$Letrec sfns $ Sets sets se)) ∧

[~Let:]
  (compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (Let x_opt te1 te2) (Let x_opt se1 se2)) ∧

[~If:]
  (compile_rel te se ∧
   compile_rel te1 se1 ∧
   compile_rel te2 se2 ⇒
  compile_rel (If te te1 te2) (If se se1 se2)) ∧

[~Delay:]
  (compile_rel te se ∧
   u ∉ freevars se ⇒
  compile_rel (Delay te) (App Ref [inl $ Lam u se])) ∧

[~Box:]
  (compile_rel te se ⇒
  compile_rel (Box te) (App Ref [inr se])) ∧

[~Force:]
  (compile_rel te se ⇒
  compile_rel (Force te) (App AppOp [force; se])) ∧

  letrec_funs_rel fvs [] [] [] ∧

  (letrec_funs_rel fvs tfns sfns sets ∧ compile_rel te se ∧
   f_fn ∉ fvs ∧ u ∉ freevars se ⇒
  letrec_funs_rel fvs
    ((f, Delay te)::tfns) ((f_fn, u, se)::sfns) ((Var f, inl (Var f_fn))::sets)) ∧

  (letrec_funs_rel fvs tfns sfns sets ∧ compile_rel te se ⇒
   letrec_funs_rel fvs
    ((f, Lam x te)::tfns) ((f, x, se)::sfns) ((Var f, inl (Var f))::sets)) ∧

  (letrec_funs_rel fvs tfns sfns sets ∧ compile_rel te se ⇒
  letrec_funs_rel fvs ((f, Box te)::tfns) sfns ((Var f, inr se)::sets))

End
(* TODO HOL gives "index too large" error if below comment is
   within Inductive ... End and does not name all rules *)

  (*
    In general, we have:
      envLang$Letrec [(x, y); ...] e
    -->
      Let x (Ref (INL (fn u => Raise Bind))) ... (* declare all references *)
      Letrec [...] (* use the bindings *)
        (x := INL (fn u => y); ...) (* update the references *)

  As `y` can only be `Box`, `Delay`, or `Lam`:
      envLang$Letrec [(x, Lam a b); ...] e
    -->
      Let x (Ref _) ... (Letrec [(x, a, b'); ...] (x := INL x; ...; e'))

      envLang$Letrec [(x, Delay d); ...] e
    -->
      Let x (Ref _) ... (Letrec [(fresh1, fresh2, d'); ...] (x := INL fresh1; ...; e'))

      envLang$Letrec [(x, Box b); ...] e
    -->
      Let x (Ref _) ... (Letrec [...] (x := INR b'; ...; e'))
  *)


(* TODO *)
Inductive value_rel:
[~Constructor:]
  (LIST_REL (value_rel st) tvs svs ⇒
  value_rel st (envLang$Constructor s tvs) (stateLang$Constructor s svs)) ∧

[~Closure:]
  (MAP FST tenv = MAP FST senv ∧
   LIST_REL (value_rel st) (MAP SND tenv) (MAP SND senv) ∧
   compile_rel te se ⇒
  value_rel st (Closure x tenv te) (Closure x senv se)) ∧

[~ThunkL:]
  (value_rel st tv sv ∧
   oEL n st = SOME $ Constructor "INL" [sv] ⇒
  value_rel st (Thunk $ INL tv) (Atom $ Loc n)) ∧

[~ThunkR:]
  (MAP FST tenv = MAP FST senv ∧
   LIST_REL (value_rel st) (MAP SND tenv) (MAP SND senv) ∧
   compile_rel te se ∧
   x ∉ freevars se ∧
   oEL n st = SOME $ Constructor "INL" [Closure x senv se] ⇒
  value_rel st (Thunk $ INR (tenv, te)) (Atom $ Loc n)) ∧

[~Atom:]
  value_rel st (Atom a) (Atom a)
End


(******************** Notes ********************)

(*

  thunks are ((unit -> 'a) + 'a) ref

  envLang                       stateLang

  Prim (Cons "Ret") [x]       --> (fn u => App "force" (compile x ()))
  Prim (Cons "Bind") [x; y]   --> (fn u => Let v (compile x ()) (compile y () v))
  Prim (Cons "Handle") [x; y] --> (fn u => Handle (compile x ()) v (compile y () v))
  Prim (Msg ffi) [x]          --> (fn u => App (FFI ffi) [compile x])
  Prim (Cons "Act" [msg])     --> (fn u => compile msg ())

  Box x                       --> (Ref (Cons "INR" [(compile x)]))
  Delay x                     --> (Ref (Cons "INL" [fn u => (compile x) ()]))
  Force x                     --> force (compile x)

fun force t =
  case !t of
  | INL f => let val v = f () in (t := INR v; v) end
  | INR v => v


  env$Letrec [(x, y + 1); ...] rest

-->

  (* declare all references *)
  Let x (Ref (INL (fn u => Raise Bind)))
  (* use the bindings *)
  Letrec [...]
  (* update the references *)
    (x := INL (fn u => y + 1); compiler rest))



  step (Exp (LitInt i)) s c = (Val (Lit i), s, c)
  step (Exp (Raise x)) s c = (Exp x, s, RaiseC c)

  step (Val v) s (RaiseC (LetC ... c)) = (Val v, s, RaiseC c)

  eval exp s c = Act ffi msg s' c'



  env$semantics (Bind (Bind (Ret ...) (Bind ... (Act ...))))
~
  state$eval (fn _ => ...) ()

  eval : exp -> v

  itree_of : exp -> itree

  cakeml_semantics : exp -> io_oracle -> io_trace

*)

(****************************************)

val _ = export_theory ();
