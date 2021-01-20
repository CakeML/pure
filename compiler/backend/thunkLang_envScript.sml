(*
  An environment-based semantics for thunkLang.

  (The semantics in [thunkLang_substScript.sml] is substitution-based.)

 *)
open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory;
open thunkLangTheory;

val _ = new_theory "thunkLang_env";

Definition bind_funs_def:
  bind_funs funs env =
    MAP (λ(fn, _). (fn, Recclosure funs env fn)) funs ++ env
End

Definition dest_Closure_def:
  dest_Closure (Closure s env x) = return (s, env, x) ∧
  dest_Closure _ = fail Type_error
End

Definition dest_Thunk_def:
  dest_Thunk (Thunk env x) = return (env, x) ∧
  dest_Thunk _ = fail Type_error
End

Definition lookup_var_def:
  lookup_var env x =
    case ALOOKUP env x of
      NONE => fail Type_error
    | SOME v => return v
End

Definition dest_Recclosure_def:
  dest_Recclosure (Recclosure funs env fn) = return (funs, env, fn) ∧
  dest_Recclosure _ = fail Type_error
End

Definition dest_anyClosure_def:
  dest_anyClosure v =
    dest_Closure v ++
    do
      (funs, env, fn) <- dest_Recclosure v;
      (var, bod) <- lookup_var funs fn ;
      return (var, bind_funs funs env, bod)
    od
End

Definition get_lits_def:
  get_lits [] = return [] ∧
  get_lits (x::xs) =
    (do
       y <- case x of Atom l => return l | _ => fail Type_error ;
       ys <- get_lits xs ;
       return (y::ys)
     od)
End

Definition do_prim_def:
  do_prim op vs =
    case op of
      Cons s => return (Constructor s vs)
    | Proj s i =>
        (if LENGTH vs ≠ 1 then fail Type_error else
           case HD vs of
             Constructor t ys =>
               if t = s ∧ i < LENGTH ys then
                 return (EL i ys)
               else
                 fail Type_error
           | _ => fail Type_error)
    | IsEq s i =>
        (if LENGTH vs ≠ 1 then fail Type_error else
           case HD vs of
             Constructor t ys =>
               if t ≠ s then
                 return (Constructor "False" [])
               else if i = LENGTH ys then
                 return (Constructor "True" [])
               else
                 fail Type_error
           | _ => fail Type_error)
    | Lit l => if vs = [] then return (Atom l) else fail Type_error
    | AtomOp x =>
        do
          xs <- get_lits vs;
          case config.parAtomOp x xs of
            SOME v => return (Atom v)
          | NONE => fail Type_error
        od
End

(* TODO
 * - Overload fail Type_error and fail Diverge?
 *)

Definition eval_to_def:
  eval_to k env (Var n) = lookup_var env n ∧
  eval_to k env (Prim op xs) =
    (if k = 0n then fail Diverge else
       do
         vs <- map (eval_to (k - 1) env) xs;
         do_prim op vs
       od) ∧
  eval_to k env (App f x) =
    (if k = 0 then fail Diverge else
       do
         fv <- eval_to (k - 1) env f;
         xv <- eval_to (k - 1) env x;
         (s, env, body) <- dest_anyClosure fv ;
         eval_to (k - 1) ((s, xv)::env) body
       od) ∧
  eval_to k env (Lam s x) = return (Closure s env x) ∧
  eval_to k env (If x y z) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) env x;
         if v = Constructor "True" [] then
           eval_to (k - 1) env y
         else if v = Constructor "False" [] then
           eval_to (k - 1) env z
         else
           fail Type_error
       od) ∧
  eval_to k env (Letrec funs x) =
    (if k = 0 then fail Diverge else
       eval_to (k - 1) (bind_funs funs env) x) ∧
  eval_to k env (Delay x) = return (Thunk env x) ∧
  eval_to k env (Force x) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) env x;
         (env', body) <- dest_Thunk v;
         w <- eval_to (k - 1) env' body;
         if can dest_Thunk w then fail Type_error else return w
       od)
End

Definition eval_def:
  eval env x =
    case some k. eval_to k env x ≠ INL Diverge of
      NONE => fail Diverge
    | SOME k => eval_to k env x
End

val _ = export_theory ();

