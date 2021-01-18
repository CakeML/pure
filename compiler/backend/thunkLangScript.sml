
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory;

val _ = new_theory "thunkLang";

Type vname = “:string”;
Type op = “:pure_exp$op”;

Datatype:
  exp = Var vname                        (* variable                *)
      | Prim op (exp list)               (* primitive operations    *)
      | App exp exp                      (* function application    *)
      | Lam vname exp                    (* lambda                  *)
      | Letrec ((vname # exp) list) exp  (* mutually recursive exps *)
      | Delay exp                        (* creates a Thunk value   *)
      | Force exp                        (* evaluates a Thunk       *)
End


Datatype:
  v = Constructor string (v list)
    | Closure vname ((vname # v) list) exp
    | Thunk ((vname # v) list) exp
    | Atom lit
End

(*
 * thunkLang.
 * ~~~~~~~~~~
 *
 *  - Extends the pureLang syntax with “Delay” and “Force” in :exp, and
 *    “Thunk” in :v.
 *  - Call by value.
 *  - Environment semantics (avoids mutual recursion between exp and v;
 *    “Thunk env exp”).
 *)

Datatype:
  err = Type_error
      | Diverge
End

Definition dest_Closure_def:
  dest_Closure (Closure s env x) = SOME (s, env, x) ∧
  dest_Closure _ = NONE
End

(* TODO:
 * - Probably much neater to write this in the sum monad!
 * - Letrec
 * - At first I thought that “Force” should walk the expression and do
 *   something clever, but now I think it should just strip all “Delay”s
 *   in the expression, and then proceed to evaluate the expression as usual.
 *)

Definition force_def:
  force (App f x) = App (force f) (force x) ∧
  force _ = ARB
End

Definition eval_to_def:
  eval_to k env (Var n) = INL Type_error ∧
  eval_to k env (App f x) =
    (if k = 0n then INL Diverge else
       case eval_to (k - 1) env f of
         INL err => INL err
       | INR fv =>
           case eval_to (k - 1) env x of
             INL err => INL err
           | INR xv =>
             case dest_Closure fv of
               NONE => INL Type_error
             | SOME (s, env, body) =>
               eval_to (k - 1) ((s, xv)::env) body) ∧
  eval_to k env (Lam s x) = INR (Closure s env x) ∧
  eval_to k env (Letrec funs x) = ARB ∧
  eval_to k env (Delay x) = INR (Thunk env x) ∧
  eval_to k env (Force x) =
    if k = 0 then INL Diverge else eval_to (k - 1) env (force x)
End


val _ = export_theory ();

