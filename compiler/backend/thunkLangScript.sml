(*
   thunkLang.
   ~~~~~~~~~~

   thunkLang is the next language in the compiler after pureLang.
   - It has a call-by-value semantics.
   - It extends the pureLang syntax with explicit syntax for delaying and
     forcing computations (“Delay” and “Force”) and “Thunk” values.
   - This version has an environment-based semantics. See
     [thunkLang_substScript.sml] for a substitution-based version.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory thunkLang_primitivesTheory;

val _ = new_theory "thunkLang";

val _ = numLib.prefer_num();

Type vname = “:string”;
Type op = “:pure_exp$op”;

Datatype:
  exp = Var vname                                (* variable                *)
      | Prim op (exp list)                       (* primitive operations    *)
      | App exp exp                              (* function application    *)
      | Lam vname exp                            (* lambda                  *)
      | Letrec ((vname # vname # exp) list) exp  (* mutually recursive exps *)
      | If exp exp exp                           (* if-then-else            *)
      | Delay bool exp                           (* delays a computation    *)
      | Force exp                                (* evaluates a Thunk       *)
End

Datatype:
  v = Constructor string (v list)
    | Closure vname ((vname # v) list) exp
    | Recclosure ((vname # vname # exp) list) ((vname # v) list) vname
    | Thunk bool v
    | Atom lit
End

Definition bind_funs_def:
  bind_funs funs env =
    MAP (λ(fn, _). (fn, Recclosure funs env fn)) funs ++ env
End

Definition dest_Closure_def:
  dest_Closure (Closure s env x) = return (s, env, x) ∧
  dest_Closure _ = fail Type_error
End

Definition dest_Thunk_def:
  dest_Thunk (Thunk nf x) = return (nf, x) ∧
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
    | If => fail Type_error
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

Definition unit_def:
  unit = Constructor "" []
End

Definition eval_to_def:
  eval_to k env (Var n) = lookup_var env n ∧
  eval_to k env (Prim op xs) =
    (if k = 0 then fail Diverge else
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
  eval_to k env (Delay b x) =
    (if k = 0 then fail Diverge else
       do
        v <- eval_to (k - 1) env x;
        return (Thunk b v)
      od) ∧
  eval_to k env (Force x) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) env x;
         (nf, w) <- dest_Thunk v;
         if nf then return w else
           do
             (s, env', body) <- dest_Closure w;
             eval_to (k - 1) ((s, unit)::env') body
           od
       od)
End

Definition eval_def:
  eval env x =
    case some k. eval_to k env x ≠ INL Diverge of
      NONE => fail Diverge
    | SOME k => eval_to k env x
End

Definition freevars_def:
  freevars (Var n) = {n} ∧
  freevars (Prim op xs) = (BIGUNION (set (MAP freevars xs))) ∧
  freevars (If x y z)  = freevars x ∪ freevars y ∪ freevars z ∧
  freevars (App x y) = freevars x ∪ freevars y ∧
  freevars (Lam s b)   = freevars b DIFF {s} ∧
  freevars (Letrec f x) =
    freevars x DIFF set (MAP FST f ++ MAP (FST o SND) f) ∧
  freevars (Delay f x) = freevars x ∧
  freevars (Force x) = freevars x
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ fs [] \\ gen_tac
  \\ Induct \\ rw []
  \\ res_tac
  \\ fs [fetch "-" "exp_size_def"]
End

Definition closed_def:
  closed e ⇔ freevars e = ∅
End

val _ = export_theory ();

