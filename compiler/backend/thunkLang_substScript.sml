(*
  A substitution-based semantics for thunkLang.

  (The semantics in [thunkLang_envScript.sml] is environment-based.)

 *)
open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory;
open thunkLangTheory;

val _ = new_theory "thunkLang_subst";

Datatype:
  v = Constructor string (v list)
    | Closure vname exp
    | Thunk exp
    | Atom lit
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

Definition dest_Closure_def:
  dest_Closure (Closure s x) = return (s, x) ∧
  dest_Closure _ = fail Type_error
End

Definition dest_Thunk_def:
  dest_Thunk (Thunk x) = return x ∧
  dest_Thunk _ = fail Type_error
End

Definition bind_def:
  bind name val bod = Var ""
End

Definition bind_funs_def:
  bind_funs funs bod = Var ""
End

Definition eval_to_def:
  eval_to k (Var n) = fail Type_error ∧
  eval_to k (Prim op xs) =
    (if k = 0n then fail Diverge else
       do
         vs <- map (eval_to (k - 1)) xs;
         do_prim op vs
       od) ∧
  eval_to k (App f x) =
    (if k = 0 then fail Diverge else
       do
         fv <- eval_to (k - 1) f;
         xv <- eval_to (k - 1) x;
         (s, body) <- dest_Closure fv ;
         eval_to (k - 1) (bind s xv body)
       od) ∧
  eval_to k (Lam s x) = return (Closure s x) ∧
  eval_to k (If x y z) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) x;
         if v = Constructor "True" [] then
           eval_to (k - 1) y
         else if v = Constructor "False" [] then
           eval_to (k - 1) z
         else
           fail Type_error
       od) ∧
  eval_to k (Letrec funs x) =
    (if k = 0 then fail Diverge else
       eval_to (k - 1) (bind_funs funs x)) ∧
  eval_to k (Delay x) = return (Thunk x) ∧
  eval_to k (Force x) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) x;
         y <- dest_Thunk v;
         w <- eval_to (k - 1) y;
         if can dest_Thunk w then fail Type_error else return w
       od)
End

Definition eval_def:
  eval x =
    case some k. eval_to k x ≠ INL Diverge of
      NONE => fail Diverge
    | SOME k => eval_to k x
End

val _ = export_theory ();

