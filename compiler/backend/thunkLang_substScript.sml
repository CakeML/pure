(*
   thunkLang.
   ~~~~~~~~~~

   thunkLang is the next language in the compiler after pureLang.
   - It has a call-by-value semantics.
   - It extends the pureLang syntax with explicit syntax for delaying and
     forcing computations (“Delay” and “Force”) and “Thunk” values.
   - This version has a substitution-based semantics. See
     [thunkLangScript.sml] for an environment-based version.
 *)
open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory thunkLang_primitivesTheory;

val _ = new_theory "thunkLang_subst";

Datatype:
  exp = Var vname                                (* variable                *)
      | Prim op (exp list)                       (* primitive operations    *)
      | App exp exp                              (* function application    *)
      | Lam vname exp                            (* lambda                  *)
      | Letrec ((vname # vname # exp) list) exp  (* mutually recursive exps *)
      | If exp exp exp                           (* if-then-else            *)
      | Delay exp                                (* creates a Thunk value   *)
      | Force exp                                (* evaluates a Thunk       *)
      | Value v;                                 (* for substitution        *)

  v = Constructor string (v list)
    | Closure vname exp
    | Thunk exp
    | Atom lit
End

val exp_size_def = fetch "-" "exp_size_def";

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

Definition dest_Closure_def:
  dest_Closure (Closure s x) = return (s, x) ∧
  dest_Closure _ = fail Type_error
End

Definition dest_Thunk_def:
  dest_Thunk (Thunk x) = return x ∧
  dest_Thunk _ = fail Type_error
End

Definition freevars_def:
  freevars (Var n) = {n} ∧
  freevars (Prim op xs) = (BIGUNION (set (MAP freevars xs))) ∧
  freevars (If x y z)  = freevars x ∪ freevars y ∪ freevars z ∧
  freevars (App x y) = freevars x ∪ freevars y ∧
  freevars (Lam s b)   = freevars b DIFF {s} ∧
  freevars (Letrec f x) =
    freevars x DIFF set (MAP FST f ++ MAP (FST o SND) f) ∧
  freevars (Delay x) = freevars x ∧
  freevars (Force x) = freevars x ∧
  freevars (Value v) = ∅ (* TODO Think about this later *)
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ fs [] \\ gen_tac
  \\ Induct \\ rw []
  \\ res_tac
  \\ fs [exp_size_def]
End

Definition closed_def:
  closed e ⇔ freevars e = ∅
End

Definition subst_def:
  subst m (Var s) =
    (case FLOOKUP m s of
       NONE => Var s
     | SOME x => x) ∧
  subst m (Prim op xs) = Prim op (MAP (subst m) xs) ∧
  subst m (If x y z) =
    If (subst m x) (subst m y) (subst m z) ∧
  subst m (App x y) = App (subst m x) (subst m y) ∧
  subst m (Lam s x) = Lam s (subst (m \\ s) x) ∧
  subst m (Letrec f x) =
    (let m1 = FDIFF m (set (MAP FST f ++ MAP (FST o SND) f)) in
      Letrec (MAP (λ(f,x,e). (f,x,subst m1 e)) f) (subst m1 x)) ∧
  subst m (Delay x) = Delay (subst m x) ∧
  subst m (Force x) = Force (subst m x) ∧
  subst m (Value v) = Value v (* TODO Think about this later *)
Termination
  WF_REL_TAC `measure (exp_size o SND)` \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
End

Overload subst1 = “λname v e. subst (FEMPTY |+ (name,v)) e”;

Definition bind_def:
  bind m e =
    if (∀n v. FLOOKUP m n = SOME v ⇒ closed v) then
      return (subst m e)
    else
      fail Type_error
End

Overload bind1 = “λname v e. bind (FEMPTY |+ (name,v)) e”;

Definition subst_funs_def:
  subst_funs f = bind (FEMPTY |++ (MAP (λ(g,v,x). (g, Letrec f x)) f))
End

Definition eval_to_def:
  eval_to k (Value v) = return v ∧
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
         y <- bind1 s (Value xv) body;
         eval_to (k - 1) y
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
       do
         y <- subst_funs funs x;
         eval_to (k - 1) y
       od) ∧
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

