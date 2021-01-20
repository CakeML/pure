(*
   thunkLang.
   ~~~~~~~~~~

    - Extends the pureLang syntax with “Delay” and “Force” in :exp, and
      “Thunk” in :v.
    - Call by value.
    - Environment semantics (avoids mutual recursion between exp and v;
      “Thunk env exp”).
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory;

val _ = new_theory "thunkLang";

Type vname = “:string”;
Type op = “:pure_exp$op”;

Datatype:
  exp = Var vname                                (* variable                *)
      | Prim op (exp list)                       (* primitive operations    *)
      | App exp exp                              (* function application    *)
      | Lam vname exp                            (* lambda                  *)
      | Letrec ((vname # vname # exp) list) exp  (* mutually recursive exps *)
      | If exp exp exp                           (* if-then-else            *)
      | Delay exp                                (* creates a Thunk value   *)
      | Force exp                                (* evaluates a Thunk       *)
End

Datatype:
  v = Constructor string (v list)
    | Closure vname ((vname # v) list) exp
    | Recclosure ((vname # vname # exp) list) ((vname # v) list) vname
    | Thunk ((vname # v) list) exp
    | Atom lit
End

Datatype:
  err = Type_error
      | Diverge
End

(* TODO
 * - Declare data type with e.g. Error | Result
 *   for readability
 *)

Definition sum_bind_def:
  sum_bind m f =
    case m of
      INL e => INL e
    | INR x => f x
End

Definition sum_ignore_bind_def:
  sum_ignore_bind m x = sum_bind m (K x)
End

Definition sum_choice_def:
  sum_choice (m1: 'a + 'b) (m2: 'a + 'b) =
    case m1 of
      INL _ => m2
    | INR _ => m1
End

val sum_monadinfo : monadinfo = {
  bind = “sum_bind”,
  ignorebind = SOME “sum_ignore_bind”,
  unit = “INR: 'b -> 'a + 'b”,
  fail = SOME “INL: 'a -> 'a + 'b”,
  choice = SOME “sum_choice”,
  guard = NONE
  };

val _ = declare_monad ("sum", sum_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "sum";

Definition map_def:
  map f [] = return [] ∧
  map f (x::xs) =
    do
      y <- f x;
      ys <- map f xs;
      return (y::ys)
    od
End

Definition can_def:
  can f x =
    case f x of
      INL _ => F
    | INR _ => T
End

val _ = export_theory ();

