(*
  Semantics primitives shared between [thunkLangScript.sml] and
  [thunkLang_substScript.sml].

 *)
open HolKernel Parse boolLib bossLib term_tactic monadsyntax
     sumTheory;

val _ = new_theory "thunkLang_primitives";

Datatype:
  err = Type_error
      | Diverge
End

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

Definition return_def[simp]:
  return = INR
End

Definition fail_def[simp]:
  fail = INL
End

val sum_monadinfo : monadinfo = {
  bind = “sum_bind”,
  ignorebind = SOME “sum_ignore_bind”,
  unit = “return”,
  fail = SOME “fail”,
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

