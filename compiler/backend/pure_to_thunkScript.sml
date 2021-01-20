(*
   A compiler from pureLang to thunkLang.

   - Moves from a substitution-based (probably) call-by-need semantics
     to an environment-based (probably) call-by-value semantics with
     explicit Delay/Force expressions.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open listTheory rich_listTheory;
open pure_expTheory thunkLangTheory;

val _ = new_theory "pure_to_thunk";

(*
 * The source language is call-by-need and the target language is call-by-value.
 * The difference between the two styles becomes apparent in value bindings
 * (letrecs) and function application:
 * - The compiler assumes that all Letrec expressions are already transformed
 *   into lambdas. That is, all non-functional declarations such as “let v = 8”
 *   have been turned into “let v = λu. 8” and all references to “v” have been
 *   changed into “v ()”.
 * - At function application sites, the compiler wraps the argument with the
 *   “Delay” constructor (essentially turning it into a thunk).
 * - The compiler inserts “Force” constructors <in some places> TODO
 * Other differences:
 * - If is a primitive operation (i.e. a “Prim”) in pureLang, but has become
 *   an expression in thunkLang.
 *)

(* TODO
 * pure_exp theorem.
 *)
Theorem exp_size_MEM:
  MEM x xs ⇒ exp_size x < exp3_size xs
Proof
  Induct_on ‘xs’ \\ rw []
  \\ fs [pure_expTheory.exp_size_def]
QED

Definition compile_exp_def:
  compile_exp (Var n : pure_exp$exp) = thunkLang$Var n ∧
  compile_exp (Prim op xs) =
    (if op = If ∧ LENGTH xs = 3 then
       If (compile_exp (EL 0 xs))
          (compile_exp (EL 1 xs))
          (compile_exp (EL 2 xs))
     else
       Prim op (MAP compile_exp xs)) ∧
  compile_exp (App x y) = App (compile_exp x) (Delay (compile_exp y)) ∧
  compile_exp (Lam v x) = Lam v (compile_exp x) ∧
  compile_exp (Letrec funs x) =
    Letrec (MAP (λ(fn, x). case x of Lam v bod =>
                             (fn, v, compile_exp bod)) funs)
           (compile_exp x)
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ dsimp [pure_expTheory.exp_size_def, LENGTH_EQ_NUM_compute]
  \\ rw []
  >- (
    rename1 ‘MEM _ xs’
    \\ Induct_on ‘xs’ \\ rw []
    \\ fs [pure_expTheory.exp_size_def])
  \\ drule exp_size_MEM \\ fs []
End

val _ = export_theory ();

