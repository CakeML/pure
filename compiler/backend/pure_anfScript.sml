(*
   Defines A-normal-form (ANF) for pure_lang.
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory mlmapTheory mlstringTheory
     pure_varsTheory;

val _ = new_theory "pure_anf";


(* definition of ANF syntax *)

Datatype:
  anf = Var vname                            (* var *)
      | If vname anf anf                     (* if *)
      | Seq (*intentional:*)exp anf          (* exp strict in rest *)
      | Let vname op (vname list) anf        (* let v = op vars in rest *)
      | LetApp vname vname (vname list) anf  (* let v = f vars in rest *)
      | LetLam vname (vname list) anf anf    (* non-recursive function *)
      | Letrec ((vname # anf) list) anf      (* recursive bindings *)
End  (* above, note that, in the Let case, op should not be If or Seq *)

Triviality anf_size_lemma:
  ∀xs n x. MEM (n,x) xs ⇒ anf_size x ≤ anf1_size xs
Proof
  Induct \\ ntac 2 (rw [fetch "-" "anf_size_def"]) \\ res_tac \\ fs []
QED


(* we use ANF as rigid way of writing normal pure_lang expressions exp *)

Definition Apps_def:
  Apps f [] = f ∧
  Apps f (x::xs) = Apps (App f x) xs
End

Definition Lams_def:
  Lams [] b = b ∧
  Lams (x::xs) b = Lam x (Lams xs b)
End

Definition exp_of_def:
  exp_of ((Var v) : anf)   = ((Var v):exp) ∧
  exp_of (If v x y)        = If (Var v) (exp_of x) (exp_of y) ∧
  exp_of (Seq e x)         = Seq e (exp_of x) ∧
  exp_of (Let v p vs x)    = Let v (Prim p (MAP Var vs)) (exp_of x) ∧
  exp_of (LetApp v f vs x) = Let v (Apps (Var f) (MAP Var vs)) (exp_of x) ∧
  exp_of (LetLam v vs b x) = Let v (Lams vs (exp_of b)) (exp_of x) ∧
  exp_of (Letrec xs y)     = Letrec (MAP (λ(n,x). (n, exp_of x)) xs) (exp_of y)
Termination
  WF_REL_TAC ‘measure anf_size’ \\ rw []
  \\ imp_res_tac anf_size_lemma \\ fs []
End

(*

TODO: to write a function anf_of and prove:

  ∀e. e ≅ exp_of (anf_of e)

The anf function should use var_set from pure_varsTheory to represent
a set of variable names for efficiency, since anf_of is part of the
implementation of the compiler.

Every Let in the generated anf ought to bind a unqiue name. Ideally,
all new names should have a recognisable prefix like "." so that we
can easily see which names are generated.

Note that LetApp and LetLam should try to maximize the number of
arguments, e.g.

  LetApp v f [x; y; z] rest

instead of:

  LetApp v f [x] (LetApp v' v [y] (LetApp v'' v' [z] rest))

Similarly LetLam should bind as many variables as possible in the Lam.

The following should also hold:

  freevars (exp_of (anf_of e)) = freevars e

*)


val _ = export_theory();
