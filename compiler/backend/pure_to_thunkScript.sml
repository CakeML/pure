(*
   A compiler from pureLang to envLang.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open listTheory rich_listTheory;
open pure_cexpTheory envLang_cexpTheory;

val _ = new_theory "pure_to_thunk"; (* TODO this name *)

Definition compile_exp_def:
  compile_exp (pure_cexp$Var a n) =
    Force a (envLang_cexp$Var a n) ∧
  compile_exp (Prim a op xs) =
    (case op, xs of
       Cons s, _ =>
         Prim a (Cons s) (MAP (λx. Delay a (compile_exp x)) xs)
     | AtomOp aop, _ =>
         Prim a (AtomOp aop) (MAP compile_exp xs)
     | Seq, [x1; x2] =>
         Let a NONE (compile_exp x1)
                    (compile_exp x2)
     | _ =>
         Prim a (Cons "") []) ∧
  compile_exp (App a f xs) =
    App a (compile_exp f)
          (MAP (λx. case x of
                      Var _ _ => compile_exp x
                    | _ => Delay a (compile_exp x)) xs) ∧
  compile_exp (Lam a vs x) =
    Lam a vs (compile_exp x) ∧
  compile_exp (Let a v x y) =
    Let a (SOME v)
          (compile_exp x)
          (compile_exp y) ∧
  compile_exp (Letrec a funs x) =
    Letrec a (MAP (λ(f,x).
                case x of
                  Lam _ _ _ => (f, compile_exp x)
                | _ => (f, Delay a (compile_exp x))) funs)
             (compile_exp x) ∧
  compile_exp (Case a x bv rows) =
    Case a (compile_exp x)
           bv
           (MAP (λ(v,vs,x). (v,vs,compile_exp x)) rows)
Termination
  WF_REL_TAC ‘measure (pure_cexp$cexp_size (K 0))’ \\ rw []
  \\ imp_res_tac cexp_size_lemma \\ gs []
  \\ first_x_assum (qspec_then ‘K 0 ’ mp_tac) \\ gs []
  \\ simp [pure_cexpTheory.cexp_size_def]
End

val _ = export_theory ();

