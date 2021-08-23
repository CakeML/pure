open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pure_inferenceTheory pure_inferenceLib;

val _ = new_theory "pure_inference_test";

(********************)

Definition example_2_exp_def[simp]:
  example_2_exp =
    pure_cexp$Lam () ["m"] $
      Let () "y" (Var () "m") $
        Let () "x" (App () (Var () "y") [Prim () (Cons "True") []]) $
         Var () "x"
End

Definition example_2_infer_def[simp]:
  example_2_infer = infer ([], [(0, [ ("True", []) ; ("False", []) ])])
                LN example_2_exp 0
End

Theorem example_2_infer:
  example_2_infer = SOME $
    ((Function (CVar 0) (CVar 1),
      fromList var_cmp [],
      [
        Unify () (CVar 0) (CVar 4);
        Implicit () (CVar 2) (LS ()) (CVar 4);
        Implicit () (CVar 1) (LS ()) (CVar 3);
        Unify () (CVar 2) (Function (PrimTy Bool) (CVar 3))
      ]), 5)
Proof
  simp[] >> CONV_TAC pure_infer_eval
QED

Definition example_2_solve_def[simp]:
  example_2_solve =
    let ((t, _, cs), cvs) = THE example_2_infer in
    (t, solve cs cvs)
End

Theorem example_2_solve:
  example_2_solve = (
    Function (CVar 0) (CVar 1),
    SOME (
      [
        FEMPTY |+ (0,CVar 4); FEMPTY |+ (2,CVar 4);
        FEMPTY |+ (4,Function (PrimTy Bool) (CVar 3));
        FEMPTY |+ (1,CVar 3)
      ],
      5)
  )
Proof
  simp[] >> CONV_TAC pure_infer_eval
QED

Definition example_2_solved_def[simp]:
  example_2_solved =
    let (t, res) = example_2_solve in
    let (subs, _) = THE res in
    subst_solution subs t
End

Theorem example_2_solved:
  example_2_solved = Function (Function (PrimTy Bool) (CVar 3)) (CVar 3)
Proof
  simp[] >> CONV_TAC pure_infer_eval
QED

(********************)

val _ = export_theory();
