open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pure_inferenceTheory pure_inferenceLib;

val _ = new_theory "pure_inference_test";

(********************)

Definition parse_and_infer_def:
  parse_and_infer parse ns str =
    let parsed = parse str in do
      (ty, as, cs) <- infer ns LN parsed;
      if ¬ null as then fail else return ();
      subs <- solve cs;
      sub_ty <<- subst_solution subs ty;
      (vars, _, gen_ty) <<- generalise 0 0 LN FEMPTY sub_ty;
      res_ty <- oreturn $ type_of gen_ty;
      return (vars, res_ty)
    od 0
End

Definition option_datatype_def[simp]:
  option_datatype : typedef = (1n, [("Nothing", []); ("Just", [TypeVar 0])])
End

Definition nat_datatype_def[simp]:
  nat_datatype nat_id : typedef = (0n, [("Z", []) ;("S", [TypeCons nat_id []])])
End

Definition list_datatype_def[simp]:
  list_datatype list_id : typedef =
    (1n, [("Nil", []); ("Cons", [TypeVar 0; TypeCons list_id [TypeVar 0]])])
End

Definition simple_ns_def[simp]:
  simple_ns = (
    [] : exndef , (* no exceptions *)
    [option_datatype; nat_datatype 1; list_datatype 2] (* options, nats, lists *)
  )
End

(********************)

Definition example_2_def[simp]:
  example_2 = "(lam (m) (let y m (let x (app y (cons True)) x)))"
End

Definition example_2_exp_def[simp]:
  example_2_exp = parse_cexp example_2
End

Theorem example_2_exp:
  example_2_exp =
    pure_cexp$Lam () ["m"] $
      Let () "y" (Var () "m") $
        Let () "x" (App () (Var () "y") [Prim () (Cons "True") []]) $
         Var () "x"
Proof
  simp[] >> CONV_TAC pure_parse_infer_eval
QED

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
  simp[] >> CONV_TAC pure_parse_infer_eval
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
  simp[] >> CONV_TAC pure_parse_infer_eval
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
  simp[] >> CONV_TAC pure_parse_infer_eval
QED

Theorem example_2_overall:
  parse_and_infer parse_cexp simple_ns example_2 =
  return (1, Function (Function (PrimTy Bool) (TypeVar 0)) (TypeVar 0)) 5
Proof
  simp[parse_and_infer_def] >> CONV_TAC pure_parse_infer_eval
QED

(********************)

val _ = export_theory();
