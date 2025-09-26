Theory pure_inference_test
Ancestors
  pure_print pure_inference
Libs
  BasicProvers dep_rewrite pure_inferenceLib

(********************)

Definition solve_def:
  solve [] = return [] ∧

  solve cs = case get_solveable cs [] of
    | NONE =>
        let active = FOLDL (λacc c. union (activevars c) acc) LN cs in
        solve (MAP (monomorphise_implicit active) cs)

    | SOME $ (Unify d t1 t2, cs) => do
        sub <- oreturn (Internal : unit inferError) $ pure_unify FEMPTY t1 t2;
        cs' <<- MAP (subst_constraint sub) cs;
        solve_rest <- solve cs';
        return (sub :: solve_rest) od

    | SOME $ (Instantiate d t (vs, scheme), cs) => do
        freshes <- fresh_vars vs;
        inst_scheme <<- isubst (MAP CVar freshes) scheme;
        solve (Unify d t inst_scheme :: cs) od

    | SOME $ (Implicit d t1 vs t2, cs) => do
        (n, s, scheme) <<- generalise 0 vs FEMPTY t2;
        solve (Instantiate d t1 (n, scheme) :: cs) od
Termination
  WF_REL_TAC `measure $ λl. SUM $ MAP constraint_weight l` >>
  reverse $ rw[constraint_weight_def, listTheory.MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
  >- (
    rename [`c::cs`,`monomorphise_implicit active`] >>
    drule get_solveable_NONE >> rw[] >> last_x_assum kall_tac >>
    gvs[SF DNF_ss, monomorphise_implicit_def] >>
    pairarg_tac >> gvs[constraint_weight_def] >>
    irule $ DECIDE ``a ≤ b ⇒ a + 2 < b + 3n`` >>
    Induct_on `cs` >> rw[] >> gvs[SF DNF_ss, monomorphise_implicit_def] >>
    pairarg_tac >> gvs[constraint_weight_def]
    ) >>
  drule get_solveable_SOME >> strip_tac >> gvs[] >>
  Cases_on `left` >> gvs[listTheory.SUM_APPEND, constraint_weight_def]
End

Definition subst_solution_def:
  subst_solution [] ty = ty ∧
  subst_solution (s::ss) ty = subst_solution ss (pure_walkstar s ty)
End

Definition parse_and_infer_def:
  parse_and_infer parse ns str = do
      parsed <<- parse str;
      (ty, as, cs) <- infer ns LN parsed;
      if ¬ null as then fail Internal else return ();
      subs <- solve cs;
      sub_ty <<- subst_solution subs ty;
      (vars, _, gen_ty) <<- generalise 0 LN FEMPTY sub_ty;
      res_ty <- oreturn Internal $ type_of gen_ty;
      return (vars, res_ty)
    od 0
End

(* do `k` steps of `solve`, for debugging purposes *)
Definition solve_k_def:
  solve_k 0 cs = return (ARB "Timeout" cs) ∧
  solve_k _ [] = return [] ∧

  solve_k (SUC n) cs = case get_solveable cs [] of
    | NONE =>
        let active = FOLDL (λacc c. union (activevars c) acc) LN cs in
        solve_k n (MAP (monomorphise_implicit active) cs)

    | SOME $ (Unify d t1 t2, cs) => do
        sub <- oreturn Internal $ pure_unify FEMPTY t1 t2;
        cs' <<- MAP (subst_constraint sub) cs;
        solve_rest <- solve_k n cs';
        return (sub :: solve_rest) od

    | SOME $ (Instantiate d t (vs, scheme), cs) => do
        freshes <- fresh_vars vs;
        inst_scheme <<- isubst (MAP CVar freshes) scheme;
        solve_k (SUC n) (Unify d t inst_scheme :: cs) od

    | SOME $ (Implicit d t1 vs t2, cs) => do
        (nvs, s, scheme) <<- generalise 0 vs FEMPTY t2;
        solve_k (SUC n) (Instantiate d t1 (nvs, scheme) :: cs) od
Termination
  WF_REL_TAC `inv_image ($< LEX $<) $ λ(k,l). (k, SUM $ MAP constraint_weight l)` >>
  rw[constraint_weight_def, listTheory.MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  drule get_solveable_SOME >> strip_tac >> gvs[] >>
  Cases_on `left` >> gvs[listTheory.SUM_APPEND, constraint_weight_def]
End

Definition parse_and_get_constraints_def:
  parse_and_get_constraints parse ns str = do
      parsed <<- parse str;
      (ty, as, cs) <- infer ns LN parsed;
      if ¬ null as then fail Internal else return (ty, cs)
    od 0
End

Definition parse_and_solve_k_def:
  parse_and_solve_k k parse ns str = do
      parsed <<- parse str;
      (ty, as, cs) <- infer ns LN parsed;
      if ¬ null as then fail Internal else return ();
      subs <- solve_k k cs;
      return subs
    od 0
End

Definition from_ok_def[simp]:
  from_ok (OK ok) = ok
End

fun debug_eval tm =
  let val cmp = pure_parse_infer_compset ()
      val _ = computeLib.extend_compset
                [computeLib.Defs [
                  fetch "-" "solve_def",
                  fetch "-" "subst_solution_def",
                  fetch "-" "solve_k_compute",
                  fetch "-" "parse_and_get_constraints_def",
                  fetch "-" "parse_and_solve_k_def",
                  fetch "-" "from_ok_def"
                  ]] cmp
  in (SIMP_CONV (srw_ss()) [parse_and_infer_def]
        THENC computeLib.CBV_CONV cmp) tm end;

Definition option_datatype_def[simp]:
  option_datatype : typedef = (1n, [(«Nothing», []); («Just», [TypeVar 0])])
End

Definition nat_datatype_def[simp]:
  nat_datatype nat_id : typedef = (0n, [(«Z», []) ;(«S», [TypeCons nat_id []])])
End

Definition list_datatype_def[simp]:
  list_datatype list_id : typedef =
    (1n, [(«Nil», []); («Cons», [TypeVar 0; TypeCons list_id [TypeVar 0]])])
End

Definition simple_ns_def[simp]:
  simple_ns = (
    [] : exndef , (* no exceptions *)
    [option_datatype; nat_datatype 1; list_datatype 2] (* bools, options, nats, lists *)
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
    pure_cexp$Lam () [«m»] $
      Let () «y» (Var () «m») $
        Let () «x» (App () (Var () «y») [Prim () (Cons «True») []]) $
         Var () «x»
Proof
  simp[] >> CONV_TAC debug_eval
QED

Definition example_2_infer_def[simp]:
  example_2_infer = infer simple_ns LN example_2_exp 0
End

Theorem example_2_infer:
  example_2_infer = OK $
    ((Function (CVar 0) (CVar 1),
      fromList var_cmp [],
      [
        Unify () (CVar 0) (CVar 0);
        Unify () (CVar 0) (CVar 4);
        Implicit () (CVar 2) (LS ()) (CVar 4);
        Implicit () (CVar 1) (LS ()) (CVar 3);
        Unify () (CVar 2) (Function (PrimTy Bool) (CVar 3))
      ]), 5)
Proof
  simp[] >> CONV_TAC debug_eval
QED

Definition example_2_solve_def[simp]:
  example_2_solve =
    let ((t, _, cs), cvs) = from_ok example_2_infer in
    (t, solve cs cvs)
End

Theorem example_2_solve:
  example_2_solve = (
    Function (CVar 0) (CVar 1),
    OK (
      [
        FEMPTY;
        FEMPTY |+ (0,CVar 4); FEMPTY |+ (2,CVar 4);
        FEMPTY |+ (4,Function (PrimTy Bool) (CVar 3));
        FEMPTY |+ (1,CVar 3)
      ],
      5)
  )
Proof
  simp[] >> CONV_TAC debug_eval
QED

Definition example_2_solved_def[simp]:
  example_2_solved =
    let (t, res) = example_2_solve in
    let (subs, _) = from_ok res in
    subst_solution subs t
End

Theorem example_2_solved:
  example_2_solved = Function (Function (PrimTy Bool) (CVar 3)) (CVar 3)
Proof
  simp[] >> CONV_TAC debug_eval
QED

Theorem example_2_overall:
  parse_and_infer parse_cexp simple_ns example_2 =
  return (1, Function (Function (PrimTy Bool) (TypeVar 0)) (TypeVar 0)) 5
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval
QED

(********************)

val add_str = toMLstring `
  (letrec
    (add (lam (x y)
      (case x temp
        ((((Z) y)
          ((S (xx)) (app add xx (cons S y)))) .
         NONE))))
    add)`;

Theorem add_str_type:
  parse_and_infer parse_cexp simple_ns ^add_str =
    return (0, Functions [TypeCons 1 []; TypeCons 1 []] (TypeCons 1 [])) 10
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval >> EVAL_TAC
QED

val add_str' = toMLstring ‘
  (letrec
    (add (lam (x y)
      (case x temp
        ((((S (xx)) (app add xx (cons S y)))) .
         (SOME ((Z 0)) y)))))
    add)
’;

Theorem add_str'_type:
  parse_and_infer parse_cexp simple_ns ^add_str' =
    return (0, Functions [TypeCons 1 []; TypeCons 1 []] (TypeCons 1 [])) 10
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval >> EVAL_TAC
QED

val even_odd_str = toMLstring `
  (letrec
    (even (lam (x)
      (case x temp
        ((((Z) (cons True))
          ((S (xx)) (app odd xx))) . NONE))))
    (odd (lam (x)
      (case x temp
        ((((Z) (cons False))
           ((S (xx)) (app even xx))) . NONE))))
    (cons 0 even odd))`;

Theorem even_odd_str_type:
  parse_and_infer parse_cexp simple_ns ^even_odd_str =
    return (0, Tuple [
      Function (TypeCons 1 []) (PrimTy Bool);
      Function (TypeCons 1 []) (PrimTy Bool)
      ]) 14
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval
QED

val ntimes_str = toMLstring `
  (letrec
    (o (lam (f g x) (app f (app g x))))

    (letrec

      (ntimes (lam (f n)
        (case n temp
          ((((Z) (lam (x) x))
            ((S (m)) (app o f (app ntimes f m)))) . NONE))))
      (cons 0 o ntimes)))`;

Theorem ntimes_str_type:
  parse_and_infer parse_cexp simple_ns ^ntimes_str =
    (* ∀α β γ δ.
          (α -> β) -> (γ -> α) -> γ -> β
          (δ -> δ) -> Nat -> (δ -> δ) *)
    return (4, Tuple [
      Functions [Function (TypeVar 0) (TypeVar 1);
                 Function (TypeVar 2) (TypeVar 0)]
        (Function (TypeVar 2) (TypeVar 1));
      Functions [Function (TypeVar 3) (TypeVar 3); TypeCons 1 []]
        (Function (TypeVar 3) (TypeVar 3))
      ]) 30
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval >> EVAL_TAC
QED

val curried_mult_str = toMLstring `
  (letrec
    (o (lam (f g x) (app f (app g x))))

  (letrec
    (ntimes (lam (f n)
      (case n temp
        ((((Z) (lam (x) x))
          ((S (m)) (app o f (app ntimes f m)))) . NONE))))
  (letrec
    (add (lam (x y)
      (case x temp
        ((((Z) y)
          ((S (xx)) (app add xx (cons S y)))) . NONE))))

  (letrec
    (mult (lam (x y) (app ntimes (app add x) y (cons Z))))

    mult))))`;

Theorem curried_mult_str_type:
  parse_and_infer parse_cexp simple_ns ^curried_mult_str =
    return (0, Functions [TypeCons 1 []; TypeCons 1 []] (TypeCons 1 [])) 43
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval >> EVAL_TAC
QED

(********************)

Definition even_nat_datatype_def[simp]:
  even_nat_datatype odd_nat_id : typedef =
    (0n, [(«Z», []) ;(«S», [TypeCons odd_nat_id []])])
End

Definition odd_nat_datatype_def[simp]:
  odd_nat_datatype even_nat_id : typedef =
    (0n, [(«O», [TypeCons even_nat_id []])])
End

Definition even_odd_ns_def[simp]:
  even_odd_ns = (
    [] : exndef , (* no exceptions *)
    [even_nat_datatype 1; odd_nat_datatype 0]
  )
End

val add_even_even_str = toMLstring `
  (letrec
    (add_ee (lam (e1 e2)
      (case e1 temp1
        ((((Z) e2)
          ((S (o1))
           (case o1 temp1
                    ((((O (e)) (cons S (cons O (app add_ee e e2))))) . NONE))))
         . NONE))))
    add_ee)`;

Theorem add_str_type[allow_rebind]:
  parse_and_infer parse_cexp even_odd_ns ^add_even_even_str =
    return (0, Functions [TypeCons 0 []; TypeCons 0 []] (TypeCons 0 [])) 12
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval >> EVAL_TAC
QED

val add_even_odd_nats_str = toMLstring `
  (letrec
    (add_ee (lam (e1 e2)
      (case e1 temp
        ((((Z) e2)
          ((S (o1)) (cons S (app add_eo e2 o1)))) . NONE))))

    (add_eo (lam (e o)
      (case e temp
        ((((Z) o)
          ((S (o1)) (cons O (app add_oo o1 o)))) . NONE))))

    (add_oo (lam (o1 o2)
      (case o1
            temp
            ((((O (e)) (cons S (app add_eo e o2)))) . NONE))))

  (cons 0 add_ee add_eo add_oo))`;

Theorem add_str_type[allow_rebind]:
  parse_and_infer parse_cexp even_odd_ns ^add_even_odd_nats_str =
    return (0, Tuple [
      Functions [TypeCons 0 []; TypeCons 0 []] (TypeCons 0 []);
      Functions [TypeCons 0 []; TypeCons 1 []] (TypeCons 1 []);
      Functions [TypeCons 1 []; TypeCons 1 []] (TypeCons 0 []);
      ]) 29
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval >> EVAL_TAC
QED

val length_poly_str = toMLstring `
  (letrec
    (length (lam (l)
      (case l temp
        ((((Nil) (int 0))
          ((Cons (h t)) (+ (int 1) (app length t)))) . NONE))))

  (cons 0
    (app length (cons Cons (int 0) (cons Nil)))
    (app length (cons Cons (cons True) (cons Nil)))
  ))`;

Theorem length_poly_str_type:
  parse_and_infer parse_cexp simple_ns ^length_poly_str =
    return (0, Tuple [PrimTy Integer; PrimTy Integer]) 17
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval >> EVAL_TAC
QED

val id_poly_str = toMLstring `
  (letrec
    (id (lam (x) x))
  (app id id))`;

Theorem id_poly_str_type:
  parse_and_infer parse_cexp simple_ns ^id_poly_str =
    return (1, Function (TypeVar 0) (TypeVar 0)) 7
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval >> EVAL_TAC
QED

val ntimes_poly_str = toMLstring `
  (letrec
    (id (lam (x) x))
    (letrec
      (ntimes (lam (f n x)
        (case n temp
          ((((Z) x)
            ((S (m)) (app f (app (app (app ntimes f) m) x)))) . NONE))))
      (cons 0
        ntimes
        (app (app (app ntimes id) (cons Z)) (cons True))
        (app (app (app ntimes id) (cons Z)) (cons Z))
        )))`;

Theorem ntimes_poly_str_type:
  parse_and_infer parse_cexp simple_ns ^ntimes_poly_str =
    return (1, Tuple [
      Functions
        [Function (TypeVar 0) (TypeVar 0); TypeCons 1 []]
        (Function (TypeVar 0) (TypeVar 0));
      PrimTy Bool;
      TypeCons 1 []]) 33
Proof
  simp[parse_and_infer_def] >> CONV_TAC debug_eval >> EVAL_TAC
QED


(********************)
