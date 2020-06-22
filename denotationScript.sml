
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory;

val _ = new_theory "denotation";


(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)
Type fname = “:string”  (* function name *)

Datatype:
  op = Equal | Add
End

Datatype:
  exp = Lit num              (* constant number *)
      | Var vname            (* variable *)
      | Binop op exp exp     (* primitive operations *)
      | Let vname exp exp    (* let binding *)
      | If exp exp exp       (* if expression *)
      | App exp exp          (* function application *)
      | Fn fname vname exp   (* lambda that binds its own name (fname) *)
End


(* a call-by-name semantics in a denotational semantics style *)

Datatype:
  v = Num num | Closure fname vname exp
End

Datatype:
  res = Result v | Diverge | Error
End

Definition subst_def:
  subst name v (Lit n) = Lit n ∧
  subst name v (Var s) = (if name = s then v else Var s) ∧
  subst name v (Binop op x y) =
    Binop op (subst name v x) (subst name v y) ∧
  subst name v (Let s x y) =
    Let s (subst name v x) (if s = name then y else subst name v y) ∧
  subst name v (If x y z) =
    If (subst name v x) (subst name v y) (subst name v z) ∧
  subst name v (App x y) =
    App (subst name v x) (subst name v y) ∧
  subst name v (Fn f s x) =
    Fn f s (if s = name ∨ f = name then x else subst name v x)
End

Definition eval_op_def:
  eval_op Add (Result (Num m)) (Result (Num n)) =
    Result (Num (m + n)) ∧
  eval_op Equal (Result (Num m)) (Result (Num n)) =
    Result (Num (if m = n then 1 else 0)) ∧
  eval_op _ Diverge _ = Diverge ∧
  eval_op _ _ Diverge = Diverge ∧
  eval_op _ _ _       = Error
End

Definition eval_to_def:
  eval_to k (Lit n) = Result (Num n) ∧
  eval_to k (Var s) = Error ∧
  eval_to k (Let s x y) =
    (if k = 0 then Diverge else eval_to (k-1) (subst s x y)) ∧
  eval_to k (If x y z) =
    (case eval_to k x of
     | Result (Num 1) => eval_to k y
     | Result (Num 0) => eval_to k z
     | Result _ => Error
     | other => other) ∧
  eval_to k (Binop op x y) = eval_op op (eval_to k x) (eval_to k y) ∧
  eval_to k (Fn f s x) = Result (Closure f s x) ∧
  eval_to k (App x y) =
    case eval_to k x of
    | Diverge => Diverge
    | Result (Closure f v body) =>
        if k = 0 then Diverge else
          eval_to (k-1) (subst v y (subst f (Fn f v body) body))
    | _ => Error
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(k,x). (k,exp_size x))`
End

(* this definition is hard to use, but see the nicer presentation in eval_eqs below *)
Definition eval_def:
  eval x =
    (* select some k such that eval_to k x terminates *)
    case some k. eval_to k x ≠ Diverge of
    (* if no such clock exists, then return Diverge *)
    | NONE => Diverge
    (* if some such a clock k exists, then use it to evaluate the program *)
    | SOME k => eval_to k x
End


(* minor lemmas about eval *)

Theorem eval_op_eq_div:
  eval_op op x y = Diverge ⇔ x = Diverge ∨ y = Diverge
Proof
  fs [DefnBase.one_line_ify NONE eval_op_def, AllCaseEqs(), eval_op_def]
  \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ fs []
QED

Theorem eval_to_determ_lemma:
  ∀n x k. eval_to n x ≠ Diverge ⇒ eval_to (n+k) x = eval_to n x
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ TRY (fs [eval_to_def] \\ NO_TAC)
  THEN1 (Cases_on ‘n’ \\ fs [ADD1] \\ fs [eval_to_def])
  THEN1
   (fs [eval_to_def] \\ Cases_on ‘eval_to n x’ \\ fs []
    \\ Cases_on ‘v’ \\ fs []
    \\ rename [‘if k = 0 then _ else _’]
    \\ Cases_on ‘k = 0’ \\ fs []
    \\ Cases_on ‘k = 1’ \\ fs [])
  THEN1 (fs [eval_to_def,eval_op_eq_div])
  \\ fs [eval_to_def] \\ Cases_on ‘eval_to n x’ \\ fs []
  \\ Cases_on ‘v’ \\ fs []
  \\ Cases_on ‘n’ \\ fs []
QED

Theorem eval_to_determ:
  eval_to n x ≠ Diverge ∧ eval_to m x ≠ Diverge ⇒
  eval_to n x = eval_to m x
Proof
  ‘m ≤ n ∨ n ≤ m’ by fs []
  \\ fs [LESS_EQ_EXISTS] \\ rw []
  \\ imp_res_tac eval_to_determ_lemma \\ fs []
  \\ metis_tac [ADD_COMM]
QED

Theorem eval_to_mono:
  eval_to n x ≠ Diverge ∧ n ≤ m ⇒
  eval_to m x = eval_to n x
Proof
  fs [LESS_EQ_EXISTS] \\ rw []
  \\ imp_res_tac eval_to_determ_lemma \\ fs []
  \\ metis_tac [ADD_COMM]
QED

Theorem eval_to_div_mono_lemma:
  ∀n x m. m < n ⇒ eval_to m x = Diverge ∨ eval_to m x = eval_to n x
Proof
  ho_match_mp_tac eval_to_ind \\ rw []
  \\ TRY (fs [eval_to_def] \\ NO_TAC)
  THEN1 (fs [] \\ fs [eval_to_def] \\ Cases_on ‘m = 0’ \\ fs [])
  THEN1
   (fs [] \\ fs [eval_to_def] \\ res_tac \\ fs []
    \\ Cases_on ‘eval_to n x’ \\ fs []
    \\ Cases_on ‘v’ \\ fs [] \\ rw [])
  THEN1 (fs [eval_op_eq_div,eval_to_def] \\ res_tac \\ fs [])
  \\ fs [] \\ fs [eval_to_def]
  \\ Cases_on ‘eval_to n x’ \\ fs []
  \\ res_tac \\ fs []
  \\ Cases_on ‘v’ \\ fs []
  \\ Cases_on ‘m = 0’ \\ fs []
QED

Theorem eval_to_div_mono:
  eval_to n x = Diverge ∧ m < n ⇒ eval_to m x = Diverge
Proof
  metis_tac [eval_to_div_mono_lemma]
QED

Theorem eval_to_div_mono_contrapos:
  eval_to m x ≠ Diverge ⇒ m < n ⇒ eval_to n x ≠ Diverge
Proof
  rpt strip_tac
  \\ drule_all eval_to_div_mono
  \\ simp []
QED

(* proving correctness of a clock-free presentation of eval *)

Theorem eval_eqs:
  eval (Lit n) = Result (Num n) ∧
  eval (Var s) = Error (* free variables are not allowed *) ∧
  eval (Let s x y) = eval (subst s x y) ∧
  eval (If x y z) =
    (case eval x of
     | Result (Num 1) => eval y
     | Result (Num 0) => eval z
     | Result _ => Error
     | other => other) ∧
  eval (Binop op x y) = eval_op op (eval x) (eval y) ∧
  eval (Fn f s x) = Result (Closure f s x) ∧
  eval (App x y) =
    case eval x of
    | Diverge => Diverge
    | Result (Closure f v body) =>
        eval (subst v y (subst f (Fn f v body) body))
    | _ => Error
Proof
  rw []
  THEN1 (* Lit case *)
    fs [eval_def,eval_to_def,AllCaseEqs(),some_def]
  THEN1 (* Var case *)
    fs [eval_def,eval_to_def,AllCaseEqs(),some_def]
  THEN1 (* Let case *)
   (fs [eval_def,eval_to_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    THEN1
     (DEEP_INTRO_TAC some_intro \\ rw []
      THEN1 (match_mp_tac eval_to_determ \\ fs [])
      \\ qsuff_tac ‘∀k. eval_to k (subst s x y) = Diverge’ \\ fs []
      \\ rw [] \\ first_x_assum (qspec_then ‘k+1’ mp_tac) \\ fs [])
    \\ qsuff_tac ‘∀k. eval_to k (subst s x y) = Diverge’ \\ fs []
    \\ rw [] \\ first_x_assum (qspec_then ‘k+1’ mp_tac) \\ fs [])
  THEN1 (* If case *)
   (fs [eval_def,eval_to_def]
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ rename [‘eval_to k’]
    THEN1
     (Cases_on ‘eval_to k x = Diverge’ \\ fs []
      \\ imp_res_tac eval_to_determ \\ fs [] \\ rw []
      \\ BasicProvers.TOP_CASE_TAC \\ fs []
      \\ Cases_on ‘v’ \\ fs []
      \\ rename [‘if k = 0 then _ else _’]
      \\ Cases_on ‘k’ \\ fs [ADD1]
      \\ DEEP_INTRO_TAC some_intro \\ rw []
      \\ imp_res_tac eval_to_determ \\ fs [])
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs []
    THEN1 (first_x_assum (qspec_then ‘k’ assume_tac) \\ fs [] \\ rfs [])
    \\ Cases_on ‘v’ \\ fs [] \\ rw [] \\ fs []
    \\ TRY (first_x_assum (qspec_then ‘k’ mp_tac) \\ fs [] \\ NO_TAC)
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ (rename [‘eval_to n _ = Diverge’]
        \\ Cases_on ‘n < k’
        THEN1
         (first_x_assum (qspec_then ‘k’ mp_tac) \\ fs []
          \\ metis_tac [eval_to_div_mono])
        \\ fs [NOT_LESS]
        \\ ‘eval_to k x ≠ Diverge’ by fs []
        \\ imp_res_tac eval_to_mono \\ fs []
        \\ first_x_assum (qspec_then ‘n’ mp_tac)
        \\ fs []))
  THEN1 (* Binop case *)
   (simp [eval_def, eval_to_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_op_eq_div]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_op_eq_div]
    \\ DEEP_INTRO_TAC some_intro \\ simp [eval_op_eq_div]
    \\ rpt strip_tac
    THEN1
      (dxrule_all eval_to_determ
       \\ dxrule_all eval_to_determ
       \\ simp [])
    \\ rename1 ‘eval_to k1 y’
    \\ rename1 ‘eval_to k2 x’
    \\ qexists_tac ‘SUC (MAX k1 k2)’
    \\ dxrule eval_to_div_mono_contrapos
    \\ dxrule eval_to_div_mono_contrapos
    \\ rw [MAX_DEF])
  THEN1 (* Fn case *)
    fs [eval_def,eval_to_def,AllCaseEqs(),some_def]
  THEN (* App case *)
  fs [eval_def,eval_to_def]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1
   (Cases_on ‘eval_to x'' x = Diverge’ \\ fs []
    \\ imp_res_tac eval_to_determ \\ fs [] \\ rw []
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ Cases_on ‘v’ \\ fs []
    \\ rename [‘if k = 0 then _ else _’]
    \\ Cases_on ‘k’ \\ fs [ADD1]
    \\ DEEP_INTRO_TAC some_intro \\ rw []
    \\ imp_res_tac eval_to_determ \\ fs [])
  \\ ‘∃f v body. eval_to x' x = Result (Closure f v body)’ by
    (first_assum (qspec_then ‘x'’ mp_tac)
     \\ simp_tac std_ss [AllCaseEqs()] \\ fs [] \\ rw [] \\ fs [])
  \\ fs []
  \\ qsuff_tac
     ‘∀k. eval_to k (subst v y (subst f (Fn f v body) body)) = Diverge’
  \\ fs [] \\ strip_tac
  \\ rename [‘eval_to n x = Result _’]
  \\ Cases_on ‘k < n’
  THEN1
   (‘n ≤ n+1’ by fs []
    \\ imp_res_tac eval_to_mono \\ fs []
    \\ pop_assum (qspec_then ‘x’ assume_tac) \\ rfs []
    \\ first_x_assum (qspec_then ‘n+1’ mp_tac)
    \\ fs [] \\ metis_tac [eval_to_div_mono])
  \\ fs [NOT_LESS]
  \\ ‘eval_to n x ≠ Diverge’ by fs []
  \\ ‘n ≤ k+1’ by fs []
  \\ imp_res_tac eval_to_mono \\ fs []
  \\ first_x_assum (qspec_then ‘k+1’ mp_tac)
  \\ fs []
QED


(* prove that bottom diverges *)

Definition bottom_def:
  bottom =
    Let "bot"
      (Fn "bot" "n" (App (Var "bot") (Lit 0)))
      (App (Var "bot") (Lit 0))
End

Theorem eval_bottom:
  eval bottom = Diverge
Proof
  qsuff_tac ‘∀k. eval_to k bottom = Diverge’
  THEN1 fs [eval_def]
  \\ fs [bottom_def,eval_to_def]
  \\ Cases \\ fs [subst_def]
  \\ Induct_on ‘n’ \\ fs []
  \\ simp [eval_to_def,subst_def]
QED


val _ = export_theory();
