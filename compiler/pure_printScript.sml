(*
   Pretty printing and basic parsing of cexp
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_cexpTheory printingTheory parsingTheory intLib source_valuesTheory;

val _ = new_theory "pure_print";

(* --- pretty printing --- *)
Overload Name' = “λs. Name $ explode s”
Definition sexp_of_op_def:
  sexp_of_op (pure_cexp$Cons s) = [Name "cons"; Name' s] ∧
  sexp_of_op Seq = [Name "seq"] ∧
  sexp_of_op (AtomOp (Lit (Int i))) =
    (if i < 0 then [Name "int-"; Num (integer$Num (0-i))] else
                   [Name "int"; Num (integer$Num i)]) ∧
  sexp_of_op (AtomOp (Lit (Str s))) = [Name "str"; Name s] ∧
  sexp_of_op (AtomOp (Lit (Loc l))) = [Name "loc"; Num l] ∧
  sexp_of_op (AtomOp (Lit (Msg t u))) = [Name "msg"; Name t; Name u] ∧
  sexp_of_op (AtomOp Eq) = [Name "="] ∧
  sexp_of_op (AtomOp Add) = [Name "+"] ∧
  sexp_of_op (AtomOp Sub) = [Name "-"] ∧
  sexp_of_op (AtomOp Mul) = [Name "*"] ∧
  sexp_of_op (AtomOp Div) = [Name "div"] ∧
  sexp_of_op (AtomOp Mod) = [Name "mod"] ∧
  sexp_of_op (AtomOp Lt) = [Name "<"] ∧
  sexp_of_op (AtomOp Leq) = [Name "<="] ∧
  sexp_of_op (AtomOp Gt) = [Name ">"] ∧
  sexp_of_op (AtomOp Geq) = [Name ">="] ∧
  sexp_of_op (AtomOp Len) = [Name "len"] ∧
  sexp_of_op (AtomOp Elem) = [Name "elem"] ∧
  sexp_of_op (AtomOp Concat) = [Name "concat"] ∧
  sexp_of_op (AtomOp Implode) = [Name "implode"] ∧
  sexp_of_op (AtomOp Substring) = [Name "substring"] ∧
  sexp_of_op (AtomOp StrLt) = [Name "str-<"] ∧
  sexp_of_op (AtomOp StrLeq) = [Name "str-<="] ∧
  sexp_of_op (AtomOp StrGt) = [Name "str->"] ∧
  sexp_of_op (AtomOp StrGeq) = [Name "str->="] ∧
  sexp_of_op (AtomOp (Message s)) = [Name "message"; Name s]
End

Definition sexp_of_def:
  sexp_of (Var d n)       = Name' n ∧
  sexp_of (Prim d p xs)   = list (sexp_of_op p ++ MAP sexp_of xs) ∧
  sexp_of (Let d v x y)   = list [Name "let"; sexp_of x; sexp_of y] ∧
  sexp_of (App _ f xs)    = list ([Name "app"; sexp_of f] ++ MAP sexp_of xs) ∧
  sexp_of (Lam d vs x)    = list ([Name "lam"; list (MAP Name' vs); sexp_of x])∧
  sexp_of (Letrec d rs x) = list ([Name "letrec"] ++
                                  MAP (λ(n,x). list [Name' n; sexp_of x]) rs ++
                                  [sexp_of x]) ∧
  sexp_of (Case d x v rs eopt) =
    list ([Name "case"; sexp_of x; Name' v] ++
          [Pair
            (list $ MAP (λ(c,vs,x). list [list (MAP Name' (c::vs)); sexp_of x]) rs)
            (case eopt of
              | NONE => Name "NONE"
              | SOME (cn_ars, x) => list (
                [Name "SOME" ;
                  list $ MAP (λ(cn,ar). list [Name' cn; Num ar]) cn_ars ;
                    sexp_of x]))])
Termination
  WF_REL_TAC ‘measure (cexp_size (K 0))’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ first_x_assum (qspec_then ‘K 0’ mp_tac) \\ fs []
End

Definition str_of_def:
  str_of x = vs2str [sexp_of x] []
End

Triviality str_of_test1:
  str_of (Lam () [«x»;«y»] (Prim () (AtomOp Add) [Var () «x»; Var () «y»])) =
    "\n(lam (x y) (+ x y))\n\n"
Proof
  EVAL_TAC
QED

Triviality str_of_test2:
  str_of (Letrec () [(«x»,(Prim () (AtomOp Add) [Var () «x»; Var () «y»]))]
           (Var () «y»)) = "\n(letrec (x (+ x y)) y)\n\n"
Proof
  EVAL_TAC
QED

Triviality str_of_test3:
  str_of (Case () (App () (Var () «f») [Prim () (AtomOp (Lit (Int 7))) []]) «xs»
            [(«nil»,[],Var () «xs»);
             («cons»,[«y»;«ys»],Var () «ys»)] NONE) =
  "\n(case (app f (int 7)) xs ((((nil) xs) ((cons y ys) ys))  .  NONE))\n\n"
Proof
  EVAL_TAC
QED

(* --- basic parsing --- *)

Definition num_to_str_aux_def:
  num_to_str_aux n aux =
    if n = 0:num then aux else num_to_str_aux (n DIV 256) (CHR (n MOD 256) :: aux)
End

Definition num_to_str_def:
  num_to_str n = num_to_str_aux n []
End

Definition name_of_def:
  name_of (Num n) = implode $ num_to_str n ∧
  name_of _ = «[malformed]»
End

Definition names_of_def:
  names_of (Num n) = [] ∧
  names_of (Pair h t) = name_of h :: names_of t
End

Definition num_of_def:
  num_of (source_values$Num n) = n ∧
  num_of _ = 0
End

Definition cop_of_def:
  cop_of h h' h'' xs =
    if h = Name "=" then Prim () (AtomOp Eq) xs else
    if h = Name "+" then Prim () (AtomOp Add) xs else
    if h = Name "-" then Prim () (AtomOp Sub) xs else
    if h = Name "*" then Prim () (AtomOp Mul) xs else
    if h = Name "div" then Prim () (AtomOp Div) xs else
    if h = Name "mod" then Prim () (AtomOp Mod) xs else
    if h = Name "<" then Prim () (AtomOp Lt) xs else
    if h = Name "<=" then Prim () (AtomOp Leq) xs else
    if h = Name ">" then Prim () (AtomOp Gt) xs else
    if h = Name ">=" then Prim () (AtomOp Geq) xs else
    if h = Name "len" then Prim () (AtomOp Len) xs else
    if h = Name "elem" then Prim () (AtomOp Elem) xs else
    if h = Name "concat" then Prim () (AtomOp Concat) xs else
    if h = Name "implode" then Prim () (AtomOp Implode) xs else
    if h = Name "substring" then Prim () (AtomOp Substring) xs else
    if h = Name "str-<" then Prim () (AtomOp StrLt) xs else
    if h = Name "str-<=" then Prim () (AtomOp StrLeq) xs else
    if h = Name "str->" then Prim () (AtomOp StrGt) xs else
    if h = Name "str->=" then Prim () (AtomOp StrGeq) xs else
    if h = Name "seq" then Prim () Seq xs else
    if h = Name "cons" then Prim () (Cons (name_of h')) (TL xs) else
    if h = Name "message" then
      Prim () (AtomOp (Message (explode $ name_of h'))) (TL xs) else
    if h = Name "msg" then
      Prim ()
           (AtomOp (Lit (Msg (explode $ name_of h') (explode $ name_of h''))))
           (TL (TL xs)) else
    if h = Name "loc" then Prim () (AtomOp (Lit (Loc (num_of h')))) (TL xs) else
    if h = Name "str" then
      Prim () (AtomOp (Lit (Str (explode $ name_of h')))) (TL xs) else
    if h = Name "int" then
      Prim () (AtomOp (Lit (Int (& num_of h')))) (TL xs)
    else
      Prim () (AtomOp (Lit (Int (- & num_of h')))) (TL xs)
End

Definition cn_ars_of_def:
  cn_ars_of (Num n) = [] ∧
  cn_ars_of (Pair (Pair cn (Pair (Num ar) (Num n))) rest) =
    (name_of cn, ar) :: cn_ars_of rest ∧
  cn_ars_of _ = []
End

Definition cexp_of_def:
  cexp_of (Num n) = pure_cexp$Var () (implode $ num_to_str n) ∧
  cexp_of (Pair h t) =
    (if h = Name "let" then
       Let () (name_of (el0 t)) (cexp_of (el1 t)) (cexp_of (el2 t))
     else if h = Name "lam" then
       Lam () (names_of (el0 t)) (cexp_of (el1 t))
     else if h = Name "app" then
       App () (cexp_of (el0 t)) (cexps_of (tail t))
     else if h = Name "letrec" then
       let (fs,x) = letrec_of t in
         Letrec () fs x
     else if h = Name "case" then
       Case () (cexp_of (el0 t)) (name_of (el1 t))
            (rows_of (head (el2 t)))
            (if tail $ el2 t = Name "NONE" then NONE
             else SOME (cn_ars_of $ el1 $ tail $ el2 t, cexp_of $ el2 $ tail $ el2 t))
     else (* must be a Prim case *)
       cop_of h (el0 t) (el1 t) (cexps_of t)) ∧
  cexps_of (Num n) = [] ∧
  cexps_of (Pair h t) = cexp_of h :: cexps_of t ∧
  letrec_of (Num n) = ([],Var () «[malformed]») ∧
  letrec_of (Pair h t) =
    (if isNum t then ([],cexp_of h) else
       let (fs,x) = letrec_of t in
         ((name_of (el0 h), cexp_of (el1 h)) :: fs, x)) ∧
  rows_of (Num n) = [] ∧
  rows_of (Pair h t) =
    (name_of (el0 (el0 h)),names_of (el1 (el0 h)),cexp_of (el1 h)) :: rows_of t
Termination
  WF_REL_TAC ‘measure (λv. case v of INL v => v_size v
                                   | INR (INL v) => v_size v
                                   | INR (INR (INL v)) => v_size v
                                   | INR (INR (INR v)) => v_size v)’
  \\ rpt strip_tac
  \\ rpt (goal_term (fn tm => tmCases_on (find_term is_var (rator tm)) [] \\ fs []))
End

Definition parse_cexp_def:
  parse_cexp s = cexp_of (head (parse (lexer s) (Num 0) []))
End

Definition bindings_of_def:
  bindings_of (Num _) = ([], [], Var () «[malformed]») ∧
  bindings_of (Pair h t) =
    if isNum t then
      ([],[],cexp_of h)
    else if el0 h = Name "define" then
      let (vs,data,main) = bindings_of t in
        ((name_of (el1 h),cexp_of (el2 h))::vs,data,main)
    else if el0 h = Name "data" then
      let (vs,data,main) = bindings_of t in
        (vs,tail h::data,main)
    else bindings_of t
End

Definition parse_prog_def:
  parse_prog s =
    let (values,_,main) = bindings_of (parse (lexer s) (Num 0) []) in
      Letrec () values main
End

Triviality parse_cexp_test1:
  parse_cexp "(+ a b)" =
    Prim () (AtomOp Add) [Var () «a»; Var () «b»]
Proof
  EVAL_TAC
QED

Triviality parse_cexp_test2:
  parse_cexp "(let a (int 6) (+ a b))" =
     Let () «a» (Prim () (AtomOp (Lit (Int 6))) [])
       (Prim () (AtomOp Add) [Var () «a»; Var () «b»])
Proof
  EVAL_TAC
QED

Theorem parse_cexp_test3 =
        EVAL “parse_cexp "(case (app f (int 7)) xs ((((nil) xs) ((cons (y ys)) ys))  .  NONE))"”

Theorem parse_cexp_test4 =
        EVAL “parse_cexp "(case (app f (int 7)) xs ((((nil) xs) ((cons (y ys)) ys))  .  (SOME (int 3))))"”

Theorem parse_cexp_test5 =
        EVAL “parse_cexp "(case (app f (int 7)) xs ((((nil) xs) ((cons (y ys)) ys))  .  (SOME x)))"”

val _ = export_theory();
