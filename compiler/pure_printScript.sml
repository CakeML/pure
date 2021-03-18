(*
   Perrty printing of cexp
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_cexpTheory printingTheory intLib;

val _ = new_theory "pure_print";

Definition sexp_of_op_def:
  sexp_of_op (Cons s) = [Name "cons"; Name s] ∧
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
  sexp_of (Var d n)       = Name n ∧
  sexp_of (Prim d p xs)   = list (sexp_of_op p ++ MAP sexp_of xs) ∧
  sexp_of (Let d v x y)   = list [Name "let"; sexp_of x; sexp_of y] ∧
  sexp_of (App _ f xs)    = list ([Name "app"; sexp_of f] ++ MAP sexp_of xs) ∧
  sexp_of (Lam d vs x)    = list ([Name "lam"; list (MAP Name vs); sexp_of x]) ∧
  sexp_of (Letrec d rs x) = list ([Name "letrec"] ++
                                  MAP (λ(n,x). list [Name n; sexp_of x]) rs ++
                                  [sexp_of x]) ∧
  sexp_of (Case d x v rs) = list ([Name "case"; sexp_of x; Name v] ++
             MAP (λ(c,vs,x). list [list (MAP Name (c::vs)); sexp_of x]) rs)
Termination
  WF_REL_TAC ‘measure (cexp_size (K 0))’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ first_x_assum (qspec_then ‘K 0’ mp_tac) \\ fs []
End

Definition str_of_def:
  str_of x = vs2str [sexp_of x] []
End

(*

fun print_cexp tm =
  “str_of ^tm” |> EVAL |> concl |> rand |> stringSyntax.fromHOLstring |> print;

*)

Triviality str_of_test1:
  str_of (Lam () ["x";"y"] (Prim () (AtomOp Add) [Var () "x"; Var () "y"])) =
    "\n(lam (x y) (+ x y))\n\n"
Proof
  EVAL_TAC
QED

Triviality str_of_test1:
  str_of (Letrec () [("x",(Prim () (AtomOp Add) [Var () "x"; Var () "y"]))]
           (Var () "y")) = "\n(letrec (x (+ x y)) y)\n\n"
Proof
  EVAL_TAC
QED

Triviality str_of_test1:
  str_of (Case () (App () (Var () "f") [Prim () (AtomOp (Lit (Int 7))) []]) "xs"
            [("nil",[],Var () "xs");
             ("cons",["y";"ys"],Var () "ys")]) =
    "\n(case (app f (int 7)) xs ((nil) xs) ((cons y ys) ys))\n\n"
Proof
  EVAL_TAC
QED

val _ = export_theory();
