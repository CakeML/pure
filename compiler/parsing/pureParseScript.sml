open HolKernel Parse boolLib bossLib;

(* supposed to contain all the things *)

open purePEGTheory cst_to_astTheory ast_to_shortASTTheory ast_to_cexpTheory
open pure_inferenceTheory


val _ = new_theory "pureParse";

Definition string_to_cst_def:
  string_to_cst s =
  case ispeg_exec purePEG (nt (INL nModules) I lrOK) (pure_lexer_impl$lexer_fun s)
                  lpTOP [] NONE [] done failed
  of
    Result (Success [] pts _ _ ) => SOME pts
  | _ => NONE
End

val _ = computeLib.add_funs [pure_lexer_implTheory.get_token_def,
                             listTheory.LIST_REL_def,
                             ASCIInumbersTheory.s2n_compute,
                             numposrepTheory.l2n_def]


val fact_s = “"module Fact with\n\
               \f :: Int -> Int\n\
               \f x = if x == 0 then 1 else x * f(x - 1)\n\
               \z = 4\n"”
val fact_cst = EVAL “string_to_cst ^fact_s”

val do_s = “"module Foo with\n\
             \f t = do x <- \n\
             \           g y\n\
             \         return (x + 1)"”
val do_cst = EVAL “string_to_cst ^do_s”

val two_modules = “"module Foo with\n\
                    \f t = t + 1\n\
                    \g t = 1\n\
                    \module Bar with\n\
                    \import Foo\n\
                    \h x = let f t = t in\n\
                    \                (f 0) + (g 0) + (h 0)"”
val two_modules_cst = EVAL “string_to_cst ^two_modules”

Definition string_to_asts_def:
  string_to_asts s =
  do
    csts <- string_to_cst s ;
    cst <- oHD csts ;
    astModules cst
  od
End

val fact_ast = EVAL “string_to_asts ^fact_s”

val do_ast = EVAL “string_to_asts ^do_s”

val two_modules_ast = EVAL “string_to_asts ^two_modules”

val fact_ast_without_modules = EVAL “case string_to_asts ^fact_s of
                                       NONE => NONE
                                     | SOME asts => SOME (remove_modules asts)”

val do_ast_without_modules = EVAL “case string_to_asts ^do_s of
                                     NONE => NONE
                                   | SOME asts => SOME (remove_modules asts)”

val two_modules_ast_without_modules = EVAL “case string_to_asts ^two_modules of
                                              NONE => NONE
                                            | SOME asts => SOME (remove_modules asts)”

Definition string_to_cexp0_def:
  string_to_cexp0 s =
  do
    asts <- string_to_asts s ;
    asts' <- remove_modules asts ;
    decls_to_letrec asts'
  od
End

Definition string_to_cexp_def:
  string_to_cexp s =
  do
    asts <- string_to_asts s ;
    asts' <- remove_modules asts ;
    (ce, tysig) <- decls_to_letrec asts' ;
    assert (closed_under empty ce) ;
    return (ce, tysig)
  od
End

Overload "𝕍" = “λs. Var () s”
Overload "𝕀" = “λi. Prim () (AtomOp (Lit (Int i))) []”
Overload "*" = “λx y. Prim () (AtomOp Mul) [x; y]”
Overload "-" = “λx y. Prim () (AtomOp Sub) [x; y]”

Theorem fact_cexp = EVAL “string_to_cexp ^fact_s”

(* doesn't EVAL *)
Definition parse_tcheck_def:
  parse_tcheck s =
  do
    (ce, tysig) <- string_to_cexp s ;
    tyresult <- to_option $
                  infer_top_level ((I ## K tysig) initial_namespace) () ce ;
    return (ce, tyresult) ;
  od
End

val _ = export_theory();
