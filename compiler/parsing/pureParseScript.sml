open HolKernel Parse boolLib bossLib;

(* supposed to contain all the things *)

open purePEGTheory cst_to_astTheory ast_to_cexpTheory
open pure_inferenceTheory


val _ = new_theory "pureParse";

Definition string_to_cst_def:
  string_to_cst s =
  case ispeg_exec purePEG (nt (INL nDecls) I lrOK) (pure_lexer_impl$lexer_fun s)
                  lpTOP [] NONE [] done failed
  of
    Result (Success [] pts _ _ ) => SOME pts
  | _ => NONE
End

val _ = computeLib.add_funs [pure_lexer_implTheory.get_token_def,
                             listTheory.LIST_REL_def,
                             ASCIInumbersTheory.s2n_compute,
                             numposrepTheory.l2n_def]


val fact_s = “"f :: Int -> Int\n\
              \f x = if x == 0 then 1 else x * f(x - 1)\n\
              \z = 4\n"”
val fact_cst = EVAL “string_to_cst ^fact_s”

Definition string_to_asts_def:
  string_to_asts s =
  do
    csts <- string_to_cst s ;
    cst <- oHD csts ;
    astDecls cst
  od
End

val fact_ast = EVAL “string_to_ast ^fact_s”

Definition string_to_cexp_def:
  string_to_cexp s =
  do
    asts <- string_to_asts s ;
    (ce, tysig) <- decls_to_letrec asts ;
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
    tyresult <- infer_top_level ((I ## K tysig) initial_namespace) () ce ;
    return (ce, tyresult) ;
  od
End

val _ = export_theory();
