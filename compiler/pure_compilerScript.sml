(*
   PureLang compiler: concrete syntax -> CakeML AST
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_cexpTheory pure_to_cakeTheory pureParseTheory pure_inferenceTheory
     pure_letrec_cexpTheory pure_demands_analysisTheory
     fromSexpTheory simpleSexpParseTheory;

val _ = set_grammar_ancestry
          ["pure_cexp", "pure_to_cake", "pureParse", "pure_inference",
           "pure_letrec_cexp", "pure_demands_analysis", "fromSexp",
           "simpleSexpParse"];

val _ = new_theory "pure_compiler";

Definition ast_to_string_def:
  ast_to_string prog = print_sexp (listsexp (MAP decsexp prog))
End

Definition compile_def:
  compile s =
    let _ = empty_ffi (strlit "starting...") in
    let r = string_to_cexp s in
    let _ = empty_ffi (strlit "parsing") in
    case r of
    | NONE => NONE
    | SOME (e1,ns) =>
      let e2 = transform_cexp e1 in
      let _ = empty_ffi (strlit "transform_cexp") in
      let i = infer_types ns e2 in
      let _ = empty_ffi (strlit "infer_types") in
        case to_option i of
        | NONE => NONE
        | SOME _ =>
          let e3 = demands_analysis e2 in
          let _ = empty_ffi (strlit "demands_analysis") in
            SOME (ast_to_string $ pure_to_cake ns e3)
End

Theorem compile_monadically:
  compile s =
  do
    (e1,ns) <- string_to_cexp s ;
    e2 <<- transform_cexp e1 ;
    to_option $ infer_types ns e2 ;
    e3 <<- demands_analysis e2 ;
    return (ast_to_string $ pure_to_cake ns e3)
  od
Proof
  simp[compile_def] >> EVERY_CASE_TAC >> simp[]
QED


val _ = export_theory();
