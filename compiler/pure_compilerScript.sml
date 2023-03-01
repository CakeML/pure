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
  compile c s =
    let _ = empty_ffi (strlit "starting...") in
    let r = string_to_cexp s in
    let _ = empty_ffi (strlit "parsing") in
    case r of
    | NONE => NONE
    | SOME (e1,ns) =>
      let e2 = transform_cexp c e1 in
      let _ = empty_ffi (strlit "transform_cexp") in
      let i = infer_types ns e2 in
      let _ = empty_ffi (strlit "infer_types") in
        case to_option i of
        | NONE => NONE
        | SOME _ =>
          let e3 = demands_analysis c e2 in
          let _ = empty_ffi (strlit "demands_analysis") in
            SOME (ast_to_string $ pure_to_cake c ns e3)
End

Definition compile_to_ast_def:
  compile_to_ast c s =
    case string_to_cexp s of
    | NONE => NONE
    | SOME (e1,ns) =>
      let e2 = transform_cexp c e1 in
      let i = infer_types ns e2 in
        case to_option i of
        | NONE => NONE
        | SOME _ =>
          let e3 = demands_analysis c e2 in
          SOME (pure_to_cake c ns e3)
End

(********** Alternative phrasings **********)

Theorem compile_monadically:
  compile c s =
  do
    (e1,ns) <- string_to_cexp s ;
    e2 <<- transform_cexp c e1 ;
    to_option $ infer_types ns e2 ;
    e3 <<- demands_analysis c e2 ;
    return (ast_to_string $ pure_to_cake c ns e3)
  od
Proof
  simp[compile_def] >> EVERY_CASE_TAC >> simp[]
QED

Definition frontend_def:
  frontend c s =
    case string_to_cexp s of
    | NONE => NONE
    | SOME (e1,ns) =>
      let e2 = transform_cexp c e1 in
      let i = infer_types ns e2 in
        case to_option i of
        | NONE => NONE
        | SOME _ => SOME (e2,ns)
End

Theorem compile_to_string:
  compile c s = OPTION_MAP ast_to_string $ compile_to_ast c s
Proof
  rw[compile_def, compile_to_ast_def] >>
  rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem compile_to_ast_alt_def:
  compile_to_ast c s =
    case frontend c s of
    | NONE => NONE
    | SOME (e2,ns) =>
        let e3 = demands_analysis c e2 in
        SOME (pure_to_cake c ns e3)
Proof
  rw[compile_to_ast_def, frontend_def] >>
  rpt (TOP_CASE_TAC >> simp[])
QED

val _ = export_theory();
