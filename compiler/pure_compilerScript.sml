(*
   PureLang compiler: concrete syntax -> CakeML AST
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory dep_rewrite
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_cexpTheory pure_to_cakeTheory pureParseTheory pure_inferenceTheory
     pure_letrec_cexpTheory pure_demands_analysisTheory pure_inline_cexpTheory
     fromSexpTheory simpleSexpParseTheory pure_printTheory;

val _ = set_grammar_ancestry
          ["pure_cexp", "pure_to_cake", "pureParse", "pure_inference",
           "pure_letrec_cexp", "pure_demands_analysis",
           "pure_inline_cexp", "fromSexp", "simpleSexpParse"];

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
    | SOME (e,ns) =>
      let e = transform_cexp c e in
      let _ = empty_ffi (strlit "transform_cexp") in
      let i = infer_types ns e in
      let _ = empty_ffi (strlit "infer_types") in
        case to_option i of
        | NONE => NONE
        | SOME _ =>
            let e = clean_cexp c e in
            let _ = empty_ffi (strlit "clean_cexp") in
            let e = demands_analysis c e in
            let _ = empty_ffi (strlit "demands_analysis") in
            let _ = (if c.do_explore then
                       empty_ffi (implode ("after demands:\n" ++
                                  pure_print$str_of e ++ "\n"))
                     else ()) in
            let e = inline_top_level c e in
            let _ = empty_ffi (strlit "inlining") in
            let _ = (if c.do_explore then
                       empty_ffi (implode ("after inlining:\n" ++
                                  pure_print$str_of e ++ "\n"))
                     else ()) in
              SOME (ast_to_string $ pure_to_cake c ns e)
End

Definition compile_to_ast_def:
  compile_to_ast c s =
    case string_to_cexp s of
    | NONE => NONE
    | SOME (e,ns) =>
      let e = transform_cexp c e in
      let i = infer_types ns e in
        case to_option i of
        | NONE => NONE
        | SOME _ =>
          let e = clean_cexp c e in
          let e = demands_analysis c e in
          let e = inline_top_level c e in
            SOME (pure_to_cake c ns e)
End

(********** Alternative phrasings **********)

Theorem compile_monadically:
  compile c s =
  do
    (e,ns) <- string_to_cexp s ;
    e <<- transform_cexp c e ;
    to_option $ infer_types ns e ;
    e <<- clean_cexp c e ;
    e <<- demands_analysis c e ;
    e <<- inline_top_level c e ;
    return (ast_to_string $ pure_to_cake c ns e)
  od
Proof
  simp[compile_def]>> EVERY_CASE_TAC >> simp[]
QED

Definition frontend_def:
  frontend c s =
    case string_to_cexp s of
    | NONE => NONE
    | SOME (e,ns) =>
      let e = transform_cexp c e in
      let i = infer_types ns e in
        case to_option i of
        | NONE => NONE
        | SOME _ => SOME (e,ns)
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
    | SOME (e,ns) =>
        let e = clean_cexp c e in
        let e = demands_analysis c e in
        let e = inline_top_level c e in
          SOME (pure_to_cake c ns e)
Proof
  rw[compile_to_ast_def, frontend_def] >>
  rpt (TOP_CASE_TAC >> simp[])
QED

val _ = export_theory();
