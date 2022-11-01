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
           "pure_letrec_cexp", "pure_demands_analysis", "fromSexp"];

val _ = new_theory "pure_compiler";

Definition ast_to_string_def:
  ast_to_string full_prog =
    implode(simpleSexpParse$print_sexp (listsexp (MAP decsexp full_prog)))
End

Definition compile_def:
  compile s =
    case string_to_cexp (explode s) of
    | NONE => NONE
    | SOME (e1, tysig) =>
      let e2 = transform_cexp e1 in
      let ty = (I ## K tysig) initial_namespace in
        case infer_top_level ty (pure_vars$empty) e2 of
        | NONE => NONE
        | SOME _ =>
          let e3 = demands_analysis e2 in
            case infer_top_level ty (pure_vars$empty) e3 of
            | NONE => NONE
            | SOME _ =>
                SOME (ast_to_string $ pure_to_cake ty e3)
End

val _ = export_theory();
