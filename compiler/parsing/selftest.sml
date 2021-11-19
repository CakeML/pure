open HolKernel Parse boolLib bossLib
open cst_to_astTheory purePEGTheory testutils

val errcount = ref 0
val _ = diemode := Remember errcount

val _ = computeLib.add_funs [lexer_funTheory.get_token_def,
                             listTheory.LIST_REL_def,
                             ASCIInumbersTheory.s2n_compute,
                             numposrepTheory.l2n_def]

val gencst = “λn s. ispeg_exec purePEG (nt (INL n) I lrOK) (lexer_fun s)
                             lpTOP [] NONE [] done failed”

val fullparse =
    “λn s f. case ispeg_exec purePEG (nt (INL n) I lrOK) (lexer_fun s)
                             lpTOP [] NONE [] done failed
            of
               Result (Success [] [pt] _ _) => f pt
             | _ => (NONE : α option)”;

fun KNL s = String.translate (fn #"\n" => "\\n" | c => str c) s
fun fptest (nt, s, cf, exp) =
    (tprint ("Parsing (" ^ term_to_string nt ^ ") \"" ^ KNL s ^ "\"");
     require_msg (check_result (aconv exp)) term_to_string
                 (rand o rhs o concl o EVAL)
                 (list_mk_icomb(fullparse,
                                [nt,stringSyntax.fromMLstring s,
                                 inst [alpha |-> “:locs”] cf])))

val _ = app fptest [
  (“nTy”, "[Int]", “astType nTy”, “listTy intTy”),
  (“nTy”, "a -> B", “astType nTy”, “funTy (tyVar "a") (tyOp "B" [])”),
  (“nTy”, "(Tree a, B)", “astType nTy”, “tyTup [tyOp "Tree" [tyVar "a"];
                                                tyOp "B" []]”),
  (“nTy”, "[Int -> ()]", “astType nTy”, “listTy (funTy intTy $ tyTup [])”),
  (“nExp”, "f 2 x", “astExp nExp”,
   “expApp (expApp (expVar "f") (expLit $ litInt 2)) (expVar "x")”),
  (“nExp”, "\\x y -> y x", “astExp nExp”,
   “expAbs (patVar "x")
     (expAbs (patVar "y") (expApp (expVar "y") (expVar "x")))”),
  (“nExp”, " if p x \nthen 1 else 2", “astExp nExp”,
   “expIf (expApp (expVar "p") (expVar "x")) (expLit (litInt 1))
          (expLit (litInt 2)) ”)
]

