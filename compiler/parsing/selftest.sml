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
fun checkrand t =
    rand t handle HOL_ERR _ =>
    raise mk_HOL_ERR "" "" "Got NONE"

val ptree_ty = ty_antiq “: (token,ppegnt, locs) parsetree”
val ptSOME = “SOME : ^ptree_ty -> ^ptree_ty option”
fun fptest (nt, s, cf, exp) =
    (tprint ("Parsing (" ^ term_to_string nt ^ ") \"" ^ KNL s ^ "\"");
     require_msg (check_result (aconv exp)) term_to_string
                 (checkrand o rhs o concl o EVAL)
                 (list_mk_icomb(fullparse,
                                [nt,stringSyntax.fromMLstring s,
                                 inst [alpha |-> “:locs”] cf])))
fun sp (* simple parse *) nt s =
    EVAL (list_mk_icomb(fullparse, [hd (decls nt), stringSyntax.fromMLstring s,
                                    ptSOME]))

val threetimesfour = “expApp (expApp (expVar "*") (expLit (litInt 3)))
                             (expLit (litInt 4))”
val _ = temp_overload_on("𝕀", “λi. expLit (litInt i)”);
val _ = app fptest [
  (“nTy”, "[Int]", “astType nTy”, “listTy intTy”),
  (“nTy”, "a -> B", “astType nTy”, “funTy (tyVar "a") (tyOp "B" [])”),
  (“nTy”, "(Tree a, B)", “astType nTy”, “tyTup [tyOp "Tree" [tyVar "a"];
                                                tyOp "B" []]”),
  (“nTy”, "[Int -> ()]", “astType nTy”, “listTy (funTy intTy $ tyTup [])”),
  (“nExp”, "f 2 x", “astExp nExp”, “‹f› ⬝ 𝕀 2 ⬝ ‹x›”),
  (“nExp”, "\\x y -> y x", “astExp nExp”,
   “expAbs (patVar "x") (expAbs (patVar "y") (‹y› ⬝ ‹x›))”),
  (“nExp”, " if p x \nthen 1 else 2", “astExp nExp”,
   “expIf (expApp (expVar "p") (expVar "x")) (𝕀 1) (𝕀 2)”),
  (“nExp”, "z + if p x \nthen 1 else 2", “astExp nExp”,
   “‹+› ⬝ ‹z› ⬝ expIf (expApp (expVar "p") (expVar "x")) (𝕀 1) (𝕀 2)”),
  (“nExp”, "3 * 4 + 6", “astExp nExp”, “‹+› ⬝ (‹*› ⬝ 𝕀 3 ⬝ 𝕀 4) ⬝ 𝕀 6”),
  (“nExp”, "6 + 3 * 4", “astExp nExp”, “‹+› ⬝ 𝕀 6 ⬝ (‹*› ⬝ 𝕀 3 ⬝ 𝕀 4)”),
  (“nExp”, "(6 + 3) * 4", “astExp nExp”, “‹*› ⬝ (‹+› ⬝ 𝕀 6 ⬝ 𝕀 3) ⬝ 𝕀 4”),
  (“nExp”, "h1:h2:t", “astExp nExp”, “‹h1› ::ₚ ‹h2› ::ₚ ‹t›”),
  (“nExp”, "1+3:t", “astExp nExp”, “(‹+› ⬝ 𝕀 1 ⬝ 𝕀 3) ::ₚ ‹t›”),
  (“nExp”, "C () 3", “astExp nExp”, “expCon "C" [expTup []; 𝕀 3]”),
  (“nExp”, "C (x+y) 3", “astExp nExp”, “expCon "C" [‹+› ⬝ ‹x› ⬝ ‹y›; 𝕀 3]”),
  (“nExp”, "C (x,y) 3", “astExp nExp”, “expCon "C" [expTup [‹x›; ‹y›]; 𝕀 3]”),
  (“nExp”, "D [] 3", “astExp nExp”, “expCon "D" [pNIL; 𝕀 3]”),
  (“nExp”, "f [x,y] 3", “astExp nExp”,
   “‹f› ⬝ (‹x› ::ₚ ‹y› ::ₚ pNIL) ⬝ 𝕀 3”),
  (“nExp”, "let y = x + 3 in y + z",
   “astExp nExp”,
   “expLet [expdecFunbind "y" [] (‹+› ⬝ ‹x› ⬝ 𝕀 3)] (‹+› ⬝ ‹y› ⬝ ‹z›)”),
  (“nExp”, "let\n\
           \  y = x + 3\n\
           \  z = 10 in y + z",
   “astExp nExp”,
   “expLet [expdecFunbind "y" [] (‹+› ⬝ ‹x› ⬝ 𝕀 3);
            expdecFunbind "z" [] (𝕀 10)] (‹+› ⬝ ‹y› ⬝ ‹z›)”),
  (“nExp”, "do x <- f y 3\n\
           \   foo x",
   “astExp nExp”,
   “expDo [expdostmtBind (patVar "x") (‹f› ⬝ ‹y› ⬝ 𝕀 3)] (‹foo› ⬝ ‹x›)”),
  (“nExp”, "do let y = 10\n\
           \       f :: Int -> Int\n\
           \       f z = z + 1\n\
           \   x <- g (f y) 3\n\
           \   foo x",
   “astExp nExp”,
   “expDo [expdostmtLet [expdecFunbind "y" [] (𝕀 10);
                         expdecTysig "f" (funTy intTy intTy);
                         expdecFunbind "f" [patVar "z"] (‹+› ⬝ ‹z› ⬝ 𝕀 1)];
           expdostmtBind (patVar "x") (‹g› ⬝ (‹f› ⬝ ‹y›) ⬝ 𝕀 3)]
          (‹foo› ⬝ ‹x›)”),
  (“nExp”, "case e of [] -> 3\n\
           \          h:t -> 4",
   “astExp nExp”,
   “expCase ‹e› [(patApp "[]" [], 𝕀 3);
                 (patApp ":" [patVar "h"; patVar "t"], 𝕀 4)]”),
  (“nDecl”, "f :: a -> Int", “astDecl”,
   “declTysig "f" (funTy (tyVar "a") (tyOp "Int" []))”),
  (“nDecl”, "f x y = x + y", “astDecl”,
   “declFunbind "f" [patVar "x"; patVar "y"] (‹+› ⬝ ‹x› ⬝ ‹y›)”),
  (“nDecl”, "h:t = f e", “astDecl”,
   “declPatbind (patApp ":" [patVar "h"; patVar "t"]) (‹f› ⬝ ‹e›)”),
  (“nDecl”, "data Foo a = C a Int | D [Int]", “astDecl”,
   “declData "Foo" ["a"] [("C", [tyVar "a"; tyOp "Int" []]);
                          ("D", [tyOp "List" [tyOp "Int"[]]])]”)
]
