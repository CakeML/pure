open HolKernel Parse boolLib bossLib
open cst_to_astTheory purePEGTheory testutils ast_to_cexpTheory

val errcount = ref 0
val _ = diemode := Remember errcount

val _ = computeLib.add_funs [pure_lexer_implTheory.get_token_def,
                             listTheory.LIST_REL_def,
                             ASCIInumbersTheory.s2n_compute,
                             numposrepTheory.l2n_def]

val gencst = “λn s. ispeg_exec purePEG (nt (INL n) I lrOK) (lexer_fun s)
                             lpTOP [] NONE [] done failed”

fun lex s =
    EVAL (mk_comb(“MAP FST o pure_lexer_impl$lexer_fun”,
                  stringSyntax.fromMLstring s))

val fullparse =
    “λn s f. case ispeg_exec purePEG (nt (INL n) I lrOK) (lexer_fun s)
                             lpTOP [] NONE [] done failed
            of
               Result (Success [] [pt] _ _) => f pt
             | _ => (NONE : α option)”;
val fullparse0 =
    “λn s. case ispeg_exec purePEG (nt (INL n) I lrOK) (lexer_fun s)
                             lpTOP [] NONE [] done failed
            of
               Result (Success [] [pt] _ _) => SOME pt
             | _ => NONE”;

fun filetake n f =
    let val is = TextIO.openIn f
        fun getlines c A =
            if c < n then
              case TextIO.inputLine is of
                  NONE => String.concat (List.rev A)
                | SOME line => getlines (c + 1) (line::A)
            else String.concat (List.rev A)
    in
      getlines 0 [] before TextIO.closeIn is
    end

fun KNL s = String.translate (fn #"\n" => "\\n" | c => str c) s
fun checkrand t =
    rand t handle HOL_ERR _ =>
    raise mk_HOL_ERR "" "" "Got NONE"

fun maybe_aconv t1 t2 =
    same_const “option$NONE” t1 orelse aconv t1 t2

val ptree_ty = ty_antiq “: (token,ppegnt, locs) parsetree”
val ptSOME = “SOME : ^ptree_ty -> ^ptree_ty option”
fun fullparsef nt s cf =
    list_mk_icomb(fullparse,
                  [nt,stringSyntax.fromMLstring s, inst [alpha |-> “:locs”] cf])
fun fptest0 (nt, s, cf, exp) =
     require_msg (check_result (maybe_aconv exp)) term_to_string
                 (checkrand o rhs o concl o EVAL)
                 (fullparsef nt s cf)

fun lextest (s, t) =
    (tprint ("Lexing " ^ s);
     require_msg (check_result (aconv t o rhs o concl)) thm_to_string lex s)

fun fptest (x as (nt, s, cf, exp)) =
    (tprint ("Parsing (" ^ term_to_string nt ^ "/" ^ term_to_string cf ^ ") \"" ^
             KNL s ^ "\"");
     fptest0 x)

fun filetest (fname, NONE) =
    let val is = TextIO.openIn fname
        val str = TextIO.inputAll is
        val _ = TextIO.closeIn is
    in
      tprint ("Parsing contents of "^fname);
      fptest0 (“nDecls”, str, “astDecls”, “NONE”)
    end
  | filetest (fname, SOME c) =
    let val s = filetake c fname
        val _ = tprint ("Parsing " ^ Int.toString c ^ " lines of " ^ fname)
    in
      fptest0 (“nDecls”, s, “astDecls”, “NONE”)
    end
fun sp (* simple parse *) nt s =
    EVAL (list_mk_icomb(fullparse, [hd (decls nt), stringSyntax.fromMLstring s,
                                    ptSOME]))

val threetimesfour = “expApp (expApp (expVar "*") (expLit (litInt 3)))
                             (expLit (litInt 4))”
val _ = temp_overload_on("𝕀", “λi. expLit (litInt i)”);
val _ = temp_overload_on("𝕁", “λi. Prim () (AtomOp (Lit (Int i))) []”);
val _ = temp_overload_on("𝕍", “pure_cexp$Var ()”)
val _ = temp_overload_on("ASTEXP", “astExp nExp”)
val _ = temp_overload_on("CEXP",
  “flip (OPTION_BIND o ASTEXP) (translate_exp LN)
    : (token, ppegnt, locs) parsetree -> unit cexp option”)

val _ = temp_overload_on("::ₑ", “λh t. Prim () (Cons «:») [h; t]”)
val _ = temp_set_fixity "::ₑ" (Infixr 490)
val _ = temp_overload_on("[]ₑ", “Prim () (Cons «[]») []”)

val _ = temp_overload_on ("+ₑ", “λe1 e2. Prim () (AtomOp Add) [e1; e2]”)
val _ = temp_set_fixity "+ₑ" (Infixl 500)


val _ = app lextest [("->", “[SymbolT "->"]”),
                     (": :: <-", “[SymbolT ":"; SymbolT "::"; SymbolT "<-"]”),
                     ("do x", “[AlphaT "do"; AlphaT "x"]”),
                     ("foo_bar _", “[AlphaT "foo_bar"; UnderbarT]”)]

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
  (“nExp”, " if p x \nthen 1 else 2", “CEXP”,
   “Case () (App () (pure_cexp$Var () «p») [pure_cexp$Var () «x»]) «»
         [(«True», [], Prim () (AtomOp (Lit (Int 1))) []);
          («False», [], Prim () (AtomOp (Lit (Int 2))) []);
         ] NONE”),
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
  (“nExp”, "D [] 3", “CEXP”,
   “Prim () (Cons «D») [Prim () (Cons «[]») []; 𝕁 3]”),
  (“nExp”, "f [x,y] 3", “astExp nExp”,
   “‹f› ⬝ (‹x› ::ₚ ‹y› ::ₚ pNIL) ⬝ 𝕀 3”),
  (“nExp”, "f [x,y] 3", “CEXP”,
   “App () (𝕍 «f») [𝕍 «x» ::ₑ 𝕍 «y» ::ₑ []ₑ; 𝕁 3]”),
  (“nExp”, "let y = x + 3 in y + z",
   “astExp nExp”,
   “expLet [expdecFunbind "y" [] (‹+› ⬝ ‹x› ⬝ 𝕀 3)] (‹+› ⬝ ‹y› ⬝ ‹z›)”),
  (“nExp”, "let\n\
           \  y = x + 3\n\
           \  z = 10 in y + z",
   “astExp nExp”,
   “expLet [expdecFunbind "y" [] (‹+› ⬝ ‹x› ⬝ 𝕀 3);
            expdecFunbind "z" [] (𝕀 10)] (‹+› ⬝ ‹y› ⬝ ‹z›)”),
  (“nExp”, "let\n\
           \  y = x + 3\n\
           \  z = 10 in y + z", “CEXP”,
   “Letrec () [(«y», Lam () [] (𝕍 «x» +ₑ 𝕁 3));
               («z», Lam () [] (𝕁 10))]
              (𝕍 «y» +ₑ 𝕍 «z»)”),
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
  (“nPatAlt”, "_ -> 10", “astPatAlt”, “(patUScore, 𝕀 10)”),
  (“nExp”, "case e of [] -> 3\n\
           \          h:t -> 4",
   “astExp nExp”,
   “expCase ‹e› [(patApp "[]" [], 𝕀 3);
                 (patApp ":" [patVar "h"; patVar "t"], 𝕀 4)]”),
  (“nExp”, "case e of [] -> 3\n\
           \          h:t -> 4",
   “CEXP”,
   “Case () (𝕍 «e») «» [(«[]», [], 𝕁 3); («:», [«h»; «t»], 𝕁 4)] NONE”),
  (“nExp”, "case e of h : t -> 3\n\
           \          _ -> 10",
   “astExp nExp”,
    “expCase ‹e› [(patApp ":" [patVar "h"; patVar "t"], 𝕀 3); (patUScore, 𝕀 10)]”),
  (“nExp”, "case e of h : t -> 3\n\
           \          _ -> 10",
   “CEXP”,
   “Case () (𝕍 «e») «» [(«:», [«h»; «t»], 𝕁 3)] (SOME (𝕁 10))”),
  (“nExp”, "case e of h : t -> 3",
   “astExp nExp”,
   “expCase ‹e› [(patApp ":" [patVar "h"; patVar "t"], 𝕀 3)]”),
  (“nExp”, "case e of h : t -> 3",
   “CEXP”,
   “Case () (𝕍 «e») «» [(«:», [«h»; «t»], 𝕁 3)] NONE”),
  (“nDecl”, "f :: a -> Int", “astDecl”,
   “declTysig "f" (funTy (tyVar "a") (tyOp "Int" []))”),
  (“nDecl”, "f x y = x + y", “astDecl”,
   “declFunbind "f" [patVar "x"; patVar "y"] (‹+› ⬝ ‹x› ⬝ ‹y›)”),
  (“nDecl”, "h:t = f e", “astDecl”,
   “declPatbind (patApp ":" [patVar "h"; patVar "t"]) (‹f› ⬝ ‹e›)”),
  (“nDecl”, "data Foo a = C a Int | D [Int]", “astDecl”,
   “declData "Foo" ["a"] [("C", [tyVar "a"; tyOp "Int" []]);
                          ("D", [tyOp "List" [tyOp "Int"[]]])]”),
  (“nDecls”, "data Bar = C | D Int Bar\nf:: Bar -> Int", “astDecls”,
   “[declData "Bar" [] [("C", []); ("D", [tyOp "Int" []; tyOp "Bar" []])];
     declTysig "f" (funTy (tyOp "Bar" []) (tyOp "Int" []))]”)
]

val _ = app filetest [("test1.hs", NONE)]
