open HolKernel Parse boolLib bossLib
open cst_to_astTheory purePEGTheory testutils ast_to_cexpTheory
open pureParseTheory;

open pure_inferenceLib pure_letrec_cexpTheory pure_demands_analysisTheory

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

fun filetake nopt f =
    let val is = TextIO.openIn f
        fun getlines c A =
            if nopt = NONE orelse c < valOf nopt then
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

fun filetest (fname, sem, NONE) =
    let val str = filetake NONE fname
    in
      tprint ("Parsing contents of "^fname);
      fptest0 (“nDecls”, str, sem, “NONE”)
    end
  | filetest (fname, sem, SOME c) =
    let val s = filetake (SOME c) fname
        val _ = tprint ("Parsing " ^ Int.toString c ^ " lines of " ^ fname)
    in
      fptest0 (“nDecls”, s, sem, “NONE”)
    end
fun sp (* simple parse *) nt s =
    EVAL (list_mk_icomb(fullparse, [hd (decls nt), stringSyntax.fromMLstring s,
                                    ptSOME]))

val threetimesfour = “expApp (expApp (expVar «*») (expLit (litInt 3)))
                             (expLit (litInt 4))”
val _ = temp_overload_on("𝕀", “λi. expLit (litInt i)”);
val _ = temp_overload_on("𝕁", “λi. Prim () (AtomOp (Lit (Int i))) []”);
val _ = temp_overload_on("𝕊", “λs. expLit (litString s)”);
val _ = temp_overload_on("𝕋", “λs. Prim () (AtomOp (Lit (Str s))) []”);
val _ = temp_overload_on("𝕍", “pure_cexp$Var”)
val _ = temp_overload_on("𝕍u", “pure_cexp$Var ()”)
val _ = temp_overload_on("ASTEXP", “astExp nExp”)
val _ = temp_overload_on("CEXP",
  “flip (OPTION_BIND o ASTEXP)
     (translate_exp (insert (empty str_compare) «[]» listinfo))
    : (tokens$token, ppegnt, locs) parsetree -> unit cexp option”)
val _ = temp_overload_on ("CMAIN", “𝕍u «main»”);

val _ = temp_overload_on ("CDECLS",
                          inst [alpha |-> “:locs”]
                               “flip (OPTION_BIND o astDecls) decls_to_letrec”);

val _ = temp_overload_on("::ₑ", “λh t. Prim () (Cons «::») [h; t]”)
val _ = temp_set_fixity "::ₑ" (Infixr 490)
val _ = temp_overload_on("[]ₑ", “Prim () (Cons «[]») []”)
val _ = temp_overload_on(">>=", “λe1 e2. Prim () (Cons «Bind») [e1;e2]”)
val _ = set_fixity ">>=" $ Infix(NONASSOC, 100)

val _ = temp_overload_on ("+ₑ", “λe1 e2. Prim () (AtomOp Add) [e1; e2]”)
val _ = temp_set_fixity "+ₑ" (Infixl 500)

val _ = temp_overload_on ("*ₑ", “λe1 e2. Prim () (AtomOp Mul) [e1; e2]”)
val _ = temp_set_fixity "*ₑ" (Infixl 600)


val _ = app lextest [
  ("->", “[SymbolT «->»]”),
  (": :: <-", “[SymbolT «:»; SymbolT «::»; SymbolT «<-»]”),
  ("do x", “[AlphaT «do»; AlphaT «x»]”),
  ("foo_bar _", “[AlphaT «foo_bar»; UnderbarT]”),
  ("foo \"bar\\n\" baz", “[AlphaT «foo»; StringT «bar\n»; AlphaT «baz»]”),
  ("foo #(foo)", “[AlphaT «foo»; FFIT «foo»]”),
  ("foo\n--bar", “[AlphaT «foo»]”),
  ("foo\n--bar\n", “[AlphaT «foo»]”)
];

val _ = app fptest [
  (“nTy”, "[Integer]", “astType nTy”, “listTy intTy”),
  (“nTy”, "a -> B", “astType nTy”, “funTy (tyVar «a») (tyOp «B» [])”),
  (“nTy”, "(Tree a, B)", “astType nTy”, “tyTup [tyOp «Tree» [tyVar «a»];
                                                tyOp «B» []]”),
  (“nTy”, "[Integer -> ()]", “astType nTy”, “listTy (funTy intTy $ tyTup [])”),
  (“nExp”, "f 2 x", “astExp nExp”, “expVar «f» ⬝ 𝕀 2 ⬝ expVar «x»”),
  (“nExp”, "\\x y -> y x", “astExp nExp”,
   “expAbs (patVar «x») (expAbs (patVar «y») (expVar «y» ⬝ expVar «x»))”),
  (“nExp”, " if p x \nthen 1 else 2", “astExp nExp”,
   “expIf (expApp (expVar «p») (expVar «x»)) (𝕀 1) (𝕀 2)”),
  (“nExp”, " if p x \nthen 1 else 2", “CEXP”,
   “Case () (App () (pure_cexp$Var () «p») [pure_cexp$Var () «x»]) «»
         [(«True», [], Prim () (AtomOp (Lit (Int 1))) []);
          («False», [], Prim () (AtomOp (Lit (Int 2))) []);
         ] NONE”),
  (“nExp”, "z + if p x \nthen 1 else 2", “astExp nExp”,
   “expVar «+» ⬝ expVar «z» ⬝ expIf (expApp (expVar «p») (expVar «x»)) (𝕀 1) (𝕀 2)”),
  (“nExp”, "3 * 4 + 6", “astExp nExp”, “expVar «+» ⬝ (expVar «*» ⬝ 𝕀 3 ⬝ 𝕀 4) ⬝ 𝕀 6”),
  (“nExp”, "3 `mod` z + 7", “ASTEXP”, “expVar «+» ⬝ (expVar «mod» ⬝ 𝕀 3 ⬝ expVar «z») ⬝ 𝕀 7”),
  (“nExp”, "x * y `mod` z", “ASTEXP”, “expVar «mod» ⬝ (expVar «*» ⬝ expVar «x» ⬝ expVar «y») ⬝ expVar «z»”),
  (“nExp”, "x + y `foo` z", “ASTEXP”, “expVar «+» ⬝ expVar «x» ⬝ (expVar «foo» ⬝ expVar «y» ⬝ expVar «z»)”),
  (“nExp”, "x `seq` z", “ASTEXP”, “expVar «seq» ⬝ expVar «x» ⬝ expVar «z»”),
  (“nExp”, "x `seq` z", “CEXP”, “Prim () Seq [𝕍 «x»; 𝕍 «z»]”),
  (“nExp”, "6 + 3 * 4", “astExp nExp”, “expVar «+» ⬝ 𝕀 6 ⬝ (expVar «*» ⬝ 𝕀 3 ⬝ 𝕀 4)”),
  (“nExp”, "(6 + 3) * 4", “astExp nExp”, “expVar «*» ⬝ (expVar «+» ⬝ 𝕀 6 ⬝ 𝕀 3) ⬝ 𝕀 4”),
  (“nExp”, "h1:h2:t", “astExp nExp”, “expVar «h1» ::ₚ expVar «h2» ::ₚ expVar «t»”),
  (“nExp”, "1+3:t", “astExp nExp”, “(expVar «+» ⬝ 𝕀 1 ⬝ 𝕀 3) ::ₚ expVar «t»”),
  (“nExp”, "C () 3", “astExp nExp”, “expCon «C» [expTup []; 𝕀 3]”),
  (“nExp”, "C (x+y) 3", “astExp nExp”, “expCon «C» [expVar «+» ⬝ expVar «x» ⬝ expVar «y»; 𝕀 3]”),
  (“nExp”, "C (x,y) 3", “astExp nExp”, “expCon «C» [expTup [expVar «x»; expVar «y»]; 𝕀 3]”),
  (“nExp”, "D [] 3", “astExp nExp”, “expCon «D» [pNIL; 𝕀 3]”),
  (“nExp”, "D [] 3", “CEXP”,
   “Prim () (Cons «D») [Prim () (Cons «[]») []; 𝕁 3]”),
  (“nExp”, "#(stdout) \"Hello, world!\\n\"", “astExp nExp”,
   “expOp (Message «stdout») [𝕊 «Hello, world!\n»]”),
  (“nExp”, "#(stdout) \"Hello, world!\\n\"", “CEXP”,
   “Prim () (AtomOp (Message «stdout»)) [𝕋 «Hello, world!\n»]”),
  (“nExp”, "#(__Len) \"Hello, world!\\n\"", “astExp nExp”,
   “expOp Len [𝕊 «Hello, world!\n»]”),
  (“nExp”, "#(__Len) \"Hello, world!\\n\"", “CEXP”,
   “Prim () (AtomOp Len) [𝕋 «Hello, world!\n»]”),
  (“nExp”, "f [x,y] 3", “astExp nExp”,
   “expVar «f» ⬝ (expVar «x» ::ₚ expVar «y» ::ₚ pNIL) ⬝ 𝕀 3”),
  (“nExp”, "f [x,y] 3", “CEXP”,
   “App () (𝕍u «f») [𝕍u «x» ::ₑ 𝕍u «y» ::ₑ []ₑ; 𝕁 3]”),
  (“nExp”, "f \"foo\"", “astExp nExp”, “expVar «f» ⬝ 𝕊 «foo»”),
  (“nExp”, "f \"foo\"", “CEXP”, “App () (𝕍u «f») [𝕋 «foo»]”),
  (“nExp”, "let y = x + 3 in y + z",
   “astExp nExp”,
   “expLet [expdecFunbind «y» [] (expVar «+» ⬝ expVar «x» ⬝ 𝕀 3)] (expVar «+» ⬝ expVar «y» ⬝ expVar «z»)”),
  (“nExp”, "let\n\
           \  y = x + 3\n\
           \  z = 10 in y + z",
   “astExp nExp”,
   “expLet [expdecFunbind «y» [] (expVar «+» ⬝ expVar «x» ⬝ 𝕀 3);
            expdecFunbind «z» [] (𝕀 10)] (expVar «+» ⬝ expVar «y» ⬝ expVar «z»)”),
  (“nExp”, "let\n\
           \  y = x + 3\n\
           \  z = 10 in y + z", “CEXP”,
   “Letrec () [(«y», 𝕍u «x» +ₑ 𝕁 3); («z», 𝕁 10)] (𝕍u «y» +ₑ 𝕍u «z»)”),
  (“nExp”, "let { y = x + 3; z = 10; } in y + z", “CEXP”,
   “Letrec () [(«y», 𝕍u «x» +ₑ 𝕁 3);
               («z», 𝕁 10)]
              (𝕍 «y» +ₑ 𝕍 «z»)”),
  (“nExp”, "do x <- f y 3\n\
           \   foo x",
   “astExp nExp”,
   “expDo [expdostmtBind (patVar «x») (expVar «f» ⬝ expVar «y» ⬝ 𝕀 3)] (expVar «foo» ⬝ expVar «x»)”),
  (“nExp”, "do do x\n\
           \   y",
   “astExp nExp”,
   “expDo [expdostmtExp (expDo [] (expVar «x»))] (expVar «y»)”),
  (“nExp”, "do x <- f y 3\n\
           \   foo x",
   “CEXP”,
   “App () (𝕍u «f») [𝕍u «y»; 𝕁 3] >>=
    Lam () [«x»] (App () (𝕍u «foo») [𝕍u «x»])”),
  (“nExp”, "do let y = 10\n\
           \       f :: Integer -> Integer\n\
           \       f z = z + 1\n\
           \   x <- g (f y) 3\n\
           \   foo x",
   “astExp nExp”,
   “expDo [expdostmtLet [expdecFunbind «y» [] (𝕀 10);
                         expdecTysig «f» (funTy intTy intTy);
                         expdecFunbind «f» [patVar «z»] (expVar «+» ⬝ expVar «z» ⬝ 𝕀 1)];
           expdostmtBind (patVar «x») (expVar «g» ⬝ (expVar «f» ⬝ expVar «y») ⬝ 𝕀 3)]
          (expVar «foo» ⬝ expVar «x»)”),
  (“nPatAlt”, "_ -> 10", “astPatAlt”, “(patUScore, 𝕀 10)”),
  (“nExp”, "case e of [] -> 3\n\
           \          h:t -> 4",
   “astExp nExp”,
   “expCase (expVar «e») [(patApp «[]» [], 𝕀 3);
                 (patApp «::» [patVar «h»; patVar «t»], 𝕀 4)]”),
  (“nExp”, "case e of [] -> 3\n\
           \          h:t -> 4",
   “CEXP”,
   “Case () (𝕍u «e») «» [(«[]», [], 𝕁 3); («::», [«h»; «t»], 𝕁 4)] NONE”),
  (“nExp”, "case e of h : t -> 3\n\
           \          _ -> 10",
   “astExp nExp”,
    “expCase (expVar «e») [(patApp «::» [patVar «h»; patVar «t»], 𝕀 3);
                  (patUScore, 𝕀 10)]”),
  (“nExp”, "case e of h : t -> 3\n\
           \          _ -> 10",
   “CEXP”,
   “Case () (𝕍 «e») «» [(«::», [«h»; «t»], 𝕁 3)] (SOME ([(«[]», 0)], 𝕁 10))”),
  (“nExp”, "case e of h : t -> 3",
   “astExp nExp”,
   “expCase (expVar «e») [(patApp «::» [patVar «h»; patVar «t»], 𝕀 3)]”),
  (“nExp”, "case e of h : t -> 3",
   “CEXP”,
   “Case () (𝕍 «e») «» [(«::», [«h»; «t»], 𝕁 3)] NONE”),
  (“nDecl”, "f :: a -> Integer", “astDecl”,
   “declTysig «f» (funTy (tyVar «a») intTy)”),
  (“nDecl”, "f x y = x + y", “astDecl”,
   “declFunbind «f» [patVar «x»; patVar «y»] (expVar «+» ⬝ expVar «x» ⬝ expVar «y»)”),
  (“nDecl”, "h:t = f e", “astDecl”,
   “declPatbind (patApp «::» [patVar «h»; patVar «t»]) (expVar «f» ⬝ expVar «e»)”),
  (“nDecl”, "data Foo a = C a Integer | D [Integer]", “astDecl”,
   “declData «Foo» [«a»] [(«C», [tyVar «a»; intTy]);
                          («D», [tyOp «[]» [intTy]])]”),
  (“nDecls”, "data Bar = C | D Integer Bar\nf:: Bar -> Integer", “astDecls”,
   “[declData «Bar» [] [(«C», []); («D», [intTy; tyOp «Bar» []])];
     declTysig «f» (funTy (tyOp «Bar» []) intTy)]”),
  (“nDecls”, "data Bar = C | D Integer Bar\nf:: Bar -> Integer", “CDECLS”,
   “(Letrec () [] CMAIN,
     [(1n, [(«[]»,[]); («::»,[TypeVar 0; TypeCons 0 [TypeVar 0]])]);
      (0n, [(«C»,[]); («D»,[PrimTy Integer; TypeCons 1 []])])])”),
  (“nDecls”, "f x = x + 1\ndata Foo a b = C Bool a Integer | D b [Foo a b]",
   “CDECLS”,
   “(Letrec () [(«f», Lam () [«x»] (𝕍 «x» +ₑ 𝕁 1))] CMAIN,
     [(1n,[(«[]»,[]); («::»,[TypeVar 0; TypeCons 0 [TypeVar 0]])]);
      (2n,
       [(«C»,[PrimTy Bool; TypeVar 0; PrimTy Integer]);
        («D»,[TypeVar 1; TypeCons 0 [TypeCons 1 [TypeVar 0; TypeVar 1]]])])])”),
  (“nDecls”, "data Foo a b = C Bool a Integer | D b [Bar a]\n\
             \data Bar d = E d | F (Foo d Integer)\n\
             \f x = case x of\n\
             \        C b a i -> i + 1\n\
             \        _ -> 3", “CDECLS”,
   “(Letrec () [
      («f»,Lam () [«x»] (Case () (𝕍 «x») «»
                              [(«C», [«b»; «a»; «i»], 𝕍 «i» +ₑ 𝕁 1)]
                              (SOME([(«D», 2)], 𝕁 3))))
      ] CMAIN,
     [(1n,[(«[]»,[]); («::»,[TypeVar 0; TypeCons 0 [TypeVar 0]])]);
      (1n,
       [(«E»,[TypeVar 0]); («F»,[TypeCons 2 [TypeVar 0; PrimTy Integer]])]);
      (2n,
       [(«C»,[PrimTy Bool; TypeVar 0; PrimTy Integer]);
        («D»,[TypeVar 1; TypeCons 0 [TypeCons 1 [TypeVar 0]]])])])”),
  (“nDecls”, "main = do\n\
             \  #(stdout) \"Hello, world!\\n\"\n",
   “CDECLS”,
   “(Letrec () [
     («main», (Prim () (AtomOp (Message «stdout»)) [𝕋 «Hello, world!\n»]))
     ] CMAIN,
     [(1n,[(«[]»,[]); («::»,[TypeVar 0; TypeCons 0 [TypeVar 0]])])])”)
];

val _ = app filetest [("test1.hs", “astDecls”, NONE)];

val _ = app convtest [
  ("s2cexp hello world",
   EVAL, “string_to_cexp "main = do Act (#(stdout) \"Boo!\")"”,
   “SOME (Letrec () [
     («main», Prim () (Cons «Act») [Prim () (AtomOp (Message «stdout»)) [𝕋 «Boo!»]])
     ] CMAIN,
     [(1n,[(«[]»,[]); («::»,[TypeVar 0; TypeCons 0 [TypeVar 0]])])])”),
  ("s2cexp bracey-let",
   EVAL, “string_to_cexp "main = 4\n\
                         \f x = let { y = x + 1; z = y * 2 } in [z,y]"”,
   “SOME (Letrec () [
     («main», 𝕁 4);
     («f», Lam () [«x»] (Letrec () [(«y», 𝕍 «x» +ₑ 𝕁 1); («z», 𝕍 «y» *ₑ 𝕁 2)]
                                (𝕍 «z» ::ₑ 𝕍 «y» ::ₑ []ₑ)))] CMAIN,
     [(1n,[(«[]»,[]); («::»,[TypeVar 0; TypeCons 0 [TypeVar 0]])])])”)
]


val handle_inferResult_def = Define‘
  handle_inferResult ires =
    case ires of
        OK x => SOME x
      | Err _ => NONE
’
val upto_demands_def = Define‘
  upto_demands (opts:compiler_opts) s =
  do
    (e1,ns) <- string_to_cexp s;
    e2 <<- transform_cexp opts e1;
    handle_inferResult $ infer_types ns e2 ;
    return e2;
  od
’;

val c0 = REWRITE_CONV [upto_demands_def] THENC
         LAND_CONV EVAL THENC
         REWRITE_CONV [optionTheory.OPTION_BIND_def] THENC
         pairLib.GEN_BETA_CONV THENC RAND_CONV EVAL THENC SCONV [LET_THM]
val upto_eval0 =
  c0 THENC
  LAND_CONV (pure_inferenceLib.pure_infer_eval THENC EVAL THENC
             SCONV[])

val upto_eval = upto_eval0 THENC SCONV[]


val hworld = "return v = Ret v\n\
             \s1 ++ s2 = #(__Concat) s1 s2\n\
             \print s = Act (#(stdout) (s ++ \"\\n\"))\n\
             \main = do\n\
             \  print \"Hello\"\n\
             \  return ()"

val _ = temp_add_user_printer("maphide", “mlmap$Map c bm”,
            (fn _ => fn be => fn syspr => fn {add_string,...} =>
             fn gravs => fn depth => fn t => add_string "𝕸"))
fun extract_int adds t =
    let val aop = el 2 (#2 (strip_comb t))
        val i_t = rand (rand (rand aop))
        val i = intSyntax.int_of_term i_t
        fun slice s = String.extract(s, 0, SOME (size s - 1))
    in
      adds (slice (Arbint.toString i) ^ "ₑ")
    end

fun extract_mlstring adds t =
    let val s_t = rand t
        val s = stringSyntax.fromHOLstring s_t
    in
      adds (Literal.string_literalpp {ldelim = "‹",rdelim = "›"} s)
    end


val _ = temp_add_user_printer("prettyint", “Prim m (AtomOp (Lit (Int i))) []”,
            (fn _ => fn be => fn syspr => fn {add_string,...} =>
             fn gravs => fn depth => fn t => extract_int add_string t
                 handle HOL_ERR _ => raise term_pp_types.UserPP_Failed))

val _ = temp_add_user_printer("prettylet", “pure_cexp$Let m”,
            (fn _ => fn be => fn syspr => fn {add_string,...} =>
             fn gravs => fn depth => fn t => add_string "Let"
                 handle HOL_ERR _ => raise term_pp_types.UserPP_Failed))

val _ = temp_add_user_printer("prettynil", “Prim m (Cons «[]») []”,
            (fn _ => fn be => fn syspr => fn {add_string,...} =>
             fn gravs => fn depth => fn t => add_string "[]ₑ"))

val _ = temp_add_user_printer("prettyvar", “pure_cexp$Var m s”,
            (fn _ => fn be => fn syspr => fn {add_string,...} =>
             fn gravs => fn depth => fn t => extract_mlstring add_string(rand t)
                 handle HOL_ERR _ => raise term_pp_types.UserPP_Failed))

fun op2str t =
  case #Name (dest_thy_const t) of
      "Mul" => "*"
    | "Add" => "+"
    | "Sub" => "-"
    | "Lt" => "<"
    | "Gt" => ">"
    | s => s

val _ = temp_add_user_printer(
  "prettybinop",
  “pure_cexp$Prim m (AtomOp p) [arg1; arg2]”,
   (fn _ => fn be => fn syspr => fn {add_string,ublock,add_break,...} =>
             fn gravs => fn depth => fn t =>
                let open smpp term_pp_types
                    val (_, [_, aop, args_t]) = strip_comb t
                    val pr = syspr {gravs = (Top,Top,Top), binderp = false,
                                    depth = depth - 1}
                    val (args, _) = listSyntax.dest_list args_t
                in
                  add_string "(" >>
                  ublock PP.INCONSISTENT 1 (
                     pr (el 1 args) >> add_string " " >>
                     add_string (op2str (rand aop)) >> add_break(1,0) >>
                     pr (el 2 args)
                  ) >> add_string ")"
                end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed))

val _ = temp_add_user_printer(
  "prettyapp",
  “pure_cexp$App m f args”,
   (fn _ => fn be => fn syspr => fn {add_string,ublock,add_break,...} =>
             fn gravs => fn depth => fn t =>
                let open smpp term_pp_types
                    val (_, [_, f, args_t]) = strip_comb t
                    val pr = syspr {gravs = (Top,Top,Top), binderp = false,
                                    depth = depth - 1}
                in
                  ublock PP.INCONSISTENT 0 (
                     pr f >> add_break(0,0) >> pr args_t
                  )
                end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed))

val _ = temp_add_user_printer(
  "prettypcons",
  “pure_cexp$Prim m (Cons s) args”,
   (fn _ => fn be => fn syspr => fn {add_string,ublock,add_break,...} =>
             fn gravs => fn depth => fn t =>
                let open smpp term_pp_types
                    val (_, [_, f, args_t]) = strip_comb t
                    val pr = syspr {gravs = (Top,Top,Top), binderp = false,
                                    depth = depth - 1}
                in
                  ublock PP.INCONSISTENT 0 (
                     add_string "PCons" >>
                     pr (rand f) >> add_break(0,0) >> pr args_t
                  )
                end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed))


val _ = set_trace "pp_avoids_symbol_merges" 0


fun filetake' fname nopt =
    let
      val s0 = filetake nopt fname
      val sfx = case nopt of NONE => "" | SOME _ => "\n\nmain = main"
    in
      s0 ^ sfx
    end

fun string_check s c f =
    let
      val s_t = stringSyntax.fromMLstring s
    in
      c “^f ^s_t”
    end;

val with_demands_def = Define‘
  with_demands opts s =
  do
    (e1,ns) <- string_to_cexp s;
    e2 <<- transform_cexp opts e1;
    handle_inferResult $ infer_types ns e2;
    e3 <<- demands_analysis opts e2;
    handle_inferResult $ infer_types ns e3;
    return e3
  od
’;

val d0 = REWRITE_CONV [with_demands_def] THENC
         LAND_CONV EVAL THENC
         REWRITE_CONV [optionTheory.OPTION_BIND_def] THENC
         pairLib.GEN_BETA_CONV THENC RAND_CONV EVAL THENC
         PURE_ONCE_REWRITE_CONV [LET_THM] THENC
         pairLib.GEN_BETA_CONV

val wd0 =
  d0 THENC
  LAND_CONV (pure_inferenceLib.pure_infer_eval THENC EVAL THENC
             SCONV[])

val wd = wd0 THENC
         PURE_REWRITE_CONV[optionTheory.OPTION_IGNORE_BIND_thm] THENC
         RAND_CONV EVAL THENC
         PURE_ONCE_REWRITE_CONV[LET_THM] THENC pairLib.GEN_BETA_CONV THENC
         LAND_CONV (pure_inferenceLib.pure_infer_eval THENC EVAL THENC
                    SCONV[]) THENC
         PURE_REWRITE_CONV[optionTheory.OPTION_IGNORE_BIND_thm]

val notypes_def = Define‘
  notypes opts s =
  do
    (e1,ns) <- string_to_cexp s;
    e2 <<- transform_cexp opts e1;
    return e2
  od
’;

(* val _ = tprint "string_to_cexp paper.hs" *)
(* string_check (filetake' "paper.hs" NONE) EVAL ``string_to_cexp``; *)
