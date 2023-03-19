open HolKernel Parse boolLib bossLib;


open stringTheory grammarTheory ispegexecTheory ispegTheory tokenUtilsTheory
     pureNTTheory pureTokenUtilsTheory
local open pure_lexer_implTheory stringLib in end

val _ = new_theory "purePEG";

val _ = set_grammar_ancestry
        ["pureTokenUtils", "grammar", "pure_lexer_impl", "ispegexec", "pureNT"]


Definition sumID_def[simp]:
  sumID (INL x) = x ∧ sumID (INR y) = y
End

Definition mkNT_def:
  mkNT n ptl = [Nd (INL n, ptree_list_loc ptl) ptl]
End

Definition NT_def:
  NT (n:α) = nt (INL n : α + num)
End

Overload TK = “grammar$TOK : token -> (token,ppegnt) grammar$symbol”

val _ = app clear_overloads_on ["seql", "choicel", "pegf"]

Definition mktoklf_def:
  mktokLf t = [Lf (TK (FST t), SND t)]
End

Definition pegf_def: pegf sym f = seq sym (empty []) (λl1 l2. f l1)
End

Definition seql_def:
  seql l f = pegf (FOLDR (\p acc. seq p acc (++)) (empty []) l) f
End

Definition choicel_def:
  choicel [] = not (empty []) [] ∧
  choicel (h::t) = choice h (choicel t) sumID
End

Definition RPT1_def:
  RPT1 e = seql [e; rpt e FLAT] I
End

Definition sepby1_def:
  sepby1 e sep = seql [e; rpt (seql [sep; e] I) FLAT] I
End
Definition sepby_def:
  sepby e sep = choicel [sepby1 e sep; empty []]
End

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

Overload tokGE = “λp. tok p mktokLf lrGE”
Overload tokGT = “λp. tok p mktokLf lrGT”
Overload tokEQ = “λp. tok p mktokLf lrEQ”
Overload NTGE = “λn. NT n I lrGE”
Overload NTGT = “λn. NT n I lrGT”
Overload NTEQ = “λn. NT n I lrEQ”

Definition odds_def[simp]:
  odds [] = [] ∧
  odds [x] = [x] ∧
  odds (x::y::rest) = x :: odds rest
End

Definition purePEG_def[nocompute]:
  purePEG = <|
    anyEOF := "Didn't expect an EOF";
    tokFALSE := "Failed to see expected token";
    tokEOF := "Failed to see expected token; saw EOF instead";
    notFAIL := "Not combinator failed";
    iFAIL := "Indentation failure";
    start := NT nDecls I lrOK;
    rules :=
    FEMPTY |++ [
        (INL nDecls, pegf (rpt (NT nDecl I lrEQ) FLAT) (mkNT nDecls));
        (INL nDecl,
         choicel [
             (* declare id and its type *)
             seql [tok lcname_tok mktokLf lrEQ;
                   tokGT ((=) $ SymbolT "::");
                   NT nTy I lrGT] (mkNT nDecl);
             (* declare new data type and its constructors *)
             seql [tokEQ ((=) $ AlphaT "data") ;
                   tokGT capname_tok;
                   rpt (tokGT lcname_tok) FLAT;
                   tokGT ((=) EqualsT) ;
                   sepby1 (NT nTyConDecl I lrGT)
                          (tokGT ((=) BarT))]
                  (mkNT nDecl);
             (* define value *)
             pegf (NT nValBinding I lrEQ) (mkNT nDecl)]);
        (INL nValBinding,
         seql [NT nExpEQ I lrEQ; tokGT ((=) $ EqualsT); NT nExp I lrEQ]
              (mkNT nValBinding));
        (INL nTyConDecl,
         seql [tokGE capname_tok; rpt (NT nTyBase I lrGE) FLAT]
              (mkNT nTyConDecl));

        (INL nTyBase,
         choicel [pegf (tok capname_tok mktokLf lrGE) (mkNT nTyBase);
                  pegf (tok lcname_tok mktokLf lrGE) (mkNT nTyBase);
                  seql [tokGE ((=) LparT);
                        sepby (NT nTy I lrGE) (tokGE ((=) CommaT));
                        tokGE ((=) RparT) ]
                       (mkNT nTyBase);
                  seql [tokGE ((=)LbrackT); NT nTy I lrGE; tokGE((=) RbrackT)]
                       (mkNT nTyBase)]);
        (INL nTyApp,
         choicel [seq
                  (tokGE capname_tok)
                  (choice (RPT1 (NT nTyBase I lrGE)) (empty []) sumID)
                  (λpt1 pt2. if NULL pt2 then mkNT nTyApp (mkNT nTyBase pt1)
                             else mkNT nTyApp (pt1 ++ pt2));
                  pegf (NT nTyBase I lrGE) (mkNT nTyApp)]);

        (INL nTy,
         pegf (sepby1 (NT nTyApp I lrGE) (tokGE ((=) $ SymbolT "->")))
              (mkNT nTy));

        (INL nEqBindSeq,
         choicel [
             seql [tokGT ((=) LbraceT);
                   sepby (NT nFreeEqBind I lrOK)
                         (tok ((=) SemicolonT) mktokLf lrOK);
                   choicel [tok ((=) SemicolonT) mktokLf lrOK; empty[]];
                   tok ((=) RbraceT) mktokLf lrOK] (mkNT nEqBindSeq);
             NTGT nEqBindSeq';
           ]);

        (INL nEqBindSeq',
         pegf (rpt (NT nEqBind I lrEQ) FLAT) (mkNT nEqBindSeq));

        (INL nFreeEqBind,
         choicel [seql [NT nExp I lrOK;
                        tok ((=) EqualsT) mktokLf lrOK;
                        NT nExp I lrOK] (mkNT nEqBind);
                  seql [tok lcname_tok mktokLf lrOK;
                        tok ((=) $ SymbolT "::") mktokLf lrOK;
                        NT nTy I lrOK]
                       (mkNT nEqBind)]);

        (INL nEqBind,
         choicel [seql [NT nExpEQ I lrEQ; tokGT ((=) EqualsT) ; NTGT nExp]
                       (mkNT nEqBind);
                  seql [tok lcname_tok mktokLf lrEQ;
                        tokGT ((=) $ SymbolT "::");
                        NT nTy I lrGT]
                       (mkNT nEqBind)]);
        (INL nOp,
         choicel [pegf (tok isSymbolOpT mktokLf lrEQ) (mkNT nOp);
                  seql [tok ((=) (SymbolT "`")) mktokLf lrEQ;
                        tok isAlphaT mktokLf lrGE;
                        tok ((=) (SymbolT "`")) mktokLf lrGE] (mkNT nOp)]);

        (INL nIExp,
         seql [NTEQ nFExp; rpt (seql [NTGT nOp; NTEQ nFExp2] I) FLAT]
              (mkNT nIExp));
        (INL nIExpEQ,
         seql [NTEQ nFExpEQ; rpt (seql [NTGE nOp; NTGE nFExp2] I) FLAT]
              (mkNT nIExp));
        (INL nFExp2, pegf (choicel [NTGE nLSafeExp; NTGE nFExp]) (mkNT nFExp2));
        (INL nFExp,
         seql [NTEQ nAExp; rpt (NTEQ nAExp) FLAT] (mkNT nFExp));
        (INL nFExpEQ,
         seql [NTEQ nAExpEQ; rpt (NTEQ nAExp) FLAT] (mkNT nFExp));
        (INL nDoBlock,
         choicel [
             seql [tokGT ((=) LbraceT); NT nDoStmtSeq I lrOK;
                   tok ((=) RbraceT) mktokLf lrOK]
                  (mkNT nDoBlock o FRONT o DROP 1);
             pegf (NTGT nDoBlockLayout) (mkNT nDoBlock)
           ]);
        (INL nDoBlockLayout, RPT1 (NTEQ nDoStmtSeqEQ));
        (INL nDoStmtSeq,
         pegf (sepby1 (NTEQ nDoStmt) (tokGT ((=) SemicolonT))) odds);
        (INL nDoStmtSeqEQ,
         seql [NTEQ nDoStmtEQ;
               rpt (seql [tokGT ((=) SemicolonT); NTEQ nDoStmt] I) FLAT]
              odds);
        (INL nDoStmt,
         choicel [
             seql [NTEQ nExp;
                   choicel [seql [tokGT ((=) $ SymbolT "<-"); NTGT nExp] I;
                            empty []]
                  ] (mkNT nDoStmt);
             seql [tokGT ((=) LetT); NTGT nEqBindSeq'] (mkNT nDoStmt)
           ]);
        (INL nDoStmtEQ,
         choicel [
             seql [NTEQ nExpEQ;
                   choicel [seql [tokGT ((=) $ SymbolT "<-"); NTGT nExp] I;
                            empty []]
                  ] (mkNT nDoStmt);
             seql [tokEQ ((=) LetT); NTGT nEqBindSeq'] (mkNT nDoStmt)
           ]);
        (* an "l-safe" expression is one that begins with a token that
           ensures the rest of the text of the expression belongs under
           that "constructor", regardless of infixes that might appear
           after the beginning left-token.  These are lambda, if-then-else,
           do, and let expressions *)
        (INL nLSafeExp,
         choicel [seql [tokGT ((=) $ SymbolT "\\") ; RPT1 (NTEQ nAPat);
                        tokGT ((=) $ SymbolT "->");
                        NTEQ nExp] (mkNT nExp);
                  seql [tokGT ((=) IfT); NTEQ nExp;
                        tokGT ((=) ThenT); NTEQ nExp;
                        tokGT ((=) ElseT); NTEQ nExp] (mkNT nExp);
                  seql [tokGT ((=) LetT) ; NTEQ nEqBindSeq ;
                        tokGT ((=) InT) ; NTEQ nExp] (mkNT nExp);
                  seql [tokGT ((=) $ AlphaT "do"); NTEQ nDoBlock] (mkNT nExp);
                  seql [tokGT ((=) CaseT); NTEQ nExp; tokGT ((=) OfT);
                        NTGT nPatAlts] (mkNT nExp);
                 ]);
        (INL nLSafeExpEQ,
         choicel [seql [tokEQ ((=) $ SymbolT "\\") ; RPT1 (NTEQ nAPat);
                        tokGT ((=) $ SymbolT "->");
                        NTEQ nExp] (mkNT nExp);
                  seql [tokEQ ((=) IfT); NTEQ nExp;
                        tokGT ((=) ThenT); NTEQ nExp;
                        tokGT ((=) ElseT); NTEQ nExp] (mkNT nExp);
                  seql [tokEQ ((=) LetT) ; NTEQ nEqBindSeq ;
                        tokGT ((=) InT) ; NTEQ nExp] (mkNT nExp);
                  seql [tokEQ ((=) $ AlphaT "do"); NTGT nDoBlock] (mkNT nExp);
                  seql [tokEQ ((=) CaseT); NTEQ nExp; tokGT ((=) OfT);
                        NTGT nPatAlts] (mkNT nExp);
                 ]);

        (INL nAPat,
         choicel [pegf (tokGT lcname_tok) (mkNT nAPat);
                  pegf (NTEQ nLit) (mkNT nAPat);
                  pegf (tokGT ((=) UnderbarT)) (mkNT nAPat)]);
        (INL nPat, pegf (NT nAPat I lrEQ) (mkNT nPat));

        (INL nPatAlts, pegf (rpt (NTEQ nPatAlt) FLAT) (mkNT nPatAlts));
        (INL nPatAlt, seql [NTEQ nExpEQ; tokGT ((=) $ SymbolT "->"); NTGT nExp]
                           (mkNT nPatAlt));
        (INL nExp,
         choicel [NTEQ nLSafeExp; pegf (NTEQ nIExp) (mkNT nExp)]);
        (INL nExpEQ,
         choicel [NTEQ nLSafeExpEQ; pegf (NTEQ nIExpEQ) (mkNT nExp)]);

        (INL nAExp, (* "atomic" / bottom-of-grammar expressions *)
         choicel [pegf (NTGT nLit) (mkNT nAExp);
                  seql [tokGT ((=) LparT) ;
                        sepby (NT nExp I lrEQ) (tokGT ((=) CommaT));
                        tokGT ((=) RparT)] (mkNT nAExp);
                  seql [tokGT ((=) LbrackT) ;
                        sepby (NT nExp I lrEQ) (tokGT ((=) CommaT));
                        tokGT ((=) RbrackT)] (mkNT nAExp);
                  pegf (tokGT isAlphaT) (mkNT nAExp);
                  pegf (tokGT ((=) UnderbarT)) (mkNT nAExp);
                  pegf (tokGT (IS_SOME o destFFIT)) (mkNT nAExp)
                 ]);

        (INL nAExpEQ,
         choicel [pegf (NTEQ nLit) (mkNT nAExp);
                  seql [tokEQ ((=) LparT) ;
                        sepby (NT nExp I lrEQ) (tokGT ((=) CommaT));
                        tokGT ((=) RparT)] (mkNT nAExp);
                  seql [tokEQ ((=) LbrackT) ;
                        sepby (NT nExp I lrEQ) (tokGT ((=) CommaT));
                        tokGT ((=) RbrackT)] (mkNT nAExp);
                  pegf (tokEQ isAlphaT) (mkNT nAExp) ;
                  pegf (tokEQ ((=) UnderbarT)) (mkNT nAExp);
                  pegf (tokEQ (IS_SOME o destFFIT)) (mkNT nAExp)
                 ]);

        (INL nLit,
         choicel [tok isInt (mkNT nLit o mktokLf) lrEQ;
                  tok isString (mkNT nLit o mktokLf) lrEQ]);
      ]
  |>
End
val rules_t = ``purePEG.rules``
fun ty2frag ty = let
  open simpLib
  val {convs,rewrs} = TypeBase.simpls_of ty
in
  merge_ss (rewrites rewrs :: map conv_ss convs)
end
(* can't use srw_ss() as it will attack the bodies of the rules,
   and in particular, will destroy predicates from tok
   constructors of the form
        do ... od = SOME ()
   which matches optionTheory.OPTION_BIND_EQUALS_OPTION, putting
   an existential into our rewrite thereby *)
val rules = SIMP_CONV (bool_ss ++ ty2frag ``:(α,β,γ,δ)ispeg``)
                      [purePEG_def, combinTheory.K_DEF,
                       finite_mapTheory.FUPDATE_LIST_THM] rules_t

val _ = print "Calculating application of purePEG rules\n"
val purepeg_rules_applied = let
  val app0 = finite_mapSyntax.fapply_t
  val theta =
    Type.match_type (type_of app0 |> dom_rng |> #1) (type_of rules_t)
  val app = inst theta app0
  val app_rules = AP_TERM app rules
  val sset = bool_ss ++ ty2frag ``:'a + 'b`` ++ ty2frag ``:ppegnt``
  fun mkrule t =
    AP_THM app_rules ``INL ^t : ppegnt + num``
      |> SIMP_RULE sset
                   [finite_mapTheory.FAPPLY_FUPDATE_THM]
  val ths = TypeBase.constructors_of ``:ppegnt`` |> map mkrule
in
  save_thm("purepeg_rules_applied", LIST_CONJ ths);
  ths
end

Theorem FDOM_purePEG =
  SIMP_CONV (srw_ss()) [purePEG_def,
                        finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
                        finite_mapTheory.DOMSUB_FUPDATE_THM,
                        finite_mapTheory.FUPDATE_LIST_THM]
            ``FDOM purePEG.rules``;



val spec0 =
    ispeg_nt_thm |> Q.GEN `G`  |> Q.ISPEC `purePEG`
                 |> SIMP_RULE (srw_ss()) [FDOM_purePEG]
                 |> Q.GEN `n`

val mkNT = ``INL : ppegnt -> ppegnt + num``

Theorem frange_image[local]:
  FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)
Proof
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem peg_range[local] =
    SCONV (FDOM_purePEG :: frange_image :: purepeg_rules_applied)
          “FRANGE purePEG.rules”

Theorem subexprs_NT[local]:
  subexprs (NT n f r) = {NT n f r}
Proof
  simp[subexprs_def, NT_def]
QED

val sugar_rwts = [choicel_def, seql_def, pegf_def, NT_def,
                  sepby1_def, RPT1_def, sepby_def]

Theorem purePEG_exprs =
  “Gexprs purePEG”
    |> SIMP_CONV (srw_ss())
         ([Gexprs_def, subexprs_def, subexprs_NT,
           pred_setTheory.INSERT_UNION_EQ, purePEG_def, peg_range] @
          sugar_rwts)

val topo_nts = [“nLit”, “nAExp”, “nAExpEQ”,
                “nFExpEQ”, “nFExp”,  “nOp”, “nLSafeExp”,
                “nFExp2”,
                “nIExpEQ”, “nLSafeExpEQ”, “nIExp”, “nExp”,
                “nExpEQ”, “nValBinding”, “nDecl”, “nPatAlt”, “nAPat”,
                “nEqBind”, “nDoStmt”, “nDoStmtEQ”, “nTyBase”,
                “nDoStmtSeqEQ”, “nDoStmtSeq”, “nDoBlockLayout”,
                “nDoBlock”]

fun npeg0(t,acc) =
  let
   val _ = print ("Proving peg0 result for " ^ term_to_string t ^ "\n")
   val th = Q.prove(‘peg0 purePEG (nt (INL ^t) f R) = F ∧
                     pegfail purePEG (nt (INL ^t) f R)’,
                    simp [peg0_nt] >>
                    SIMP_TAC (srw_ss()) (purepeg_rules_applied @ sugar_rwts @
                                         [FDOM_purePEG, peg0_rwts] @ acc))
  in
    th::acc
  end

Theorem npeg_rwts = List.foldl npeg0 [] topo_nts |> LIST_CONJ

fun wfnt(t,acc) = let
  val _ = print ("Proving wfpeg for " ^ term_to_string t ^ "\n")
  val th =
    Q.prove(`wfpeg purePEG (nt (INL ^t) f R)`,
          SIMP_TAC (srw_ss())
                   (purepeg_rules_applied @
                    [wfpeg_nt, FDOM_purePEG, wfpeg_rwts,
                     peg0_rwts, npeg_rwts] @
                    sugar_rwts @ acc))
in
  th::acc
end;

val wfpeg_nt_rwts =
  List.foldl wfnt []
    (topo_nts @ [“nPatAlts”, “nDecls”, “nEqBindSeq”, “nDoBlock”,
                 “nEqBindSeq'”, “nTyApp”, “nTy”, “nFreeEqBind”,
                 “nTyConDecl”])
  |> LIST_CONJ

Theorem PEG_wellformed[simp]:
   wfG purePEG
Proof
  simp[wfG_def, purePEG_exprs] >> rw[] >>
  simp(wfpeg_rwts :: FDOM_purePEG :: pegf_def :: peg0_rwts ::
       npeg_rwts :: wfpeg_nt_rwts ::
       purepeg_rules_applied)
QED

Theorem purePEG_exec_thm[compute] =
  TypeBase.constructors_of ``:ppegnt``
    |> map (fn t => ISPEC (mk_comb(mkNT, t)) spec0)
    |> map (SIMP_RULE bool_ss (purepeg_rules_applied @
                               [pureNTs_distinct, sumTheory.INL_11]))
    |> LIST_CONJ;

Theorem peg_start = SCONV [purePEG_def] “purePEG.start”
Theorem parse_nDecls_total =
        MATCH_MP (GEN_ALL ispeg_exec_total) PEG_wellformed
        |> SRULE [peg_start]

Theorem coreloop_nDecls_total =
  MATCH_MP coreloop_total PEG_wellformed
    |> REWRITE_RULE [peg_start] |> Q.GEN `i`

Theorem owhile_nDecls_total =
        SIMP_RULE (srw_ss()) [coreloop_def] coreloop_nDecls_total



Theorem gettok[local,compute] = pure_lexer_implTheory.get_token_def
(* val input1 = EVAL “lexer_fun "foo :: A -> B"”
val input2 = EVAL “lexer_fun "foo ::\n A -> B"”
val input3 = EVAL “lexer_fun "foo :: A\n     ->\n B"”
*)

fun test n s =
  EVAL “ispeg_exec purePEG (nt (INL ^n) I lrOK)
          (lexer_fun ^(stringLib.fromMLstring s))
          lpTOP [] NONE [] done failed” |> concl |> rhs
val testty = test “nTy”


val good1 = test “nDecls”
                     "foo :: A -> (B,\n\
                     \ C,D)\n\
                     \bar :: C\n\
                     \   -> D\n\
                     \baz :: D\n\
                     \qux::(A->B)->C"

Theorem good2 =
    EVAL “ispeg_exec purePEG (nt (INL nDecls) I lrOK)
          (lexer_fun " foo :: A -> [B -> C]\n\
                     \ bar :: C\n")
          lpTOP [] NONE [] done failed”

Theorem good3 =
        EVAL “ispeg_exec purePEG (nt (INL nDecls) I lrOK)
             (lexer_fun "foo b x = if b then 10 else g (x + 11)")
             lpTOP [] NONE [] done failed”

(* stops at arrow line, leaving it in input still to be consumed *)
Theorem fail1 =
    EVAL “ispeg_exec purePEG (nt (INL nDecls) I lrOK)
          (lexer_fun "foo :: A -> B\n\
                     \bar :: C\n\
                     \-> D\n\
                     \baz :: D")
          lpTOP [] NONE [] done failed”

(* also stops at arrow *)
Theorem fail1a =
    EVAL “ispeg_exec purePEG (nt (INL nDecls) I lrOK)
          (lexer_fun "bar :: C\n\
                     \-> D")
          lpTOP [] NONE [] done failed”

(* and again *)
Theorem fail1b =
    EVAL “ispeg_exec purePEG (nt (INL nDecl) I lrOK)
          (lexer_fun "bar :: C\n\
                     \-> D")
          lpTOP [] NONE [] done failed”

(* stops with at bar line *)
Theorem fail2 =
    EVAL “ispeg_exec purePEG (nt (INL nDecls) I lrOK)
          (lexer_fun " foo :: A -> B\n\
                     \bar :: C\n")
          lpTOP [] NONE [] done failed”


val ty1 = testty "Foo"
val ty1a = testty "a"
val ty2 = testty "Foo -> a"
val ty3 = testty "a -> b -> c"
val ty4 = testty "(a -> B) -> c"
val ty5 = testty "Foo a B"
val ty6 = testty "Foo [Bar] -> a"
val ty7 = testty " Foo Bar ->\na"

Overload P[local] = “POSN”
Overload L[local] = “Locs”

Theorem gooddata1 =
        EVAL “ispeg_exec purePEG (nt (INL nDecls) I lrOK)
             (lexer_fun "data Ei a b = \n\
                        \   Left a (Int -> Int) |\n\
                        \ Right b [b] | Nothing\n\
                        \data Point = Point Int Int | Q ()") lpTOP [] NONE []
             done failed”

(* stops at the | after Left a
   and says it has a successful parse up to that point *)
Theorem faildata1 =
        EVAL “ispeg_exec purePEG (nt (INL nDecls) I lrOK)
             (lexer_fun "data Maybe a = Just a | Nothing\n\
                        \data Either a b = \n\
                        \   Left a |\n\
                        \Right b ") lpTOP [] NONE []
             done failed”

val data1 = test “nDecls”
  "data Foo a = C1 a Int (E (D Bool)Int) | C2 (D Bool) Int"

val letexp1 = test “nExp”
  "let x = 3\n\
  \    y = 4 in x + y"
val letexp2 = test “nExp”
  "let\n\
  \ x = 3\n\
  \ y = 4\n\
  \ in x + y"
val letexp3 = test “nExp”
  "   let\n\
  \x = 3\n\
  \y = 4 in x + y"
val letexp3 = test “nExp”
  "z * let\n\
  \x = 3\n\
  \y = 4 in x + y"
val caseexp1 =
  test “nExp” "case h:t of\n\
                  \  y -> 3\n\
                  \   + 6\n\
                  \  z -> y"
val caseexp2 =
  test “nExp” "case h\n\
              \of y->4\n\
              \   z-> 5"

val caseexp3 =
  test “nExp” "case e of [] -> 3\n\
              \          h:t -> 4"

val letbraces1 =
  test “nDecl” "y = let\n\
               \{x=\n\
               \10;y::Int;}\n\
               \ in x"

val doblock1 =
test “nExp” "do x <- \n\
            \     f y\n\
            \   return (x + 1)"

val doblock2 =
test “nExp” "do x <- f y ; check (x + 1)\n\
            \   return (x,y)"

val doblock3 =
test “nExp” "do {\n\
            \x <- f y ; check 3; \n\
            \return (x + 1)}"


val _ = export_theory();
