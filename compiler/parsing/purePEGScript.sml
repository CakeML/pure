open HolKernel Parse boolLib bossLib;


open stringTheory grammarTheory ispegexecTheory ispegTheory tokenUtilsTheory
     pureNTTheory pureTokenUtilsTheory
local open lexer_funTheory stringLib in end

val _ = new_theory "purePEG";

val _ = set_grammar_ancestry
        ["pureTokenUtils", "grammar", "lexer_fun", "ispegexec", "pureNT"]


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
         seql [NT nExp I lrEQ; tokGT ((=) $ EqualsT); NT nExp I lrGT]
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

        (INL nAPat,
         choicel [pegf (tok lcname_tok mktokLf lrEQ) (mkNT nAPat);
                  pegf (NT nLit I lrEQ) (mkNT nAPat)]);
        (INL nPat, pegf (NT nAPat I lrEQ) (mkNT nPat));

        (INL nEqBindSeq, pegf (rpt (NT nEqBind I lrEQ) FLAT) (mkNT nEqBindSeq));
        (INL nEqBind,
         choicel [seql [NT nExpEQ I lrEQ; tokGT ((=) EqualsT) ; NTGT nExp]
                       (mkNT nEqBind);
                  seql [tok lcname_tok mktokLf lrEQ;
                        tokGT ((=) $ SymbolT "::");
                        NT nTy I lrGT]
                       (mkNT nEqBind)]);
        (INL nOp, tok isSymbolOpT mktokLf lrEQ);

        (INL nIExp,
         seql [NTGE nFExp; rpt (seql [NTGE nOp; NTGE nFExp2] I) FLAT]
              (mkNT nIExp));
        (INL nIExpEQ,
         seql [NTEQ nFExpEQ; rpt (seql [NTGE nOp; NTGE nFExp2] I) FLAT]
              (mkNT nIExp));
        (INL nFExp2, pegf (choicel [NTGE nLSafeExp; NTGE nFExp]) (mkNT nFExp2));
        (INL nFExp,
         seql [NTGE nAExp; rpt (NTGE nAExp) FLAT] (mkNT nFExp));
        (INL nFExpEQ,
         seql [NTEQ nAExpEQ; rpt (NTGE nAExp) FLAT] (mkNT nFExp));
        (INL nDoBlock, pegf (rpt (NTEQ nDoStmt) FLAT) (mkNT nDoBlock));
        (INL nDoStmt,
         choicel [
             seql [NTEQ nExpEQ;
                   choicel [seql [tokGT ((=) $ SymbolT "<-"); NTGT nExp] I;
                            empty []]
                  ] (mkNT nDoStmt);
             seql [tokEQ ((=) LetT); NTGE nEqBindSeq] (mkNT nDoStmt)
           ]);
        (INL nLSafeExp,
         choicel [seql [tokGE ((=) $ SymbolT "\\") ; RPT1 (NTGE nAPat);
                        tokGE ((=) $ SymbolT "->");
                        NTGE nExp] (mkNT nExp);
                  seql [tokGE ((=) IfT); NTGE nExp;
                        tokGE ((=) ThenT); NTGE nExp;
                        tokGE ((=) ElseT); NTGE nExp] (mkNT nExp);
                  seql [tokGE ((=) LetT) ; NTGE nEqBindSeq ;
                        tokGE ((=) InT) ; NTGE nExp] (mkNT nExp);
                  seql [tokGE ((=) $ AlphaT "do"); NTGE nDoBlock] (mkNT nExp);
                  seql [tokGE ((=) CaseT); NTGE nExp; tokGE ((=) OfT);
                        NTGE nPatAlts] (mkNT nExp);
                 ]);
        (INL nLSafeExpEQ,
         choicel [seql [tokEQ ((=) $ SymbolT "\\") ; RPT1 (NTGE nAPat);
                        tokGE ((=) $ SymbolT "->");
                        NTGE nExp] (mkNT nExp);
                  seql [tokEQ ((=) IfT); NTGE nExp;
                        tokGE ((=) ThenT); NTGE nExp;
                        tokGE ((=) ElseT); NTGE nExp] (mkNT nExp);
                  seql [tokEQ ((=) LetT) ; NTGE nEqBindSeq ;
                        tokGE ((=) InT) ; NTGE nExp] (mkNT nExp);
                  seql [tokEQ ((=) $ AlphaT "do"); NTGE nDoBlock] (mkNT nExp);
                  seql [tokEQ ((=) CaseT); NTGE nExp; tokGE ((=) OfT);
                        NTGE nPatAlts] (mkNT nExp);
                 ]);
        (INL nPatAlts, pegf (rpt (NTEQ nPatAlt) FLAT) (mkNT nPatAlts));
        (INL nPatAlt, seql [NTEQ nExpEQ; tokGT ((=) $ SymbolT "->"); NTGT nExp]
                           (mkNT nPatAlt));
        (INL nExp,
         choicel [NTGE nLSafeExp; pegf (NTGE nIExp) (mkNT nExp)]);
        (INL nExpEQ,
         choicel [NTEQ nLSafeExpEQ; pegf (NTEQ nIExpEQ) (mkNT nExp)]);

        (INL nAExp,
         choicel [pegf (NTGE nLit) (mkNT nAExp);
                  seql [tokGE ((=) LparT) ;
                        sepby (NT nExp I lrGE) (tokGE ((=) CommaT));
                        tokGE ((=) RparT)] (mkNT nAExp);
                  seql [tokGE ((=) LbrackT) ;
                        sepby (NT nExp I lrGE) (tokGE ((=) CommaT));
                        tokGE ((=) RbrackT)] (mkNT nAExp);
                  pegf (tokGE isAlphaT) (mkNT nAExp)]);

        (INL nAExpEQ,
         choicel [pegf (NTEQ nLit) (mkNT nAExp);
                  seql [tokEQ ((=) LparT) ;
                        sepby (NT nExp I lrGE) (tokGE ((=) CommaT));
                        tokGE ((=) RparT)] (mkNT nAExp);
                  seql [tokEQ ((=) LbrackT) ;
                        sepby (NT nExp I lrGE) (tokGE ((=) CommaT));
                        tokGE ((=) RbrackT)] (mkNT nAExp);
                  pegf (tokEQ isAlphaT) (mkNT nAExp)]);

        (INL nLit,
         choicel [tok isInt (mkNT nLit o mktokLf) lrEQ]);
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

Theorem purePEG_exec_thm[compute] =
  TypeBase.constructors_of ``:ppegnt``
    |> map (fn t => ISPEC (mk_comb(mkNT, t)) spec0)
    |> map (SIMP_RULE bool_ss (purepeg_rules_applied @
                               [pureNTs_distinct, sumTheory.INL_11]))
    |> LIST_CONJ;


Theorem gettok[local,compute] = lexer_funTheory.get_token_def
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

val _ = export_theory();
