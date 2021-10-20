open HolKernel Parse boolLib bossLib;


open stringTheory grammarTheory ispegexecTheory ispegTheory tokenUtilsTheory
local open lexer_funTheory in end

val _ = new_theory "purePEG";

val _ = set_grammar_ancestry
        ["tokenUtils", "grammar", "lexer_fun", "ispegexec"]


Datatype:
  ppegnt = nDecls | nDecl | nTyBase | nTy | nTySeq1
End

val distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:ppegnt``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  recurse ntlist
end


val _ = computeLib.add_thms distinct_ths computeLib.the_compset


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

Definition mktoklf_def:
  mktokLf t = [Lf (TK (FST t), SND t)]
End

Definition pegf_def: pegf sym f = seq sym (empty []) (λl1 l2. f l1)
End

Definition seql_def:
  seql l f = pegf (FOLDR (\p acc. seq p acc (++)) (empty []) l) f
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
        (INL nDecls, rpt (NT nDecl I lrEQ) FLAT);
        (INL nDecl,
         seql [tok isAlphaT mktokLf lrEQ;
               tok ((=) $ SymbolT "::") mktokLf lrGT;
               NT nTy I lrGT] (mkNT nDecl));
        (INL nTyBase,
         choice (pegf (tok isAlphaT mktokLf lrGE) (mkNT nTyBase))
                (seql [tok ((=) LparT) mktokLf lrGE;
                       NT nTySeq1 I lrGE;
                       tok ((=) RparT) mktokLf lrGE]
                 (mkNT nTyBase)) sumID);
        (INL nTy,
         seql [NT nTyBase I lrGE;
               choice (seql [tok ((=) ArrowT) mktokLf lrGE; NT nTy I lrGE] I)
                      (empty [])
                      sumID]
              (mkNT nTy));
        (INL nTySeq1,
         seql [NT nTy I lrGE;
               choice
                 (seql [tok ((=) CommaT) mktokLf lrGE; NT nTySeq1 I lrGE] I)
                 (empty [])
                 sumID]
              (mkNT nTySeq1))
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
    |> map (SIMP_RULE bool_ss (purepeg_rules_applied @ distinct_ths @
                               [sumTheory.INL_11]))
    |> LIST_CONJ;


Theorem gettok[local,compute] = lexer_funTheory.get_token_def
(* val input1 = EVAL “lexer_fun "foo :: A -> B"”
val input2 = EVAL “lexer_fun "foo ::\n A -> B"”
val input3 = EVAL “lexer_fun "foo :: A\n     ->\n B"”
*)
Theorem good1 =
    EVAL “ispeg_exec purePEG (nt (INL nDecls) I lrOK)
          (lexer_fun "foo :: A -> (B,\n\
                     \ C,D)\n\
                     \bar :: C\n\
                     \   -> D\n\
                     \baz :: D\n\
                     \qux::(A->B)->C")
          lpTOP [] NONE [] done failed”

Theorem good2 =
    EVAL “ispeg_exec purePEG (nt (INL nDecls) I lrOK)
          (lexer_fun " foo :: A -> B -> C\n\
                     \ bar :: C\n")
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

val _ = export_theory();
