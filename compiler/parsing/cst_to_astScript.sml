open HolKernel Parse boolLib bossLib;

open pureNTTheory pureASTTheory tokenUtilsTheory pureTokenUtilsTheory
     grammarTheory
local open precparserTheory in end

val _ = new_theory "cst_to_ast";

val _ = set_grammar_ancestry ["pureNT", "pureTokenUtils", "pureAST",
                              "precparser"]

Overload lift[local] = “option$OPTION_MAP”
Overload "'"[local] = “λf a. OPTION_BIND a f”

Definition tokcheck_def:
  tokcheck pt tok <=> destTOK ' (destLf pt) = SOME tok
End

Overload monad_bind = “λa f. OPTION_BIND a f”

Overload ptsize = “parsetree_size (K 0) (K 0) (K 0)”;
Overload ptlsize = “parsetree1_size (K 0) (K 0) (K 0)”;

Definition mkFunTy_def:
  mkFunTy [] = tyOp (Short "Bool") [] ∧ (* bogus but should never occur *)
  mkFunTy [ty] = ty ∧
  mkFunTy (ty::rest) = tyOp (Short "Fun") [ty; mkFunTy rest]
End

Definition grab_def:
  grab f [] = SOME ([], []) ∧
  grab f (h::t) =
  do
    v <- f h;
    (vs, tail) <- grab f t;
    SOME (v::vs, tail)
  od ++ SOME([], h::t)
End
(* OPT_MMAP astExpDec *)
fun mkgrab_def gtm gdef name tm =
  let
    val rhs = mk_icomb(gtm, tm)
    val def0 = new_definition(name ^ "_def0",
                              mk_eq(mk_var(name,type_of rhs), rhs))
    fun myinst th =
      let val (_, arg1::_) = th |> concl |> strip_forall |> #2 |> lhs
                                |> strip_comb
          val tytheta = match_type (type_of arg1) (type_of tm)
      in
        th |> SPEC_ALL |> INST_TYPE tytheta |> INST [inst tytheta arg1 |-> tm]
      end
    val def =
      save_thm(name ^ "_def",
               LIST_CONJ (map myinst $ CONJUNCTS gdef)
                 |> REWRITE_RULE [GSYM def0])
  in
    SIMP_RULE bool_ss [GSYM def0, SF ETA_ss]
  end




Theorem grab_EQ_SOME_APPEND:
  ∀xs res xs'. grab f xs = SOME (res, xs') ⇒
               ∃px. xs = px ++ xs'
Proof
  Induct_on ‘xs’ >>
  simp[grab_def, miscTheory.option_eq_some, DISJ_IMP_THM, PULL_EXISTS,
       pairTheory.FORALL_PROD] >> rpt strip_tac >>
  first_x_assum $ drule_then strip_assume_tac >> rw[]
QED

Theorem grab_cong[defncong]:
  ∀l1 l2 f1 f2. l1 = l2 ∧ (∀e. MEM e l2 ⇒ f1 e = f2 e) ⇒
                grab f1 l1 = grab f2 l2
Proof
  simp[] >> Induct >>
  simp[grab_def, DISJ_IMP_THM, FORALL_AND_THM, miscTheory.option_eq_some]>>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Definition grabPairs_def[simp]:
  grabPairs vf opf A [] = SOME (REVERSE A) ∧
  grabPairs vf opf A [_] = NONE ∧
  grabPairs vf opf A (pt1 :: pt2 :: rest) =
  do
    opv <- opf pt1 ;
    v <- vf pt2 ;
    grabPairs vf opf (INR v :: INL opv :: A) rest
  od
End

Theorem grabPairs_cong[defncong]:
  ∀opf1 opf2 l1 l2 vf1 vf2 A1 A2 .
    opf1 = opf2 ∧ l1 = l2 ∧ (∀e. MEM e l2 ⇒ vf1 e = vf2 e) ∧ A1 = A2 ⇒
    grabPairs vf1 opf1 A1 l1 = grabPairs vf2 opf2 A2 l2
Proof
  simp[] >> qx_genl_tac [‘opf2’, ‘l2’, ‘vf1’, ‘vf2’] >>
  completeInduct_on ‘LENGTH l2’ >>
  gs[SF DNF_ss] >> Cases_on ‘l2’ >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >> gvs[] >> rename [‘grabPairs _ _ _ (h::t)’] >>
  Cases_on ‘t’ >> simp[]
QED

Definition grabsepby_def:
  grabsepby pf tok [] = ([],[]) ∧
  (grabsepby pf tok [pt1] =
     case pf pt1 of
       NONE => ([], [pt1])
     | SOME v => ([v], [])) ∧
  (grabsepby pf tok (pt1::pt2::rest) =
     case pf pt1 of
       NONE => ([], pt1::pt2::rest)
     | SOME v => if tokcheck pt2 tok then
                   (CONS v ## I) (grabsepby pf tok rest)
                 else ([v], pt2::rest))
End

Theorem grabsepby_cong[defncong]:
  ∀pf1 pf2 tok1 tok2 l1 l2.
    tok1 = tok2 ∧ l1 = l2 ∧ (∀e. MEM e l2 ⇒ pf1 e = pf2 e) ⇒
    grabsepby pf1 tok1 l1 = grabsepby pf2 tok2 l2
Proof
  simp[] >> rpt gen_tac >> completeInduct_on ‘LENGTH l2’ >>
  gs[SF DNF_ss] >> Cases >> simp[grabsepby_def] >>
  rename [‘grabsepby pf1 tok (pt1::rest)’] >>
  Cases_on ‘rest’ >> simp[grabsepby_def]
QED

Definition astType_def:
  astType nt (Lf _) = NONE ∧
  (astType nt1 (Nd nt2 args) =
   if FST nt2 ≠ INL nt1 then NONE
   else if nt1 = nTyBase then
     case args of
     | [] => NONE
     | [pt] =>
         do
           s <- destAlphaT ' (destTOK ' (destLf pt));
           c1 <- oHD s;
           if isUpper c1 then SOME $ tyOp (string_to_long_name (s:string)) []
           else SOME $ tyVar s
         od
     | [ld; rd] => do assert(tokcheck ld LparT ∧ tokcheck rd RparT) ;
                      SOME (tyTup [])
                   od
     | [ld; typt; rd] =>
         do
           t <- destTOK ' (destLf ld);
           ty <- astType nTy typt;
           if t = LparT then
             do
               assert(tokcheck rd RparT);
               SOME ty
             od
           else if t = LbrackT then
             do
               assert(tokcheck rd RbrackT);
               SOME $ tyOp (Short "[]") [ty]
             od
           else NONE
         od
     | (ld :: pt1 :: rest) =>
         do
           assert(tokcheck ld LparT);
           ty1 <- astType nTy pt1;
           (tys, rest') <- astSepType CommaT nTy rest;
           assert(LIST_REL tokcheck rest' [RparT]);
           SOME $ tyTup (ty1::tys)
         od
   else if nt1 = nTy then
     case args of
       [] => NONE
     | pt::rest =>
         do
           ty1 <- astType nTyApp pt ;
           (tys, rest') <- astSepType (SymbolT "->") nTyApp rest;
           SOME $ mkFunTy (ty1::tys)
         od
   else if nt1 = nTyApp then
     case args of
     | [] => NONE
     | [pt] => astType nTyBase pt
     | op_pt :: rest =>
         do
           opnm <- destAlphaT ' (destTOK ' (destLf op_pt)) ;
           ty_args <- astTypeBaseL rest ;
           SOME $ tyOp (string_to_long_name opnm) ty_args
         od
   else
     NONE) ∧
  (astSepType sept nt [] = SOME ([], [])) ∧
  (astSepType sept nt [pt] = SOME ([], [pt])) ∧
  (astSepType sept nt (pt1::pt2::rest) =
       do
         assert(tokcheck pt1 sept);
         r <- astType nt pt2 ;
         (rs, pts) <- astSepType sept nt rest;
         SOME (r::rs, pts)
       od ++ SOME ([], pt1::pt2::rest)) ∧
  (astTypeBaseL [] = SOME []) ∧
  (astTypeBaseL (pt::rest) = do
     ty1 <- astType nTyBase pt ;
     tys <- astTypeBaseL rest ;
     SOME (ty1 :: tys)
   od)
Termination
  WF_REL_TAC ‘measure (λs. case s of
                             INL (_, pt) => ptsize pt
                           | INR (INL (_, _, pts)) => ptlsize pts
                           | INR (INR pts) => ptlsize pts)’ >> rw[]
End


Definition astLit_def:
  astLit (Lf _) = NONE ∧
  astLit (Nd nt args) =
  if FST nt ≠ INL nLit then NONE
  else
    case args of
      [] => NONE
    | [pt] => (lift litInt $ destIntT ' (destTOK ' (destLf pt))) ++
              (lift litString $ destStringT ' (destTOK ' (destLf pt)))
    | _ => NONE
End

Definition astOp_def:
  astOp (Lf _) = NONE ∧
  astOp (Nd nt args) =
  if FST nt ≠ INL nOp then NONE
  else
    case args of
    | [pt] =>
        do
          t <- destTOK ' (destLf pt) ;
          destSymbolT t ++ (if t = StarT then SOME "*"
                            else if t = ColonT then SOME ":"
                            else NONE)
        od
    | [bqt1; idpt; bqt2] =>
        do
          assert (tokcheck bqt1 (SymbolT "`") ∧
                  tokcheck bqt2 (SymbolT "`"));
          t <- destTOK ' (destLf idpt);
          destAlphaT t
        od
    | _ => NONE
End

Theorem SUM_MAP_EL_lemma:
  ∀xs i. i < LENGTH xs ⇒ f (EL i xs) ≤ SUM (MAP f xs)
Proof
  Induct >> simp[] >> Cases_on ‘i’ >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Definition astalpha_def:
  astalpha pt = destAlphaT ' (destTOK ' (destLf pt))
End


Definition astlcname_def:
  astlcname pt =
  do
    nm <- astalpha pt;
    assert (lcname nm);
    return nm;
  od
End

Definition astcapname_def:
  astcapname pt =
  do
    nm <- astalpha pt;
    assert (capname nm);
    return nm
  od
End


Definition astPat_def:
  astPat _ (Lf _) = NONE ∧
  (astPat nt1 (Nd nt2 args) =
   if INL nt1 ≠ FST nt2 then NONE
   else if nt1 = nAPat then
     case args of
       [pt] => do
                vnm <- astalpha pt;
                SOME $ patVar vnm
              od ++ (lift patLit $ astLit pt) ++
              do
                assert (tokcheck pt UnderbarT);
                SOME patUScore
              od
     | _ => NONE
   else NONE)
End

Datatype: associativity = Left | Right | NonAssoc
End

(* Table 4.1 from
     https://www.haskell.org/onlinereport/haskell2010/haskellch4.html
*)
val tabinfo = [
  ("!!", (10, “Left”)),
  (".", (9, “Right”)),
  ("^", (8, “Right”)),
  ("^^", (8, “Right”)),
  ("**", (8, “Right”)),
  ("*", (7, “Left”)),
  ("/", (7, “Left”)),
  ("mod", (7, “Left”)),
  ("div", (7, “Left”)),
  ("quot", (7, “Left”)),
  ("rem", (7, “Left”)),
  ("+", (6, “Left”)),
  ("-", (6, “Left”)),
  (":", (5, “Right”)),
  ("++", (5, “Right”)),
  ("==", (4, “NonAssoc”)),
  ("elem", (4, “NonAssoc”)),
  ("notElem", (4, “NonAssoc”)),
  ("/=", (4, “NonAssoc”)),
  ("<", (4, “NonAssoc”)),
  ("<=", (4, “NonAssoc”)),
  (">", (4, “NonAssoc”)),
  (">=", (4, “NonAssoc”)),
  ("&&", (3, “Right”)),
  ("||", (2, “Right”)),
  (">>", (1, “Left”)),
  (">>=", (1, “Left”)),
  ("$", (0, “Right”)),
  ("seq", (0, “Right”)),
  ("$!", (0, “Right”))
]
val s = mk_var("s", “:string”)
val def = List.foldr (fn ((t,(i,tm)), A) =>
              mk_cond(mk_eq(s,stringSyntax.fromMLstring t),
                      optionSyntax.mk_some
                         (pairSyntax.mk_pair(
                           numSyntax.mk_numeral (Arbnum.fromInt i), tm)),
                      A))
            “SOME(9, Left) : (num # associativity) option”
            tabinfo
Definition tokprec_def:
tokprec s = ^def
End

Definition tok_action_def:
  tok_action (INL stktok, INL inptok) =
  do (stkprec, stka) <- tokprec stktok ;
     (inpprec, inpa) <- tokprec inptok ;
     if inpprec < stkprec then SOME Reduce
     else if stkprec < inpprec then SOME Shift
     else if stka ≠ inpa ∨ stka = NonAssoc then NONE
     else if stka = Left then SOME Reduce
     else SOME Shift
  od ∧
  tok_action _ = NONE
End

Definition mkSym_def:
  mkSym s =
  let ln = string_to_long_name s in
    let n = id_to_n ln
    in
      THE (do
            c1 <- oHD n ;
            if isUpper c1 then SOME $ expCon ln []
            else if isAlpha c1 ∨ c1 ≠ #":" then SOME $ expVar ln
            else if s = ":" then SOME $ expCon (Short "::") []
            else SOME $ expCon ln []
          od ++ SOME (expVar ln))
End

Definition mkFFISym_def:
  mkFFISym s : pure_config$atom_op =
  if s = "__Len" then Len
  else if s = "__Elem" then Elem
  else if s = "__Concat" then Concat
  else if s = "__Implode" then Implode
  else if s = "__Substring" then Substring
  else if s = "__StrEq" then StrEq
  else if s = "__StrLt" then StrLt
  else if s = "__StrLeq" then StrLeq
  else if s = "__StrGt" then StrGt
  else if s = "__StrGeq" then StrGeq
  else Message s
End

Definition mkApp_def:
  mkApp f args =
  case f of
    expCon s args0 => expCon s (args0 ++ args)
  | expOp op args0 => expOp op (args0 ++ args)
  | _ => FOLDL expApp f args
End

Definition ast_OUTR_def:
  ast_OUTR (INR x) = (x:expAST) ∧
  ast_OUTR _ = expTup []
End

Definition str_OUTL_def:
  str_OUTL (INL x) = (x:string) ∧
  str_OUTL _ = ""
End

Definition handlePrecs_def:
  handlePrecs sumlist =
  precparser$precparse
  <| rules := tok_action ;
     reduce :=
       (λa1 op a2. SOME $ mkApp (mkSym $ str_OUTL op) [a1; a2]);
     lift := ast_OUTR ;
     isOp := ISL;
     mkApp := (λa b. SOME $ expApp a b) (* won't get called *)
  |> ([], sumlist)
End


Theorem list_size_MAP_SUM:
  list_size f l = LENGTH l + SUM (MAP f l)
Proof
  Induct_on‘l’ >> simp[listTheory.list_size_def]
QED

Theorem ptsize_nonzero[simp]:
  0 < ptsize a
Proof
  Cases_on ‘a’ >> simp[parsetree_size_def]
QED

Theorem NUMS_LT_SUC[local,simp]:
  (2 < SUC x ⇔ 1 < x) ∧
  (1 < SUC x ⇔ 0 < x)
Proof
  simp[]
QED


Datatype:
  resolve_decl = resolve_declPattern patAST
               | resolve_declFun string (patAST list)
End

Definition exp_to_pat_def:
  exp_to_pat (expVar (Short s)) = (if s = "_" then SOME $ patUScore else SOME $ patVar s) ∧
  exp_to_pat (expCon s es) = OPTION_MAP (patApp s) (OPT_MMAP exp_to_pat es) ∧
  exp_to_pat (expTup es) = OPTION_MAP patTup (OPT_MMAP exp_to_pat es) ∧
  exp_to_pat (expLit l) = SOME $ patLit l ∧
  exp_to_pat _ = NONE
Termination
  WF_REL_TAC ‘measure expAST_size’
End

Definition resolve_decl_def:
  resolve_decl e =
  case exp_to_pat e of
    SOME (patVar s) => SOME $ resolve_declFun s []
  | SOME p => SOME $ resolve_declPattern p
  | NONE => (case strip_comb e of
               (expVar (Short fname), args) =>
                 OPTION_MAP (resolve_declFun fname) (OPT_MMAP exp_to_pat args)
             | _ => NONE)
End

Definition optLAST_def:
  optLAST k f [] = NONE ∧
  optLAST k f [e] = OPTION_MAP (k []) (f e) ∧
  optLAST k f (h::t) = optLAST (λxs y. k (h::xs) y) f t
End

Definition dostmt_to_exp_def:
  dostmt_to_exp (expdostmtExp e) = SOME e ∧
  dostmt_to_exp _ = NONE
End

Definition astExp_def:
  (astExp _ (Lf _) = NONE) ∧
  (astExp nt1 (Nd nt2 args) =
   if INL nt1 ≠ FST nt2 then NONE
   else if nt1 = nAExp then
     case args of
       [] => NONE
     | [pt] =>
         do
           vnm <- destAlphaT ' (destTOK ' (destLf pt)) ;
           SOME $ mkSym vnm
         od ++ (lift expLit $ astLit pt) ++
         do
           assert (tokcheck pt UnderbarT) ;
           SOME $ expVar (Short "_")
         od ++
         do
           ffi_s <- destFFIT ' (destTOK ' (destLf pt)) ;
           return $ expOp (mkFFISym ffi_s) []
         od
     | [lp;rp] =>
         do
           assert (tokcheck lp LparT ∧ tokcheck rp RparT);
           SOME $ expTup []
         od ++
         do assert (tokcheck lp LbrackT ∧ tokcheck rp RbrackT);
            SOME $ pNIL
         od
     | ld :: pt1 :: rest =>
         do rd <- (do assert (tokcheck ld LparT); SOME RparT; od) ++
                  (do assert (tokcheck ld LbrackT); SOME RbrackT; od) ;
            ast1 <- astExp nExp pt1;
            asts <- astSepExp rd rest ;
            if rd = RparT then
              if NULL asts then SOME ast1
              else SOME $ expTup (ast1::asts)
            else SOME (FOLDR pCONS pNIL (ast1::asts))
         od
   else if nt1 = nExp then
     case args of
       [pt] => astExp nIExp pt
     | [do_pt; doblock_pt] =>
         do
           assert (tokcheck do_pt (AlphaT "do")) ;
           doblock <- astDoBlock doblock_pt ;
           optLAST expDo dostmt_to_exp doblock ;
         od
     | pt1::rest =>
         do
           assert (tokcheck pt1 IfT ∧ LENGTH rest = 5 ∧
                   LIST_REL (λP pt. P pt) [K T; flip tokcheck ThenT; K T;
                                           flip tokcheck ElseT; K T]
                            rest);
           gd_e <- astExp nExp ' (oEL 0 rest);
           then_e <- astExp nExp ' (oEL 2 rest);
           else_e <- astExp nExp ' (oEL 4 rest);
           SOME $ expIf gd_e then_e else_e;
         od ++
         do
           assert (tokcheck pt1 (SymbolT "\\"));
           (pats,tail) <- grab (astPat nAPat) rest;
           assert (LIST_REL (λP pt. P pt)
                   [flip tokcheck (SymbolT "->"); K T] tail);
           body_e <- astExp nExp ' (oEL 1 tail);
           SOME $ FOLDR expAbs body_e pats
         od ++
         do
           assert (tokcheck pt1 LetT ∧ LENGTH rest = 3 ∧
                   LIST_REL (λP pt. P pt) [K T; flip tokcheck InT; K T] rest);
           seq_pt <- oEL 0 rest;
           let_encoded_eqs <- astExp nEqBindSeq seq_pt;
           (eqs, _) <- dest_expLet let_encoded_eqs ;
           body <- astExp nExp ' (oEL 2 rest) ;
           SOME $ expLet eqs body
         od ++
         do
           assert (tokcheck pt1 CaseT ∧
                   LIST_REL (λP pt. P pt) [K T; flip tokcheck OfT; K T] rest);
           gdexp_pt <- oEL 0 rest;
           gdexp <- astExp nExp gdexp_pt ;
           patasts_pt <- oEL 2 rest;
           patasts <- astPatAlts patasts_pt ;
           SOME $ expCase gdexp patasts
         od
     | _ => NONE
   else if nt1 = nIExp then
     case args of
     | [] => NONE
     | pt :: rest => do
                      v <- astExp nFExp pt ;
                      preclist <- grabPairs (astExp nFExp2) astOp [INR v] rest ;
                      handlePrecs preclist
                    od
   else if nt1 = nFExp2 then
     case args of
     | [] => NONE
     | [pt] => astExp nExp pt ++ astExp nFExp pt
     | _ => NONE
   else if nt1 = nFExp then
     case args of
       [] => NONE
     | fpt :: rest =>
         do
           f_e <- astExp nAExp fpt;
           (aes, tail) <- grab (astExp nAExp) rest;
           assert (NULL tail);
           SOME $ mkApp f_e aes
         od
   else if nt1 = nEqBindSeq then
     case args of
       [] => return (expLet [] (expVar (Short "")))
     | pt1 :: rest =>
         do
           assert (tokcheck pt1 LbraceT);
           (adecs,rest') <<- grabsepby astExpDec SemicolonT rest;
           rbpt <- oHD rest';
           assert (tokcheck rbpt RbraceT ∧ LENGTH rest' = 1);
           return (expLet adecs (expVar (Short "")))
         od ++
         OPTION_MAP (λads. expLet ads (expVar (Short "")))
                    (OPT_MMAP astExpDec (pt1::rest))
   else
     NONE) ∧
  (astSepExp rd [] = NONE) ∧
  (astSepExp rd [pt] = do assert (tokcheck pt rd); SOME [] od) ∧
  (astSepExp rd (pt1 :: pt2 :: rest) =
   do
     assert (tokcheck pt1 CommaT);
     ast <- astExp nExp pt2 ;
     asts <- astSepExp rd rest ;
     SOME (ast :: asts)
   od) ∧
  (astExpDec (Lf _) = NONE) ∧
  (astExpDec (Nd nt args) =
   if FST nt ≠ INL nEqBind then NONE
   else
     case args of
       [e1_pt; eq_t; e2_pt] =>
         do
           assert (tokcheck eq_t EqualsT);
           le <- astExp nExp e1_pt ;
           re <- astExp nExp e2_pt ;
           rdecl <- resolve_decl le ;
           case rdecl of
           | resolve_declPattern p => SOME $ expdecPatbind p re
           | resolve_declFun id ps => SOME $ expdecFunbind id ps re
         od ++
         do
           assert (tokcheck eq_t (SymbolT "::")) ;
           vnm <- destAlphaT ' (destTOK ' (destLf e1_pt)) ;
           ty <- astType nTy e2_pt;
           SOME (expdecTysig vnm ty)
         od
     | _ => NONE) ∧
  (astDoStmt (Lf _) = NONE) ∧
  (astDoStmt (Nd nt args) =
   if FST nt ≠ INL nDoStmt then NONE
   else
     case args of
     | [e] => OPTION_MAP expdostmtExp (astExp nExp e)
     | [let_pt; seq_pt] =>
         do
           assert (tokcheck let_pt LetT);
           let_encoded_des <- astExp nEqBindSeq seq_pt ;
           (des, _) <- dest_expLet let_encoded_des ;
           return $ expdostmtLet des
         od
     | [pat_pt; arrow_pt; exp_pt] =>
         do
           assert (tokcheck arrow_pt (SymbolT "<-"));
           patexp <- astExp nExp pat_pt  ;
           pat <- exp_to_pat patexp ;
           exp <- astExp nExp exp_pt;
           SOME (expdostmtBind pat exp)
         od
     | _ => NONE) ∧
  (astDoBlock (Lf _) = NONE) ∧
  (astDoBlock (Nd nt args) =
   if FST nt ≠ INL nDoBlock then NONE
   else OPT_MMAP astDoStmt args) ∧
  (astPatAlts (Lf _) = NONE) ∧
  (astPatAlts (Nd nt args) =
   if FST nt ≠ INL nPatAlts then NONE
   else OPT_MMAP astPatAlt args) ∧
  (astPatAlt (Lf _) = NONE) ∧
  (astPatAlt (Nd nt args) =
   if FST nt ≠ INL nPatAlt then NONE
   else
     case args of
       [pat_pt; arrow; exp_pt] =>
         do
           assert (tokcheck arrow (SymbolT "->"));
           ep <- astExp nExp pat_pt ;
           p <- exp_to_pat ep ;
           e <- astExp nExp exp_pt ;
           SOME (p,e)
         od
     | _ => NONE)
Termination
  WF_REL_TAC ‘measure (λs. case s of
     (* astExp *)        | INL (_, pt) => ptsize pt
     (* astSepExp *)     | INR (INL (_, pts)) => 1 + SUM (MAP ptsize pts)
     (* astExpDec *)     | INR (INR (INL pt)) => ptsize pt
     (* astDoStmt *)     | INR (INR (INR (INL pt))) => ptsize pt
     (* astDoBlock *)    | INR (INR (INR (INR (INL pt)))) => ptsize pt
     (* astPatAsts *)    | INR $ INR $ INR $ INR $ INR $ INL pt => ptsize pt
     (* astPatAst *)     | INR $ INR $ INR $ INR $ INR $ INR pt => ptsize pt)’>>
  simp[miscTheory.LLOOKUP_EQ_EL, parsetree_size_eq, list_size_MAP_SUM,
       quantHeuristicsTheory.LIST_LENGTH_1] >>
  rpt strip_tac >> simp[arithmeticTheory.ZERO_LESS_ADD] >> gvs[] >>
  TRY (drule_then strip_assume_tac grab_EQ_SOME_APPEND >>
       pop_assum (assume_tac o Q.AP_TERM ‘SUM o MAP ptsize’) >>
       gs[listTheory.SUM_APPEND]) >~
  [‘MEM pt pts’]
  >- (simp[parsetree_size_def, basicSizeTheory.pair_size_def,
           basicSizeTheory.full_sum_size_def, basicSizeTheory.sum_size_def] >>
      simp[parsetree_size_eq, list_size_MAP_SUM] >>
      gvs[listTheory.MEM_EL] >>
      drule_then (qspec_then ‘ptsize’ assume_tac) SUM_MAP_EL_lemma >> simp[]) >>
  qmatch_goalsub_abbrev_tac ‘ptsize (EL i ptl)’ >>
  ‘ptsize (EL i ptl) ≤ SUM (MAP ptsize ptl)’
    suffices_by simp[Abbr‘i’] >>
  simp[Abbr‘i’, Abbr‘ptl’, SUM_MAP_EL_lemma]
End

Theorem translate_this_astExp =
  astExp_def
    |> mkgrab_def “grab” grab_def "gAExp" “astExp nAExp”
    |> mkgrab_def “grabPairs” grabPairs_def "gpFexp2" “astExp nFExp2”
    |> mkgrab_def “OPT_MMAP” listTheory.OPT_MMAP_def "OMMexpDec" “astExpDec”

Definition astFunPatBindf_def:
  astFunPatBindf e =
  do
    p <- exp_to_pat e;
    return (declPatbind p)
  od ++
  do
    (f, args) <<- strip_comb e ;
    fln <- dest_expVar f;
    fnm <- dest_Short fln;
    arg_pats <- OPT_MMAP exp_to_pat args;
    return (declFunbind fnm arg_pats)
  od
End

Definition astValBinding_def:
  astValBinding (Lf _) = NONE ∧
  astValBinding (Nd nt args) =
  if FST nt ≠ INL nValBinding then NONE
  else
    case args of
      [expl_pt; eq; expr_pt] =>
        do
          assert (tokcheck eq EqualsT);
          exp_or_pat <- astExp nExp expl_pt;
          fpbindf <- astFunPatBindf exp_or_pat;
          exp <- astExp nExp expr_pt;
          return (fpbindf exp)
        od
    | _ => NONE
End

Definition astTyConDecl_def:
  astTyConDecl (Lf _) = NONE ∧
  astTyConDecl (Nd nt args) =
  if FST nt ≠ INL nTyConDecl then NONE
  else
    case args of
      [] => NONE
    | connm_pt :: rest0 =>
        do
          connm <- astcapname connm_pt ;
          (args, rest) <- grab (astType nTyBase) rest0;
          assert (rest = []) ;
          return (connm, args)
        od
End

Definition astTycons_def:
  astTycons [] = NONE ∧
  astTycons [pt] = do con <- astTyConDecl pt; return [con] od ∧
  astTycons (pt::bar::rest) =
  do
    con1 <- astTyConDecl pt;
    assert (tokcheck bar BarT) ;
    cons <- astTycons rest;
    return (con1 :: cons)
  od
End


Definition astDecl_def:
  (astDecl (Lf _) = NONE) ∧
  (astDecl (Nd nt args) =
   if FST nt ≠ INL nDecl then NONE
   else
     case args of
       [vb_pt] => astValBinding vb_pt
     | [idtok; coloncolontok; ty_pt] =>
         do
           assert (tokcheck coloncolontok (SymbolT "::"));
           vnm <- destAlphaT ' (destTOK ' (destLf idtok)) ;
           ty <- astType nTy ty_pt;
           return (declTysig vnm ty)
         od
     | (datatok :: dname_tok :: arg1_or_eq :: rest) =>
         do
           assert (tokcheck datatok (AlphaT "data"));
           dnm <- destAlphaT ' (destTOK ' (destLf dname_tok));
           (args, rhs) <- grab astlcname (arg1_or_eq :: rest);
           assert (2 ≤ LENGTH rhs) ;
           eqpt <- oEL 0 rhs;
           assert (tokcheck eqpt EqualsT);
           cons <- astTycons (TL rhs);
           return (declData dnm args cons)
         od
     | _ => NONE)
End

Definition astDecls_def:
  (astDecls (Lf _) = NONE) ∧
  (astDecls (Nd nt args) =
   if FST nt ≠ INL nDecls then NONE
   else OPT_MMAP astDecl args)
End

Definition astImport_def:
  (astImport (Lf _) = NONE) ∧
  (astImport (Nd nt args) =
   if FST nt ≠ INL nImport then NONE
   else
     case args of
       (importtok :: importname_tok :: rest) =>
         do
           assert (tokcheck importtok (AlphaT "import"));
           importname <- astcapname importname_tok;
           importln <- string_to_moduleName importname;
           assert (rest = []) ;
           return (import importln);
         od
     | _ => NONE)
End

Definition astImports_def:
  (astImports (Lf _) = NONE) ∧
  (astImports (Nd nt args) =
   if FST nt ≠ INL nImports then NONE
   else OPT_MMAP astImport args)
End

Definition astModule_def:
  (astModule (Lf _) = NONE) ∧
  (astModule (Nd nt args) =
   if FST nt ≠ INL nModule then NONE
   else
     case args of
       (moduletok :: modulename_tok :: withtok :: importstok :: declstok :: rest) =>
         do
           assert (tokcheck moduletok (AlphaT "module"));
           modulename <- astcapname modulename_tok;
           moduleln <- string_to_moduleName modulename;
           assert (tokcheck withtok (AlphaT "with"));
           imports <- astImports importstok;
           decls <- astDecls declstok;
           assert (rest = []);
           return (module moduleln imports decls)
         od
     | _ => NONE)
End

Definition astModules_def:
  (astModules (Lf _) = NONE) ∧
  (astModules (Nd nt args) =
   if FST nt ≠ INL nModules then NONE
   else OPT_MMAP astModule args)
End

(* translator help *)

Definition grab'_def:
  grab' [] ys = SOME ([],[]) ∧
  grab' (h::t) ys =
    do v <- h; (vs,tail) <- grab' t (TL ys); SOME (v::vs,tail) od ++
    SOME ([],ys)
End

Theorem grab_eq:
  ∀xs f. grab f xs = grab' (MAP f xs) xs
Proof
  Induct \\ fs [grab_def,grab'_def]
QED

Definition grabPairs'_def:
  grabPairs' A ys =
    case ys of
    | [] => SOME (REVERSE A)
    | [v0] => NONE
    | (pt1::pt2::rest) =>
      do
        opv <- SND pt1;
        v <- FST pt2;
        grabPairs' (INR v::INL opv::A) rest
      od
End

Theorem grabPairs_eq:
  ∀f g a xs. grabPairs f g a xs = grabPairs' a (ZIP (MAP f xs, MAP g xs))
Proof
  ho_match_mp_tac grabPairs_ind \\ rw []
  \\ simp [grabPairs_def,Once grabPairs'_def] \\ rw []
  \\ Cases_on ‘g pt1’ \\ fs []
  \\ Cases_on ‘f pt2’ \\ fs []
QED

Definition grabsepby'_def:
  grabsepby' tok [] ys = ([],[]) ∧
  grabsepby' tok [pt1] ys =
     (case pt1 of NONE => ([],ys) | SOME v => ([v],[])) ∧
  grabsepby' tok (pt1::pt2::rest) ys =
     case pt1 of
       NONE => ([],ys)
     | SOME v =>
       case ys of
       | (y1::y2::ys1) =>
         (if tokcheck y2 tok
          then (CONS v ## I) (grabsepby' tok rest ys1)
          else ([v],TL ys))
       | _ => ([],[])
End

Theorem grabsepby_eq:
  ∀f tok xs. grabsepby f tok xs = grabsepby' tok (MAP f xs) xs
Proof
  ho_match_mp_tac grabsepby_ind
  \\ fs [grabsepby_def,grabsepby'_def]
  \\ rw [] \\ Cases_on ‘f pt1’ \\ fs []
  \\ IF_CASES_TAC \\ fs []
QED

val _ = export_theory();
