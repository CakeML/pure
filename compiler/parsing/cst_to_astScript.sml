open HolKernel Parse boolLib bossLib;

open pureNTTheory pureASTTheory tokenUtilsTheory grammarTheory

val _ = new_theory "cst_to_ast";

Overload lift[local] = “option$OPTION_MAP”
Overload "'"[local] = “λf a. OPTION_BIND a f”

Definition tokcheck_def:
  tokcheck pt tok <=> destTOK ' (destLf pt) = SOME tok
End

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"
Overload monad_bind = “λa f. OPTION_BIND a f”

Overload ptsize = “parsetree_size (K 0) (K 0) (K 0)”;
Overload ptlsize = “parsetree1_size (K 0) (K 0) (K 0)”;

Definition mkFunTy_def:
  mkFunTy [] = tyOp "Bool" [] ∧ (* bogus but should never occur *)
  mkFunTy [ty] = ty ∧
  mkFunTy (ty::rest) = tyOp "Fun" [ty; mkFunTy rest]
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
           if isUpper c1 then SOME $ tyOp s []
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
               SOME $ tyOp "List" [ty]
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
           (tys, rest') <- astSepType ArrowT nTyApp rest;
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
           SOME $ tyOp opnm ty_args
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
    | [pt] => lift litInt $ destIntT ' (destTOK ' (destLf pt))
    | _ => NONE
End

Theorem SUM_MAP_EL_lemma:
  ∀xs i. i < LENGTH xs ⇒ f (EL i xs) ≤ SUM (MAP f xs)
Proof
  Induct >> simp[] >> Cases_on ‘i’ >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Definition astPat_def:
  astPat _ (Lf _) = NONE ∧
  (astPat nt1 (Nd nt2 args) =
   if INL nt1 ≠ FST nt2 then NONE
   else if nt1 = nAPat then
     case args of
       [pt] => do
                vnm <- destAlphaT ' (destTOK ' (destLf pt));
                SOME $ patVar vnm
              od ++ (lift patLit $ astLit pt)
     | _ => NONE
   else NONE)
End


Definition astExp_def:
  astExp _ (Lf _) = NONE ∧
  (astExp nt1 (Nd nt2 args) =
   if INL nt1 ≠ FST nt2 then NONE
   else if nt1 = nAExp then
     case args of
       [pt] =>
         do
           vnm <- destAlphaT ' (destTOK ' (destLf pt)) ;
           SOME $ expVar vnm
         od ++ (lift expLit $ astLit pt)
     | [lp;ept;rp] =>
         do
           assert (tokcheck lp LparT ∧ tokcheck rp RparT);
           astExp nExp ept;
         od
     | _ => NONE
   else if nt1 = nExp then
     case args of
       [pt] => astExp nIExp pt
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
           assert (LIST_REL (λP pt. P pt) [flip tokcheck ArrowT; K T] tail);
           body_e <- astExp nExp ' (oEL 1 tail);
           SOME $ FOLDR expAbs body_e pats
         od
     | _ => NONE
   else if nt1 = nIExp then
     case args of
       [pt] => astExp nFExp pt
     | _ => NONE
   else if nt1 = nFExp then
     case args of
       [] => NONE
     | fpt :: rest =>
         do
           f_e <- astExp nAExp fpt;
           (aes, tail) <- grab (astExp nAExp) rest;
           assert (NULL tail);
           SOME $ FOLDL expApp f_e aes
         od
   else
     NONE)
Termination
  WF_REL_TAC ‘measure (ptree_size o SND)’ >> simp[miscTheory.LLOOKUP_EQ_EL] >>
  rpt strip_tac >~
  [‘MEM x xs’, ‘ptree_size x < _’, ‘MAP ptree_size xs’]
  >- (‘ptree_size x ≤ SUM (MAP ptree_size xs)’ suffices_by simp[] >>
      qpat_x_assum ‘MEM _ _’ mp_tac >> Induct_on ‘xs’ >> simp[DISJ_IMP_THM] >>
      rpt strip_tac >> gs[]) >>
  TRY (drule_then strip_assume_tac grab_EQ_SOME_APPEND >>
       pop_assum (assume_tac o Q.AP_TERM ‘SUM o MAP ptree_size’) >>
       gs[listTheory.SUM_APPEND]) >>
  qmatch_goalsub_abbrev_tac ‘ptree_size (EL i ptl)’ >>
  ‘ptree_size (EL i ptl) ≤ SUM (MAP ptree_size ptl)’
    suffices_by simp[Abbr‘i’] >>
  simp[Abbr‘i’, Abbr‘ptl’, SUM_MAP_EL_lemma]
End

val _ = export_theory();
