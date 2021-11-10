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


val _ = export_theory();
