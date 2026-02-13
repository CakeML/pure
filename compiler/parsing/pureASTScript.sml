Theory pureAST
Ancestors[qualified]
  mlstring integer pure_config

(* by convention tyOps will be capitalised alpha-idents, or "->",
   and tyVars will be lower-case alpha-idents.

   The tyTup constructor should never be applied to a singleton list
*)
Datatype:
  tyAST = tyOp mlstring (tyAST list)
        | tyVar mlstring
        | tyTup (tyAST list)
End

Overload boolTy = “tyOp «Bool» []”;
Overload intTy = “tyOp «Integer» []”
Overload listTy = “λty. tyOp «[]» [ty]”
Overload funTy = “λd r. tyOp «Fun» [d; r]”

Datatype:
  litAST = litInt int | litString mlstring
End

Datatype:
  patAST = patVar mlstring
         | patApp mlstring (patAST list)
         | patTup (patAST list)
         | patLit litAST
         | patUScore
End

Datatype:
  expAST = expVar mlstring
         | expCon mlstring (expAST list)
         | expOp pure_config$atom_op (expAST list)
         | expTup (expAST list)
         | expApp expAST expAST
         | expAbs patAST expAST
         | expIf expAST expAST expAST
         | expLit litAST
         | expLet (expdecAST list) expAST
         | expDo (expdostmtAST list) expAST
         | expCase expAST ((patAST # expAST) list);
  expdecAST = expdecTysig mlstring tyAST
            | expdecPatbind patAST expAST
            | expdecFunbind mlstring (patAST list) expAST ;
  expdostmtAST = expdostmtExp expAST
               | expdostmtBind patAST expAST
               | expdostmtLet (expdecAST list)
End

Theorem better_expAST_induction =
        TypeBase.induction_of “:expAST”
          |> Q.SPECL [‘eP’, ‘dP’, ‘doP’,
                      ‘λpes. ∀p e. MEM (p,e) pes ⇒ eP e’,
                      ‘λpe. eP (SND pe)’,
                      ‘λdds. ∀ds. MEM ds dds ⇒ doP ds’,
                      ‘λes. ∀e. MEM e es ⇒ eP e’,
                      ‘λds. ∀d. MEM d ds ⇒ dP d’]
          |> SRULE [DISJ_IMP_THM, FORALL_AND_THM, pairTheory.FORALL_PROD,
                    DECIDE “p ∧ q ⇒ q ⇔ T”]
          |> UNDISCH
          |> SRULE [Cong (DECIDE “p = p' ∧ (p' ⇒ q = q') ⇒ (p ∧ q ⇔ p' ∧ q')”)]
          |> DISCH_ALL
          |> Q.GENL [‘eP’, ‘dP’, ‘doP’]

Overload pNIL = “expCon «[]» []”
Overload pCONS = “λe1 e2. expCon «::» [e1;e2]”
val _ = set_mapped_fixity {fixity = Infixr 490,term_name = "pCONS",tok = "::ₚ"}

val _ = set_fixity "⬝" (Infixl 600)
Overload "⬝" = “expApp”

Definition strip_comb_def:
  strip_comb (expApp f x) = (I ## (λl. l ++ [x])) (strip_comb f) ∧
  strip_comb e = (e, [])
End

Definition dest_expVar_def:
  dest_expVar (expVar s) = SOME s ∧
  dest_expVar _ = NONE
End

Definition dest_expLet_def:
  dest_expLet (expLet ads e) = SOME (ads,e) ∧
  dest_expLet _ = NONE
End

val _ = add_rule {term_name = "expAbs", fixity = Prefix 1,
                  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  pp_elements = [TOK "𝝺", TM, TOK "．", BreakSpace(1,2)],
                  paren_style = OnlyIfNecessary}

Datatype:
  declAST = declTysig mlstring tyAST
          | declData mlstring (mlstring list)
                     ((mlstring # tyAST list) list)
          | declFunbind mlstring (patAST list) expAST
          | declPatbind patAST expAST
End


