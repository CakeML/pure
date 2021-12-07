open HolKernel Parse boolLib bossLib;

local open stringTheory integerTheory in end
val _ = new_theory "pureAST";

(* by convention tyOps will be capitalised alpha-idents, or "->",
   and tyVars will be lower-case alpha-idents.

   The tyTup constructor should never be applied to a singleton list
*)
Datatype:
  tyAST = tyOp string (tyAST list)
        | tyVar string
        | tyTup (tyAST list)
End

Overload boolTy = “tyOp "Bool" []”;
Overload intTy = “tyOp "Int" []”
Overload listTy = “λty. tyOp "List" [ty]”
Overload funTy = “λd r. tyOp "Fun" [d; r]”

Datatype:
  litAST = litInt int
End

Datatype:
  patAST = patVar string
         | patApp string (patAST list)
         | patTup (patAST list)
         | patLit litAST
End

Datatype:
  expAST = expVar string
         | expCon string (expAST list)
         | expTup (expAST list)
         | expApp expAST expAST
         | expAbs patAST expAST
         | expIf expAST expAST expAST
         | expLit litAST
End

val _ = add_strliteral_form {ldelim = "‹", inj = “expVar”}
Overload pNIL = “expCon "[]" []”
Overload pCONS = “λe1 e2. expCon ":" [e1;e2]”
val _ = set_mapped_fixity {fixity = Infixr 490,term_name = "pCONS",tok = "::ₚ"}

val _ = set_fixity "⬝" (Infixl 600)
Overload "⬝" = “expApp”
val _ = add_rule {term_name = "expAbs", fixity = Prefix 1,
                  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  pp_elements = [TOK "𝝺", TM, TOK "．", BreakSpace(1,2)],
                  paren_style = OnlyIfNecessary}

Datatype:
  declAST = declId string tyAST
          | declData string (string list)
                     ((string # tyAST list) list)
          | declDefn string (patAST list) expAST
End


val _ = export_theory();
