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
         | expApp expAST expAST
         | expAbs patAST expAST
         | expIf expAST expAST expAST
         | expLit litAST
End

Datatype:
  declAST = declId string tyAST
          | declData string (string list)
                     ((string # tyAST list) list)
          | declDefn string (patAST list) expAST
End


val _ = export_theory();
