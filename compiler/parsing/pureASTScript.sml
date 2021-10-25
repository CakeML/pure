open HolKernel Parse boolLib bossLib;

local open stringTheory in end
val _ = new_theory "pureAST";

(* by convention tyOps will be capitalised alpha-idents, or "->",
   and tyVars will be lower-case alpha-idents.

   The use of the ugly tyTup constructor guarantees the absence of unary tuples.
*)
Datatype:
  tyAST = tyOp string (tyAST list)
        | tyVar string
        | tyUnit
        | tyTup tyAST tyAST (tyAST list)
End

Datatype:
  patAST = patVar string
         | patApp string (patAST list)
End


Datatype:
  expAST = expVar string
         | expApp expAST expAST
         | expAbs (patAST list) expAST
         | expIf expAST expAST expAST
End

Datatype:
  declAST = declId string tyAST
          | declData string (string list)
                     ((string # tyAST list) list)
          | declDefn string (patAST list) expAST
End


val _ = export_theory();
