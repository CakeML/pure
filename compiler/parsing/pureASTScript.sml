open HolKernel Parse boolLib bossLib;

local open stringTheory integerTheory pure_configTheory namespaceTheory in end
val _ = new_theory "pureAST";

val _ = set_grammar_ancestry ["string", "integer", "pure_config", "namespace"]

Type long_name = “:(string, string) id”

Definition mods_to_string_def:
  mods_to_string [] = "" ∧
  mods_to_string ((mn: string):: mns) =
  case mns of
    [] => mn
  | _ => STRCAT (STRCAT mn ".") (mods_to_string mns)
End

Definition long_name_to_string_def:
  long_name_to_string ln =
  STRCAT (STRCAT (mods_to_string (id_to_mods ln)) ".") (id_to_n ln)
End


val test1 = EVAL “long_name_to_string (Long "Foo" (Short "f"))”;

val test1 = EVAL “long_name_to_string (Short "f")”;

val test1 = EVAL “long_name_to_string (Long "Bar" (Long "Foo" (Short "f")))”;


Definition string_to_mods_def:
  (string_to_mods s mods [] = (s, mods)) ∧
  (string_to_mods s mods (c::rest) =
   if c = #"." then
     string_to_mods "" (mods ++ [s]) rest
   else string_to_mods (s ++ [c]) mods rest)
End

Definition string_to_long_name_def:
  string_to_long_name s =
  let (n, mods) = string_to_mods "" [] s in
    mk_id mods n
End

Definition dest_Short_def:
  dest_Short (Short s) = SOME s ∧
  dest_Short _ = NONE
End

(* by convention tyOps will be capitalised alpha-idents, or "->",
   and tyVars will be lower-case alpha-idents.

   The tyTup constructor should never be applied to a singleton list
*)
Datatype:
  tyAST = tyOp long_name (tyAST list)
        | tyVar string
        | tyTup (tyAST list)
End

Overload boolTy = “tyOp (Short "Bool") []”;
Overload intTy = “tyOp (Short "Integer") []”
Overload listTy = “λty. tyOp (Short "[]") [ty]”
Overload funTy = “λd r. tyOp (Short "Fun") [d; r]”

Datatype:
  litAST = litInt int | litString string
End

Datatype:
  patAST = patVar string
         | patApp long_name (patAST list)
         | patTup (patAST list)
         | patLit litAST
         | patUScore
End

Datatype:
  expAST = expVar long_name
         | expCon long_name (expAST list)
         | expOp pure_config$atom_op (expAST list)
         | expTup (expAST list)
         | expApp expAST expAST
         | expAbs patAST expAST
         | expIf expAST expAST expAST
         | expLit litAST
         | expLet (expdecAST list) expAST
         | expDo (expdostmtAST list) expAST
         | expCase expAST ((patAST # expAST) list);
  expdecAST = expdecTysig string tyAST
            | expdecPatbind patAST expAST
            | expdecFunbind string (patAST list) expAST ;
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

val _ = add_strliteral_form {ldelim = "‹", inj = “expVar”}
Overload pNIL = “expCon (Short "[]") []”
Overload pCONS = “λe1 e2. expCon (Short "::") [e1;e2]”
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
  declAST = declTysig string tyAST
          | declData string (string list)
                     ((string # tyAST list) list)
          | declFunbind string (patAST list) expAST
          | declPatbind patAST expAST
End

Datatype:
  importAST = import (string list)
End

Datatype:
  moduleAST = module (string list) (importAST list) (declAST list)
End


val _ = export_theory();
