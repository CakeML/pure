open HolKernel Parse boolLib bossLib;

open pureASTTheory mlmapTheory pure_cexpTheory

val _ = new_theory "ast_to_cexp";

val _ = set_grammar_ancestry ["pureAST", "mlmap", "pure_cexp"]

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

Definition build_conmap_def:
  build_conmap A [] = A ∧
  build_conmap A (d :: ds) =
  case d of
    declData _ _ cons =>
      build_conmap (FOLDL (λA (cnm,_). insert A cnm cons) A cons) ds
  | _ => build_conmap A ds
End

Definition translate_patcase_def:
  translate_patcase conmap pnm pat rhs = ARB

End

Theorem strip_comb_reduces_size:
  (∀e f es. strip_comb e = (f, es) ⇒
            expAST_size f ≤ expAST_size e ∧
            ∀e0. MEM e0 es ⇒ expAST_size e0 < expAST_size e)
Proof
  qmatch_abbrev_tac ‘P’ >>
  ‘P ∧ (∀d : expdecAST. T) ∧ (∀ds : expdostmtAST. T)’ suffices_by simp[] >>
  qunabbrev_tac ‘P’ >>
  Induct >> simp[strip_comb_def, expAST_size_eq] >>
  simp[expAST_size_def] >> rpt strip_tac >>
  rename [‘(I ## _) (strip_comb f) = (f0, es)’] >>
  Cases_on ‘strip_comb f’ >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Overload If = “λl g t e. Case l g ""
                            [("True", ["True"; "False"], t);
                             ("False", ["True"; "False"], e)]”

Definition translate_exp_def:
  translate_exp conmap (expVar s) = SOME (Var () s) ∧
  translate_exp conmap (expCon s es) =
  do
    rs <- OPT_MMAP (translate_exp conmap) es;
    SOME (Prim () (Cons s) rs)
  od ∧
  translate_exp conmap (expTup es) =
  do
    rs <- OPT_MMAP (translate_exp conmap) es;
    SOME (Prim () (Cons "") rs)
  od ∧
  translate_exp conmap (expApp fe xe) =
  do
    (fe0, es) <<- strip_comb fe ;
    f <- translate_exp conmap fe0 ;
    args <- OPT_MMAP (translate_exp conmap) (es ++ [xe]) ;
    SOME (App () f args)
  od ∧
  (translate_exp conmap (expAbs p e) =
   case p of
     patVar n => do
                  body <- translate_exp conmap e ;
                  SOME (Lam () [n] body)
                od
   | _ => do
           ce <- translate_patcase conmap "" p e;
           SOME (Lam () [""] ce)
         od) ∧
  (translate_exp conmap (expIf g t e) =
   do
     gc <- translate_exp conmap g ;
     tc <- translate_exp conmap t ;
     ec <- translate_exp conmap e ;
     SOME (If () gc tc ec)
   od) ∧
  (translate_exp conmap (expLit (litInt i)) =
   SOME (Prim () (AtomOp (Lit (Int i))) []))
Termination
  WF_REL_TAC ‘measure (pureAST$expAST_size o SND)’ >>
  rw[] >> simp[] >>
  rpt (qpat_x_assum ‘_ = strip_comb _’ (assume_tac o SYM)) >>
  drule_then strip_assume_tac strip_comb_reduces_size >> simp[] >>
  first_x_assum drule >> simp[]
End

val _ = export_theory();
