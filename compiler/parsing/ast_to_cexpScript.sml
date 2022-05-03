open HolKernel Parse boolLib bossLib;

open pureASTTheory mlmapTheory pure_cexpTheory mlstringTheory

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

Definition dest_pvar_def[simp]:
  dest_pvar (patVar s) = SOME s ∧
  dest_pvar _ = NONE
End

Definition translate_headop_def:
  (translate_headop (Var l s) =
   case s of
   | "+" => Prim l (AtomOp Add)
   | "-" => Prim l (AtomOp Sub)
   | "*" => Prim l (AtomOp Mul)
   | "==" => Prim l (AtomOp Eq)
   | _ => App l (Var l s)) ∧
  translate_headop e = App () e (* forces unit *)
End

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
    lhs <<- translate_headop f;
    args <- OPT_MMAP (translate_exp conmap) (es ++ [xe]) ;
    SOME (lhs args)
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
   SOME (Prim () (AtomOp (Lit (Int i))) [])) ∧
  (translate_exp conmap (expLet decs body) =
   do
     recbinds <- translate_edecs conmap decs ;
     bodyce <- translate_exp conmap body;
     SOME (Letrec () recbinds bodyce)
   od) ∧
  (translate_edecs conmap [] = SOME []) ∧
  (translate_edecs conmap (d :: ds) =
   do
     rest <- translate_edecs conmap ds ;
     case d of
       expdecTysig _ _ => SOME rest
     | expdecPatbind (patVar s) e =>
         do
           ce <- translate_exp conmap e ;
           SOME ((s, ce) :: rest)
         od
     | expdecPatbind _ _ => NONE
     | expdecFunbind s args body =>
         do
           vs <- OPT_MMAP dest_pvar args ;
           bce <- translate_exp conmap body ;
           SOME ((s, Lam () vs bce) :: rest)
         od
   od)
Termination
  WF_REL_TAC
  ‘measure (λs. case s of
                  INL (_, e) => pureAST$expAST_size e
                | INR (_, ds) => list_size expdecAST_size ds)’ >>
  rw[] >> simp[] >>
  rpt (qpat_x_assum ‘_ = strip_comb _’ (assume_tac o SYM)) >>
  drule_then strip_assume_tac strip_comb_reduces_size >> simp[] >>
  first_x_assum drule >> simp[]
End

(* passes over declarations; ignoring type annotations because they're
   not handled; and ignoring datatype declarations because they've already
   been extracted into the conmap
 *)
Definition translate_decs_def:
  translate_decs conmap [] = SOME [] ∧
  translate_decs conmap (declTysig _ _ :: ds) = translate_decs conmap ds ∧
  translate_decs conmap (declData _ _ _  :: ds) = translate_decs conmap ds ∧
  translate_decs conmap (declFunbind s args body :: ds) =
  do
    rest <- translate_decs conmap ds ;
    vs <- OPT_MMAP dest_pvar args ;
    bce <- translate_exp conmap body ;
    SOME ((s, Lam () vs bce) :: rest)
  od ∧
  translate_decs conmap (declPatbind p e :: ds) =
  do
    rest <- translate_decs conmap ds ;
    v <- dest_pvar p ;
    ce <- translate_exp conmap e ;
    SOME ((v,ce) :: rest)
  od
End

Overload str_compare = “ternaryComparisons$list_compare string$char_compare”

Definition decls_to_letrec_def:
  decls_to_letrec ds =
  do
    conmap <<- build_conmap (mlmap$empty str_compare) ds ;
    binds <- translate_decs conmap ds ;
    SOME (Letrec () binds (App () (Var () "main") [Prim () (Cons "") []]))
  od
End



val _ = export_theory();
