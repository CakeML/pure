open HolKernel Parse boolLib bossLib;

open pureASTTheory mlmapTheory pure_cexpTheory mlstringTheory
open pairTheory optionTheory pure_typingTheory

val _ = new_theory "ast_to_cexp";

val _ = set_grammar_ancestry ["pureAST", "mlmap", "pure_cexp", "pure_typing"]

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

Definition build_tyinfo_def:
  build_tyinfo A [] = A ∧
  build_tyinfo A (d :: ds) =
  case d of
    declData opnm args cons =>
      build_tyinfo (insert A (implode opnm) (args, MAP (implode ## I) cons)) ds
  | _ => build_tyinfo A ds
End

Definition translate_patcase_def:
  translate_patcase tyinfo pnm pat rhs = ARB
End

Definition find_unused_siblings_def:
  find_unused_siblings tyi [] = NONE ∧
  find_unused_siblings tyi (cnm :: rest) =
  let foldthis tynm (opargs, cons) Aopt =
      case Aopt of
      | SOME _ => Aopt
      | NONE => if MEM cnm (MAP FST cons) then
                  SOME (MAP
                        (λ(cnm',args). (cnm', LENGTH args))
                        (FILTER (λ(cnm', args). ¬MEM cnm' (cnm :: rest)) cons))
                else NONE
  in
    mlmap$foldrWithKey foldthis NONE tyi
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

Overload If = “λl g t e. Case l g «» [(«True», [], t); («False», [], e)] NONE”

Definition dest_pvar_def[simp]:
  dest_pvar (patVar s) = SOME (implode s) ∧
  dest_pvar _ = NONE
End

Definition translate_headop_def:
  (translate_headop (Var l s) =
   let opopt =
       if strlen s = 1 then
         case strsub s 0 of
         | #"+" => SOME Add
         | #"-" => SOME Sub
         | #"*" => SOME Mul
         | _ => NONE
       else if s = «==» then SOME Eq
       else NONE
   in
     case opopt of
       NONE => App l (Var l s)
     | SOME op => Prim l (AtomOp op)) ∧
  translate_headop e = App () e (* forces unit *)
End

Definition dest_patVar_def:
  dest_patVar (patVar s) = SOME (implode s) ∧
  dest_patVar _ = NONE
End

Definition translate_pat_def:
  translate_pat (patTup pvs) =
  do
    vs <- OPT_MMAP dest_patVar pvs ;
    SOME («», vs)
  od ∧
  translate_pat (patApp s pvs) =
  do
    vs <- OPT_MMAP dest_patVar pvs ;
    SOME (implode s, vs)
  od ∧
  translate_pat _ = NONE
End

Definition mkLam_def:
  mkLam d [] e = e ∧
  mkLam d vs e = Lam d vs e
End

Overload Bind = “λa1 a2. pure_cexp$Prim () (Cons «Bind») [a1;a2]”
Definition translate_exp_def:
  translate_exp tyinfo (expVar s) = SOME (Var () (implode s)) ∧
  translate_exp tyinfo (expCon s es) =
  do
    rs <- OPT_MMAP (translate_exp tyinfo) es;
    SOME (Prim () (Cons (implode s)) rs)
  od ∧
  translate_exp tyinfo (expOp op es) =
  do
    rs <- OPT_MMAP (translate_exp tyinfo) es;
    return (Prim () (AtomOp op) rs)
  od ∧
  translate_exp tyinfo (expTup es) =
  do
    rs <- OPT_MMAP (translate_exp tyinfo) es;
    SOME (Prim () (Cons «») rs)
  od ∧
  translate_exp tyinfo (expApp fe xe) =
  do
    (fe0, es) <<- strip_comb fe ;
    f <- translate_exp tyinfo fe0 ;
    lhs <<- translate_headop f;
    args <- OPT_MMAP (translate_exp tyinfo) (es ++ [xe]) ;
    SOME (lhs args)
  od ∧
  (translate_exp tyinfo (expAbs p e) =
   case p of
     patVar n => do
                  body <- translate_exp tyinfo e ;
                  SOME (Lam () [implode n] body)
                od
   | _ => do
           ce <- translate_patcase tyinfo «» p e;
           SOME (Lam () [«»] ce)
         od) ∧
  (translate_exp tyinfo (expIf g t e) =
   do
     gc <- translate_exp tyinfo g ;
     tc <- translate_exp tyinfo t ;
     ec <- translate_exp tyinfo e ;
     SOME (If () gc tc ec)
   od) ∧
  (translate_exp tyinfo (expLit (litInt i)) =
   SOME (Prim () (AtomOp (Lit (Int i))) [])) ∧
  (translate_exp tyinfo (expLit (litString s)) =
   SOME (Prim () (AtomOp (Lit (Str s))) [])) ∧
  (translate_exp tyinfo (expLet decs body) =
   do
     recbinds <- translate_edecs tyinfo decs ;
     bodyce <- translate_exp tyinfo body;
     SOME (Letrec () recbinds bodyce)
   od) ∧
  (translate_exp tyinfo (expCase ge pats) =
   do
     assert (pats ≠ []);
     g <- translate_exp tyinfo ge;
     (pats',usopt) <<-
        case LAST pats of
          (patUScore, ue) => (FRONT pats, SOME ue)
        | _ => (pats, NONE) ;
     pes <- OPT_MMAP (λ(p_e,rhs_e). do
                                      (conname, conargs) <- translate_pat p_e ;
                                      rhs <- translate_exp tyinfo rhs_e ;
                                      return (conname, conargs, rhs)
                                    od)
                     pats' ;
     (ceopt : ((mlstring # num) list # unit cexp) option) <-
       case usopt of
         NONE => return NONE
       | SOME us_e => do e <- translate_exp tyinfo us_e ;
                         unused <- find_unused_siblings tyinfo (MAP FST pes) ;
                         return (SOME (unused, e))
                      od ;
     return (pure_cexp$Case () g «» pes ceopt)
   od) ∧
  (translate_exp tyinfo (expDo dostmts finalexp) =
   (* see https://www.haskell.org/onlinereport/haskell2010/haskellch3.html
      section 3.14 *)
   case dostmts of
   | [] => translate_exp tyinfo finalexp
   | expdostmtExp ee :: reste =>
       do
         e <- translate_exp tyinfo ee;
         rest <- translate_exp tyinfo (expDo reste finalexp) ;
         return (Bind e $ Lam () [«»] rest)
       od
   | expdostmtBind pe ee :: reste =>
       do
         case pe of
         | patVar n =>
             do
               e <- translate_exp tyinfo ee ;
               rest <- translate_exp tyinfo (expDo reste finalexp) ;
               return (Bind e $ Lam () [implode n] rest)
             od
         | patUScore =>
             do
               e <- translate_exp tyinfo ee ;
               rest <- translate_exp tyinfo (expDo reste finalexp) ;
               return (Bind e $ Lam () [«»] rest)
             od
         | _ => NONE (*
             do
               e <- translate_exp tyinfo ee ;
               rest <- translate_exp tyinfo (expDo reste finalexp) ;
               Let () «» (Lam () « 1»
                          (NestedCase
                            ()
                            (Var () « 1»)
                            « 2»


               ce <- translate_patcase tyinfo «» p rest;
           SOME (Lam () [«»] ce) *)
         od
   | expdostmtLet decs :: reste =>
       do
         recbinds <- translate_edecs tyinfo decs ;
         rest <- translate_exp tyinfo (expDo reste finalexp);
         SOME (Letrec () recbinds rest)
       od) ∧

  (translate_edecs tyinfo [] = SOME []) ∧
  (translate_edecs tyinfo (d :: ds) =
   do
     rest <- translate_edecs tyinfo ds ;
     case d of
       expdecTysig _ _ => SOME rest
     | expdecPatbind (patVar s) e =>
         do
           ce <- translate_exp tyinfo e ;
           SOME ((implode s, ce) :: rest)
         od
     | expdecPatbind _ _ => NONE
     | expdecFunbind s args body =>
         do
           vs <- OPT_MMAP dest_pvar args ;
           bce <- translate_exp tyinfo body ;
           SOME ((implode s, mkLam () vs bce) :: rest)
         od
   od)
Termination
  WF_REL_TAC
  ‘measure (λs. case s of
                  INL (_, e) => pureAST$expAST_size e
                | INR (_, ds) => list_size expdecAST_size ds)’ >>
  rw[] >> simp[] >>
  rpt (qpat_x_assum ‘_ = strip_comb _’ (assume_tac o SYM)) >>~-
  ([‘strip_comb’],
   drule_then strip_assume_tac strip_comb_reduces_size >> simp[] >>
   first_x_assum drule >> simp[]) >~
  [‘OPT_MMAP’]
  >- (gvs[AllCaseEqs()] >> rename [‘LAST pats’] >> Cases_on ‘pats’ >> gvs[] >>
      rename [‘LAST (pe::pes) = (patUScore, e)’] >>
      ‘MEM (patUScore, e) (pe::pes)’ by metis_tac[rich_listTheory.MEM_LAST] >>
      pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
      qspec_tac (‘pe::pes’, ‘pes’) >> Induct_on ‘pes’ >>
      simp[expAST_size_def, FORALL_PROD, DISJ_IMP_THM, FORALL_AND_THM] >>
      rpt strip_tac >> gs[]) >>
  rename [‘MEM (p_e, rhs_e) pats'’, ‘LAST pats’] >>
  ‘MEM (p_e, rhs_e) pats’
    by (gvs[AllCaseEqs()] >> Cases_on ‘pats’ >> gvs[] >>
        drule rich_listTheory.MEM_FRONT >> simp[]) >>
  pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
  Induct_on ‘pats’ >>
  simp[expAST_size_def, FORALL_PROD, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >> gs[]
End

Definition translate_expl_def[simp]:
  translate_expl tyi [] = SOME [] ∧
  translate_expl tyi (h::t) =
  do
    e <- translate_exp tyi h ;
    es <- translate_expl tyi t ;
    return (e::es)
  od
End

Theorem OPT_MMAP_translate_exp[local]:
  OPT_MMAP (translate_exp tyi) = translate_expl tyi
Proof
  simp[FUN_EQ_THM] >> Induct >> simp[]
QED

Theorem translate_this_translate_exp =
        SRULE [SF ETA_ss, OPT_MMAP_translate_exp] translate_exp_def

(* passes over declarations; ignoring type annotations because they're
   not handled; and ignoring datatype declarations because they've already
   been extracted
 *)
Definition translate_decs_def:
  translate_decs tyinfo [] = SOME [] ∧
  translate_decs tyinfo (declTysig _ _ :: ds) = translate_decs tyinfo ds ∧
  translate_decs tyinfo (declData _ _ _  :: ds) = translate_decs tyinfo ds ∧
  translate_decs tyinfo (declFunbind s args body :: ds) =
  do
    rest <- translate_decs tyinfo ds ;
    vs <- OPT_MMAP dest_pvar args ;
    bce <- translate_exp tyinfo body ;
    SOME ((implode s, mkLam () vs bce) :: rest)
  od ∧
  translate_decs tyinfo (declPatbind p e :: ds) =
  do
    rest <- translate_decs tyinfo ds ;
    v <- dest_pvar p ;
    ce <- translate_exp tyinfo e ;
    SOME ((v,ce) :: rest)
  od
End

Definition uniq_prefix_def:
  uniq_prefix pfx slist =
  case FILTER (λs. pfx ≼ s) slist of
    [] => pfx
  | bads => uniq_prefix (pfx ++ "%") bads
Termination
  WF_REL_TAC ‘measure (λ(p,l). 1 + SUM (MAP LENGTH l) - LENGTH p)’ >> rw[] >>
  gvs[listTheory.FILTER_EQ_CONS] >> rename [‘pfx ≼ s’] >>
  ‘∃sfx. s = pfx ++ sfx’ by metis_tac[rich_listTheory.IS_PREFIX_APPEND] >>
  gvs[listTheory.SUM_APPEND] >>
  qmatch_abbrev_tac ‘SUM (MAP LENGTH (FILTER P ll)) + 1 < _’ >>
  ‘SUM (MAP LENGTH (FILTER P ll)) ≤ SUM (MAP LENGTH ll)’
    suffices_by simp[] >>
  rpt (pop_assum kall_tac) >> qid_spec_tac ‘ll’ >> Induct >> rw[]
End

Theorem uniq_prefix_prefix:
  ∀p ss. p ≼ uniq_prefix p ss
Proof
  recInduct uniq_prefix_ind >> rw[] >> simp[Once uniq_prefix_def] >>
  BasicProvers.TOP_CASE_TAC >> gs[] >>
  irule rich_listTheory.IS_PREFIX_TRANS >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem uniq_prefix_correct:
  ∀p ss sfx. ¬MEM (uniq_prefix p ss ++ sfx) ss
Proof
  recInduct uniq_prefix_ind >> rw[] >>
  simp[Once uniq_prefix_def] >> rename [‘FILTER _ strings’] >>
  Cases_on ‘FILTER (λs. pfx ≼ s) strings’ >> simp[]
  >- (gvs[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
      strip_tac >> first_x_assum drule >> simp[]) >>
  gvs[listTheory.FILTER_EQ_CONS] >>
  qmatch_abbrev_tac ‘¬MEM (UP ++ sfx) l1 ∧ ¬MEM (UP ++ sfx) l2’ >>
  ‘∀sfx. pfx ≼ UP ++ sfx’
    by (strip_tac >> irule rich_listTheory.IS_PREFIX_TRANS >>
        irule_at Any rich_listTheory.IS_PREFIX_APPEND3 >>
        irule rich_listTheory.IS_PREFIX_TRANS >> simp[Abbr‘UP’] >>
        irule_at Any rich_listTheory.IS_PREFIX_APPEND3 >>
        irule_at Any uniq_prefix_prefix) >>
  rpt strip_tac
  >- (gvs[listTheory.EVERY_MEM, listTheory.FILTER_EQ_NIL] >>
      first_x_assum drule >> simp[]) >>
  gvs[FORALL_AND_THM, listTheory.MEM_FILTER]
QED

(* nm_map maps type-operator names to their indices in the typing
   signature/map; the arg_map maps type variables (the vector vs after
   something like data Op vs = ...) into integers
 *)

Definition translate_type_def:
  translate_type nm_map arg_map (tyOp s tys) =
  (if s = "Fun" then
     do
       assert (LENGTH tys = 2);
       dty <- oHD tys ;
       rty <- oEL 1 tys ;
       d <- translate_type nm_map arg_map dty;
       r <- translate_type nm_map arg_map rty;
       return (pure_typing$Function d r)
     od
   else if s = "Bool" then do assert (tys = []); return $ PrimTy Bool; od
   else if s = "Integer" then do assert (tys = []); return $ PrimTy Integer od
   else if s = "String" then do assert (tys = []); return $ PrimTy String od
   else if s = "M" then do assert (LENGTH tys = 1);
                           t <- translate_type nm_map arg_map (HD tys);
                           return $ M t;
                        od
   else if s = "Array" then do assert (LENGTH tys = 1);
                               t <- translate_type nm_map arg_map (HD tys);
                               return $ Array t;
                            od
   else
     do
       opidx <- lookup nm_map (implode s) ;
       args <- OPT_MMAP (translate_type nm_map arg_map) tys ;
       return $ TypeCons opidx args
     od) ∧

  translate_type nm_map arg_map (tyVar s) =
  do
    varidx <- lookup arg_map (implode s);
    return $ TypeVar varidx
  od ∧

  translate_type nm_map arg_map (tyTup tys) =
  do
    args <- OPT_MMAP (translate_type nm_map arg_map) tys;
    return $ Tuple args;
  od
Termination
  WF_REL_TAC ‘measure (λ(_,_,ty). tyAST_size ty)’ >> rw[] >>
  rename [‘LENGTH tys = _’] >> Cases_on ‘tys’ >> gvs[tyAST_size_def] >>
  rename [‘LENGTH tys = _’] >> Cases_on ‘tys’ >>
  gvs[tyAST_size_def, listTheory.oEL_def]
End

(* for translator's sake *)
Definition translate_typel_def[simp]:
  translate_typel nm_map arg_map [] = SOME [] ∧
  translate_typel nm_map arg_map (h::t) =
  do
    ty <- translate_type nm_map arg_map h ;
    tys <- translate_typel nm_map arg_map t ;
    return (ty::tys)
  od
End

Theorem OPT_MMAP_translate_type:
  OPT_MMAP (translate_type nm_map arg_map) =
  translate_typel nm_map arg_map
Proof
  simp[FUN_EQ_THM] >> Induct >> simp[]
QED

Theorem translate_this_translate_type =
  SRULE [OPT_MMAP_translate_type, SF ETA_ss] translate_type_def


Overload str_compare = “mlstring$compare”

(*  (n (* idx *),
     [(mlstring (* con-name *),
       [pure_typing$type] (* con arg-types *))])
 *)

Definition MFOLDL_def:
  MFOLDL f [] A = SOME A ∧
  MFOLDL f (h::t) A =
  do
    A' <- f h A ;
    MFOLDL f t A'
  od
End

Definition build_tysig1_def:
  build_tysig1 nm_map (opname, (vs, cons)) sig =
  do
    (arg_map, numvs) <<-
      FOLDL (λ(m,i) v. (mlmap$insert m (implode v) i, i + 1))
            (empty str_compare, 0n)
            vs;
    coninfo <-
       let
         mapthis (c, tys) =
         do
           tys' <- OPT_MMAP (translate_type nm_map arg_map) tys;
           return (c, tys') ;
         od
       in
         OPT_MMAP mapthis cons;
    return ((numvs, coninfo) :: sig)
  od
End

Definition listinfo_def:
  listinfo = (["a"], [(«[]», []); («::», [tyVar "a"; tyOp "[]" [tyVar "a"]])])
End

Definition decls_to_letrec_def:
  decls_to_letrec ds =
  do
    tyinfo <<- build_tyinfo (empty str_compare) ds ;
    tyinfo_l <<- toAscList tyinfo ;
    (nm_map, nops) <<- FOLDL (λ(m,i) (opn, info). (insert m opn i, i + 1))
                             (insert (empty str_compare) «[]» 0n, 1)
                             tyinfo_l ;
    sig0 <- MFOLDL (build_tysig1 nm_map) tyinfo_l (SND initial_namespace) ;
    binds <- translate_decs (insert tyinfo «[]» listinfo) ds ;
    SOME (Letrec () binds (Var () «main»), REVERSE sig0)
  od
End


val _ = export_theory();
