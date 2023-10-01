open HolKernel Parse boolLib bossLib dep_rewrite BasicProvers;

open pairTheory optionTheory listTheory pred_setTheory finite_mapTheory
open pureASTTheory mlmapTheory pure_cexpTheory mlstringTheory
     pure_typingTheory pure_varsTheory

val _ = new_theory "ast_to_cexp";

val _ = set_grammar_ancestry [
          "pureAST", "mlmap", "pure_cexp", "pure_typing", "pure_vars"]

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
         | #"<" => SOME Lt
         | #">" => SOME Gt
         | _ => NONE
       else if s = «==» then SOME Eq
       else if s = «div» then SOME Div
       else if s = «mod» then SOME Mod
       else NONE
   in
     case opopt of
       NONE => if s = «seq» then Prim l Seq else App l (Var l s)
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
     assert (¬NULL pats);
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
   else if s = "IO" then do assert (LENGTH tys = 1);
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

(********** closedness and well-formedness **********)

(* unused *)
Definition freevars_cexp_impl_def:
  freevars_cexp_impl (Var c v) = insert empty v () ∧
  freevars_cexp_impl (Prim c op es) = freevars_cexp_impl_l es ∧
  freevars_cexp_impl (App c e es) =
    union (freevars_cexp_impl e) (freevars_cexp_impl_l es) ∧
  freevars_cexp_impl (Lam c vs e) = list_delete (freevars_cexp_impl e) vs ∧
  freevars_cexp_impl (Let c v e1 e2) =
    union (freevars_cexp_impl e1) (delete (freevars_cexp_impl e2) v) ∧
  freevars_cexp_impl (Letrec c fns e) = (
    let (fs, bodies) = UNZIP fns in
    list_delete (union (freevars_cexp_impl e) (freevars_cexp_impl_l bodies)) fs) ∧

  freevars_cexp_impl (Case c e v css eopt) = (
    let css_vars =
        (FOLDL (λacc (cn,vs,e).
          union acc (list_delete (freevars_cexp_impl e) vs)) empty css) in
    let e_css_vars = union (freevars_cexp_impl e) (delete css_vars v) in
    case eopt of
    | NONE => e_css_vars
    | SOME (a,e) => union (delete (freevars_cexp_impl e) v) e_css_vars) ∧

  freevars_cexp_impl_l [] = empty ∧
  freevars_cexp_impl_l (e::es) = union (freevars_cexp_impl e) (freevars_cexp_impl_l es)
Termination
  WF_REL_TAC `measure (λs. case s of
    | INL e => cexp_size (K 0) e
    | INR l => list_size (cexp_size (K 0)) l)` >>
  ntac 2 gen_tac >> Induct >> rw[cexp_size_def] >> gvs[list_size_def] >>
  Cases_on `UNZIP fns` >> PairCases_on `h` >> gvs[cexp_size_def]
End

Theorem freevars_cexp_impl:
  (∀(e:'a cexp) s. freevars_cexp_impl e = s ∧ NestedCase_free e ⇒
    map_ok s ∧ cmp_of s = var_cmp ∧ FDOM (to_fmap s) = freevars_cexp e) ∧
  (∀(es:'a cexp list) s. freevars_cexp_impl_l es = s ∧ EVERY NestedCase_free es ⇒
    map_ok s ∧ cmp_of s = var_cmp ∧
    FDOM (to_fmap s) = BIGUNION (set (MAP freevars_cexp es)))
Proof
  ho_match_mp_tac freevars_cexp_impl_ind >> rw[] >>
  gvs[freevars_cexp_impl_def, NestedCase_free_def, UNZIP_MAP, SF ETA_ss] >>
  every_case_tac >> gvs[] >>
  gvs[insert_thm, union_thm, delete_thm, list_delete_thm] >>
  gvs[pure_miscTheory.FDOM_FDIFF_alt]
  >- simp[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY] >>
  `map_ok (FOLDL (λacc (cn,vs,e').
    union acc $ list_delete (freevars_cexp_impl e') vs) empty css) ∧
   cmp_of (FOLDL (λacc (cn,vs,e').
    union acc $ list_delete (freevars_cexp_impl e') vs) empty css)
    = var_cmp` by (
    qabbrev_tac `foo = (empty : var_set)` >>
    `map_ok foo ∧ cmp_of foo = var_cmp` by (unabbrev_all_tac >> gvs[]) >>
    ntac 2 $ pop_assum mp_tac >> pop_assum kall_tac >>
    qid_spec_tac `foo` >> Induct_on `css` >> gvs[] >>
    ntac 2 (gen_tac >> ntac 2 strip_tac) >>
    last_x_assum irule >> PairCases_on `h` >> gvs[] >>
    simp[union_thm, list_delete_thm] >> gvs[DISJ_IMP_THM, FORALL_AND_THM]) >>
  DEP_REWRITE_TAC[cj 1 union_thm, cj 2 union_thm, cj 3 union_thm] >> simp[] >>
  DEP_REWRITE_TAC[cj 1 delete_thm, cj 2 delete_thm, cj 3 union_thm] >> simp[] >>
  qsuff_tac
    `∀foo:var_set. map_ok foo ∧ cmp_of foo = var_cmp ⇒
      FDOM (to_fmap (FOLDL (λacc (cn,vs,e').
        union acc $ list_delete (freevars_cexp_impl e') vs) foo css)) =
      BIGUNION (set (MAP (λ(_,vs,ec). freevars_cexp ec DIFF set vs) css)) ∪
        FDOM (to_fmap foo)` >>
  simp[UNION_DELETE, AC UNION_ASSOC UNION_COMM] >>
  ntac 2 $ pop_assum kall_tac >> Induct_on `css` >> rw[] >>
  PairCases_on `h` >> gvs[] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  last_x_assum drule >>
  disch_then $ qspec_then
    `union foo $ list_delete (freevars_cexp_impl h2) h1` mp_tac >>
  simp[union_thm, list_delete_thm] >> strip_tac >>
  simp[pure_miscTheory.FDOM_FDIFF_alt, AC UNION_ASSOC UNION_COMM]
QED

Definition cepat_vars_impl_def:
  cepat_vars_impl cepatUScore = empty ∧
  cepat_vars_impl (cepatVar v) = insert empty v () ∧
  cepat_vars_impl (cepatCons s ps) = cepat_vars_impl_l ps ∧

  cepat_vars_impl_l [] = empty ∧
  cepat_vars_impl_l (p::ps) = union (cepat_vars_impl p) (cepat_vars_impl_l ps)
End

Definition contains_def:
  contains (s:var_set) v = (lookup s v = SOME ())
End

Definition closed_under_def:
  closed_under vs (Var c v) = contains vs v ∧
  closed_under vs (Prim c op es) = EVERY (closed_under vs) es ∧
  closed_under vs (App c e es) = (closed_under vs e ∧ EVERY (closed_under vs) es) ∧
  closed_under vs (Lam c xs e) = closed_under (list_insert_set vs xs) e ∧
  closed_under vs (Let c x e1 e2) =
    (closed_under vs e1 ∧ closed_under (insert vs x ()) e2) ∧
  closed_under vs (Letrec c fns e) = (
    let (fs, bodies) = UNZIP fns in
    let vs' = list_insert_set vs fs in
    closed_under vs' e ∧ EVERY (closed_under vs') bodies) ∧

  closed_under vs (Case c e v css eopt) = (
    closed_under vs e ∧
    let vs' = insert vs v () in
    EVERY (λ(cn,pvs,e). closed_under (list_insert_set vs' pvs) e) css ∧
    case eopt of
    | NONE => T
    | SOME (a,e) => closed_under vs' e) ∧

  closed_under vs (NestedCase c g gv p e pes) = (
    closed_under vs g ∧
    let vs' = insert vs gv () in
    EVERY (λ(pat,e).
      closed_under (mlmap$union (cepat_vars_impl pat) vs') e) ((p,e)::pes))
Termination
  WF_REL_TAC `measure $ cexp_size (K 0) o SND` >>
  gvs[UNZIP_MAP, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> conj_tac >> gen_tac >>
  Induct >> rw[] >> gvs[cexp_size_def] >> res_tac >> simp[] >>
  first_x_assum $ qspecl_then [`p`,`gv`,`e`] assume_tac >> gvs[]
End

Theorem cepat_vars_impl:
  (∀p m. cepat_vars_impl p = m ⇒
    map_ok m ∧ cmp_of m = var_cmp ∧ FDOM (to_fmap m) = cepat_vars p) ∧
  (∀ps m. cepat_vars_impl_l ps = m ⇒
    map_ok m ∧ cmp_of m = var_cmp ∧
    FDOM (to_fmap m) = BIGUNION (set (MAP cepat_vars ps)))
Proof
  Induct >> rw[] >> gvs[cepat_vars_impl_def, SF ETA_ss] >>
  gvs[insert_thm, union_thm]
QED

Theorem closed_under:
  ∀m e. map_ok m ∧ cmp_of m = var_cmp ⇒
  closed_under m e = (freevars_cexp e ⊆ FDOM (to_fmap m))
Proof
  recInduct closed_under_ind >> rw[closed_under_def, contains_def] >>
  gvs[union_thm, lookup_thm, insert_thm, list_insert_set_thm, FDOM_FUPDATE_LIST] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, UNZIP_MAP] >>
  gvs[pure_miscTheory.DIFF_SUBSET, SUBSET_INSERT_DELETE] >>
  gvs[AC UNION_ASSOC UNION_COMM]
  >- gvs[FLOOKUP_DEF]
  >- (Induct_on `es` >> rw[])
  >- (AP_TERM_TAC >> Induct_on `es` >> rw[])
  >- (
    AP_TERM_TAC >> rename1 `list_insert_set _ fs` >>
    Induct_on `fns` >> rw[] >> PairCases_on `h` >> gvs[]
    )
  >- (
    AP_TERM_TAC >> CASE_TAC
    >- (
      Induct_on `css` >> rw[] >> PairCases_on `h` >> gvs[] >>
      gvs[GSYM SUBSET_INSERT_DELETE, pure_miscTheory.DIFF_SUBSET] >> metis_tac[]
      )
    >- (
      CASE_TAC >> gvs[GSYM SUBSET_INSERT_DELETE] >>
      simp[Once CONJ_SYM] >> AP_TERM_TAC >>
      Induct_on `css` >> rw[] >> PairCases_on `h` >> gvs[] >>
      gvs[pure_miscTheory.DIFF_SUBSET] >> metis_tac[]
      )
    )
  >- (
    AP_TERM_TAC >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    qspec_then `p` assume_tac $ cj 1 cepat_vars_impl >> gvs[union_thm, insert_thm] >>
    gvs[GSYM SUBSET_INSERT_DELETE, pure_miscTheory.DIFF_SUBSET] >> AP_TERM_TAC >>
    Induct_on `pes` >> rw[] >> PairCases_on `h` >> gvs[] >>
    qspec_then `h0` assume_tac $ cj 1 cepat_vars_impl >> gvs[union_thm, insert_thm] >>
    gvs[GSYM SUBSET_INSERT_DELETE, pure_miscTheory.DIFF_SUBSET]
    )
QED

Definition monad_cn_mlstrings_def:
  monad_cn_mlstrings =
    [«Ret»;«Bind»;«Raise»;«Handle»;«Alloc»;«Length»;«Deref»;«Update»;«Act»]
End

Triviality implodeEQ:
  y = implode x ⇔ (explode y = x)
Proof
  rw[EQ_IMP_THM] >> simp[]
QED

Triviality MEM_monad_cn_mlstrings:
  MEM x monad_cn_mlstrings ⇔ explode x ∈ monad_cns
Proof
  rw[monad_cn_mlstrings_def, pure_configTheory.monad_cns_def] >>
  simp[SRULE [mlstringTheory.implode_def] implodeEQ]
QED

Theorem cexp_wf_alt_def[compute]:
  (∀v0 v. cexp_wf (Var v0 v) ⇔ T) ∧
  (∀v1 op es.
    cexp_wf (Prim v1 op es) ⇔
    num_args_ok op (LENGTH es) ∧ EVERY (λa. cexp_wf a) es ∧
    (case op of
     | AtomOp (Lit (Int i)) => T
     | AtomOp (Lit (Str s)) => T
     | AtomOp (Lit _) => F
     | AtomOp (Message m) => m ≠ ""
     | _ => T)) ∧
  (∀v2 es e.
    cexp_wf (App v2 e es) ⇔
    cexp_wf e ∧ EVERY (λa. cexp_wf a) es ∧ ¬ NULL es) ∧
  (∀vs v3 e. cexp_wf (Lam v3 vs e) ⇔ cexp_wf e ∧ ¬ NULL vs) ∧
  (∀v4 v e2 e1. cexp_wf (Let v4 v e1 e2) ⇔ cexp_wf e1 ∧ cexp_wf e2) ∧
  (∀v5 fns e.
    cexp_wf (Letrec v5 fns e) ⇔
    EVERY (λa. cexp_wf a) (MAP SND fns) ∧ cexp_wf e ∧ ¬ NULL fns) ∧
  (∀v6 v eopt e css.
    cexp_wf (Case v6 e v css eopt) ⇔
    cexp_wf e ∧ EVERY (λa. cexp_wf a) (MAP (SND ∘ SND) css) ∧ ¬ NULL css ∧
    EVERY ALL_DISTINCT (MAP (FST ∘ SND) css) ∧
    OPTION_ALL
      (λ(a,e').
           ¬ NULL a ∧ cexp_wf e' ∧
           EVERY (λ(cn,_). ¬ MEM cn monad_cn_mlstrings) a) eopt ∧
    ¬MEM v (FLAT (MAP (FST ∘ SND) css)) ∧
    ALL_DISTINCT
      (MAP FST css ++ case eopt of NONE => [] | SOME (a,v2) => MAP FST a) ∧
    EVERY (λ(cn,_,_). ¬MEM cn monad_cn_mlstrings) css) ∧
  (∀v7 pes p gv g e.
   cexp_wf (NestedCase v7 g gv p e pes) ⇔
   cexp_wf g ∧ cexp_wf e ∧ EVERY (λa. cexp_wf a) (MAP SND pes) ∧
   ¬MEM gv (FLAT (MAP (cepat_vars_l ∘ FST) ((p,e)::pes))))
Proof
  rw[] >> simp[cexp_wf_def] >> gvs[NULL_EQ]
  >- (
    eq_tac >> rw[] >> gvs[] >>
    rpt (FULL_CASE_TAC >> gvs[])
    )
  >- (
    simp[MEM_monad_cn_mlstrings] >>
    gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD]
    )
QED

val _ = export_theory();
